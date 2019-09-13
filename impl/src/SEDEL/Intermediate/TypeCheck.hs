{-# LANGUAGE FlexibleContexts, PatternGuards, NoImplicitPrelude, LambdaCase, OverloadedStrings #-}

module SEDEL.Intermediate.TypeCheck
  ( bidirect
  ) where

import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Protolude
import           Unbound.Generics.LocallyNameless
import           Unsafe


import           SEDEL.Common
import           SEDEL.Environment
import           SEDEL.PrettyPrint
import           SEDEL.Intermediate.Desugar
import           SEDEL.Intermediate.Subtyping
import           SEDEL.Intermediate.Syntax
import qualified SEDEL.Target.Syntax as T
import           SEDEL.Translations

-- | Kinding.
kind :: Fresh m => ICtx -> FType -> m (Maybe Kind)
kind d (TVar a) = return $ lookupTVarKindMaybe d a
kind _ NumT = return $ Just Star
kind _ BoolT = return $ Just Star
kind _ TopT = return $ Just Star
kind _ BotT = return $ Just Star
kind d (Arr t1 t2) = justStarIffAllHaveKindStar d [t1, t2]
kind d (And t1 t2) = justStarIffAllHaveKindStar d [t1, t2]
kind d (DForall b) = do
  ((a, _), t) <- unbind b
  kind (extendTVarCtx a Star d) t
kind d (SRecT _ t) = justStarIffAllHaveKindStar d [t]

{- |
    Δ,x::k1 ⊢ t :: k
    -------------------- (K-Abs)
    Δ ⊢ λx:k1. t :: k1 -> k
-}
kind d (OpAbs b) = do
  ((x, Embed k1), t) <- unbind b
  maybe_k <- kind (extendTVarCtx x k1 d) t
  case maybe_k of
    Nothing -> return Nothing
    Just k  -> return $ Just (KArrow k1 k)

{- |
    Δ ⊢ t1 :: k11 -> k12  Δ ⊢ t2 :: k11
    ------------------------------------ (K-App)
    Δ ⊢ t1 t2 :: k12
-}
kind d (OpApp t1 t2) = do
  maybe_k1 <- kind d t1
  maybe_k2 <- kind d t2
  case (maybe_k1, maybe_k2) of
    (Just (KArrow k11 k12), Just k2)
      | k2 == k11 -> return (Just k12)
    _ -> return Nothing



justStarIffAllHaveKindStar :: Fresh m => ICtx -> [FType] -> m (Maybe Kind)
justStarIffAllHaveKindStar d ts = do
  ps <- mapM (hasKindStar d) ts
  if and ps
    then return $ Just Star
    else return Nothing

hasKindStar :: Fresh m => ICtx -> FType -> m Bool
hasKindStar d t = do
  k <- kind d t
  return (k == Just Star)


---------------------------
-- Γ ⊢ e ⇒ A ~> E
---------------------------

bidirect :: FExpr -> ITcMonad (FType, T.UExpr)

{- |

Γ ⊢ ⊤ ⇒ ⊤  ~> ()

-}
bidirect Top = return (TopT, T.UUnit)

bidirect (LitV n) = return (NumT, T.ULitV n)

bidirect (BoolV b) = return (BoolT, T.UBoolV b)

{- |

   x:A ∈ Γ
---------------
Γ ⊢ x ⇒ A ~> x

-}
bidirect (Var x) = do
  t <- lookupVarTy x
  return (t, T.UVar (translate x)) -- Change the sort of a name

{- |

Γ ⊢ e ⇐ A  ~> E
------------------
Γ ⊢ e : A ⇒ A ~> E

-}
bidirect (Anno e a) = do
  c <- askCtx
  let a' = expandType c a
  e' <- tcheck e a'
  return (a, e')

{- |

Γ ⊢ e1 ⇒ A1 -> A2  ~> E1
Γ ⊢ e2 ⇐ A1        ~> E2
----------------------------
Γ ⊢ e1 e2 ⇒ A2     ~> E1 E2

-}
bidirect (App e1 e2) = do
  (arr, e1') <- bidirect e1
  c <- askCtx
  case expandType c arr of
    Arr a1 a2 -> do
      e2' <- tcheck e2 a1
      return (a2, T.UApp e1' e2')
    x -> errThrow [DS "Term application mismatch", DD x]

{- |

Γ ⊢ e ⇒ ∀(α ∗ B). C  ~> E
Γ ⊢ A
Γ ⊢ A ∗ B
-------------------------------
Γ ⊢ e A ⇒ [α := A] C  ~> E

-}
bidirect (TApp e a) = do
  wf a
  (t, e') <- bidirect e
  ctx <- askCtx
  case expandType ctx t of
    DForall t' -> do
      ((x, Embed b), c) <- unbind t'
      disjoint ctx (expandType ctx a) (expandType ctx b)
      return (subst x a c, e')
    _ -> errThrow [DS "FType application mismatch"]

{- |

Γ ⊢ e1 ⇒ A ~> E1
Γ ⊢ e2 ⇒ B ~> E2
Γ ⊢ A∗B
------------------------------
Γ ⊢ e1,,e2 ⇒ A&B ~> (E1, E2)

-}
bidirect (Merge e1 e2) = do
  (a, e1') <- bidirect e1
  (b, e2') <- bidirect e2
  ctx <- askCtx
  disjoint ctx (expandType ctx a) (expandType ctx b)
  return (And a b, T.UPair e1' e2')

{- |

Γ ⊢ e ⇒ A ~> E
----------------------
Γ ⊢{l=e} ⇒ {l:A} ~> E

-}
bidirect (Rec l e) = do
  (a, e') <- bidirect e
  return (SRecT l a, e')

{- |

Γ ⊢ e ⇒ {l : A} ~> E
----------------------
Γ ⊢ e.l ⇒ A ~> E

The above is what is shown in the paper. In the implementation, we'd like to
avoid annotating a record before projection. The following is the modified rule:

Γ ⊢ e ⇒ t ~> E
t • l = t1 ~> c
-----------------------
Γ ⊢ e.l ⇒ t1 ~> c E

-}

bidirect (Acc e l) = do
  (t, e') <- bidirect e
  ctx <- askCtx
  case select (expandType ctx t) l of
    [] -> errThrow [DS $ "Expected a record with label" <+> Pretty.squotes (Pretty.pretty l)]
    ls -> -- non-empty list, safe to use unsafe features
      let (tys, cs) = unzip ls
      in return
           ( unsafeFromJust (foldl1May And tys)
           , unsafeFromJust (foldl1May T.UPair (map (`T.UApp` e') cs)))


{- |


Γ ⊢ e ⇒ t ~> E
t \ l = t1 ~> c
-----------------------
Γ ⊢ e \ l ⇒ t1 ~> c E

-}

bidirect (Remove e l lt) = do
  (t, e') <- bidirect e
  ctx <- askCtx
  let t' = expandType ctx t
  case restrict t' l lt of
    Just (a, c) -> return (a, T.UApp c e')
    -- Silently... like nothing happened
    _ ->
      errThrow [DS $ "Expected a record with label" <+> Pretty.squotes (Pretty.pretty l)]


{- |

Γ ⊢ A
Γ , a * A ⊢ e ⇒ B ~> E
a fresh
---------------------------------
Γ ⊢ Λ(α∗A).e ⇒ ∀(α∗A).B ~> E

-}
bidirect (DLam t) = do
  ((x, Embed a), e) <- unbind t
  wf a
  (b, e') <- localCtx (extendConstrainedTVarCtx x a) $  bidirect e
  return (DForall (bind (x, embed a) b), e')

bidirect (PrimOp op e1 e2) =
  case op of
    Arith _ -> do
      e1' <- tcheck e1 NumT
      e2' <- tcheck e2 NumT
      return (NumT, T.UPrimOp op e1' e2')
    Logical _ -> do
      e1' <- tcheck e1 BoolT
      e2' <- tcheck e2 BoolT
      return (BoolT, T.UPrimOp op e1' e2')
    Comp cop | cop == Equ || cop == Neq -> do
      let res1 = do
            e1' <- tcheck e1 NumT
            e2' <- tcheck e2 NumT
            return (e1', e2')
          res3 = do
            e1' <- tcheck e1 BoolT
            e2' <- tcheck e2 BoolT
            return (e1', e2')
      (e1', e2') <- res1 `catchError` const res3
      return (BoolT, T.UPrimOp op e1' e2')
    Comp _ -> do
      e1' <- tcheck e1 NumT
      e2' <- tcheck e2 NumT
      return (BoolT, T.UPrimOp op e1' e2')

bidirect (If e1 e2 e3) = do
  e1' <- tcheck e1 BoolT
  (t2, e2') <- bidirect e2
  (t3, e3') <- bidirect e3
  ctx <- askCtx
  let t2' = expandType ctx t2
  let t3' = expandType ctx t3
  if aeq t2' t3'
    then return (t2, T.UIf e1' e2' e3')
    else return (TopT, T.UUnit)
    -- else errThrow [DS "If branch type mismatch"]

{- |

Γ, x:t ⊢ e1 ⇐ t ~> e1'
Γ, x:t ⊢ e2 ⇒ t' ~> e2'
-----------------------------------------------------
Γ ⊢ letrec x : t = e1 in e2 ⇒ t' ~> let x = e1' in e2'

Γ ⊢ e1 ⇒ t ~> e1'
Γ, x:t ⊢ e2 ⇒ t' ~> e2'
-----------------------------------------------------
Γ ⊢ let x = e1 in e2 ⇒ t' ~> let x = e1' in e2'

-}
bidirect (Letrec b) = do
  ((x, Embed ty), (e1, e2)) <- unbind b
  (e1', e2', t') <-
    maybe
      (do (t, e1') <- bidirect e1
          (t', e2') <- localCtx (extendVarCtx x t) $ bidirect e2
          return (e1', e2', t'))
      (\t -> do
         e1' <- localCtx (extendVarCtx x t) $ tcheck e1 t
         (t', e2') <- localCtx (extendVarCtx x t) $ bidirect e2
         return (e1', e2', t'))
      ty
  return (t', T.elet (translate x) e1' e2')



bidirect (LamA t) = do
  ((x, Embed a), e) <- unbind t
  wf a
  (b, e') <- localCtx (extendVarCtx x a) $ bidirect e
  return (Arr a b, T.ULam (bind (translate x) e'))

bidirect (Pos p tm) = extendSourceLocation p tm $ bidirect tm


-- Value of forall A . A, evaluating it would cause disaster :-)
bidirect Bot = return (BotT, T.Bot)

bidirect a = errThrow [DS "Infer not implemented:", DD a]




------------------------
-- Γ ⊢ e ⇐ A ~> E
------------------------

tcheck :: FExpr -> FType -> ITcMonad T.UExpr

{- |

Γ ⊢ A
Γ , x:A ⊢ e ⇐ B ~> E
---------------------------
Γ ⊢ λx. e ⇐ A → B ~> λx. E

-}
tcheck (Lam l) (Arr a b) = do
  (x, e) <- unbind l
  wf a
  e' <- localCtx (extendVarCtx x a) $ tcheck e b
  return (T.ULam (bind (translate x) e'))

{- |

Γ ⊢ A
Γ , a * A ⊢ e ⇐ B ~> E
---------------------------------
Γ ⊢ Λ(α∗A).e ⇐ ∀(α∗A).B ~> E

-}
tcheck (DLam l) (DForall b) =
  unbind2 l b >>= \case
    Just ((x, Embed a), e, _, t') -> do
      wf a
      localCtx (extendConstrainedTVarCtx x a) $ tcheck e t'
    Nothing -> errThrow [DS "Patterns have different binding variables"]

{- |

TODO: This is not correct, not sure how to do properly

Γ ⊢ e1 ⇐ A ~> E1
Γ ⊢ e2 ⇐ B ~> E2
Γ ⊢ A∗B
------------------------------
Γ ⊢ e1,,e2 ⇐ A&B ~> (E1, E2)

-}
-- tcheck e@(Merge e1 e2) b@(And a' b') = do
--   ctx <- askCtx
--   let re1 = checkMode e b
--       re2 = do
--         e1' <- tcheck e1 a'
--         e2' <- tcheck e2 b'
--         let aa = expandType ctx a'
--         let bb = expandType ctx b'
--         disjoint ctx aa bb
--         return (T.UPair e1' e2')
--   re2 `catchError` const re1



{- |

Γ ⊢ e ⇐ A ~> E
----------------------
Γ ⊢{l=e} ⇐ {l:A} ~> E

-}

tcheck (Rec l e) (SRecT l' a) = do
  when (l /= l') $
    errThrow [DS $ "Labels not equal" <+> Pretty.pretty l <+> "and" <+> Pretty.pretty l']
  tcheck e a


tcheck (Pos p tm) ty = extendSourceLocation p tm $ tcheck tm ty


{- |

Γ ⊢ e ⇒ A ~> E
A <: B ~> c
Γ ⊢ B
-------------------
Γ ⊢ e ⇐ B ~> c E

-}

tcheck e b = checkMode e b


checkMode :: FExpr -> FType -> ITcMonad T.UExpr
checkMode e b = do
  wf b
  (a, e') <- bidirect e
  ctx <- askCtx
  let res = subtype ctx a b
  case res of
    Right c -> return (T.UApp c e')
    Left er -> errThrow [DS $ "Subtyping failed:" <+> er]


-- | Check that a (expanded) type is well-formed
wf :: FType -> ITcMonad ()
wf ty = do
  ctx <- askCtx
  let t' = expandType ctx ty
  maybe_kind <- kind ctx t'
  case maybe_kind of
    Nothing ->
      errThrow [DS $ Pretty.squotes (pprint ty) <+> "is not well-kinded"]
    Just Star -> go t'
    Just k ->
      errThrow
        [ DS
            (Pretty.hang 2 $
             "expect type" <+>
             Pretty.squotes (pprint ty) <+>
             "has kind star" <> Pretty.line <> "but got" <+>
             Pretty.squotes (pprint k))
        ]
  where
    go NumT = return ()
    go BoolT = return ()
    go (Arr a b) = go a >> go b
    go (And a b) = do
      go a
      go b
    go (TVar x) = void $ lookupTVarConstraint x
    go (DForall t) = do
      ((x, Embed a), b) <- unbind t
      go a
      localCtx (extendConstrainedTVarCtx x a) $ go b
    go (SRecT _ t) = go t
    go TopT = return ()
    go BotT = return ()
    go t = errThrow [DS $ "type" <+> Pretty.squotes (pprint t) <+> "is not well-formed"]


{-

WARN: This is the most critical component!!!

Anything new added in the types, we should double check how it
affects the disjointess relation

-}


topLike :: Fresh m => FType -> m Bool
topLike TopT = return True
topLike (And a b) = (&&) <$> (topLike a) <*> (topLike b)
topLike (Arr a b) = topLike b
topLike (SRecT _ t) = topLike t
topLike (DForall b) = do
  ((_, _), t) <- unbind b
  topLike t
topLike _ = return False

disjoint :: ICtx -> FType -> FType -> ITcMonad ()
disjoint _ TopT _ = return ()
disjoint _ _ TopT = return ()

disjoint _ BotT a = do
  isTop <- topLike a
  if isTop
    then return ()
    else errThrow
           [ DS $
             "Bottom is only disjoint to top-like types, but" <+>
             Pretty.squotes (pprint a) <+> "is not top-like"
           ]
disjoint _ a BotT = do
  isTop <- topLike a
  if isTop
    then return ()
    else errThrow
           [ DS $
             "Bottom is only disjoint to top-like types, but" <+>
             Pretty.squotes (pprint a) <+> "is not top-like"
           ]

disjoint ctx (TVar x) b
  | Just a <- lookupTVarConstraintMaybe ctx x
  , Right _ <- subtype ctx a b = return ()
disjoint ctx b (TVar x)
  | Just a <- lookupTVarConstraintMaybe ctx x
  , Right _ <- subtype ctx a b = return ()
disjoint _ (TVar x) (TVar y) =
  errThrow
    [ DS $
      "FType variables" <+>
      Pretty.pretty x <+> "and" <+> Pretty.pretty y <+> "are not disjoint"
    ]

disjoint ctx (DForall t) (DForall t') =
  unbind2 t t' >>= \case
    Just ((x, Embed a1), b, (_, Embed a2), c) ->
      disjoint (extendConstrainedTVarCtx x (And a1 a2) ctx) b c
    _ -> errThrow [DS "Patterns have different binding variables"]

disjoint ctx tm1@(SRecT l a) tm2@(SRecT l' b) =
  when (l == l') $
  disjoint ctx a b `catchError`
  const
    (errThrow
       [ DS $
         Pretty.squotes (pprint tm1) <+>
         "and" <+> Pretty.squotes (pprint tm2) <+> "are not disjoint"
       ])

disjoint ctx (Arr _ a2) (Arr _ b2) = disjoint ctx a2 b2
disjoint ctx (And a1 a2) b = do
  disjoint ctx a1 b
  disjoint ctx a2 b
disjoint ctx a (And b1 b2) = do
  disjoint ctx a b1
  disjoint ctx a b2
disjoint _ a b =
  unless (disjointAx a b) $
  errThrow
    [ DS $
      Pretty.squotes (pprint a) <+>
      "and" <+> Pretty.squotes (pprint b) <+> "are not disjoint"
    ]


disjointAx :: FType -> FType -> Bool
disjointAx t1 t2 =
  type2num t1 < 5 && type2num t2 < 5 && type2num t1 /= type2num t2
  where
    type2num :: FType -> Int
    type2num NumT = 0
    type2num BoolT = 1
    type2num Arr {} = 2
    type2num DForall {} = 3
    type2num SRecT {} = 4
    type2num TopT {} = 5
    type2num And {} = 6
    type2num TVar {} = 7
    type2num OpAbs {} = 8
    type2num OpApp {} = 9
    type2num BotT {} = 10





--------------------
-- τ1 • l = τ2  ~> C
--------------------

-- | Select a label l from t
-- Return a list of possible types with their projections
select :: FType -> Label -> [(FType, T.UExpr)]
select t l =
  fromMaybe [] (M.lookup l m)
  where
    m = recordFields t

recordFields :: FType -> Map Label [(FType, T.UExpr)]
recordFields = go identity
  where
    go :: (T.UExpr -> T.UExpr) -> FType -> Map Label [(FType, T.UExpr)]
    go cont (And t1 t2) =
      M.unionWith (++) (go (T.UP1 . cont) t1) (go (T.UP2 . cont) t2)
    go cont (SRecT l' t') =
      M.fromList [(l', [(t', T.elam "x" (cont (T.evar "x")))])]
    go _ _ = M.empty


----------------------
-- τ1 \ l = τ2 ~> C
----------------------

restrict :: FType -> Label -> Maybe FType -> Maybe (FType, T.UExpr)
restrict t l lt = go t
  where
    go (SRecT l' t') = if l == l' && maybe True (`aeq` t') lt then Just (TopT, T.elam "x" T.UUnit) else Nothing
    go (And t1 t2) =
      let m1 = go t1
          m2 = go t2
          m1' = fmap (\(tt, c) -> (And tt t2, T.elam "x" (T.UPair (T.UApp c (T.UP1 (T.evar "x"))) (T.UP2 (T.evar "x"))))) m1
          m2' = fmap (\(tt, c) -> (And t1 tt, T.elam "x" (T.UPair (T.UP1 (T.evar "x")) (T.UApp c (T.UP2 (T.evar "x")))))) m2
      in m1' <|> m2'
    go _ = Nothing
