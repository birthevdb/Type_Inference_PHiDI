{-# LANGUAGE NoImplicitPrelude,
             LambdaCase #-}


module SEDEL.Source.Desugar
  ( desugarExpr
  , desugar
  , desugarTmBind
  , normalizeTmDecl
  , expandType
  ) where

import Protolude
import Unbound.Generics.LocallyNameless

import SEDEL.Environment
import SEDEL.Source.Syntax
import SEDEL.Fix

desugar :: [SDecl] -> [SDecl]
desugar = map go
 where
   go :: SDecl -> SDecl
   go (DefDecl decl) = DefDecl $ desugarTmBind decl

desugarTmBind :: TmBind -> TmBind
desugarTmBind b = b {bindRhs = desugarExpr (bindRhs b)}

desugarExpr :: Expr -> Expr
desugarExpr = runFreshM . go
  where

    go :: Fresh m => Expr -> m Expr

    -- Interesting cases
    go (DRec' b) =
      let (l, e) = normalizeTmDecl (desugarTmBind b)
      in return $ Rec l e

    -- Routine
    go (App e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      return $ App e1' e2'
    go (Lam t) = do
      (n, body) <- unbind t
      body' <- go body
      return $ Lam (bind n body')

    go (Let t) = do
      (n, (e, body)) <- unbind t
      bind' <- go e
      body' <- go body
      return $ Let (bind n (bind', body'))

    go (Rec l e) = do
      e' <- go e
      return $ Rec l e'
    go (Proj e l) = do
      e' <- go e
      return $ Proj e' l

    go (Merge e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      return $ Merge e1' e2'
    go (PrimOp op e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      return $ PrimOp op e1' e2'
    go (If e1 e2 e3) = do
      e1' <- go e1
      e2' <- go e2
      e3' <- go e3
      return $ If e1' e2' e3'
    go (Pos p e) = do
      e' <- go e
      return (Pos p e')
    go e = return e

{- |

(1): Translate
f [(A, T1), (B, T2)] [(x, A), (y, B)] = e
to
(f, /\ A*T1. B*T2. \x : A .\y : B . e)

(2): Translate
f [(A, T1), (B, T2)] [(x, A), (y, B)] C = e
to
(f, letrec f : forall (A * T1) (B * T2) . A -> B -> C = /\ A*T1. B*T2. \x y . e in f)

-}
normalizeTmDecl :: TmBind -> (RawName, Expr)
normalizeTmDecl decl =
  ( bindName decl
  , ex)
  where
    (ex, typ) =
      normalize
        (bindTyParams decl)
        (bindParams decl)
        (bindRhs decl)
        (bindRhsTyAscription decl)

{- |

Note: Make sure everything is desugarred before normalizing
Normalize
[(A, T1), (B, T2)] [(x, A), (y, B)] e C
to
\/ A*T1. B*T2. A -> B -> C
and
/\ A*T1. B*T2. \x.\y.e

-}
normalize :: [(TyName, SType)] -> [(TmName, Maybe Scheme)] -> Expr -> Maybe Scheme -> (Expr, Maybe Scheme)
normalize tyParams params e ret = (body, tbody)
  where
    tbody =
      maybe
        Nothing
        (\arr' ->
           Just
             (foldr (\(n, s) tm -> DForall (bind (n, Embed s) tm)) arr' tyParams))
        arr
    arr =
      maybe
        Nothing
        (\t ->
           foldrM
             (\(_, x) y -> maybe Nothing (\x' -> getSType y >>= \y' ->
                                                 getSType x' >>= \x'' ->
                                                 Just $ SType $ mkArr x'' y') x)
             t
             params)
        ret
    body =
      foldr
        (\(n, t) tm -> (Lam (bind n tm)))
           e
           params

getSType :: Scheme -> Maybe SType
getSType (SType x) = Just x
getSType  _        = Nothing

-- | Recursively expand all type synonyms. The given type must be well-kinded.
expandType :: SCtx -> Scheme -> Scheme
expandType ctx ty = runFreshM (go ctx ty)
  where
    -- Interesting cases:
    alg' :: SCtx -> SType' (FreshM SType) ->  FreshM SType
    alg' d (TVar a) = case lookupTVarSynMaybe d a of
      Nothing -> return $ mkTVar a
      Just t -> cata (alg' d) t
    alg' d t = fmap In $ sequence t

    go :: SCtx -> Scheme -> FreshM Scheme
    go d (DForall b) = do
      ((a, Embed t1), t2) <- unbind b
      t1' <- cata (alg' d) t1
      t2' <- go d t2
      return $ DForall (bind (a, embed t1') t2')
    go d (SType t) = SType <$> cata (alg' d) t
