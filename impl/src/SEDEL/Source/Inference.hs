{-# LANGUAGE FlexibleContexts,
             PatternGuards,
             NoImplicitPrelude,
             LambdaCase,
             OverloadedStrings #-}

module SEDEL.Source.Inference
  ( tcModule, topLevelInfer ) where

import           Protolude
import           Unbound.Generics.LocallyNameless
import           Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Set as Set
import qualified Data.List as List

import           SEDEL.Environment
import           SEDEL.PrettyPrint
import           SEDEL.Source.Syntax
import qualified SEDEL.Target.Syntax as T
import qualified SEDEL.Intermediate.Syntax as I
import           SEDEL.Intermediate.TypeCheck as TC
import           SEDEL.Util
import           SEDEL.Common
import           SEDEL.Source.Desugar
import           SEDEL.Translations
import           SEDEL.Fix

import Debug.Trace as DT

---------------------
-- GENERAL METHODS --
---------------------

tcModule :: Module -> STcMonad (Scheme, I.FExpr, T.UExpr)
tcModule m = do
 let (DefDecl mainE) = mainExpr m
 let  main           = desugarTmBind mainE
 (ty, target, val)  <- tcM main
 return (ty, target, val)
 where
   tcM :: TmBind -> STcMonad (Scheme, I.FExpr, T.UExpr)
   tcM main = tcTmDecl main >>= \(dbind, (_, e1), (_, e2))
                            -> return $ (snd dbind, e1, e2)


tcTmDecl :: TmBind -> STcMonad ((TmName, Scheme), (I.TmName, I.FExpr), (T.UName , T.UExpr))
tcTmDecl decl =
  lookupTmDef (s2n n) >>= \case
    Nothing -> do
      (typ, fTerm)    <- topLevelInfer term
      let ty           = bidirect fTerm
      (typFi, tranFi) <- iTcMtoSTcM $ ty
      return $ ((s2n n, typ), (s2n n, fTerm), (s2n n, tranFi))
    Just _  -> errThrow [DS $ "Multiple definitions of" <+> Pretty.pretty n]
  where
    (n, term) = normalizeTmDecl decl

---------------------
-- DATA STRUCTURES --
---------------------

-- | Rule representing 1 subtyping constraint of the form T1 <: T2
type SubRule = (PType, PType)
-- | Rule representing 1 disjointness constraint of the form P1 * P2
type DisRule = (PType, PType)

-- | Queue consisting of labels and/or types
data Queue = EmptyQ
           | QL Label Queue
           | QA PType Queue
           deriving (Show, Eq)

pushLabel :: Label -> Queue -> Queue
pushLabel l EmptyQ    = QL l EmptyQ
pushLabel l (QL l' q) = QL l' (pushLabel l q)
pushLabel l (QA t q)  = QA t (pushLabel l q)

pushType :: PType -> Queue -> Queue
pushType t EmptyQ    = QA t EmptyQ
pushType t (QL l q)  = QL l (pushType t q)
pushType t (QA t' q) = QA t' (pushType t q)

-- | Collection of substitutions of the form [u+ -> T, ...] or [u- -> T, ...]
data Substitution typ = EmptyS
                      | PosS TUni typ (Substitution typ)
                      | NegS TUni typ (Substitution typ)
                      deriving Show
-- | Polar types, annotated with a + or -
data Polarity = PosT | NegT deriving (Show, Eq)
type Polar ty = (Polarity, ty)

-- | Substitutions in the pr function do not include the notion of polarity
data PrSubs typ = EmptyPrS | Subs TyName typ (PrSubs typ) deriving Show

------------------
-- ⊢ E : A ~> e --
------------------

topLevelInfer :: Expr -> STcMonad (Scheme, I.FExpr)
topLevelInfer expr = do
  (gam, dis, ty, fTerm) <- infer expr
  (principal, theta)    <- ground $ flatten $ ty
  let dis'               = applySubst theta dis
  del                   <- reorder =<< combine =<< groundDestruct dis'
  theta'                <- translSubst theta
  f'                    <- substFExpr theta' fTerm
  fTerm'                <- constructFinalTerm del f'
  let ty'                = constructFinalType del principal
  return (ty', fTerm')


translSubst :: Fresh m => PrSubs SType -> m (PrSubs I.FType)
translSubst EmptyPrS = return $ EmptyPrS
translSubst (Subs name st subs) = do
  ft <- translSType st
  subs' <- translSubst subs
  return (Subs name ft subs')


---------------------------------
-- ALGORITHMIC INFERENCE RULES --
-- Π ⊢ E [Γ; ∆] τ ~> e         --
---------------------------------

infer :: Expr -> STcMonad (Gam, Dis, PType, I.FExpr)

-- Γ ⊢ ⊤ : [•; •] ⊤ ~> ⊤
infer Top = return (EmptyG, EmptyDis, mkTopT, I.Top)

-- Γ ⊢ i : [•; •] Int ~> i
infer (LitV n) = return (EmptyG, EmptyDis, mkNumT, I.LitV n)

-- Γ ⊢ b : [•; •] Bool ~> b
infer (BoolV b) = return (EmptyG, EmptyDis, mkBoolT, I.BoolV b)

{-
   Π (x) = [Γ; ∆] τ       ∆ = α * τ'       u fresh
   ---------------------------------------------------
   Π ⊢ x : [ [α -> u]Γ; [α -> u]∆] [α -> u]τ ~> x |u|

-}
infer (VarPoly x) = do
  CtxSch gam del ty       <- lookupVarTy x
  (gam', dis', ty', vars) <- findAndSubstVars gam del ty
  return (gam', dis', ty', applyVars (I.Var (translate x)) vars)

{-
  --------------------------------
  Π ⊢ x : [x : u ; u * ⊤] u ~> x
-}
infer (Var x) = do
  uFresh  <- getFreshUni
  let gam  = Gamma x (mkUni uFresh) EmptyG
  let dis  = Disj (mkUni uFresh) mkTopT EmptyDis
  return (gam, dis, mkUni uFresh, I.Var (translate x))

{-
  Π ⊢ E : [Γ; ∆] τ ~> e
  ----------------------------------------------------------
  Π ⊢ \x . E : [Γ_x ; ∆ ] Γ(x) -> τ ~> \x . e : |Γ(x) -> τ|
  -}
infer (Lam b) = do
  (x, e) <- unbind b
  (gam', dis', t', f') <- infer e
  let gam = removeFromGam gam' x
  case lookupGam gam' x of
    Nothing -> do
      (st, _)  <- ground $ flatten (mkArr mkTopT t')
      tFi      <- translSType st
      let fterm = I.Anno (I.Lam (bind (translate x) f')) tFi
      return (gam, dis', mkArr mkTopT t', fterm)
    Just ty -> do
      (st, _)  <- ground $ flatten $ (mkArr ty t')
      tFi      <- translSType st
      let fterm = I.Anno (I.Lam (bind (translate x) f')) tFi
      return (gam, dis', mkArr ty t', fterm)

{-
      Π ⊢ E1 : [Γ1; ∆1] τ1 ~> e1                  u fresh
      Π ⊢ E2 : [Γ2; ∆2] τ2 ~> e2                  θ = solve(τ1 <: τ2 -> u)
  -------------------------------------------------------------------------------
  Π ⊢ E1 E2 : [θ(Γ1 ∪ Γ2); θ(∆1 ∪ ∆2 ∪ (u * ⊤))] θ(u) ~> |θ| (e1 : |τ2 -> u| e2)
-}
infer (App e1 e2) = do
  (gam1', dis1', t1', f1') <- infer e1
  (gam2', dis2', t2', f2') <- infer e2
  uFresh  <- DT.trace ("t1:     " ++ show t1' ++ "\nt2:     " ++ show t2') $ getFreshUni
  theta   <- solve $ initC ((t1', mkArr t2' (mkUni uFresh)))
  let gam  = substInGam (joinGam gam1' gam2') theta
  let dis  = substInDis (joinDis (joinDis dis1' dis2') (Disj (mkUni uFresh) mkTopT EmptyDis)) theta
  let t    = substInType theta (PosT, (mkUni uFresh))
  (st, _) <- ground $ flatten $ (mkArr t2' t)
  tFi     <- translSType st
  let f    = I.App (I.Anno f1' tFi) f2'
  return (gam, dis, t, f)

{-
    Π ⊢ E1 : [Γ1; ∆1] τ1 ~> e1             Π ⊢ E2 : [Γ2; ∆2] τ2 ~> e2
  ------------------------------------------------------------------
  Π ⊢ E1 ,, E2 : [Γ1 ∪ Γ2; ∆1 ∪ ∆2 ∪ (τ1 * τ2)] τ1 & τ2 ~> e1 ,, e2
-}
infer (Merge e1 e2) = do
  (gam1', dis1', t1', f1') <- infer e1
  (gam2', dis2', t2', f2') <- infer e2
  let gam     = joinGam gam1' gam2'
  let dis     = joinDis (joinDis dis1' dis2') (Disj t1' t2' EmptyDis)
  (pr1, th1) <- ground $ flatten t1'
  (pr2, th2) <- ground $ flatten t2'
  let t       = mkAnd (replaceVars $ convertSType pr1) (replaceVars $ convertSType pr2)
  return (gam, dis, t, I.Merge f1' f2')

{-
              Π ⊢ E : [Γ; ∆] τ ~> e
  -------------------------------------------
  Π ⊢ {l = E} : [Γ; ∆] { l : τ } ~> { l = e }
-}
infer (Rec l e) = do
  (gam', dis', t', f') <- infer e
  return (gam', dis', mkSRecT l t', I.Rec l f')

{-
  Π ⊢ E : [Γ; ∆] τ ~> e     u fresh    θ = solve(τ <: {l : u})
  -------------------------------------------------------------
  Π ⊢ E.l ; [θ(Γ); θ(∆ ∪ (u * ⊤))] θ(τ) ~> |θ|(e:|{l : u}|.l)
-}
infer (Proj e l) = do
  (gam', dis', t', f') <- infer e
  uFresh <- getFreshUni
  theta  <- solve $ initC ((t', mkSRecT l (mkUni uFresh)))
  let gam = substInGam gam' theta
  let dis = substInDis (joinDis dis' (Disj (mkUni uFresh) mkTopT EmptyDis)) theta
  let t   = substInType theta (PosT, (mkUni uFresh))
  (st, _) <- ground $ flatten $ (mkSRecT l t)
  tFi     <- translSType st
  let f    = I.Acc (I.Anno f' tFi) l
  return (gam, dis, t, f)

{-
  A = [Γ'; ∆'] τ'
  Π, ^x : [Γ'; ∆'] τ' ⊢ E1 : [Γ1; ∆1] τ1 ~> e1
  θ = solve(τ1 <: τ')                   ∆' |= θ(∆1)
  Π, ^x : [Γ'; ∆'] τ' ⊢ E2 : [Γ2; ∆2] τ2 ~> e2
  -------------------------------------------------------------------------------
  Π ⊢ let ^x : A = E1 in E2 : [Γ1 ∪ Γ2; ∆2] τ2 ~> let x : |A| = |θ|(e1) in e2
-}
infer (Letrec b) = do
  ((x, Embed a), (e1, e2)) <- unbind b
  -- A = [Γ'; ∆'] τ'
  (CtxSch gam' del' t')    <- convertScheme a
  -- Π, ^x : [Γ'; ∆'] τ' ⊢ E1 : [Γ1; ∆1] τ1 ~> e1
  (gam1, dis1, t1, f1)     <- localCtx (extendVarCtx x (CtxSch gam' del' t')) $ infer e1
  -- θ = solve(τ1 <: τ')
  th                       <- unification [(EmptyQ, (t1, t'))]
  case th of
    Just theta -> do
      -- (∆_loc, ∆_glob) = splitDel Γ ∆
      let (loc1, glob1)         = splitDel gam1 dis1
      -- Π, ^x : [Γ'; ∆'] τ' ⊢ E2 : [Γ2; ∆2] τ2 ~> e2
      (gam2, dis2, t2, f2)     <- localCtx (extendVarCtx x (CtxSch gam' del' t')) $ infer e2
      -- Γ = Γ1 ∪ Γ2
      let gam                   = substInGam (joinGam gam1 gam2) theta
      -- ∆ = ∆_glob ∪ ∆2
      let dis                   = substInDis (joinDis glob1 dis2) theta
      -- θ(∆_loc)
      del1                     <- reorder =<< combine =<< groundDestruct (substInDis loc1 theta)
      del''                    <- reorder del'
      -- check  ∆' |= θ(∆_loc)
      entails del'' del1
      -- θ(e1)
      aFi                      <- translType a
      theta'                   <- groundS theta EmptyPrS
      f'                       <- substFExpr theta' f1
      f1'                      <- constructFinalTerm del1 f'
      return (gam, dis, t2, I.Letrec (bind (translate x, embed (Just aFi)) (f1', f2)))
    Nothing    -> errThrow [DS "Letrec not possible"]

{-
  Π ⊢ E1 : [Γ1; ∆1] τ1 ~> e1
  Π ⊢ E2 : [Γ2; ∆2] τ2 ~> e2                u fresh
  Π ⊢ E3 : [Γ3; ∆3] τ3 ~> e3                θ = solve(τ1 <: Bool, τ2 <: u, τ3 <: u)
  ---------------------------------------------------------------------------------------------
  Π ⊢ If E1 E2 E3 : [θ(Γ1 ∪ Γ2 ∪ Γ3); θ(∆1 ∪ ∆2 ∪ ∆3 ∪ (u * ⊤))] θ(u) ~> |θ|(if e1 then e2 else e3)
-}
infer (If e1 e2 e3) = do
  (gam1', dis1', t1', f1') <- infer e1
  (gam2', dis2', t2', f2') <- infer e2
  (gam3', dis3', t3', f3') <- infer e3
  uFresh  <- getFreshUni
  let cons = (initC (t1', mkBoolT)) ++ (initC (t2', mkUni uFresh)) ++ (initC (t3', mkUni uFresh))
  theta   <- solve cons
  let gam  = substInGam (joinGam gam1' (joinGam gam2' gam3')) theta
  let dis  = substInDis (joinDis (joinDis dis1' (joinDis dis2' dis3')) (Disj (mkUni uFresh) mkTopT EmptyDis)) theta
  let t    = substInType theta (PosT, (mkUni uFresh))
  (_, th) <- ground $ flatten $ t1'
  theta'  <- translSubst th
  f       <- substFExpr theta' (I.If f1' f2' f3')
  return (gam, dis, t, f)

{-
  Π ⊢ E1 : [Γ1; ∆1] τ1 ~> e1
  Π ⊢ E2 : [Γ2; ∆2] τ2 ~> e2       u fresh       θ = solve(...)
  ---------------------------------------------------------------------------------
  Π ⊢ PrimOp Op E1 E2 : [θ(Γ1 ∪ Γ2); θ(∆1 ∪ ∆2 ∪ (u * ⊤))] θ(u) ~> |θ|(PrimOp Op e1 e2)
-}
infer (PrimOp op e1 e2) = do
  (gam1', dis1', t1', f1') <- infer e1
  (gam2', dis2', t2', f2') <- infer e2
  uFresh <- getFreshUni
  case op of
    Arith   _ -> do
      let cons = (initC (mkNumT, mkUni uFresh)) ++ (initC (t1', mkNumT)) ++ (initC (t2', mkNumT))
      theta   <- solve cons
      let gam  = substInGam (joinGam gam1' gam2') theta
      let dis  = substInDis (joinDis (joinDis dis1' dis2') (Disj (mkUni uFresh) mkTopT EmptyDis)) theta
      let t    = substInType theta (PosT, (mkUni uFresh))
      (_, th1) <- ground $ flatten $ t1'
      theta1'  <- translSubst th1
      (_, th2) <- ground $ flatten $ t2'
      theta2'  <- translSubst th2
      f        <- substFExpr theta1' (I.PrimOp op f1' f2')
      f'       <- substFExpr theta2' f
      return (gam, dis, t, f')
    Comp    _ -> do
      let cons = (initC (mkBoolT, mkUni uFresh)) ++ (initC (t1', mkNumT)) ++ (initC (t2', mkNumT))
      theta   <- solve cons
      let gam  = substInGam (joinGam gam1' gam2') theta
      let dis  = substInDis (joinDis (joinDis dis1' dis2') (Disj (mkUni uFresh) mkTopT EmptyDis)) theta
      let t    = substInType theta (PosT, (mkUni uFresh))
      (_, th1) <- ground $ flatten $ t1'
      theta1'  <- translSubst th1
      (_, th2) <- ground $ flatten $ t2'
      theta2'  <- translSubst th2
      f        <- substFExpr theta1' (I.PrimOp op f1' f2')
      f'       <- substFExpr theta2' f
      return (gam, dis, t, f')
    Logical _ -> do
      let cons = (initC (mkBoolT, mkUni uFresh)) ++ (initC (t1', mkBoolT)) ++ (initC (t2', mkBoolT))
      theta   <- solve cons
      let gam  = substInGam (joinGam gam1' gam2') theta
      let dis  = substInDis (joinDis (joinDis dis1' dis2') (Disj (mkUni uFresh) mkTopT EmptyDis)) theta
      let t    = substInType theta (PosT, (mkUni uFresh))
      (_, th1) <- ground $ flatten $ t1'
      theta1'  <- translSubst th1
      (_, th2) <- ground $ flatten $ t2'
      theta2'  <- translSubst th2
      f        <- substFExpr theta1' (I.PrimOp op f1' f2')
      f'       <- substFExpr theta2' f
      return (gam, dis, t, f')

infer (Pos p tm) = extendSourceLocation p tm $ infer tm

infer a = errThrow [DS "Infer not implemented:", DD a]

replaceVars :: PType -> PType
replaceVars = cata alg
  where
    alg :: PType' PType -> PType
    alg (Inl (TVar name)) = mkUni (translate name)
    alg pt = In $ pt

---------------------------------------
-- SPLIT DISJOINTNESS LOCAL - GLOBAL --
---------------------------------------

-- splitDel :: Γ -> ∆ -> (∆_loc, ∆_glob)
splitDel :: Gam -> Dis -> (Dis, Dis)
splitDel gam EmptyDis = (EmptyDis, EmptyDis)
splitDel gam (Disj p1 p2 dis) = if isGlob then (loc, Disj p1 p2 glob) else (Disj p1 p2 loc, glob)
  where
    (loc, glob) = splitDel gam dis
    isGlob = any (gamContains gam) (findUnis p1 ++ findUnis p2)

findUnis :: PType -> [TUni]
findUnis = cata alg
  where
    alg :: PType' [TUni] -> [TUni]
    alg (Inr (Uni uni)) = [uni]
    alg (Inl ty) = concat ty
    alg (Inr ty) = concat ty

--------------------
-- ENTAILMENT LET --
--------------------

entails :: Del -> Del -> STcMonad ()
entails del1 EmptyD = return ()
entails del1 (Delta name ty del2) = do
  ent del1 (translate name) ty
  entails del1 del2
  where
    ent :: Del -> TyName -> SType -> STcMonad ()
    ent EmptyD _ _ = errThrow [DS "No entailment in letrec."]
    ent (Delta u1 (In (TVar a)) d) u2 (In (TVar b)) = if u1 == b && a == u2
                                                      then return ()
                                                      else ent d u2 (mkTVar b)
    ent (Delta u1 a d) u2 b | u1 == u2 =
      unification [(EmptyQ, (convertSType a, convertSType b))] >>= \th -> case th of
        Nothing -> if (topLike b) then return () else ent d u2 b
        Just x  -> return ()
    ent (Delta u1 a d) u2 b = ent d u2 b

---------------------------
-- UNIFICATION ALGORITHM --
---------------------------

-- Initialization function
initC :: SubRule -> [(Queue, SubRule)]
initC (a1, a2) = [(EmptyQ, (a1, a2))]

solve :: [(Queue, SubRule)] -> STcMonad (Substitution PType)
solve [] = return $ EmptyS
solve cons = DT.trace ("cons:    " ++ show cons) $ unification cons >>= \subs -> case subs of
  Just sub -> DT.trace ("sub:    " ++ show sub) $ return $ sub
  Nothing -> errThrow [DS "Destruct subtyping impossible case"]

--------------------------------------------------------------------------------

unification :: [(Queue, SubRule)] -> STcMonad (Maybe (Substitution PType))
unification []                = return $ Just EmptyS
unification ((EmptyQ, s):lqc) | substWithUni s = do
    theta1 <- makeSubst s
    sub    <- unification $ applySubstC theta1 lqc
    case sub of
      Just theta2 -> return $ Just (appendS theta1 theta2)
      Nothing     -> return $ Nothing
unification ((EmptyQ, (t1, t2)) : lqc) | t1 == t2 = unification lqc
unification ((EmptyQ, (In (Inl NumT), In (Inl BoolT)))    :lqc) = return $ Nothing
unification ((EmptyQ, (In (Inl BoolT), In (Inl NumT)))    :lqc) = return $ Nothing
unification ((EmptyQ, (In (Inl BoolT), In (Inl (TVar _)))):lqc) = return $ Nothing
unification ((EmptyQ, (In (Inl NumT), In (Inl (TVar _)))) :lqc) = return $ Nothing
unification ((EmptyQ, (In (Inl (TVar _)), In (Inl NumT))) :lqc) = return $ Nothing
unification ((EmptyQ, (In (Inl (TVar _)), In (Inl BoolT))):lqc) = return $ Nothing
unification ((EmptyQ, (In (Inl (TVar a)), In (Inl (TVar b)))):lqc) = return $ Nothing

unification ((_,(In (Inl BotT), _)):lqc) = unification lqc
unification ((_,(_,In (Inl TopT))) :lqc) = unification lqc

unification ((q,(In (Inr (Join a1 a2)), a)):lqc) = unification ((q,(a1,a)):(q,(a2,a)):lqc)
unification ((q,(a, In (Inr (Meet a1 a2)))):lqc) = unification ((q,(a,a1)):(q,(a,a2)):lqc)
unification ((q,(a, In (Inl (And a1 a2)))) :lqc) = unification ((q,(a,a1)):(q,(a,a2)):lqc)

unification ((q,(In (Inl (And (In (Inl (Arr a1 a2))) (In (Inl (Arr a3 a4))))), In (Inl (Arr a5 a6)))):lqc) | a1 == a3 =
  unification ((q,(mkArr a1 (mkAnd a2 a4), mkArr a5 a6)):lqc)
unification ((q,(In (Inl (And (In (Inl (Arr a1 a2))) (In (Inl (Arr a3 a4))))), In (Inl (Arr a5 a6)))):lqc) | a2 == a4 =
  unification ((q,(mkArr (mkAnd a1 a3) a2, mkArr a5 a6)):lqc)
unification ((q,(In (Inl (And (In (Inl (SRecT l1 a1))) (In (Inl(SRecT l2 a2))))), In (Inl (SRecT l3 a3)))):lqc) | l1 == l2 =
  unification ((q,(mkSRecT l1 (mkAnd a1 a2), mkSRecT l3 a3)):lqc)
--------------------------------------------------------------------------------

unification ((q,(a1, In (Inl (SRecT l a2)))):lqc) = unification ((pushLabel l  q,(a1,a2)):lqc)
unification ((q,(a1, In (Inl (Arr a2 a3)))) :lqc) = unification ((pushType  a2 q,(a1,a3)):lqc)

unification ((QA p q,(In (Inl (Arr a1 a2)), a)) : lqc) = unification [(EmptyQ,(p, a1))] >>= \sub -> case sub of
    Just cs -> unification ((EmptyQ,(p, a1)) : (q, (a2, a)):lqc)
    Nothing -> unification ((q,(mkTopT, a)) : lqc)
unification ((QL l q,(In (Inl (SRecT l1 a1)), a2)):lqc) | l == l1 = unification ((q,(a1, a2)) :lqc)
--------------------------------------------------------------------------------
unification ((q,(In (Inl (And a1 a2)), a3))  :lqc) = unification [(q, (a1, a3))] >>= \res1 -> case res1 of
  Just sub1 -> (unification $ applySubstC sub1 [(q, (a2, a3))]) >>= \res2 -> case res2 of
    Just sub2 -> do
      let sub = composeSubs sub1 sub2
      unification (applySubstC sub lqc) >>= \res3 -> case res3 of
        Just uni -> return $ Just $ appendS sub uni
        Nothing  -> return $ Nothing
    Nothing   -> unification ((q, (a1, a3)) : lqc)
  Nothing -> unification [(q, (a2, a3))] >>= \res2 -> case res2 of
    Just sub2 -> unification ((q, (a2, a3)) : lqc)
    Nothing   -> return $ Nothing
--------------------------------------------------------------------------------

-- unification ((QA p q, (Uni u1, a2))    :lqc) = unification ((q,(Uni u1, PArr p a2)) :lqc)
-- unification ((QL l q, (Uni u1, a2))    :lqc) = unification ((q,(Uni u1, PRecT l a2)):lqc)
-- unification ((QA p q, (a1,     Uni u2)):lqc) = unification ((q,(P TopT, Uni u2))    :lqc)
-- unification ((QL l q, (a1,     Uni u2)):lqc) = unification ((q,(P TopT, Uni u2))    :lqc)

unification x = DT.trace ("other:   " ++ show x) $ return Nothing

--------------------------------------------------------------------------------

composeSubs :: Substitution PType -> Substitution PType -> Substitution PType
composeSubs EmptyS sub2 = sub2
composeSubs (PosS u ty sub1) sub2 = appendS result (composeSubs sub1 sub2')
  where (result, sub2') = compose PosT u ty sub2
composeSubs (NegS u ty sub1) sub2 = appendS result (composeSubs sub1 sub2')
  where (result, sub2') = compose NegT u ty sub2

compose :: Polarity -> TUni -> PType -> Substitution PType -> (Substitution PType, Substitution PType)
compose _ _ _ EmptyS = (EmptyS, EmptyS)
compose PosT u1 (In (Inr (Join u3 ty1))) (PosS u2 (In (Inr (Join u4 ty2))) sub) | u1 == u2 && u3 == u4 = let (res, sub2) = compose PosT u1 ty1 sub in (PosS u1 (mkJoin u3 (mkAnd ty1 ty2)) res, sub2)
compose PosT u1 ty1 (PosS u2 ty2 sub) | u1 == u2 = let (res, sub2) = compose PosT u1 ty1 sub in (PosS u1 (mkAnd ty1 ty2) res, sub2)
compose NegT u1 (In (Inr (Meet u3 ty1))) (NegS u2 (In (Inr (Meet u4 ty2))) sub) | u1 == u2 && u3 == u4 = let (res, sub2) = compose NegT u1 ty1 sub in (NegS u1 (mkMeet u3 (mkAnd ty1 ty2)) res, sub2)
compose NegT u1 ty1 (NegS u2 ty2 sub) | u1 == u2 = let (res, sub2) = compose NegT u1 ty1 sub in (NegS u1 (mkAnd ty1 ty2) res, sub2)
compose pol u1 ty1 (PosS u2 ty2 sub) = let (res, sub2) = compose pol u1 ty1 sub in (PosS u2 ty2 res, sub2)
compose pol u1 ty1 (NegS u2 ty2 sub) = let (res, sub2) = compose pol u1 ty1 sub in (NegS u2 ty2 res, sub2)

--------------------------------------------------------------------------------

-- Construct a substitution [u- |-> u /\ P] or [u+ |-> u \/ P]
makeSubst :: SubRule -> STcMonad (Substitution PType)
makeSubst (In (Inr (Uni u1)), In (Inr (Uni u2))) =
                             if u1 == u2
                             then return $ EmptyS
                             else return $ NegS u1 (mkMeet (mkUni u1) (mkUni u2))
                                          (PosS u2 (mkJoin (mkUni u1) (mkUni u2)) EmptyS)
makeSubst (In (Inr (Uni u)), t) =
                             if occursCheck (NegT, u) (NegT, t)
                             then errThrow [DS $ "Occurs check: cannot construct infinite type."]
                             else return $ NegS u (mkMeet (mkUni u) t) EmptyS
makeSubst (t, In (Inr (Uni u))) =
                             if occursCheck (PosT, u) (PosT, t)
                             then errThrow [DS $ "Occurs check: cannot construct infinite type."]
                             else return $ PosS u (mkJoin (mkUni u) t) EmptyS
makeSubst  _               = errThrow [DS $ "Solve impossible case"]

-------------------
-- SUBSTITUTIONS --
-------------------

-- Concatenate substitutions
appendS :: Substitution typ -> Substitution typ -> Substitution typ
appendS  EmptyS        s2 = s2
appendS (PosS u ty s1) s2 = PosS u ty (appendS s1 s2)
appendS (NegS u ty s1) s2 = NegS u ty (appendS s1 s2)

--------------------------------------------------------------------------------

-- Concatenate principality substitutions
appendPr :: PrSubs typ -> PrSubs typ -> PrSubs typ
appendPr  EmptyPrS     s2 = s2
appendPr (Subs u t s1) s2 = Subs u t (appendPr s1 s2)

--------------------------------------------------------------------------------

-- Check whether a unification variable gets substituted
substWithUni :: SubRule -> Bool
substWithUni (In (Inr (Uni u)), _) = True
substWithUni (_, In (Inr (Uni u))) = True
substWithUni  _                    = False

--------------------------------------------------------------------------------

-- Apply a polar substitution to a term context
-- Negative type since it is an input
substInGam :: Gam -> Substitution PType -> Gam
substInGam EmptyG _ = EmptyG
substInGam (Gamma x ty gam) sub = Gamma x (substInType sub (NegT, ty)) (substInGam gam sub)

--------------------------------------------------------------------------------

-- Apply a polar substitution to disjointness requirements
-- Positive type since it is an output
substInDis :: Dis -> Substitution PType -> Dis
substInDis EmptyDis _ = EmptyDis
substInDis (Disj pty1 pty2 dis) sub = Disj (substInType sub (PosT, pty1)) (substInType sub (PosT, pty2)) (substInDis dis sub)

--------------------------------------------------------------------------------

-- Substitute type variables with unification variables in a given type scheme
findAndSubstVars :: Gam -> Del -> PType -> STcMonad (Gam, Dis, PType, [TUni])
findAndSubstVars gam EmptyD ty = return (gam, EmptyDis, ty, [])
findAndSubstVars gam (Delta alph st del) ty | gamContains gam (translate alph) = do
  (gam', dis', ty', vars') <- findAndSubstVars gam del ty
  return (gam', Disj (mkUni $ translate alph) (convertSType st) dis', ty', (translate alph) : vars')
findAndSubstVars gam (Delta alph st del) ty = do
  (gam', dis', ty', vars') <- findAndSubstVars gam del ty
  uFresh <- getFreshUni
  let newGam = replaceGam (translate alph) uFresh gam'
  let newDis = Disj (mkUni uFresh) (convertSType st) dis'
  let newTy  = replaceTVar (translate alph) uFresh ty'
  return (newGam, newDis, newTy, uFresh : vars')

--------------------------------------------------------------------------------

-- Apply a polar substitution to subtyping constraints
applySubstC :: (Substitution PType) -> [(Queue, SubRule)] -> [(Queue, SubRule)]
applySubstC EmptyS lqc                   = lqc
applySubstC _      []                    = []
applySubstC s      ((q, (ty1, ty2)):lqc) = ((q, (substInType s (PosT, ty1),
                                                 substInType s (NegT, ty2)))
                                            :(applySubstC s lqc))

--------------------------------------------------------------------------------

applySubst :: PrSubs SType -> Dis -> Dis
applySubst EmptyPrS dis = dis
applySubst subs EmptyDis = EmptyDis
applySubst subs (Disj p1 p2 dis) = Disj (groundSubstInPType subs p1) (groundSubstInPType subs p2) (applySubst subs dis)

--------------------------------------------------------------------------------

-- Apply a polar substitution to a polar type
substInType :: Substitution PType -> Polar PType -> PType
substInType EmptyS (_, ty) = ty

substInType _ (_, In (Inl NumT))     = mkNumT
substInType _ (_, In (Inl BoolT))    = mkBoolT
substInType _ (_, In (Inl (TVar x))) = mkTVar x
substInType _ (_, In (Inl TopT))     = mkTopT
substInType _ (_, In (Inl BotT))     = mkBotT

substInType sub (pol, In (Inr (Join ty1 ty2))) = mkJoin (substInType sub (pol, ty1)) (substInType sub (pol, ty2))
substInType sub (pol, In (Inr (Meet ty1 ty2))) = mkMeet (substInType sub (pol, ty1)) (substInType sub (pol, ty2))

substInType sub (pol, In (Inl (Arr ty1 ty2))) = mkArr (substInType sub (inv pol, ty1)) (substInType sub (inv pol, ty2))
substInType sub (pol, In (Inl (And ty1 ty2))) = mkAnd (substInType sub (pol, ty1)) (substInType sub (pol, ty2))
substInType sub (pol, In (Inl (SRecT l ty)))  = mkSRecT l (substInType sub (pol, ty))
-- interesting cases
substInType (PosS u ty sub) (PosT, In (Inr (Uni u1))) | u == u1 = case sub of
  EmptyS -> ty
  _      -> substInType sub (PosT, ty)
substInType (PosS u ty sub) (PosT, In (Inr (Uni u1))) = case sub of
  EmptyS -> mkUni u1
  _      -> substInType sub (PosT, mkUni u1)
substInType (PosS u ty sub) (NegT, In (Inr (Uni u1))) = case sub of
  EmptyS -> mkUni u1
  _      -> substInType sub (NegT, mkUni u1)
substInType (NegS u ty sub) (NegT, In (Inr (Uni u1))) | u == u1 = case sub of
  EmptyS -> ty
  _      -> substInType sub (NegT, ty)
substInType (NegS u ty sub) (NegT, In (Inr (Uni u1))) = case sub of
  EmptyS -> mkUni u1
  _      -> substInType sub (NegT, mkUni u1)
substInType (NegS u ty sub) (PosT, In (Inr (Uni u1))) = case sub of
  EmptyS -> mkUni u1
  _      -> substInType sub (PosT, mkUni u1)

--------------------------------------------------------------------------------

-- Apply a non-polar substitution to a type
groundSubstInPType :: PrSubs SType -> PType -> PType
groundSubstInPType sub = cata (substInPTypeAlg sub)
  where
    substInPTypeAlg :: PrSubs SType -> PType' PType -> PType
    substInPTypeAlg EmptyPrS st = In st
    substInPTypeAlg (Subs name ty subs) (Inl (TVar x)) | name == x = groundSubstInPType subs (convertSType ty)
    substInPTypeAlg (Subs name ty subs) (Inl (TVar x)) = groundSubstInPType subs (mkTVar x)
    substInPTypeAlg (Subs name ty subs) (Inr (Uni u1)) = if name == translate u1
                                               then groundSubstInPType subs (convertSType ty)
                                               else groundSubstInPType subs (mkUni u1)
    substInPTypeAlg subs st = In st

--------------------------------------------------------------------------------

-- Apply a non-polar substitution to a PHiDI monotype
substInSType :: PrSubs SType -> SType -> SType
substInSType sub = cata (substInSTypeAlg sub)
  where
    substInSTypeAlg :: PrSubs SType -> SType' SType -> SType
    substInSTypeAlg EmptyPrS st = In st
    substInSTypeAlg (Subs name ty subs) (TVar x) | name == x = substInSTypeAlg subs (out ty)
    substInSTypeAlg (Subs name ty subs) (TVar x) = substInSTypeAlg subs (TVar x)
    substInSTypeAlg subs st = In st


--------------------------------------------------------------------------------

-- Apply a non-polar substitution to an elaborated term (Fi+)
substFExpr :: PrSubs I.FType -> I.FExpr -> STcMonad I.FExpr
substFExpr EmptyPrS fe          = return $ fe
substFExpr subs (I.Anno fe ft)  = I.Anno <$> substFExpr subs fe <*> substInFType subs ft
substFExpr subs (I.Var tn)      = return $ I.Var tn
substFExpr subs (I.App fe1 fe2) = I.App <$> substFExpr subs fe1 <*> substFExpr subs fe2
substFExpr subs (I.Lam b)       = do
  (tn, fe) <- unbind b
  fe'      <- substFExpr subs fe
  return $ I.Lam (bind tn fe')
substFExpr subs (I.Letrec b)    = do
  ((tn, Embed mft), (fe1, fe2)) <- unbind b
  fe1'                          <- substFExpr subs fe1
  fe2'                          <- substFExpr subs fe2
  case mft of
    Nothing -> return $ I.Letrec (bind (tn, embed Nothing) (fe1', fe2'))
    Just ft -> substInFType subs ft >>= \ft' ->
                return $ I.Letrec (bind (tn, embed (Just ft')) (fe1', fe2'))
substFExpr subs (I.DLam b) = do
  ((tn, Embed ft), fe) <- unbind b
  fe'                  <- substFExpr subs fe
  ft'                  <- substInFType subs ft
  return $ I.DLam (bind (tn, embed ft') fe')
substFExpr subs (I.TApp fe ft) = I.TApp <$> substFExpr subs fe <*> substInFType subs ft
substFExpr subs (I.Rec l fe)   = I.Rec l <$> substFExpr subs fe
substFExpr subs (I.Acc fe l)   = do
  fe' <- substFExpr subs fe
  return $ I.Acc fe' l
substFExpr subs (I.Remove fe l Nothing)   = do
  fe' <- substFExpr subs fe
  return $ I.Remove fe' l Nothing
substFExpr subs (I.Remove fe l (Just ft)) = do
  fe' <- substFExpr subs fe
  ft' <- substInFType subs ft
  return $ I.Remove fe' l (Just ft')
substFExpr subs (I.Merge fe1 fe2)     = I.Merge <$> substFExpr subs fe1 <*>
                                                    substFExpr subs fe2
substFExpr subs (I.LitV i)            = return $ I.LitV i
substFExpr subs (I.BoolV b)           = return $ I.BoolV b
substFExpr subs (I.PrimOp op fe1 fe2) = I.PrimOp op <$> substFExpr subs fe1 <*>
                                                        substFExpr subs fe2
substFExpr subs (I.If fe1 fe2 fe3)    = I.If <$> substFExpr subs fe1 <*>
                                                 substFExpr subs fe2 <*>
                                                 substFExpr subs fe3
substFExpr subs I.Top         = return I.Top
substFExpr subs (I.Pos sp fe) = I.Pos sp <$> substFExpr subs fe
substFExpr subs (I.LamA b)    = do
  ((tn, Embed ft), fe) <- unbind b
  fe'                  <- substFExpr subs fe
  ft'                  <- substInFType subs ft
  return $ I.LamA (bind (tn, embed ft') fe')
substFExpr subs I.Bot         = return I.Bot
substFExpr subs (I.DRec' tb)  = return $ I.DRec' tb


--------------------------------------------------------------------------------

-- Apply a non-polar substitution to an elaborated type (Fi+)
substInFType :: PrSubs I.FType -> I.FType -> STcMonad (I.FType)
substInFType EmptyPrS ft            = return ft
substInFType subs I.NumT            = return I.NumT
substInFType subs I.BoolT           = return I.BoolT
substInFType subs I.TopT            = return I.TopT
substInFType subs I.BotT            = return I.BotT
substInFType subs (I.Arr ft1 ft2)   = I.Arr <$> substInFType subs ft1 <*> substInFType subs ft2
substInFType subs (I.And ft1 ft2)   = I.And <$> substInFType subs ft1 <*> substInFType subs ft2
substInFType subs (I.SRecT l ft)    = I.SRecT l <$> substInFType subs ft
substInFType subs (I.DForall b)     = return $ I.DForall b
substInFType subs (I.OpAbs b)       = return $ I.OpAbs b
substInFType subs (I.OpApp ft1 ft2) = return $ I.OpApp ft1 ft2
substInFType (Subs u ft subs) (I.TVar tn) | u == translate tn = case subs of
  EmptyPrS -> return $ ft
  _        -> substInFType subs ft
substInFType (Subs u ft subs) (I.TVar tn) = case subs of
  EmptyPrS -> return $ (I.TVar tn)
  _        -> substInFType subs (I.TVar tn)

------------------
-- GROUNDING --
------------------

-- Convert a type to a form u1 v (u2 v (P1 v ...)) for joins, and meets accordingly
-- This flattening is needed in order to subsequently ground the type
flatten :: PType -> PType
flatten (In (Inl NumT))         = convertSType $ mkNumT
flatten (In (Inl BoolT))        = convertSType $ mkBoolT
flatten (In (Inl TopT))         = convertSType $ mkTopT
flatten (In (Inl BotT))         = convertSType $ mkBotT
flatten (In (Inl (TVar x)))     = convertSType $ mkTVar x
flatten (In (Inr (Uni u)))      = mkUni u
flatten (In (Inr (Join p1 p2))) = case p1' of
    In (Inr (Uni u1))     -> mkJoin (mkUni u1) p2'
    In (Inr (Join p3 p4)) -> mkJoin p3 (flatten $ mkJoin p4 p2')
    _                     -> case p2' of
      In (Inr (Uni u2))                      -> mkJoin (mkUni u2) p1'
      In (Inr (Join (In (Inr (Uni u2))) p3)) -> mkJoin (mkUni u2) (flatten $ mkJoin p1' p3)
      _                                      -> mkJoin p1' p2'
  where
    p1' = flatten p1
    p2' = flatten p2
flatten (In (Inl (Arr p1 p2))) = mkArr (flatten p1) (flatten p2)
flatten (In (Inl (SRecT l p))) = mkSRecT l (flatten p)
flatten (In (Inl (And p1 p2))) = case p1' of
    In (Inr (Uni u1))     -> mkAnd (mkUni u1) p2'
    In (Inl (And p3 p4))  -> mkAnd p3 (flatten $ mkAnd p4 p2')
    -- P (And p3 p4) -> Meet (P p3) (flatten (Meet (P p4) p2'))
    In (Inr (Meet p3 p4)) -> mkAnd p3 (flatten $ mkAnd p4 p2')
    _                     -> case p2' of
      In (Inr (Uni u2))                      -> mkAnd (mkUni u2) p1'
      In (Inl (And (In (Inr (Uni u2))) p3))  -> mkAnd (mkUni u2) (flatten $ mkAnd p1' p3)
      In (Inr (Meet (In (Inr (Uni u2))) p3)) -> mkAnd (mkUni u2) (flatten $ mkAnd p1' p3)
      _                                      -> mkAnd p1' p2'
  where
    p1' = flatten p1
    p2' = flatten p2
flatten (In (Inr (Meet p1 p2))) = case p1' of
    In (Inr (Uni u1))     -> mkMeet (mkUni u1) p2'
    In (Inl (And p3 p4))  -> mkMeet p3 (flatten $ mkMeet p4 p2')
    -- P (And p3 p4) -> Meet (P p3) (flatten (Meet (P p4) p2'))
    In (Inr (Meet p3 p4)) -> mkMeet p3 (flatten $ mkMeet p4 p2')
    _                     -> case p2' of
      In (Inr (Uni u2))                      -> mkMeet (mkUni u2) p1'
      In (Inl (And (In (Inr (Uni u2))) p3))  -> mkMeet (mkUni u2) (flatten $ mkMeet p1' p3)
      In (Inr (Meet (In (Inr (Uni u2))) p3)) -> mkMeet (mkUni u2) (flatten $ mkMeet p1' p3)
      _                                      -> mkMeet p1' p2'
  where
    p1' = flatten p1
    p2' = flatten p2


--------------------------------------------------------------------------------

-- Ground the type, resulting in a new type and a non-polar substitution
ground :: PType -> STcMonad (SType, PrSubs SType)
ground (In (Inl NumT))     = return $ (mkNumT, EmptyPrS)
ground (In (Inl BoolT))    = return $ (mkBoolT, EmptyPrS)
ground (In (Inl BotT))     = return $ (mkBotT, EmptyPrS)
ground (In (Inl TopT))     = return $ (mkTopT, EmptyPrS)
ground (In (Inl (TVar x))) = return $ (mkTVar x, EmptyPrS)
ground (In (Inr (Uni u)))  = return $ (mkTVar $ translate u,
                                       Subs (translate u) (mkTVar $ translate u) EmptyPrS)
ground (In (Inr (Meet (In (Inr (Uni u))) p))) = do
  (t, theta) <- ground p
  let x       = translate u
  let t'      = if (cata (occursSTypeAlg x) t && mkTVar x /= t)
                then (mkAnd (mkTVar x) t)
                else t
  return (t', appendPr theta (Subs (translate u) t EmptyPrS))
ground (In (Inr (Meet (In (Inl (TVar alph))) p))) = do
  (t, theta) <- ground p
  let x       = translate alph
  let t'      = if (cata (occursSTypeAlg x) t && mkTVar x /= t)
                then (mkAnd (mkTVar x) t)
                else t
  return (t', theta)
ground (In (Inr (Meet (In (Inl TopT)) p2))) = ground p2
ground (In (Inr (Meet p1 (In (Inl TopT))))) = ground p1
ground (In (Inr (Meet p1 p2))) = do
  (t1, theta1)  <- ground p1
  (t2', theta2) <- ground p2
  let t2         = substInSType theta1 t2'
  if (elementOf t1 t2)
              then return (t2, appendPr theta2 theta1)
              else return (mkAnd t1 t2, appendPr theta2 theta1)
ground (In (Inr (Join (In (Inr (Uni u))) p)))     = ground p >>= \(t, theta) ->
              return $ (t, appendPr theta (Subs (translate u) t EmptyPrS))
ground (In (Inr (Join (In (Inl (TVar alph))) p))) = ground p >>= \(t, theta) ->
              return $ (t, theta)
ground (In (Inr (Join p1 p2))) = do
  (t1, theta1)  <- ground p1
  (t2', theta2) <- ground p2
  let t2         = substInSType theta1 t2'
  let t'         = if ((elementOf t1 t2) || t1 == mkTopT || t2 == mkTopT)
                   then t1
                   else mkTopT
  return (t', appendPr theta2 theta1)
ground (In (Inl (And (In (Inr (Join (In (Inr (Uni u))) p1))) p2))) = do
  (t1, theta1) <- ground $ In (Inr (Join (In (Inr (Uni u))) p1))
  (t2, theta2) <- ground p2
  if (elementOf t1 t2)
    then return (mkAnd mkTopT t2, appendPr theta2 (Subs (translate u) mkTopT EmptyPrS))
    else return (mkAnd t1 t2, appendPr theta2 theta1)
ground (In (Inl (And p1 p2))) = do
  (t1, theta1)  <- ground p1
  (t2', theta2) <- ground p2
  let t2         = substInSType theta1 t2'
  return (mkAnd t1 t2, appendPr theta2 theta1)
ground (In (Inl (Arr p1 p2))) = do
  (t1, theta1)  <- ground p1
  (t2', theta2) <- ground p2
  let t2         = substInSType theta1 t2'
  return (mkArr t1 t2, appendPr theta2 theta1)
ground (In (Inl (SRecT l p))) = do
  (t, theta)    <- ground p
  return (mkSRecT l t, theta)

--------------------------------------------------------------------------------

-- ground and destruct disjointness constraints
groundDestruct :: Dis -> STcMonad Del
groundDestruct dis = do
  (del, _) <- groundDestructDo dis
  return del

groundDestructDo :: Dis -> STcMonad (Del, PrSubs SType)
groundDestructDo EmptyDis = return (EmptyD, EmptyPrS)
groundDestructDo (Disj p1 p2 d) = do
  (d', sub)  <- groundDestructDo d
  (t1', th1) <- ground $ flatten $ groundSubstInPType sub p1
  let sub' = appendPr sub th1
  (t2', th2) <- ground $ flatten $ groundSubstInPType sub' p2
  del        <- destructD t1' t2'
  return $ (joinDel del d', appendPr sub' th2)


--------------------------------------------------------------------------------

-- Ground a substitution
groundS :: Substitution PType -> PrSubs SType -> STcMonad (PrSubs I.FType)
groundS EmptyS _ = return $ EmptyPrS
groundS (PosS u p subs) groundSub = do
  (st, groundSub') <- ground $ flatten $ groundSubstInPType groundSub p
  subs'            <- groundS subs (appendPr groundSub' groundSub)
  ft               <- translSType st
  return $ Subs (translate u) ft subs'
groundS (NegS u p subs) groundSub = do
  (st, groundSub') <- ground $ flatten $ groundSubstInPType groundSub p
  subs'            <- groundS subs (appendPr groundSub' groundSub)
  ft               <- translSType st
  return $ Subs (translate u) ft subs'

--------------------------------------------------------------
-- DISJOINTNESS REQUIREMENTS, TERM CONTEXTS & TYPE CONTEXTS --
--------------------------------------------------------------

-- lookup term variable in term context
lookupGam :: Gam -> TmName -> Maybe PType
lookupGam EmptyG            _  = Nothing
lookupGam (Gamma x1 ty gam) x2 | x1 == x2 = case lookupGam gam x2 of
  Nothing -> Just ty
  Just ty' -> Just (mkMeet ty ty')
lookupGam (Gamma _  _  gam) x  = lookupGam gam x

--------------------------------------------------------------------------------
gamContains :: Gam -> TUni -> Bool
gamContains EmptyG _ = False
gamContains (Gamma x ty gam) u = occursIn u ty || gamContains gam u

--------------------------------------------------------------------------------
-- replace type variables in gamma
replaceGam :: TUni -> TUni -> Gam -> Gam
replaceGam _ _ EmptyG = EmptyG
replaceGam alph u (Gamma x ty gam) = Gamma x (replaceTVar alph u ty) (replaceGam alph u gam)

--------------------------------------------------------------------------------
-- remove the given term variable from the term context
removeFromGam :: Gam -> TmName -> Gam
removeFromGam EmptyG _ = EmptyG
removeFromGam (Gamma x ty gam) y | x == y = removeFromGam gam y
removeFromGam (Gamma x ty gam) y = Gamma x ty (removeFromGam gam y)

--------------------------------------------------------------------------------
-- Look up disjointness requirement in type context
lookupDel :: Del -> TyName -> (Maybe SType, Del)
lookupDel  EmptyD           _  = (Nothing, EmptyD)
lookupDel (Delta u1 ty del) u2 | u1 == u2 = (Just ty, del)
lookupDel (Delta u1 ty del) u  = let (t, d) = lookupDel del u in (t, Delta u1 ty d)
--------------------------------------------------------------------------------

-- combine two term contexts into one
joinGam :: Gam -> Gam -> Gam
joinGam EmptyG            gam    = gam
joinGam gam               EmptyG = gam
joinGam (Gamma x ty gam1) gam2   = Gamma x ty (joinGam gam1 gam2)
--------------------------------------------------------------------------------

-- combine two type contexts into one
joinDel :: Del -> Del -> Del
joinDel EmptyD            del    = del
joinDel del               EmptyD = del
joinDel (Delta x ty del1) del2   = Delta x ty (joinDel del1 del2)
--------------------------------------------------------------------------------

-- combine two disjointness requirement datastructures into one
joinDis :: Dis -> Dis -> Dis
joinDis EmptyDis         dis      = dis
joinDis dis              EmptyDis = dis
joinDis (Disj x ty dis1) dis2     = Disj x ty (joinDis dis1 dis2)
--------------------------------------------------------------------------------

-- Destruct disjointness constraints
destructD :: SType -> SType -> STcMonad Del
destructD (In (TVar alph)) t                = return $ Delta (translate alph) t EmptyD
destructD t (In (TVar alph))                = return $ Delta (translate alph) t EmptyD
destructD (In (Arr t1 t2)) (In (Arr t3 t4)) = destructD t2 t4
destructD (In (And t1 t2)) t3               = joinDel <$> destructD t1 t3 <*> destructD t2 t3
destructD t1 (In (And t2 t3))               = joinDel <$> destructD t1 t2 <*> destructD t1 t3
destructD (In (SRecT l1 t1)) (In (SRecT l2 t2)) | l1 == l2 = destructD t1 t2
destructD (In (SRecT l1 t1)) (In (SRecT l2 t2)) | l1 /= l2 = return $ EmptyD
destructD (In NumT) (In (Arr t1 t2))        = return $ EmptyD
destructD (In (Arr t1 t2)) (In NumT)        = return $ EmptyD
destructD (In NumT) (In (SRecT l t) )       = return $ EmptyD
destructD (In (SRecT l t)) (In NumT)        = return $ EmptyD
destructD (In (Arr t1 t2)) (In (SRecT l t)) = return $ EmptyD
destructD (In (SRecT l t)) (In (Arr t1 t2)) = return $ EmptyD
destructD (In BoolT) (In (Arr t1 t2))       = return $ EmptyD
destructD (In (Arr t1 t2)) (In BoolT)       = return $ EmptyD
destructD (In BoolT) (In (SRecT l t))       = return $ EmptyD
destructD (In (SRecT l t)) (In BoolT)       = return $ EmptyD
destructD (In BoolT) (In NumT)              = return $ EmptyD
destructD (In NumT) (In BoolT)              = return $ EmptyD
destructD t1 t2 | topLike t1 = return $ EmptyD
destructD t1 t2 | topLike t2 = return $ EmptyD
destructD a b                = errThrow [DS $ "Destruct disjointness constraint impossible case"]


--------------------------------------------------------------------------------
-- Combine disjointness constraints so that there is one constraint for each type variable
combine :: Del -> STcMonad Del
combine  EmptyD                                   = return EmptyD
combine (Delta alph (In (And t1 t2))        cons) | t1 == t2 = combine $ Delta alph t1 cons
combine (Delta alph (In (And t1 (In TopT))) cons) = combine $ Delta alph t1 cons
combine (Delta alph (In (And (In TopT) t2)) cons) = combine $ Delta alph t2 cons
combine (Delta alph t1                      cons) = case lookupDel cons alph of
          (Nothing, _)   -> combine cons >>= \c -> return $ Delta alph t1 c
          (Just t2, del) -> combine $ Delta alph (mkAnd t1 t2) del

--------------------------------------------------------------------------------
-- reordering disjointness constraints

reorder :: Del -> STcMonad Del
reorder d = reorderDo [] d

reorderDo :: [TyName] -> Del -> STcMonad Del
reorderDo _ EmptyD = return EmptyD
reorderDo names (Delta alph t1 cons)
  = if allContained t1 names
      then do
        tail <- reorderDo (alph:names) cons
        return $ Delta alph t1 tail
      else reorderDo names (joinDel cons (Delta alph t1 EmptyD))
    where
      allContained :: SType -> [TyName] -> Bool
      allContained (In (Arr ty1 ty2)) lst = allContained ty1 lst && allContained ty2 lst
      allContained (In (And ty1 ty2)) lst = allContained ty1 lst && allContained ty2 lst
      allContained (In (TVar name))   lst = List.elem name lst
      allContained (In (SRecT l ty1)) lst = allContained ty1 lst
      allContained _                  lst = True


----------------------
-- MONAD CONVERSION --
----------------------

-- Convert monads
iTcMtoSTcM :: ITcMonad a -> STcMonad a
iTcMtoSTcM x = askCtx >>= \ctx ->
               sCtxtoICtx ctx >>= \ctx' ->
               lift $ lift $ runReaderT (runFreshMT x) ctx'


--------------------------------------
-- CONSTRUCTING FINAL TYPE AND TERM --
--------------------------------------

constructFinalType :: Del -> SType -> Scheme
constructFinalType  EmptyD          t2 = SType t2
constructFinalType (Delta u t1 sub) t2 = DForall (bind (translate u, Embed t1) (constructFinalType sub t2))

constructFinalTerm :: Fresh m => Del -> I.FExpr -> m I.FExpr
constructFinalTerm  EmptyD          fe = return $ fe
constructFinalTerm (Delta u t1 sub) fe = do
  ty <- translSType t1
  del' <- constructFinalTerm sub fe
  return $ I.DLam (bind (translate u, Embed ty) del')

--------------------
-- FREE VARIABLES --
--------------------

-- Free variables of a PHiDI monotype
freevars :: SType -> Set TyName
freevars (In (TVar x))    = Set.singleton x
freevars (In (And t1 t2)) = Set.union (freevars t1) (freevars t2)
freevars (In (Arr t1 t2)) = Set.union (freevars t1) (freevars t2)
freevars (In (SRecT l t)) = freevars t
freevars _                = Set.empty

--------------------------------------------------------------------------------

-- Free variables of an Fi+ type
freevarsF :: I.FType -> Set TyName
freevarsF (I.Arr ft1 ft2) = Set.union (freevarsF ft1) (freevarsF ft2)
freevarsF (I.And ft1 ft2) = Set.union (freevarsF ft1) (freevarsF ft2)
freevarsF (I.TVar x)      = Set.singleton (translate x)
freevarsF (I.SRecT l ft)  = freevarsF ft
freevarsF _               = Set.empty

--------------------------------------------------------------------------------

-- Free variables of an Fi+ term
freevarsE :: I.FExpr -> STcMonad (Set TyName)
freevarsE (I.Anno fe ft)  = do
  fv1 <- freevarsE fe
  return $ Set.union fv1 (freevarsF ft)
freevarsE (I.Var tn)      = return $ Set.empty
freevarsE (I.App fe1 fe2) = Set.union <$> freevarsE fe1 <*> freevarsE fe2
freevarsE (I.Lam b)       = unbind b >>= \(_,fe) -> freevarsE fe
freevarsE (I.Letrec b)    = unbind b >>= \((_,Embed _),(_,fe)) -> freevarsE fe
freevarsE (I.DLam b)      = unbind b >>= \((_,Embed _),fe) -> freevarsE fe
freevarsE (I.TApp fe ft)  = do
  fv1 <- freevarsE fe
  return $ Set.union fv1 (freevarsF ft)
freevarsE (I.Rec l fe)    = freevarsE fe
freevarsE (I.Acc fe l)    = freevarsE fe
freevarsE (I.Remove fe l Nothing)   = freevarsE fe
freevarsE (I.Remove fe l (Just ft)) = do
  fv1 <- freevarsE fe
  return $ Set.union fv1 (freevarsF ft)
freevarsE (I.Merge fe1 fe2)     = Set.union <$> freevarsE fe1 <*> freevarsE fe2
freevarsE (I.LitV i)            = return $ Set.empty
freevarsE (I.BoolV b)           = return $ Set.empty
freevarsE (I.PrimOp op fe1 fe2) = Set.union <$> freevarsE fe1 <*> freevarsE fe2
freevarsE (I.If fe1 fe2 fe3)    = Set.union <$>
                                (Set.union <$> freevarsE fe1 <*> freevarsE fe2)
                                <*> freevarsE fe3
freevarsE I.Top                 = return $ Set.empty
freevarsE (I.Pos sp fe)         = freevarsE fe
freevarsE (I.LamA b)            = unbind b >>= \((_,Embed _),fe) -> freevarsE fe
freevarsE I.Bot                 = return $ Set.empty
freevarsE (I.DRec' tb)          = return $ Set.empty

------------------
-- OCCURS CHECK --
------------------

-- OccursCheck returns true if a unification variable of the same
-- polarity occurs on the other side of the constraint.
occursCheck :: Polar TUni -> Polar PType -> Bool
occursCheck (PosT,uni) (PosT,In (Inr (Uni u1))) = uni == u1
occursCheck (NegT,uni) (NegT,In (Inr (Uni u1))) = uni == u1
occursCheck uni (pol,In (Inr (Join p1 p2))) = occursCheck uni (pol,p1)     || occursCheck uni (pol,p2)
occursCheck uni (pol,In (Inr (Meet p1 p2))) = occursCheck uni (pol,p1)     || occursCheck uni (pol,p2)
occursCheck uni (pol,In (Inl (Arr p1 p2)))  = occursCheck uni (inv pol,p1) || occursCheck uni (pol,p2)
occursCheck uni (pol,In (Inl (And p1 p2)))  = occursCheck uni (pol,p1)     || occursCheck uni (pol,p2)
occursCheck uni (pol,In (Inl (SRecT l p)))  = occursCheck uni (pol, p)
occursCheck _   _                           = False

----------------------
-- HELPER FUNCTIONS --
----------------------

-- reverse the polarity
inv :: Polarity -> Polarity
inv PosT = NegT
inv NegT = PosT

--------------------------------------------------------------------------------


-- Make type application explicit
applyVars :: I.FExpr -> [TUni] -> I.FExpr
applyVars t []     = t
applyVars t (u:us) = applyVars (I.TApp t (I.TVar (translate u))) us

--------------------------------------------------------------------------------

-- Replace a type variable by a unification variable in the given P type
replaceTVar :: TUni -> TUni -> PType -> PType
replaceTVar a u = cata (alg a u)
  where
    alg :: TUni -> TUni -> PType' PType -> PType
    alg alph uni (Inr (Uni x))  | alph == x = mkUni uni
    alg alph uni (Inl (TVar x)) | alph == (translate x) = mkUni uni
    alg alph uni t = In t

--------------------------------------------------------------------------------

-- convert a type scheme (forall a. ... T) into a context type [Γ; ∆] τ
convertScheme :: Fresh m => Scheme -> m CtxType
convertScheme (SType st) = return $ CtxSch EmptyG EmptyD (convertSType st)
convertScheme (DForall b) = do
  ((alph, Embed t1), a2) <- unbind b
  let del' = Delta (translate alph) t1 EmptyD
  CtxSch gam del ty <- convertScheme a2
  return $ CtxSch gam (joinDel del' del) ty


--------------------------------------------------------------------------------
-- to convert an SType to a PType
convertSType :: SType -> PType
convertSType = cata (In . Inl)

-- to convert an AType to a PType
convertAType :: AType -> PType
convertAType = cata (In . Inr)

--------------------------------------------------------------------------------

occursSTypeAlg :: TyName -> SType' Bool -> Bool
occursSTypeAlg u (TVar u1) = u == u1
occursSTypeAlg u st = or st

occursATypeAlg :: TUni -> AType' Bool -> Bool
occursATypeAlg u (Uni u1) = u == u1
occursATypeAlg u st = or st

occursIn :: TUni -> PType -> Bool
occursIn u = cata (occursSTypeAlg (translate u) `composeAlg` occursATypeAlg u)
--------------------------------------------------------------------------------

-- A type is an element of another type if they are equal or element of
-- one of the intersected types
elementOf :: SType -> SType -> Bool
elementOf (In t1) (In (And t2 t3)) = t1 == (And t2 t3) || (elementOf (In t1) t2) || (elementOf (In t1) t3)
elementOf t1 t2                    = t1 == t2
