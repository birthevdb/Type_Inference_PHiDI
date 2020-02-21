{-# LANGUAGE FlexibleContexts, PatternGuards, NoImplicitPrelude, LambdaCase, OverloadedStrings #-}

module SEDEL.Source.Inference
  ( tcModule, topLevelInfer ) where

import           Protolude
import           Unbound.Generics.LocallyNameless
import           Data.Text.Prettyprint.Doc ((<+>))
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Set as Set

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
      let ty           = DT.trace (show typ) $ bidirect fTerm
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
data Polar typ = PosT typ
               | NegT typ
               deriving Show
-- | Substitutions in the pr function do not include the notion of polarity
data PrSubs typ = EmptyPrS | Subs TyName typ (PrSubs typ) deriving Show

------------------
-- ⊢ E : A ~> e --
------------------

topLevelInfer :: Expr -> STcMonad (Scheme, I.FExpr)
topLevelInfer expr = do
  (gam, dis, ty, fTerm) <- infer expr
  (principal, _)        <- ground $ flatten $ ty
  del                   <- combine =<< groundDestruct dis
  fTerm'                <- constructFinalTerm del fTerm
  let ty'                = constructFinalType del principal
  return (ty', fTerm')

---------------------------------
-- ALGORITHMIC INFERENCE RULES --
-- Π ⊢ E [Γ; ∆] τ ~> e         --
---------------------------------

infer :: Expr -> STcMonad (Gam, Dis, PType, I.FExpr)

-- Γ ⊢ ⊤ : [•; •] ⊤ ~> ⊤
infer Top = return (EmptyG, EmptyDis, P TopT, I.Top)

-- Γ ⊢ i : [•; •] Int ~> i
infer (LitV n) = return (EmptyG, EmptyDis, P NumT, I.LitV n)

-- Γ ⊢ b : [•; •] Bool ~> b
infer (BoolV b) = return (EmptyG, EmptyDis, P BoolT, I.BoolV b)

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
  let gam  = Gamma x (Uni uFresh) EmptyG
  let dis  = Disj (Uni uFresh) (P TopT) EmptyDis
  return (gam, dis, Uni uFresh, I.Var (translate x))

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
      (st, _)  <- ground $ flatten (PArr (P TopT) t')
      tFi      <- translSType st
      let fterm = I.Anno (I.Lam (bind (translate x) f')) tFi
      return (gam, dis', PArr (P TopT) t', fterm)
    Just ty -> do
      (st, _)  <- ground $ flatten $ (PArr ty t')
      tFi      <- translSType st
      let fterm = I.Anno (I.Lam (bind (translate x) f')) tFi
      return (gam, dis', PArr ty t', fterm)

{-
      Π ⊢ E1 : [Γ1; ∆1] τ1 ~> e1                  u fresh
      Π ⊢ E2 : [Γ2; ∆2] τ2 ~> e2                  θ = solve(τ1 <: τ2 -> u)
  -------------------------------------------------------------------------------
  Π ⊢ E1 E2 : [θ(Γ1 ∪ Γ2); θ(∆1 ∪ ∆2 ∪ (u * ⊤))] θ(u) ~> |θ| (e1 : |τ2 -> u| e2)
-}
infer (App e1 e2) = do
  (gam1', dis1', t1', f1') <- infer e1
  (gam2', dis2', t2', f2') <- infer e2
  uFresh  <- getFreshUni
  theta   <- solve $ initC ((t1', PArr t2' (Uni uFresh)))
  let gam  = substInGam (joinGam gam1' gam2') theta
  let dis  = substInDis (joinDis (joinDis dis1' dis2') (Disj (Uni uFresh) (P TopT) EmptyDis)) theta
  -- let dis  = substInDis (joinDis dis2' (Disj (Uni uFresh) (P TopT) EmptyDis)) theta
  let t    = substInType theta (PosT (Uni uFresh))
  theta'  <- groundS theta EmptyPrS
  (st, _) <- ground $ flatten $ (PArr t2' (Uni uFresh))
  tFi     <- translSType st
  f       <- substFExpr theta' (I.App (I.Anno f1' tFi) f2')
  return (gam, dis, t, f)

{-
    Π ⊢ E1 : [Γ1; ∆1] τ1 ~> e1             Π ⊢ E2 : [Γ2; ∆2] τ2 ~> e2
  ------------------------------------------------------------------
  Π ⊢ E1 ,, E2 : [Γ1 ∪ Γ2; ∆1 ∪ ∆2 ∪ (τ1 * τ2)] τ1 & τ2 ~> e1 ,, e2
-}
infer (Merge e1 e2) = do
  (gam1', dis1', t1', f1') <- infer e1
  (gam2', dis2', t2', f2') <- infer e2
  let gam = joinGam gam1' gam2'
  let dis = joinDis (joinDis dis1' dis2') (Disj t1' t2' EmptyDis)
  return (gam, dis, PAnd t1' t2', I.Merge f1' f2')

{-
              Π ⊢ E : [Γ; ∆] τ ~> e
  -------------------------------------------
  Π ⊢ {l = E} : [Γ; ∆] { l : τ } ~> { l = e }
-}
infer (Rec l e) = do
  (gam', dis', t', f') <- infer e
  return (gam', dis', PRecT l t', I.Rec l f')

{-
  Π ⊢ E : [Γ; ∆] τ ~> e     u fresh    θ = solve(τ <: {l : u})
  -------------------------------------------------------------
  Π ⊢ E.l ; [θ(Γ); θ(∆ ∪ (u * ⊤))] θ(τ) ~> |θ|(e:|{l : u}|.l)
-}
infer (Proj e l) = do
  (gam', dis', t', f') <- infer e
  uFresh <- getFreshUni
  theta  <- solve $ initC ((t', PRecT l (Uni uFresh)))
  let gam = substInGam gam' theta
  let dis = substInDis (joinDis dis' (Disj (Uni uFresh) (P TopT) EmptyDis)) theta
  let t   = substInType theta (PosT (Uni uFresh))
  theta'  <- groundS theta EmptyPrS
  (st, _) <- ground $ flatten $ (PRecT l (Uni uFresh))
  tFi     <- translSType st
  f       <- substFExpr theta' (I.Acc (I.Anno f' tFi) l)
  return (gam, dis, t, f)

{-
  Π ⊢ E1 : [Γ1; ∆1] τ1 ~> e1
  Π, ^x : [Γ1; ∆1] τ1 ⊢ E2 : [Γ2; ∆2] τ2 ~> e2
  ------------------------------------------------------------------
  Γ ⊢ let ^x = E1 in E2 : [Γ1 ∪ Γ2; ∆2] τ2 ~> let x = e1 in e2
-}
-- infer (Let b) = do
--   (x, (e1, e2))        <- unbind b
--   (gam1, dis1, t1, f1) <- infer e1
--   (principal1, _)      <- ground $ flatten $ t1
--   del1                 <- combine =<< groundDestruct dis1
--   (gam2, dis2, t2, f2) <- localCtx (extendVarCtx x (CtxSch gam1 del1 t1)) $ infer e2
--   let gam               = joinGam gam1 gam2
--   f1'                  <- constructFinalTerm del1 f1
--   return (gam, dis2, t2, I.Letrec (bind (translate x, embed Nothing) (f1', f2)))

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
  th                       <- DT.trace (show (t1, t')) $ unification [(EmptyQ, (t1, t'))]
  case th of
    Just theta -> do
      -- Π, ^x : [Γ'; ∆'] τ' ⊢ E2 : [Γ2; ∆2] τ2 ~> e2
      (gam2, dis2, t2, f2)     <- localCtx (extendVarCtx x (CtxSch gam' del' t')) $ infer e2
      -- Γ = Γ1 ∪ Γ2
      let gam                   = substInGam (joinGam gam1 gam2) theta
      -- ∆ = ∆1 ∪ ∆2
      let dis                   = substInDis dis2 theta -- substInDis (joinDis dis1 dis2) theta
      -- θ(∆1)
      del1                     <- combine =<< groundDestruct (substInDis dis1 theta)
      -- check  ∆' |= θ(∆1)
      entails del' del1
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
  uFresh <- getFreshUni
  let cons = (initC (t1', P BoolT)) ++ (initC (t2', Uni uFresh)) ++ (initC (t3', Uni uFresh))
  theta  <- solve cons
  let gam = substInGam (joinGam gam1' (joinGam gam2' gam3')) theta
  let dis = substInDis (joinDis (joinDis dis1' (joinDis dis2' dis3')) (Disj (Uni uFresh) (P TopT) EmptyDis)) theta
  let t   = substInType theta (PosT (Uni uFresh))
  theta' <- groundS theta EmptyPrS
  f      <- substFExpr theta' (I.If f1' f2' f3')
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
  let f' = I.PrimOp op f1' f2'
  uFresh <- getFreshUni
  case op of
    Arith   _ -> do
      let cons = (initC (P NumT, Uni uFresh)) ++ (initC (t1', P NumT)) ++ (initC (t2', P NumT))
      theta  <- solve cons
      let gam = substInGam (joinGam gam1' gam2') theta
      let dis = substInDis (joinDis (joinDis dis1' dis2') (Disj (Uni uFresh) (P TopT) EmptyDis)) theta
      let t   = substInType theta (PosT (Uni uFresh))
      theta' <- groundS theta EmptyPrS
      f      <- substFExpr theta' f'
      return (gam, dis, t, f)
    Comp    _ -> do
      let cons = (initC (P BoolT, Uni uFresh)) ++ (initC (t1', P NumT)) ++ (initC (t2', P NumT))
      theta  <- solve cons
      let gam = substInGam (joinGam gam1' gam2') theta
      let dis = substInDis (joinDis (joinDis dis1' dis2') (Disj (Uni uFresh) (P TopT) EmptyDis)) theta
      let t   = substInType theta (PosT (Uni uFresh))
      theta' <- groundS theta EmptyPrS
      f      <- substFExpr theta' f'
      return (gam, dis, t, f)
    Logical _ -> do
      let cons = (initC (P BoolT, Uni uFresh)) ++ (initC (t1', P BoolT)) ++ (initC (t2', P BoolT))
      theta  <- solve cons
      let gam = substInGam (joinGam gam1' gam2') theta
      let dis = substInDis (joinDis (joinDis dis1' dis2') (Disj (Uni uFresh) (P TopT) EmptyDis)) theta
      let t   = substInType theta (PosT (Uni uFresh))
      theta' <- groundS theta EmptyPrS
      f      <- substFExpr theta' f'
      return (gam, dis, t, f)

infer (Pos p tm) = extendSourceLocation p tm $ infer tm

infer a = errThrow [DS "Infer not implemented:", DD a]

--------------------
-- ENTAILMENT LET --
--------------------

entails :: Del -> Del -> STcMonad ()
entails del1 EmptyD = return ()
entails del1 (Delta uni ty del2) = do
  ent del1 (translate uni) ty
  entails del1 del2
  where
    ent :: Del -> TyName -> SType -> STcMonad ()
    ent EmptyD u1 a = errThrow [DS "No entailment in letrec."]
    ent (Delta u1 a _) u2 b | u1 == u2 = unification [(EmptyQ, (P a, P b))] >>= \th -> case th of
      Nothing -> if (topLike b) then return () else errThrow [DS "No entailment in letrec."]
      Just x -> return ()
    ent (Delta u1 a d) u2 b = ent d u2 b

---------------------------
-- UNIFICATION ALGORITHM --
---------------------------

-- Initialization function
initC :: SubRule -> [(Queue, SubRule)]
initC (a1, a2) = [(EmptyQ, (a1, a2))]

solve :: [(Queue, SubRule)] -> STcMonad (Substitution PType)
solve [] = return $ EmptyS
solve cons = DT.trace (show cons) $ unification cons >>= \subs -> case subs of
  Just sub -> return $ sub
  Nothing -> errThrow [DS "Destruct subtyping impossible case"]

unification :: [(Queue, SubRule)] -> STcMonad (Maybe (Substitution PType))
unification []                = return $ Just EmptyS
unification ((EmptyQ, s):lqc) | substWithUni s = do
    theta1 <- makeSubst s
    sub    <- unification $ applySubstC theta1 lqc
    case sub of
      Just theta2 -> return $ Just (appendS theta1 theta2)
      Nothing     -> return $ Nothing

unification ((EmptyQ, (P NumT,  P BoolT))  :lqc) = return $ Nothing
unification ((EmptyQ, (P BoolT, P NumT))   :lqc) = return $ Nothing
unification ((EmptyQ, (P BoolT, P (TVar _))):lqc) = return $ Nothing
unification ((EmptyQ, (P NumT, P (TVar _))) :lqc) = return $ Nothing
unification ((EmptyQ, (P (TVar _), P NumT)) :lqc) = return $ Nothing
unification ((EmptyQ, (P (TVar _), P BoolT)):lqc) = return $ Nothing
unification ((EmptyQ, (P NumT,  P NumT)) :lqc) = unification lqc
unification ((EmptyQ, (P BoolT, P BoolT)):lqc) = unification lqc
unification ((EmptyQ, (P (TVar a1), P (TVar a2))):lqc) | a1 == a2 = unification lqc
unification ((EmptyQ, (P (TVar a1), P (TVar a2))):lqc) = return $ Nothing

unification ((_,(P BotT, _))     :lqc) = unification lqc
unification ((_,(_,      P TopT)):lqc) = unification lqc

unification ((q,(Join a1 a2, a))            :lqc) = unification ((q,(a1,a))  :(q,(a2,a))  :lqc)
unification ((q,(a,          Meet a1 a2))   :lqc) = unification ((q,(a,a1))  :(q,(a,a2))  :lqc)
unification ((q,(a,          P (And a1 a2))):lqc) = unification ((q,(a,P a1)):(q,(a,P a2)):lqc)
unification ((q,(a,          PAnd a1 a2))   :lqc) = unification ((q,(a,a1))  :(q,(a,a2))  :lqc)

-- unification ((q,(PAnd (PArr a1 a2) (PArr a3 a4), PArr a5 a6)):lqc) | a1 == a3 =
--   unification ((q,(PArr a1 (PAnd a2 a4),PArr a5 a6)):lqc)
-- unification ((q,(PAnd (PArr a1 a2) (PArr a3 a4), PArr a5 a6)):lqc) | a2 == a4 =
--   unification ((q,(PArr (PAnd a1 a3) a2,PArr a5 a6)):lqc)

unification ((q,(a1, P (SRecT l a2))):lqc) = unification ((pushLabel l     q,(a1,P a2)):lqc)
unification ((q,(a1, PRecT l a2))    :lqc) = unification ((pushLabel l     q,(a1,a2))  :lqc)
unification ((q,(a1, P (Arr a2 a3))) :lqc) = unification ((pushType (P a2) q,(a1,P a3)):lqc)
unification ((q,(a1, PArr a2 a3))    :lqc) = unification ((pushType a2     q,(a1,a3))  :lqc)

unification ((QA p q,(P (Arr a1 a2), a)):lqc) = unification [(q,(p, P a1))] >>= \sub -> case sub of
    Just cs -> unification ((q,(p, P a1))  :(q, (P a2, a)):lqc)
    Nothing -> unification ((q,(P TopT, a)):lqc)
unification ((QA p q,(PArr a1 a2,    a)):lqc) = unification [(q,(p, a1))]   >>= \sub -> case sub of
    Just cs -> unification ((q,(p, a1))    :(q, (a2, a)):lqc)
    Nothing -> unification ((q,(P TopT, a)):lqc)
unification ((QL l q,(P (SRecT l1 a1), a2)):lqc) | l == l1 = unification ((q,(P a1,a2)):lqc)
unification ((QL l q,(PRecT l1 a1, a2))    :lqc) | l == l1 = unification ((q,(a1,a2))  :lqc)

unification ((q,(P (And a1 a2), P a3)):lqc) | a1 == a3 || a2 == a3 = unification lqc
unification ((q,(PAnd a1 a2,    a3))  :lqc) | a1 == a3 || a2 == a3 = unification lqc
unification ((q,(P (And a1 a2), a3))  :lqc) = getFreshUni >>= \u1 ->
                                              getFreshUni >>= \u2 ->
                                              unification ((q,     (P a1,                   Uni u1)):
                                                           (q,     (P a2,                   Uni u2)):
                                                           (EmptyQ,(PAnd (Uni u1) (Uni u2), a3)):
                                                           lqc)
unification ((q,(PAnd a1 a2,    a3))  :lqc) = getFreshUni >>= \u1 ->
                                              getFreshUni >>= \u2 ->
                                              unification ((q,      (a1,                     Uni u1)):
                                                           (q,      (a2,                     Uni u2)):
                                                           (EmptyQ, (PAnd (Uni u1) (Uni u2), a3)):
                                                           lqc)
unification ((QA p q, (Uni u1, a2))    :lqc) = unification ((q,(Uni u1, PArr p a2)) :lqc)
unification ((QL l q, (Uni u1, a2))    :lqc) = unification ((q,(Uni u1, PRecT l a2)):lqc)
unification ((QA p q, (a1,     Uni u2)):lqc) = unification ((q,(P TopT, Uni u2))    :lqc)
unification ((QL l q, (a1,     Uni u2)):lqc) = unification ((q,(P TopT, Uni u2))    :lqc)

unification _ = return Nothing

-- Construct a substitution [u- |-> u /\ P] or [u+ |-> u \/ P]
makeSubst :: SubRule -> STcMonad (Substitution PType)
makeSubst (Uni u1, Uni u2) = if u1 == u2
                             then return $ EmptyS
                             else return $ NegS u1 (Meet (Uni u1) (Uni u2)) (PosS u2 (Join (Uni u1) (Uni u2)) EmptyS)
makeSubst (Uni u,  t)      = if occursCheck (NegT (Uni u)) (NegT t)
                             then errThrow [DS $ "Occurs check: cannot construct infinite type."]
                             else return $ NegS u (Meet (Uni u) t) EmptyS
makeSubst (t,       Uni u) = if occursCheck (PosT (Uni u)) (PosT t)
                             then errThrow [DS $ "Occurs check: cannot construct infinite type."]
                             else return $ PosS u (Join (Uni u) t) EmptyS
makeSubst  _               = errThrow [DS $ "Solve impossible case"]

-------------------
-- SUBSTITUTIONS --
-------------------

-- Concatenate substitutions
appendS :: Substitution typ -> Substitution typ -> Substitution typ
appendS  EmptyS        s2 = s2
appendS (PosS u ty s1) s2 = PosS u ty (appendS s1 s2)
appendS (NegS u ty s1) s2 = NegS u ty (appendS s1 s2)

-- Concatenate principality substitutions
appendPr :: PrSubs typ -> PrSubs typ -> PrSubs typ
appendPr  EmptyPrS     s2 = s2
appendPr (Subs u t s1) s2 = Subs u t (appendPr s1 s2)

-- Check whether a unification variable gets substituted
substWithUni :: SubRule -> Bool
substWithUni (Uni u, _) = True
substWithUni (_, Uni u) = True
substWithUni  _         = False

-- Apply a polar substitution to a term context
-- Negative type since it is an input
substInGam :: Gam -> Substitution PType -> Gam
substInGam EmptyG _ = EmptyG
substInGam (Gamma x ty gam) sub = Gamma x (substInType sub (NegT ty)) (substInGam gam sub)

-- Apply a polar substitution to disjointness requirements
-- Positive type since it is an output
substInDis :: Dis -> Substitution PType -> Dis
substInDis EmptyDis _ = EmptyDis
substInDis (Disj pty1 pty2 dis) sub = Disj (substInType sub (PosT pty1)) (substInType sub (PosT pty2)) (substInDis dis sub)

-- Substitute type variables with unification variables in a given type scheme
findAndSubstVars :: Gam -> Del -> PType -> STcMonad (Gam, Dis, PType, [TUni])
findAndSubstVars gam EmptyD ty = return (gam, EmptyDis, ty, [])
findAndSubstVars gam (Delta alph st del) ty | gamContains gam (translate alph) = do
  (gam', dis', ty', vars') <- findAndSubstVars gam del ty
  return (gam', Disj (Uni $ translate alph) (P st) dis', ty', (translate alph) : vars')
findAndSubstVars gam (Delta alph st del) ty = do
  (gam', dis', ty', vars') <- findAndSubstVars gam del ty
  uFresh <- getFreshUni
  let newGam = replaceGam (translate alph) uFresh gam'
  let newDis = Disj (Uni uFresh) (P st) dis'
  let newTy  = replaceTVar (translate alph) uFresh ty'
  return (newGam, newDis, newTy, uFresh : vars')

-- Apply a polar substitution to subtyping constraints
applySubstC :: (Substitution PType) -> [(Queue, SubRule)] -> [(Queue, SubRule)]
applySubstC EmptyS lqc                   = lqc
applySubstC _      []                    = []
applySubstC s      ((q, (ty1, ty2)):lqc) = ((q, (substInType s (PosT ty1),
                                                 substInType s (NegT ty2)))
                                            :(applySubstC s lqc))

-- Apply a polar substitution to a polar type
substInType :: Substitution PType -> Polar PType -> PType
substInType EmptyS (PosT ty) = ty
substInType EmptyS (NegT ty) = ty

substInType _ (PosT (P NumT))     = P NumT
substInType _ (NegT (P NumT))     = P NumT
substInType _ (PosT (P BoolT))    = P BoolT
substInType _ (NegT (P BoolT))    = P BoolT
substInType _ (PosT (P (TVar x))) = P (TVar x)
substInType _ (NegT (P (TVar x))) = P (TVar x)
substInType _ (PosT (P TopT))     = P TopT
substInType _ (NegT (P TopT))     = P TopT
substInType _ (PosT (P BotT))     = P BotT
substInType _ (NegT (P BotT))     = P BotT

substInType sub (PosT (P (Arr ty1 ty2))) = (PArr (substInType sub (NegT (P ty1))) (substInType sub (PosT (P ty2))))
substInType sub (NegT (P (Arr ty1 ty2))) = (PArr (substInType sub (PosT (P ty1))) (substInType sub (NegT (P ty2))))
substInType sub (PosT (P (And ty1 ty2))) = (PAnd (substInType sub (PosT (P ty1))) (substInType sub (PosT (P ty2))))
substInType sub (NegT (P (And ty1 ty2))) = (PAnd (substInType sub (NegT (P ty1))) (substInType sub (NegT (P ty2))))
substInType sub (PosT (P (SRecT l ty1))) = (PRecT l (substInType sub (PosT (P ty1))))
substInType sub (NegT (P (SRecT l ty1))) = (PRecT l (substInType sub (NegT (P ty1))))

substInType sub (PosT (Join ty1 ty2)) = Join (substInType sub (PosT ty1)) (substInType sub (PosT ty2))
substInType sub (NegT (Join ty1 ty2)) = Join (substInType sub (NegT ty1)) (substInType sub (NegT ty2))
substInType sub (PosT (Meet ty1 ty2)) = Meet (substInType sub (PosT ty1)) (substInType sub (PosT ty2))
substInType sub (NegT (Meet ty1 ty2)) = Meet (substInType sub (NegT ty1)) (substInType sub (NegT ty2))

substInType sub (PosT (PArr ty1 ty2)) = PArr (substInType sub (NegT ty1)) (substInType sub (PosT ty2))
substInType sub (NegT (PArr ty1 ty2)) = PArr (substInType sub (PosT ty1)) (substInType sub (NegT ty2))
substInType sub (PosT (PAnd ty1 ty2)) = PAnd (substInType sub (PosT ty1)) (substInType sub (PosT ty2))
substInType sub (NegT (PAnd ty1 ty2)) = PAnd (substInType sub (NegT ty1)) (substInType sub (NegT ty2))
substInType sub (PosT (PRecT l ty1))  = PRecT l (substInType sub (PosT ty1))
substInType sub (NegT (PRecT l ty1))  = PRecT l (substInType sub (NegT ty1))
-- interesting cases
substInType (PosS u ty sub) (PosT (Uni u1)) | u == u1 = case sub of
  EmptyS -> ty
  _      -> substInType sub (PosT ty)
substInType (PosS u ty sub) (PosT (Uni u1)) = case sub of
  EmptyS -> Uni u1
  _      -> substInType sub (PosT (Uni u1))
substInType (PosS u ty sub) (NegT (Uni u1)) = case sub of
  EmptyS -> (Uni u1)
  _      -> substInType sub (NegT (Uni u1))
substInType (NegS u ty sub) (NegT (Uni u1)) | u == u1 = case sub of
  EmptyS -> ty
  _      -> substInType sub (NegT ty)
substInType (NegS u ty sub) (NegT (Uni u1)) = case sub of
  EmptyS -> (Uni u1)
  _      -> substInType sub (NegT (Uni u1))
substInType (NegS u ty sub) (PosT (Uni u1)) = case sub of
  EmptyS -> (Uni u1)
  _      -> substInType sub (PosT (Uni u1))

-- Apply a non-polar substitution to a type
groundSubstInPType :: PrSubs SType -> PType -> PType
groundSubstInPType EmptyPrS         p           = p
groundSubstInPType sub             (Join p1 p2) = Join (groundSubstInPType sub p1) (groundSubstInPType sub p2)
groundSubstInPType sub             (Meet p1 p2) = Meet (groundSubstInPType sub p1) (groundSubstInPType sub p2)
groundSubstInPType sub             (PArr p1 p2) = PArr (groundSubstInPType sub p1) (groundSubstInPType sub p2)
groundSubstInPType sub             (PAnd p1 p2) = PAnd (groundSubstInPType sub p1) (groundSubstInPType sub p2)
groundSubstInPType sub             (PRecT l p)  = PRecT l (groundSubstInPType sub p)
groundSubstInPType (Subs u t subs) (P (TVar x)) = if u == x
                                            then groundSubstInPType subs (P t)
                                            else groundSubstInPType subs (P (TVar x))
groundSubstInPType (Subs u t subs) (Uni u1)     = if u == translate u1
                                            then groundSubstInPType subs (P t)
                                            else groundSubstInPType subs (Uni u1)
groundSubstInPType sub             (P t)        = P (substInSType sub t)


-- Apply a non-polar substitution to a PHiDI monotype
substInSType :: PrSubs SType -> SType -> SType
substInSType EmptyPrS t          = t
substInSType sub     (Arr t1 t2) = Arr (substInSType sub t1) (substInSType sub t2)
substInSType sub     (And t1 t2) = And (substInSType sub t1) (substInSType sub t2)
substInSType sub     (SRecT l t) = SRecT l (substInSType sub t)
substInSType _        NumT       = NumT
substInSType _        BoolT      = BoolT
substInSType _        TopT       = TopT
substInSType _        BotT       = BotT
substInSType (Subs name ty subs) (TVar x) | name == x = substInSType subs ty
substInSType (Subs name ty subs) (TVar x) = substInSType subs (TVar x)

-- Apply a non-polar substitution to an elaborated term (Fi+)
substFExpr :: PrSubs I.FType -> I.FExpr -> STcMonad I.FExpr
substFExpr EmptyPrS fe = return $ fe
substFExpr subs (I.Anno fe ft) = do
  fe' <- substFExpr subs fe
  ft' <- substInFType subs ft
  return $ I.Anno fe' ft'
substFExpr subs (I.Var tn) = return $ I.Var tn
substFExpr subs (I.App fe1 fe2) = do
  fe1' <- substFExpr subs fe1
  fe2' <- substFExpr subs fe2
  return $ I.App fe1' fe2'
substFExpr subs (I.Lam b) = do
  (tn, fe) <- unbind b
  fe' <- substFExpr subs fe
  return $ I.Lam (bind tn fe')
substFExpr subs (I.Letrec b) = do
  ((tn, Embed mft), (fe1, fe2)) <- unbind b
  fe1' <- substFExpr subs fe1
  fe2' <- substFExpr subs fe2
  case mft of
    Nothing -> return $ I.Letrec (bind (tn, embed Nothing) (fe1', fe2'))
    Just ft -> substInFType subs ft >>= \ft' -> return $ I.Letrec (bind (tn, embed (Just ft')) (fe1', fe2'))
substFExpr subs (I.DLam b) = do
  ((tn, Embed ft), fe) <- unbind b
  fe' <- substFExpr subs fe
  ft' <- substInFType subs ft
  return $ I.DLam (bind (tn, embed ft') fe')
substFExpr subs (I.TApp fe ft) = do
  fe' <- substFExpr subs fe
  ft' <- substInFType subs ft
  return $ I.TApp fe' ft'
substFExpr subs (I.Rec l fe) = do
  fe' <- substFExpr subs fe
  return $ I.Rec l fe'
substFExpr subs (I.Acc fe l) = do
  fe' <- substFExpr subs fe
  return $ I.Acc fe' l
substFExpr subs (I.Remove fe l Nothing) = do
  fe' <- substFExpr subs fe
  return $ I.Remove fe' l Nothing
substFExpr subs (I.Remove fe l (Just ft)) = do
  fe' <- substFExpr subs fe
  ft' <- substInFType subs ft
  return $ I.Remove fe' l (Just ft')
substFExpr subs (I.Merge fe1 fe2) = do
  fe1' <- substFExpr subs fe1
  fe2' <- substFExpr subs fe2
  return $ I.Merge fe1' fe2'
substFExpr subs (I.LitV i) = return $ I.LitV i
substFExpr subs (I.BoolV b) = return $ I.BoolV b
substFExpr subs (I.PrimOp op fe1 fe2) = do
  fe1' <- substFExpr subs fe1
  fe2' <- substFExpr subs fe2
  return $ I.PrimOp op fe1' fe2'
substFExpr subs (I.If fe1 fe2 fe3) = do
  fe1' <- substFExpr subs fe1
  fe2' <- substFExpr subs fe2
  fe3' <- substFExpr subs fe3
  return $ I.If fe1' fe2' fe3'
substFExpr subs I.Top = return I.Top
substFExpr subs (I.Pos sp fe) = do
  fe' <- substFExpr subs fe
  return $ I.Pos sp fe'
substFExpr subs (I.LamA b) = do
  ((tn, Embed ft), fe) <- unbind b
  fe' <- substFExpr subs fe
  ft' <- substInFType subs ft
  return $ I.LamA (bind (tn, embed ft') fe')
substFExpr subs I.Bot = return I.Bot
substFExpr subs (I.DRec' tb) = return $ I.DRec' tb


-- Apply a non-polar substitution to an elaborated type (Fi+)
substInFType :: PrSubs I.FType -> I.FType -> STcMonad (I.FType)
substInFType EmptyPrS ft = return ft
substInFType subs I.NumT = return I.NumT
substInFType subs I.BoolT = return I.BoolT
substInFType subs I.TopT = return I.TopT
substInFType subs I.BotT = return I.BotT
substInFType subs (I.Arr ft1 ft2) = do
  ft1' <- substInFType subs ft1
  ft2' <- substInFType subs ft2
  return $ I.Arr ft1' ft2'
substInFType subs (I.And ft1 ft2) = do
  ft1' <- substInFType subs ft1
  ft2' <- substInFType subs ft2
  return $ I.And ft1' ft2'
substInFType subs (I.SRecT l ft) = do
  ft' <- substInFType subs ft
  return $ I.SRecT l ft'
substInFType (Subs u ft subs) (I.TVar tn) | u == translate tn = case subs of
  EmptyPrS -> return $ ft
  _ -> substInFType subs ft
substInFType (Subs u ft subs) (I.TVar tn) = case subs of
  EmptyPrS -> return $ (I.TVar tn)
  _ -> substInFType subs (I.TVar tn)
substInFType subs (I.DForall b) = return $ I.DForall b
substInFType subs (I.OpAbs b) = return $ I.OpAbs b
substInFType subs (I.OpApp ft1 ft2) = return $ I.OpApp ft1 ft2

------------------
-- PRINCIPALITY --
------------------

-- Convert a type to a form u1 v (u2 v (P1 v ...)) for joins, and meets accordingly
-- This flattening is needed in order to subsequently ground the type
flatten :: PType -> PType
flatten (P t)        = P t
flatten (Uni u)      = Uni u
flatten (Join p1 p2) = case p1' of
    Uni  u1    -> Join (Uni u1) p2'
    Join p3 p4 -> Join p3 (flatten (Join p4 p2'))
    _          -> case p2' of
      Uni   u2         -> Join (Uni u2) p1'
      Join (Uni u2) p3 -> Join (Uni u2) (flatten (Join p1' p3))
      _                -> Join p1' p2'
  where
    p1' = flatten p1
    p2' = flatten p2
flatten (PArr p1 p2) = PArr (flatten p1) (flatten p2)
flatten (PRecT l p)  = PRecT l (flatten p)
flatten (PAnd p1 p2) = case p1' of
    Uni  u1       -> PAnd (Uni u1) p2'
    PAnd p3 p4    -> PAnd p3 (flatten (PAnd p4 p2'))
    P (And p3 p4) -> Meet (P p3) (flatten (Meet (P p4) p2'))
    Meet p3 p4    -> PAnd p3 (flatten (PAnd p4 p2'))
    _             -> case p2' of
      Uni  u2          -> PAnd (Uni u2) p1'
      PAnd (Uni u2) p3 -> PAnd (Uni u2) (flatten (PAnd p1' p3))
      Meet (Uni u2) p3 -> PAnd (Uni u2) (flatten (PAnd p1' p3))
      _                -> PAnd p1' p2'
  where
    p1' = flatten p1
    p2' = flatten p2
flatten (Meet p1 p2) = case p1' of
    Uni  u1       -> Meet (Uni u1) p2'
    PAnd p3 p4    -> Meet p3 (flatten (Meet p4 p2'))
    P (And p3 p4) -> Meet (P p3) (flatten (Meet (P p4) p2'))
    Meet p3 p4    -> Meet p3 (flatten (Meet p4 p2'))
    _             -> case p2' of
      Uni  u2          -> Meet (Uni u2) p1'
      PAnd (Uni u2) p3 -> Meet (Uni u2) (flatten (Meet p1' p3))
      Meet (Uni u2) p3 -> Meet (Uni u2) (flatten (Meet p1' p3))
      _                -> Meet p1' p2'
  where
    p1' = flatten p1
    p2' = flatten p2

-- Ground the type, resulting in a new type and a non-polar substitution
ground :: PType -> STcMonad (SType, PrSubs SType)
ground (P (And t1 TopT))        = return (t1, EmptyPrS)
ground (P (And TopT t2))        = return (t2, EmptyPrS)
ground (P t)                    = return $ (t, EmptyPrS)
ground (Uni u)                  = return $ (TVar $ translate u, Subs (translate u) (TVar $ translate u) EmptyPrS)
ground (Meet (Uni u) p)         = do
  (t, theta) <- ground p
  let x       = translate u
  let t'      = if (occursIn x t && TVar x /= t) then (And (TVar x) t) else t
  return (t', appendPr theta (Subs (translate u) t EmptyPrS))
ground (Meet (P (TVar alph)) p) = do
  (t, theta) <- ground p
  let x       = translate alph
  let t'      = if (occursIn x t && TVar x /= t) then (And (TVar x) t) else t
  return (t', theta)
ground (Meet (P TopT) p2) = ground p2
ground (Meet p1 (P TopT)) = ground p1
ground (Meet p1 p2)             = do
  (t1, theta1) <- ground p1
  (t2', theta2) <- ground p2
  let t2 = substInSType theta1 t2'
  if (elementOf t1 t2)
              then return (t2, appendPr theta2 theta1)
              else return (And t1 t2, appendPr theta2 theta1)
ground (Join (Uni u) p)         = ground p >>= \(t, theta) -> return $ (t, appendPr theta (Subs (translate u) t EmptyPrS))
ground (Join (P (TVar alph)) p) = ground p >>= \(t, theta) -> return $ (t, theta)
ground (Join p1 p2)             = do
  (t1, theta1) <- ground p1
  (t2', theta2) <- ground p2
  let t2 = substInSType theta1 t2'
  let t'        = if (elementOf t1 t2) then t1 else TopT
  return (t', appendPr theta2 theta1)
ground (PAnd p1 p2)             = do
  (t1, theta1) <- ground p1
  (t2', theta2) <- ground p2
  let t2 = substInSType theta1 t2'
  return (And t1 t2, appendPr theta2 theta1)
ground (PArr p1 p2)             = do
  (t1, theta1) <- ground p1
  (t2', theta2) <- ground p2
  let t2 = substInSType theta1 t2'
  return (Arr t1 t2, appendPr theta2 theta1)
ground (PRecT l p)              = do
  (t, theta)   <- ground p
  return (SRecT l t, theta)

-- ground and subsequently destruct disjointness constraints
groundDestruct :: Dis -> STcMonad Del
groundDestruct  EmptyDis = return EmptyD
groundDestruct (Disj p1 p2 d) = do
  (t1', _) <- ground $ flatten p1
  (t2', _) <- ground $ flatten p2
  del      <- destructD t1' t2'
  d'       <- groundDestruct d
  return $ joinDel del d'

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
  Just ty' -> Just (Meet ty ty')
lookupGam (Gamma _  _  gam) x  = lookupGam gam x

gamContains :: Gam -> TUni -> Bool
gamContains EmptyG _ = False
gamContains (Gamma x ty gam) u = occursInP u ty || gamContains gam u

-- replace type variables in gamma
replaceGam :: TUni -> TUni -> Gam -> Gam
replaceGam _ _ EmptyG = EmptyG
replaceGam alph u (Gamma x ty gam) = Gamma x (replaceTVar alph u ty) (replaceGam alph u gam)

-- remove the given term variable from the term context
removeFromGam :: Gam -> TmName -> Gam
removeFromGam EmptyG _ = EmptyG
removeFromGam (Gamma x ty gam) y | x == y = removeFromGam gam y
removeFromGam (Gamma x ty gam) y = Gamma x ty (removeFromGam gam y)

-- Look up disjointness requirement in type context
lookupDel :: Del -> TyName -> (Maybe SType, Del)
lookupDel  EmptyD           _  = (Nothing, EmptyD)
lookupDel (Delta u1 ty del) u2 | u1 == u2 = (Just ty, del)
lookupDel (Delta u1 ty del) u  = let (t, d) = lookupDel del u in (t, Delta u1 ty d)

-- combine two term contexts into one
joinGam :: Gam -> Gam -> Gam
joinGam EmptyG            gam    = gam
joinGam gam               EmptyG = gam
joinGam (Gamma x ty gam1) gam2   = Gamma x ty (joinGam gam1 gam2)

-- combine two type contexts into one
joinDel :: Del -> Del -> Del
joinDel EmptyD            del    = del
joinDel del               EmptyD = del
joinDel (Delta x ty del1) del2   = Delta x ty (joinDel del1 del2)

-- combine two disjointness requirement datastructures into one
joinDis :: Dis -> Dis -> Dis
joinDis EmptyDis         dis      = dis
joinDis dis              EmptyDis = dis
joinDis (Disj x ty dis1) dis2     = Disj x ty (joinDis dis1 dis2)

-- Destruct disjointness constraints
destructD :: SType -> SType -> STcMonad Del
destructD (TVar alph) t             = return $ Delta (translate alph) t EmptyD
destructD t (TVar alph)             = return $ Delta (translate alph) t EmptyD
destructD t1 t2 | topLike t1        = return $ EmptyD
destructD t1 t2 | topLike t2        = return $ EmptyD
destructD (Arr t1 t2) (Arr t3 t4)   = destructD t2 t4
destructD (And t1 t2) t3            = do
  del1 <- destructD t1 t3
  del2 <- destructD t2 t3
  return $ joinDel del1 del2
destructD t1 (And t2 t3)            = do
  del1 <- destructD t1 t2
  del2 <- destructD t1 t3
  return $ joinDel del1 del2
destructD (SRecT l1 t1) (SRecT l2 t2) | l1 == l2 = destructD t1 t2
destructD (SRecT l1 t1) (SRecT l2 t2) | l1 /= l2 = return $ EmptyD
destructD NumT (Arr t1 t2)          = return $ EmptyD
destructD (Arr t1 t2) NumT          = return $ EmptyD
destructD NumT (SRecT l t)          = return $ EmptyD
destructD (SRecT l t) NumT          = return $ EmptyD
destructD (Arr t1 t2) (SRecT l t)   = return $ EmptyD
destructD (SRecT l t) (Arr t1 t2)   = return $ EmptyD
destructD BoolT (Arr t1 t2)         = return $ EmptyD
destructD (Arr t1 t2) BoolT         = return $ EmptyD
destructD BoolT (SRecT l t)         = return $ EmptyD
destructD (SRecT l t) BoolT         = return $ EmptyD
destructD BoolT NumT                = return $ EmptyD
destructD NumT BoolT                = return $ EmptyD
destructD _ _                       = errThrow [DS $ "Destruct disjointness constraint impossible case"]


-- Combine disjointness constraints so that there is one constraint for each type variable
combine :: Del -> STcMonad Del
combine  EmptyD                               = return EmptyD
combine (Delta alph (And t1 t2)   cons) | t1 == t2 = combine $ Delta alph t1 cons
combine (Delta alph (And t1 TopT) cons) = combine $ Delta alph t1 cons
combine (Delta alph (And TopT t2) cons) = combine $ Delta alph t2 cons
combine (Delta alph t1            cons) = case lookupDel cons alph of
          (Nothing, _)   -> combine cons >>= \c -> return $ Delta alph t1 c
          (Just t2, del) -> combine $ Delta alph (And t1 t2) del

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
freevars  NumT        = Set.empty
freevars  BoolT       = Set.empty
freevars  TopT        = Set.empty
freevars  BotT        = Set.empty
freevars (TVar x)     = Set.singleton x
freevars (And t1 t2)  = Set.union (freevars t1) (freevars t2)
freevars (Arr t1 t2)  = Set.union (freevars t1) (freevars t2)
freevars (SRecT l t)  = freevars t

-- Free variables of an Fi+ type
freevarsF :: I.FType -> Set TyName
freevarsF (I.Arr ft1 ft2) = Set.union (freevarsF ft1) (freevarsF ft2)
freevarsF (I.And ft1 ft2) = Set.union (freevarsF ft1) (freevarsF ft2)
freevarsF (I.TVar x) = Set.singleton (translate x)
freevarsF (I.SRecT l ft) = freevarsF ft
freevarsF _ = Set.empty

-- Free variables of an Fi+ term
freevarsE :: I.FExpr -> STcMonad (Set TyName)
freevarsE (I.Anno fe ft) = do
  fv1 <- freevarsE fe
  return $ Set.union fv1 (freevarsF ft)
freevarsE (I.Var tn) = return $ Set.empty
freevarsE (I.App fe1 fe2) = do
  fv1 <- freevarsE fe1
  fv2 <- freevarsE fe2
  return $ Set.union fv1 fv2
freevarsE (I.Lam b) = do
  (tn, fe) <- unbind b
  fv1 <- freevarsE fe
  return $ fv1
freevarsE (I.Letrec b) = do
  ((tn, Embed mft), (fe1, fe2)) <- unbind b
  -- fv1 <- freevarsE fe1
  fv2 <- freevarsE fe2
  -- return $ Set.union fv1 fv2
  return $ fv2
freevarsE (I.DLam b) = do
  ((tn, Embed ft), fe) <- unbind b
  fv1 <- freevarsE fe
  return $ fv1
freevarsE (I.TApp fe ft) = do
  fv1 <- freevarsE fe
  return $ Set.union fv1 (freevarsF ft)
freevarsE (I.Rec l fe) = do
  fv1 <- freevarsE fe
  return $ fv1
freevarsE (I.Acc fe l) = do
  fv1 <- freevarsE fe
  return $ fv1
freevarsE (I.Remove fe l Nothing) = do
  fv1 <- freevarsE fe
  return $ fv1
freevarsE (I.Remove fe l (Just ft)) = do
  fv1 <- freevarsE fe
  return $ Set.union fv1 (freevarsF ft)
freevarsE (I.Merge fe1 fe2) = do
  fv1 <- freevarsE fe1
  fv2 <- freevarsE fe2
  return $ Set.union fv1 fv2
freevarsE (I.LitV i) = return $ Set.empty
freevarsE (I.BoolV b) = return $ Set.empty
freevarsE (I.PrimOp op fe1 fe2) = do
  fv1 <- freevarsE fe1
  fv2 <- freevarsE fe2
  return $ Set.union fv1 fv2
freevarsE (I.If fe1 fe2 fe3) = do
  fv1 <- freevarsE fe1
  fv2 <- freevarsE fe2
  fv3 <- freevarsE fe3
  return $ Set.union (Set.union fv1 fv2) fv3
freevarsE I.Top = return $ Set.empty
freevarsE (I.Pos sp fe) = do
  fv1 <- freevarsE fe
  return $ fv1
freevarsE (I.LamA b) = do
  ((tn, Embed ft), fe) <- unbind b
  fv1 <- freevarsE fe
  return $ fv1
freevarsE I.Bot = return $ Set.empty
freevarsE (I.DRec' tb) = return $ Set.empty

------------------
-- OCCURS CHECK --
------------------

-- OccursCheck returns true if a unification variable of the same
-- polarity occurs on the other side of the constraint.
occursCheck :: Polar PType -> Polar PType -> Bool
occursCheck u              (PosT (P st))       = False
occursCheck u              (NegT (P st))       = False
occursCheck (PosT (Uni u)) (PosT (Uni u1))     = u == u1
occursCheck (PosT (Uni u)) (NegT (Uni u1))     = False
occursCheck (NegT (Uni u)) (PosT (Uni u1))     = False
occursCheck (NegT (Uni u)) (NegT (Uni u1))     = u == u1
occursCheck u              (PosT (Join p1 p2)) = occursCheck u (PosT p1) || occursCheck u (PosT p2)
occursCheck u              (NegT (Join p1 p2)) = occursCheck u (NegT p1) || occursCheck u (NegT p2)
occursCheck u              (PosT (Meet p1 p2)) = occursCheck u (PosT p1) || occursCheck u (PosT p2)
occursCheck u              (NegT (Meet p1 p2)) = occursCheck u (NegT p1) || occursCheck u (NegT p2)
occursCheck u              (PosT (PArr p1 p2)) = occursCheck u (NegT p1) || occursCheck u (PosT p2)
occursCheck u              (NegT (PArr p1 p2)) = occursCheck u (PosT p1) || occursCheck u (NegT p2)
occursCheck u              (PosT (PAnd p1 p2)) = occursCheck u (PosT p1) || occursCheck u (PosT p2)
occursCheck u              (NegT (PAnd p1 p2)) = occursCheck u (NegT p1) || occursCheck u (NegT p2)
occursCheck u              (PosT (PRecT l p))  = occursCheck u (PosT p)
occursCheck u              (NegT (PRecT l p))  = occursCheck u (NegT p)
occursCheck _              _                   = False

----------------------
-- HELPER FUNCTIONS --
----------------------

-- Make type application explicit
applyVars :: I.FExpr -> [TUni] -> I.FExpr
applyVars t []     = t
applyVars t (u:us) = applyVars (I.TApp t (I.TVar (translate u))) us

-- Replace a type variable by a unification variable in the given P type
replaceTVar :: TUni -> TUni -> PType -> PType
replaceTVar alph u (Uni x)      | alph == x = Uni u
replaceTVar alph u (P (TVar x)) | alph == (translate x) = Uni u
replaceTVar alph u (P (Arr p1 p2))          = PArr (replaceTVar alph u (P p1)) (replaceTVar alph u (P p2))
replaceTVar alph u (PArr p1 p2)             = PArr (replaceTVar alph u p1)     (replaceTVar alph u p2)
replaceTVar alph u (P (And p1 p2))          = PAnd (replaceTVar alph u (P p1)) (replaceTVar alph u (P p2))
replaceTVar alph u (PAnd p1 p2)             = PAnd (replaceTVar alph u p1)     (replaceTVar alph u p2)
replaceTVar alph u (P (SRecT l p))          = PRecT l (replaceTVar alph u (P p))
replaceTVar alph u (PRecT l p)              = PRecT l (replaceTVar alph u p)
replaceTVar _    _  ty                      = ty

-- convert a type scheme (forall a. ... T) into a context type [Γ; ∆] τ
convertScheme :: Fresh m => Scheme -> m CtxType
convertScheme (SType st) = return $ CtxSch EmptyG EmptyD (P st)
convertScheme (DForall b) = do
  ((alph, Embed t1), a2) <- unbind b
  let del' = Delta (translate alph) t1 EmptyD
  CtxSch gam del ty <- convertScheme a2
  return $ CtxSch gam (joinDel del' del) ty

-- Check if a unification variable occurs in a type
occursIn :: TyName -> SType -> Bool
occursIn u  NumT       = False
occursIn u  BoolT      = False
occursIn u (Arr s1 s2) = (occursIn u s1) || (occursIn u s2)
occursIn u (And s1 s2) = (occursIn u s1) || (occursIn u s2)
occursIn u (TVar u1)   = u == u1
occursIn u (SRecT l s) = occursIn u s
occursIn u  TopT       = False
occursIn u  BotT       = False

occursInP :: TUni -> PType -> Bool
occursInP u (P ty)       = occursIn (translate u) ty
occursInP u (Uni u1)     = u == u1
occursInP u (Join t1 t2) = (occursInP u t1) || (occursInP u t2)
occursInP u (Meet t1 t2) = (occursInP u t1) || (occursInP u t2)
occursInP u (PArr t1 t2) = (occursInP u t1) || (occursInP u t2)
occursInP u (PAnd t1 t2) = (occursInP u t1) || (occursInP u t2)
occursInP u (PRecT l t)  = occursInP u t

-- A type is an element of another type if they are equal or element of
-- one of the intersected types
elementOf :: SType -> SType -> Bool
elementOf t1 (And t2 t3) = t1 == (And t2 t3) || (elementOf t1 t2) || (elementOf t1 t3)
elementOf t1 t2          = t1 == t2
