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
import qualified SEDEL.Intermediate.Syntax as I
import           SEDEL.Util
import           SEDEL.Common
import           SEDEL.Source.Desugar
import           SEDEL.Translations

-- import Debug.Trace as DT


tcModule :: Module -> STcMonad (Scheme, I.FExpr)
tcModule m = do
 let (DefDecl mainE) = mainExpr m
 let  main           = desugarTmBind mainE
 (ty, target)       <- tcM main
 return (ty, target)
 where
   tcM :: TmBind -> STcMonad (Scheme, I.FExpr)
   tcM main = tcTmDecl main >>= \(dbind, (_, e)) -> return $ (snd dbind, e)


tcTmDecl :: TmBind -> STcMonad ((TmName, Scheme), (I.TmName, I.FExpr))
tcTmDecl decl =
  lookupTmDef (s2n n) >>= \case
    Nothing -> do
      (typ, fTerm)    <- topLevelInfer term
      return ((s2n n, typ), (s2n n, fTerm))
    Just _  -> errThrow [DS $ "Multiple definitions of" <+> Pretty.pretty n]
  where
    (n, term) = normalizeTmDecl decl


-- | Rule representing 1 subtyping constraint of the form T1 <: T2
type SubRule = (PType, PType)
-- | Rule representing 1 disjointness constraint of the form P1 * P2
type DisRule = (PType, PType)

-- | Collection of subtyping constraints
data SubCons = EmptyC
             | SeqC SubRule SubCons
             deriving Show

-- | Collection of disjointness constraints (P types)
data DisCons = EmptyD
             | SeqD DisRule DisCons
             deriving Show
-- | Collection of disjointness constraints (S types) of the form (alpha * T)
data Delta = EmptyDelta
           | Del (SType, SType) Delta
           deriving Show
-- | Queue consisting of labels and/or types
data Queue = EmptyQ
           | QL Label Queue
           | QA PType Queue
           deriving Show
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
data PrSubs typ = EmptyPrS | Subs TUni typ (PrSubs typ) deriving Show

-----------------------
-- Γ ⊢ E : A ~> e ~> e
-----------------------

topLevelInfer :: Expr -> STcMonad (Scheme, I.FExpr)
topLevelInfer expr = do
  -- Infer type, subtyping constraints and disjointness constraints using the
  -- algorithmic inference rules
  (ty, sub, dis, fTerm) <- infer expr
  -- Solve the subtyping constraints using a unification algorithm
  theta                 <- solve $ initC sub
  -- Ground the type after flattening it and applying the substitution
  (principal, theta')   <- ground $ flatten $ substInType theta (PosT ty)
  -- Solve and simplify the disjointness constraints
  delta                 <- combine =<< destructD =<< groundD =<< applySubstD theta dis
  -- Ground the substitution
  subs                  <- groundS theta EmptyPrS
  fTerm'                <- substFExpr subs fTerm
  -- Free variables in annotations and inferred type
  fvsE                  <- freevarsE fTerm'
  let fvsP               = freevars principal
  let fvs                = Set.toList (Set.union fvsP fvsE)
  -- Construct the final term by abstracting over the free type variables in
  -- the final type
  finalFTerm            <- constructFinalTerm delta fvs fTerm'
  -- Construct the final type by abstracting over the free variables
  let finalType          = constructFinalType delta fvs principal
  return (finalType, finalFTerm)

-------------------------------
-- Algorithmic inference rules:
-- Γ ⊢ E : P ; C ; D ~> e
-------------------------------

infer :: Expr -> STcMonad (PType, SubCons, DisCons, I.FExpr)

-- Γ ⊢ ⊤ : ⊤ ; • ; • ~> ⊤
infer Top = return (P TopT, EmptyC, EmptyD, I.Top)

-- Γ ⊢ i : Int ; • ; • ~> i
infer (LitV n) = return (P NumT, EmptyC, EmptyD, I.LitV n)

-- Γ ⊢ b : Bool ; • ; • ~> b
infer (BoolV b) = return (P BoolT, EmptyC, EmptyD, I.BoolV b)

{- |
   (x : ∀ (a * T_2).T) ∈ Γ        u fresh
------------------------------------------
Γ ⊢ x : [a -> u] T ; • ; u * T_2 ~> x |u|

   (x : u) ∈ Γ
-----------------------
Γ ⊢ x : u ; • ; • ~> x
-}
infer (Var x) = do
  let fterm = I.Var (translate x)
  lookupVarTy x >>= \var -> case var of
    CtxUni  u          -> return (Uni u, EmptyC, EmptyD, fterm)
    CtxSch (SType t)   -> return (P t,   EmptyC, EmptyD, fterm)
    CtxSch (DForall b) -> do
      (t', d', vars) <- findAndSubstVars (DForall b)
      return (t', EmptyC, d', applyVars fterm vars)

{- |
  Γ , x : u ⊢ E : P ; C ; D ~> e         u fresh
  -----------------------------------------------
  Γ ⊢ \x . E : u -> P ; C ; D ~> \x . e |u -> P|
  -}
infer (Lam b) = do
  (x, e) <- unbind b
  uFresh <- getFreshUni
  (t', c', d', f') <- localCtx (extendVarCtx x (CtxUni uFresh)) $ infer e
  let p' = PArr (Uni uFresh) t'
  tFi <- translPType p'
  let fterm = I.Anno (I.Lam (bind (translate x) f')) tFi
  return (p', c', d', fterm)

{- |
Γ ⊢ E1 : P1 ; C1 ; D1 ~> e1
Γ ⊢ E2 : P2 ; C2 ; D2 ~> e2            u fresh
--------------------------------------------------------
Γ ⊢ E1 E2 : u ; C1, C2, P1 <: P2 -> u ; D1, D2 ~> e1 e2
-}
infer (App e1 e2) = do
  (t1', c1', d1', f1') <- infer e1
  (t2', c2', d2', f2') <- infer e2
  uFresh <- getFreshUni
  let newC = SeqC (t1', PArr t2' (Uni uFresh)) EmptyC
  let c' = appendC (appendC c1' c2') newC
  let d' = appendD d1' d2'
  return (Uni uFresh, c', d', I.App f1' f2')

{- |
Γ ⊢ E1 : P1 ; C1 ; D1 ~> e1
Γ ⊢ E2 : P2 ; C2 ; D2 ~> e2             u fresh
-----------------------------------------------------------------
Γ ⊢ E1,,E2 : u ; C1, C2, P1&P2 <: u; D1, D2, P1 * P2 ~> e1 ,, e2
-}
infer (Merge e1 e2) = do
  (t1', c1', d1', f1') <- infer e1
  (t2', c2', d2', f2') <- infer e2
  uFresh <- getFreshUni
  let newC = SeqC (PAnd t1' t2', Uni uFresh) EmptyC
  let c' = appendC (appendC c1' c2') newC
  let d' = SeqD (t1', t2') (appendD d1' d2')
  return (Uni uFresh, c', d', I.Merge f1' f2')

{- |
Γ ⊢ E : P ; C ; D ~> e
-------------------------------------------
Γ ⊢ {l = E} : {l : P} ; C ; D ~> { l = e }
-}
infer (Rec l e) = do
  (t', c', d', f') <- infer e
  return (PRecT l t', c', d', I.Rec l f')

{- |
Γ ⊢ E : P ; C ; D ~> e        u fresh
-----------------------------------------
Γ ⊢ E.l : u ; C, P <: {l : u} ; D ~> e.l
-}
infer (Proj e l) = do
  (t', c', d', f') <- infer e
  uFresh <- getFreshUni
  let newC = SeqC (t', PRecT l (Uni uFresh)) EmptyC
  return (Uni uFresh, appendC c' newC, d', I.Acc f' l)

{- |
Γ ⊢ E1 : A ~> e1
Γ, x : A ⊢ E2 : P ; C ; D ~> e2
-------------------------------------------------------------
Γ ⊢ let x = E1 in E2 : P ; C ; D ~> let x : A = e1 in e2
-}
infer (Let b) = do
  (x, (e1, e2)) <- unbind b
  (a', f1') <- topLevelInfer e1
  (t', c', d', f2') <- localCtx (extendVarCtx x (CtxSch a')) $ infer e2
  aFi <- translType a'
  return (t', c', d', I.Letrec (bind (translate x, embed (Just aFi)) (f1', f2')))

{- |
Γ ⊢ E1 : P1 ; C1 ; D1 ~> e1
Γ ⊢ E2 : P2 ; C2 ; D2 ~> e2
Γ ⊢ E3 : P3 ; C3 ; D3 ~> e3           u fresh
-----------------------------------------------------------------------------------------------------
Γ ⊢ If E1 E2 E3 : u ; C1, C2, C3, P1 <: Bool, P2 <: u, P3 <: u ; D1, D2, D3 ~> if e1 then e2 else e3
-}
infer (If e1 e2 e3) = do
  (t1', c1', d1', f1') <- infer e1
  (t2', c2', d2', f2') <- infer e2
  (t3', c3', d3', f3') <- infer e3
  uFresh <- getFreshUni
  let newC = SeqC (t1', P BoolT) (SeqC (t2', Uni uFresh) (SeqC (t3', Uni uFresh) EmptyC))
  let c' = appendC c1' (appendC c2' (appendC c3' newC))
  let d' = appendD d1' (appendD d2' d3')
  return (Uni uFresh, c', d', I.If f1' f2' f3')

{- |
Γ ⊢ E1 : P1 ; C1 ; D1 ~> e1
Γ ⊢ E2 : P2 ; C2 ; D2 ~> e2        u fresh
----------------------------------------------------------------------------------------------
Γ ⊢ PrimOp Op E1 E2 : u ; C1, C2, P1 <: u , u <: P2 ; D1, D2 ~> PrimOp Op e1 e2
-}
infer (PrimOp op e1 e2) = do
  (t1', c1', d1', f1') <- infer e1
  (t2', c2', d2', f2') <- infer e2
  let f' = I.PrimOp op f1' f2'
  let d' = appendD d1' d2'
  uFresh <- getFreshUni
  case op of
    Arith   _ -> do
      let newC = SeqC (P NumT, Uni uFresh) (SeqC (t1', P NumT) (SeqC (t2', P NumT) EmptyC))
      let c' = appendC c1' (appendC c2' newC)
      return (Uni uFresh, c', d', f')
    Comp    _ -> do
      let newC = SeqC (P BoolT, Uni uFresh) (SeqC (t1', P NumT) (SeqC (t2', P NumT) EmptyC))
      let c' = appendC c1' (appendC c2' newC)
      return (Uni uFresh, c', d', f')
    Logical _ -> do
      let newC = SeqC (P BoolT, Uni uFresh) (SeqC (t1', P BoolT) (SeqC (t2', P BoolT) EmptyC))
      let c' = appendC c1' (appendC c2' newC)
      return (Uni uFresh, c', d', f')

infer (Pos p tm) = extendSourceLocation p tm $ infer tm

infer a = errThrow [DS "Infer not implemented:", DD a]

-------------------------
-- UNIFICATION ALGORITHM
-------------------------

-- Initialization function
initC :: SubCons -> [SubRule]
initC EmptyC            = []
initC (SeqC (a1, a2) c) = [(a1, a2)] ++ initC(c)


-- Unification algorithm
solve :: [SubRule] -> STcMonad (Substitution PType)
solve [] = return EmptyS
solve (s:lqc) | substWithUni s = do
  theta1 <- makeSubst s
  theta2 <- solve $ applySubstC theta1 lqc
  return $ appendS theta1 theta2
solve (s:lqc) = do
  des    <- destructC s
  solve $ des ++ lqc


-- Destruct the subtyping constraints
destructC :: SubRule -> STcMonad [SubRule]
destructC (P NumT,  P NumT)  = return []
destructC (P BoolT, P BoolT) = return []
destructC (P BotT,  _)       = return []
destructC (_,       P TopT)  = return []

destructC (Join a1 a2, a)             = return [(a1, a),(a2, a)]
destructC (a,          Meet a1 a2)    = return [(a, a1),(a, a2)]
destructC (a1,         P (And a2 a3)) = return [(a1, P a2), (a1, P a3)]
destructC (a1,         PAnd a2 a3)    = return [(a1, a2), (a1, a3)]

destructC (P (Arr a1 a2), P (Arr a3 a4)) = return [(P a2, P a4), (P a3, P a1)]
destructC (PArr a1 a2,    PArr a3 a4)    = return [(a2, a4), (a3, a1)]
destructC (P (Arr a1 a2), PArr a3 a4)    = return [(P a2, a4), (a3, P a1)]
destructC (PArr a1 a2,    P (Arr a3 a4)) = return [(a2, P a4), (P a3, a1)]

destructC (P (SRecT l1 a1), P (SRecT l2 a2)) | l1 == l2 = return [(P a1, P a2)]
destructC (PRecT l1 a1,     PRecT l2 a2)     | l1 == l2 = return [(a1, a2)]
destructC (P (SRecT l1 a1), PRecT l2 a2)     | l1 == l2 = return [(P a1, a2)]
destructC (PRecT l1 a1,     P (SRecT l2 a2)) | l1 == l2 = return [(a1, P a2)]


destructC (P (And a1 a2), P a3) | a1 == a3 || a2 == a3 = return []
destructC (PAnd a1 a2,    a3)   | a1 == a3 || a2 == a3 = return []
destructC (P (And a1 a2), p)    = getFreshUni >>= \u1 ->
                                  getFreshUni >>= \u2 ->
                                  return [(P a1, Uni u1), (P a2, Uni u2), (PAnd (Uni u1) (Uni u2), p)]
destructC (PAnd a1 a2,    p)    = getFreshUni >>= \u1 ->
                                  getFreshUni >>= \u2 ->
                                  return [(a1, Uni u1), (a2, Uni u2), (PAnd (Uni u1) (Uni u2), p)]

destructC s = errThrow [DS $ "Destruct subtyping constraints impossible case."]

------------------
-- SUBSTITUTIONS
-----------------

-- Check whether a unification variable gets substituted
substWithUni :: SubRule -> Bool
substWithUni (Uni u, _) = True
substWithUni (_, Uni u) = True
-- substWithUni (P (TVar u), _) = True
-- substWithUni (_, P (TVar u)) = True
substWithUni  _         = False


-- Construct a substitution [u- |-> u /\ P] or [u+ |-> u \/ P]
makeSubst :: SubRule -> STcMonad (Substitution PType)
makeSubst (Uni u1, Uni u2) = if u1 == u2
                             then return $ EmptyS
                             else return $ NegS u1 (Meet (Uni u1) (Uni u2)) (PosS u2 (Join (Uni u1) (Uni u2)) EmptyS)
makeSubst (Uni u,  t)      = -- return $ NegS u (Meet (Uni u) t) EmptyS
                             if occursCheck (NegT (Uni u)) (NegT t)
                             then errThrow [DS $ "Occurs check: cannot construct infinite type."]
                             else return $ NegS u (Meet (Uni u) t) EmptyS
makeSubst (t,       Uni u) = -- return $ PosS u (Join (Uni u) t) EmptyS
                             if occursCheck (PosT (Uni u)) (PosT t)
                             then errThrow [DS $ "Occurs check: cannot construct infinite type."]
                             else return $ PosS u (Join (Uni u) t) EmptyS
makeSubst  _               = errThrow [DS $ "Solve impossible case"]


-- OccursCheck returns true if a unification variable of the same
-- polarity occurs on the other side of the constraint.
occursCheck :: Polar PType -> Polar PType -> Bool
occursCheck u              (PosT (P st))       = False -- occursS u st
occursCheck u              (NegT (P st))       = False -- occursS u st
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


-- Substitute type variables with unification variables in a given type scheme
findAndSubstVars :: Scheme -> STcMonad (PType, DisCons, [TUni])
findAndSubstVars (SType t) = return (P t, EmptyD, [])
findAndSubstVars (DForall b) = do
  ((alph, Embed t1), a2) <- unbind b
  u               <- getFreshUni
  (t, cons, vars) <- findAndSubstVars a2
  let t'           = replaceTVar alph u t
  let d'           = SeqD (Uni u, P t1) cons
  return (t', d', u : vars)


-- Apply a substitution to subtyping constraints
applySubstC :: (Substitution PType) -> [SubRule] -> [SubRule]
applySubstC EmptyS lqc                   = lqc
applySubstC _      []                    = []
applySubstC s      ((ty1, ty2):lqc) = ((substInType s (PosT ty1),
                                        substInType s (NegT ty2))
                                            :(applySubstC s lqc))


-- Apply a substitution to disjointness constraints
applySubstD :: Fresh m => (Substitution PType) -> DisCons -> m DisCons
applySubstD sub  EmptyD                = return $ EmptyD
applySubstD sub (SeqD (ty1, ty2) cons) = do
  let t1 =  substInType sub (PosT ty1)
  let t2 =  substInType sub (PosT ty2)
  rest   <- applySubstD sub cons
  return $ SeqD (t1, t2) rest


-- Apply a substitution to a polar produced type
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


-- Apply principality substitution to a produced type
groundSubstInPType :: PrSubs SType -> PType -> PType
groundSubstInPType EmptyPrS         p           = p
groundSubstInPType sub             (Join p1 p2) = Join (groundSubstInPType sub p1) (groundSubstInPType sub p2)
groundSubstInPType sub             (Meet p1 p2) = Meet (groundSubstInPType sub p1) (groundSubstInPType sub p2)
groundSubstInPType sub             (PArr p1 p2) = PArr (groundSubstInPType sub p1) (groundSubstInPType sub p2)
groundSubstInPType sub             (PAnd p1 p2) = PAnd (groundSubstInPType sub p1) (groundSubstInPType sub p2)
groundSubstInPType sub             (PRecT l p)  = PRecT l (groundSubstInPType sub p)
groundSubstInPType (Subs u t subs) (P (TVar x)) = if u == translate x
                                            then groundSubstInPType subs (P t)
                                            else groundSubstInPType subs (P (TVar x))
groundSubstInPType (Subs u t subs) (Uni u1)     = if u == u1
                                            then groundSubstInPType subs (P t)
                                            else groundSubstInPType subs (Uni u1)
groundSubstInPType sub             (P t)        = P (substInSType sub t)


-- Apply principality substitution to a PHiDI monotype
substInSType :: PrSubs SType -> SType -> SType
substInSType EmptyPrS t          = t
substInSType sub     (Arr t1 t2) = Arr (substInSType sub t1) (substInSType sub t2)
substInSType sub     (And t1 t2) = And (substInSType sub t1) (substInSType sub t2)
substInSType sub     (SRecT l t) = SRecT l (substInSType sub t)
substInSType _        NumT       = NumT
substInSType _        BoolT      = BoolT
substInSType _        TopT       = TopT
substInSType _        BotT       = BotT
substInSType _       (TVar x)    = TVar x

-- Substitute in an Fi+ term
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


-- Apply a substitution to an Fi+ type
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

----------------
-- PRINCIPALITY
----------------

-- Convert the function to a form u1 v (u2 v (P1 v ...)) for joins, and meets accordingly
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
-- TODO: flatten PAnd necessary?
-- flatten (PAnd p1 p2) = PAnd (flatten p1) (flatten p2)
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

-- Transform the type to its principal type
ground :: PType -> STcMonad (SType, PrSubs SType)
ground (P t)                    = return $ (t, EmptyPrS)
ground (Uni u)                  = return $ (TVar $ translate u, Subs u (TVar $ translate u) EmptyPrS)
ground (Meet (Uni u) p)         = do
  (t, theta) <- ground p
  let x  = translate u
  let t' = if (occursIn x t) then (And (TVar x) t) else t
  return (t', appendPr theta (Subs u t EmptyPrS))
ground (Join (Uni u) p)         = ground p >>= \(t, theta) -> return $ (t, appendPr theta (Subs u t EmptyPrS))
ground (Meet (P (TVar alph)) p) = do
  (t, theta) <- ground p
  let x  = translate alph
  let t' = if (occursIn x t) then (And (TVar x) t) else t
  return (t', theta)
ground (Join (P (TVar alph)) p) = ground p >>= \(t, theta) -> return $ (t, theta)
ground (Join p1 p2) = do
  (t1, theta1) <- ground p1
  (t2, theta2) <- ground (groundSubstInPType theta1 p2)
  let t'        = if (elementOf t1 t2) then t1 else TopT
  return (t', appendPr theta2 theta1)
ground (Meet p1 p2) = do
  (t1, theta1) <- ground p1
  (t2, theta2) <- ground (groundSubstInPType theta1 p2)
  let t'        = if (elementOf t1 t2) then t2 else And t1 t2
  return (t', appendPr theta2 theta1)
ground (PAnd p1 p2) = do
  (t1, theta1) <- ground p1
  (t2, theta2) <- ground (groundSubstInPType theta1 p2)
  return (And t1 t2, appendPr theta2 theta1)
ground (PArr p1 p2) = do
  (t1, theta1) <- ground p1
  (t2, theta2) <- ground (groundSubstInPType theta1 p2)
  return (Arr t1 t2, appendPr theta2 theta1)
ground (PRecT l p) = do
  (t, theta)   <- ground p
  return (SRecT l t, theta)

-- Check if a given unification variable occurs in a given type.
occursIn :: TyName -> SType -> Bool
occursIn u  NumT       = False
occursIn u  BoolT      = False
occursIn u (Arr s1 s2) = (occursIn u s1) || (occursIn u s2)
occursIn u (And s1 s2) = (occursIn u s1) || (occursIn u s2)
occursIn u (TVar u1)   = u == u1
occursIn u (SRecT l s) = occursIn u s
occursIn u  TopT       = False
occursIn u  BotT       = False


-- A type is an element of another type if they are equal or element of
-- one of the intersected types
elementOf :: SType -> SType -> Bool
elementOf t1 (And t2 t3) = t1 == (And t2 t3) || (elementOf t1 t2) || (elementOf t1 t3)
elementOf t1 t2          = t1 == t2


-- Compute the principal types of the types in the disjointness constraint
groundD :: DisCons -> STcMonad Delta
groundD  EmptyD              = return EmptyDelta
groundD (SeqD (t1, t2) cons) = do
  c2       <- groundD cons
  (t1', _) <- ground $ flatten t1
  (t2', _) <- ground $ flatten t2
  return $ Del (t1', t2') c2

-- Compute the principal substitution
groundS :: Substitution PType -> PrSubs SType -> STcMonad (PrSubs I.FType)
groundS EmptyS _ = return $ EmptyPrS
groundS (PosS u p subs) groundSub = do
  (st, groundSub') <- ground $ flatten $ groundSubstInPType groundSub p
  subs' <- groundS subs (appendPr groundSub' groundSub)
  ft <- translSType st
  return $ Subs u ft subs'
groundS (NegS u p subs) groundSub = do
  (st, groundSub') <- ground $ flatten $ groundSubstInPType groundSub p
  subs' <- groundS subs (appendPr groundSub' groundSub)
  ft <- translSType st
  return $ Subs u ft subs'

-----------------------------
-- DISJOINTNESS CONSTRAINTS
-----------------------------

-- Destruct the disjointness constraints
destructD :: Delta -> STcMonad Delta
destructD EmptyDelta                            = return EmptyDelta
destructD (Del (TVar alph, t) cons)             = destructD cons >>= \c -> return $ Del (TVar alph, t) c
destructD (Del (t, TVar alph) cons)             = destructD cons >>= \c -> return $ Del (TVar alph, t) c
destructD (Del (t1, t2) cons) | topLike t1      = destructD cons
destructD (Del (t1, t2) cons) | topLike t2      = destructD cons
destructD (Del (Arr t1 t2, Arr t3 t4) cons)     = destructD (Del (t2, t4) cons)
destructD (Del (And t1 t2, t3) cons)            = destructD (Del (t1, t3) (Del (t2, t3) cons))
destructD (Del (t1, And t2 t3) cons)            = destructD (Del (t1, t2) (Del (t1, t3) cons))
destructD (Del (SRecT l1 t1, SRecT l2 t2) cons) | l1 == l2 = destructD (Del (t1, t2) cons)
destructD (Del (SRecT l1 t1, SRecT l2 t2) cons) | l1 /= l2 = destructD cons
destructD (Del (NumT, Arr t1 t2) cons)          = destructD cons
destructD (Del (Arr t1 t2, NumT) cons)          = destructD cons
destructD (Del (NumT, SRecT l t) cons)          = destructD cons
destructD (Del (SRecT l t, NumT) cons)          = destructD cons
destructD (Del (Arr t1 t2, SRecT l t) cons)     = destructD cons
destructD (Del (SRecT l t, Arr t1 t2) cons)     = destructD cons
destructD (Del (BoolT, Arr t1 t2) cons)         = destructD cons
destructD (Del (Arr t1 t2, BoolT) cons)         = destructD cons
destructD (Del (BoolT, SRecT l t) cons)         = destructD cons
destructD (Del (SRecT l t, BoolT) cons)         = destructD cons
destructD (Del (BoolT, NumT) cons)              = destructD cons
destructD (Del (NumT, BoolT) cons)              = destructD cons
destructD  _                                    = errThrow [DS $ "Destruct disjointness constraint impossible case"]


-- Combine disjointness constraints so that there is one constraint for each type variable
combine :: Delta -> STcMonad Delta
combine  EmptyDelta                    = return EmptyDelta
combine (Del (TVar x, And t1 t2) cons) | t1 == t2 = combine $ Del (TVar x, t1) cons
combine (Del (TVar x, t1)        cons) = case lookupDis cons x of
          Nothing -> combine cons >>= \c -> return $ Del (TVar x, t1) c
          Just t2 -> combine $ Del (TVar x, And t1 t2) cons
combine  _                             = errThrow [DS $ "Combine impossible case"]


-- Look up disjointness constraints
lookupDis :: Delta -> TyName -> Maybe SType
lookupDis  EmptyDelta             _  = Nothing
lookupDis (Del (TVar x1, t) cons) x2 = if x1 == x2 then Just t else lookupDis cons x2
lookupDis (Del  _ cons)           x2 = lookupDis cons x2


---------------------
-- MONAD CONVERSION
---------------------

-- Convert monads
iTcMtoSTcM :: ITcMonad a -> STcMonad a
iTcMtoSTcM x = askCtx >>= \ctx ->
               sCtxtoICtx ctx >>= \ctx' ->
               lift $ lift $ runReaderT (runFreshMT x) ctx'


-------------------------------------
-- CONSTRUCTING FINAL TYPE AND TERM
-------------------------------------

-- Construct the final type by abstracting over the free variables
constructFinalType :: Delta -> [TyName] -> SType -> Scheme
constructFinalType cons []          ty = SType ty
constructFinalType cons (name:rest) ty = case (lookupDis cons name) of
  (Just disj) -> case disj of
    TVar alph | elem alph rest -> constructFinalType cons (rest ++ [name]) ty
    _ -> DForall (bind (name, Embed disj) (constructFinalType cons rest ty))
  Nothing     -> DForall (bind (name, Embed TopT) (constructFinalType cons rest ty))

-- Construct the final Fi+ term by abstracting over the free type variables
constructFinalTerm :: Fresh m => Delta -> [TyName] -> I.FExpr -> m I.FExpr
constructFinalTerm cons  []         e = return $ e
constructFinalTerm cons (name:rest) e = case (lookupDis cons name) of
    Just disj -> case disj of
      TVar alph | elem alph rest -> constructFinalTerm cons (rest ++ [name]) e
      _ -> do
        ty    <- translSType disj
        other <- constructFinalTerm cons rest e
        return $ I.DLam (bind (translate name, Embed ty) other)
    Nothing -> do
      other <- constructFinalTerm cons rest e
      return $ I.DLam (bind (translate name, Embed I.TopT) other)

------------------
-- Free variables
------------------

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

--------------------
-- HELPER FUNCTIONS
--------------------

-- Make type application explicit
applyVars :: I.FExpr -> [TUni] -> I.FExpr
applyVars t []     = t
applyVars t (u:us) = applyVars (I.TApp t (I.TVar (translate u))) us

-- Replace a type variable by a unification variable in the given P type
replaceTVar :: TyName -> TUni -> PType -> PType
replaceTVar alph u (P (TVar x)) | alph == x = Uni u
replaceTVar alph u (P (Arr p1 p2))          = PArr (replaceTVar alph u (P p1)) (replaceTVar alph u (P p2))
replaceTVar alph u (PArr p1 p2)             = PArr (replaceTVar alph u p1)     (replaceTVar alph u p2)
replaceTVar alph u (P (And p1 p2))          = PAnd (replaceTVar alph u (P p1)) (replaceTVar alph u (P p2))
replaceTVar alph u (PAnd p1 p2)             = PAnd (replaceTVar alph u p1)     (replaceTVar alph u p2)
replaceTVar alph u (P (SRecT l p))          = PRecT l (replaceTVar alph u (P p))
replaceTVar alph u (PRecT l p)              = PRecT l (replaceTVar alph u p)
replaceTVar _    _  ty                      = ty

-- Concatenate subtyping constraints
appendC :: SubCons -> SubCons -> SubCons
appendC  EmptyC      c = c
appendC (SeqC c1 cs) c = SeqC c1 (appendC cs c)

-- Concatenate disjointness constraints
appendD :: DisCons -> DisCons -> DisCons
appendD  EmptyD      d = d
appendD (SeqD d1 ds) d = SeqD d1 (appendD ds d)

-- Concatenate substitutions
appendS :: Substitution typ -> Substitution typ -> Substitution typ
appendS  EmptyS        s2 = s2
appendS (PosS u ty s1) s2 = PosS u ty (appendS s1 s2)
appendS (NegS u ty s1) s2 = NegS u ty (appendS s1 s2)

-- Concatenate principality substitutions
appendPr :: PrSubs typ -> PrSubs typ -> PrSubs typ
appendPr  EmptyPrS     s2 = s2
appendPr (Subs u t s1) s2 = Subs u t (appendPr s1 s2)
