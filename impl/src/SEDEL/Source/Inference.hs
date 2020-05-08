{-# LANGUAGE FlexibleContexts,
             PatternGuards,
             NoImplicitPrelude,
             LambdaCase,
             OverloadedStrings#-}

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

-- | Queue consisting of labels and/or types
data Queue = EmptyQ
           | QL Label Queue
           | QA PType Queue
           deriving (Show, Eq)

-- | Polarity, can be either positive or negative
data Polarity = PosT | NegT deriving (Show, Eq)

-- | A substitution consists of a unification variable with a given polarity
-- | and the type it should be substituted with
type Subst' = [(Polarity, TUni, SType)]

------------------
-- ⊢ E : A ~> e --
------------------

topLevelInfer :: Expr -> STcMonad (Scheme, I.FExpr)
topLevelInfer expr = do
  (_, ty, fTerm, cons, diss) <- infer expr
  table        <- constructTable cons diss
  subs'        <- expand table
  let ty'       = convertPtoS $ multipleSubs subs' PosT ty
  f            <- substFExpr subs' fTerm
  alph         <- freevarsE f
  del'         <- reorder $ constructDel subs' table (toList alph) -- (toList $ freevars ty')
  let finalType = constructFinalType del' ty'
  finalTerm    <- DT.trace ("FINAL TYPE:\n" ++ show finalType) $ constructFinalTerm del' f
  DT.trace ("FINAL TERM:\n" ++ show finalTerm) $ return (finalType, finalTerm)

---------------------------------
-- ALGORITHMIC INFERENCE RULES --
-- Π ⊢ E : τ [Γ; S; ∆] ~> e    --
---------------------------------

infer :: Expr -> STcMonad (Gam, PType, I.FExpr, [SubRule], [DisRule])

-- Π ⊢ ⊤ : ⊤ [•; •; •] ~> ⊤
infer Top = return (EmptyG, mkTopT, I.Top, [], [])

-- Π ⊢ i : Int [•; •; •] ~> i
infer (LitV n) = return (EmptyG, mkNumT, I.LitV n, [], [])

-- Π ⊢ b : Bool [•; •; •] ~> b
infer (BoolV b) = return (EmptyG, mkBoolT, I.BoolV b, [], [])

{-
   Π (x) = [Γ; S; ∆] τ       ∆ = α * τ'       u fresh
   --------------------------------------------------------------
   Π ⊢ x : [α -> u]τ [ [α -> u]Γ; [α -> u]S; [α -> u]∆ ]~> x |u|

-}
infer (VarPoly x) = do
  CtxSch del ty  <- lookupVarTy x
  (dis', ty', vars) <- findAndSubstVars del ty
  let fTerm = applyVars (I.Var (translate x)) vars
  return (EmptyG, ty', fTerm, [], dis')

{-
  ----------------------------------
  Π ⊢ x : u [x : u ; •; •] ~> x
-}
infer (Var x) = do
  uFresh  <- getFreshUni
  let gam  = Gamma x (mkUni uFresh) EmptyG
  return (gam, mkUni uFresh, I.Var (translate x), [], [])

{-
  Π ⊢ E : τ [Γ; S; ∆] ~> e
  ------------------------------------------------------------
  Π ⊢ \x . E : Γ(x) -> τ [Γ_x; S; ∆ ] ~> \x . e : |Γ(x) -> τ|
  -}
infer (Lam b) = do
  (x, e) <- unbind b
  (gam, t, f, cons, dis) <- infer e
  let gam' = removeFromGam gam x
  case lookupGam' gam x of
    Nothing -> do
      tFi      <- translPType (mkArr mkTopT t)
      let fterm = I.Anno (I.Lam (bind (translate x) f)) tFi
      return (gam', mkArr mkTopT t, fterm, cons, dis)
    Just ty -> do
      tFi      <- translPType (mkArr ty t)
      let fterm = I.Anno (I.Lam (bind (translate x) f)) tFi
      return (gam', mkArr ty t, fterm, cons, dis)

{-
  Π ⊢ E1 : τ1 [Γ1; S1; ∆1] ~> e1      Π ⊢ E2 : τ2 [Γ2; S2; ∆2] ~> e2      u fresh
  -----------------------------------------------------------------------------------
  Π ⊢ E1 E2 : u [Γ1 ∪ Γ2; S1 ∪ S2 ∪ (τ1 <: τ2 -> u); ∆1 ∪ ∆2] ~> (e1 : |τ2 -> u|) e2
-}
infer (App e1 e2) = do
  (gam1, t1, f1, cons1, dis1) <- infer e1
  (gam2, t2, f2, cons2, dis2) <- infer e2
  uFresh  <- getFreshUni
  let gam  = joinGam gam1 gam2
  tFi     <- translPType (mkArr t2 (mkUni uFresh))
  let f    = I.App (I.Anno f1 tFi) f2
  let cons = (t1, mkArr t2 (mkUni uFresh)) : (cons1 ++ cons2)
  let dis  = dis1 ++ dis2
  return (gam, mkUni uFresh, f, cons, dis)

{-
  Π ⊢ E1 : τ1 [Γ1; S1; ∆1] ~> e1             Π ⊢ E2 : τ2 [Γ2; S2; ∆2] ~> e2
  θ1 = solve(S1; ∆1)                         θ2 = solve(S2; ∆2)
  θ = θ1, θ2
  ------------------------------------------------------------------------------
  Π ⊢ E1 ,, E2 : θ(τ1 & τ2) θ[Γ1 ∪ Γ2; S1 ∪ S2; ∆1 ∪ ∆2 ∪ (τ1 * τ2)] ~> e1 ,, e2
-}
infer (Merge e1 e2) = do
  (gam1, t1, f1, cons1, dis1) <- infer e1
  (gam2, t2, f2, cons2, dis2) <- infer e2
  table1  <- constructTable cons1 dis1
  table2  <- constructTable cons2 dis2
  subs1   <- expand table1
  subs2   <- expand table2
  let subs = subs1 ++ subs2
  let gam  = applySubstGam subs (joinGam gam1 gam2)
  let t    = replaceVars $ multipleSubs subs PosT (mkAnd t1 t2)
  f       <- substFExpr subs (I.Merge f1 f2)
  let cons = applySubstCons subs (cons1 ++ cons2)
  let dis  = applySubstDis subs ((t1, t2) : (dis1 ++ dis2))
  return (gam, t, f, cons, dis)

{-
              Π ⊢ E : τ [Γ; S; ∆]~> e
  -----------------------------------------------
  Π ⊢ {l = E} : { l : τ } [Γ; S; ∆] ~> { l = e }
-}
infer (Rec l e) = do
  (gam, t, f, cons, dis) <- infer e
  return (gam, mkSRecT l t, I.Rec l f, cons, dis)

{-
  Π ⊢ E : τ [Γ; S; ∆] ~> e             u fresh
  --------------------------------------------------------------------
  Π ⊢ E.l : τ [Γ; S ∪ (τ <: {l : u}); ∆] ~> (e:|{l : u}|).l
-}
infer (Proj e l) = do
  (gam, t, f, cons, dis) <- infer e
  uFresh   <- getFreshUni
  tFi      <- translPType (mkSRecT l (mkUni uFresh))
  let cons' = (t, mkSRecT l (mkUni uFresh)) : cons
  return (gam, mkUni uFresh, I.Acc (I.Anno f tFi) l, cons', dis)

{-
  A = [∆'] τ'
  Π, ^x : [∆'] τ' ⊢ E1 : τ1 [Γ1; S1; ∆1] ~> e1
  θ = solve(τ1 <: τ')                   ∆' |= θ(∆1loc)
  Π, ^x : [∆'] τ' ⊢ E2 : τ2 [Γ2; S2; ∆2] ~> e2
  --------------------------------------------------------------------
  Π ⊢ let ^x : A = E1 in E2 : τ2 [Γ1 ∪ Γ2; S1glob ∪ S2; ∆1glob ∪ ∆2]
                            ~> let x : |A| = |θ|(e1) in e2
-}
infer (Letrec b) = do
  ((x, Embed a), (e1, e2))    <- unbind b
  -- A = [Γ'; ∆'] τ'
  (CtxSch del' t')            <- convertScheme a
  -- Π, ^x : [Γ'; ∆'] τ' ⊢ E1 : [Γ1; ∆1] τ1 ~> e1
  (gam1, t1, f1, cons1, dis1) <- localCtx (extendVarCtx x (CtxSch del' t')) $ infer e1
  -- (S_loc, S_glob) = splitCons Γ1 S1
  let (sloc, sglob) = splitCons gam1 cons1
  -- (∆_loc, ∆_glob) = splitDis Γ1 ∆1
  let (dloc, dglob) = splitDis gam1 dis1
  -- θ = solve(τ1 <: τ')
  table <- constructTable cons1 dis1
  case destruct (initC' ((t1, t'):sloc)) table [] of
    Nothing     -> errThrow [DS "Letrec not possible"]
    Just table' -> do
      -- θ = solve(table')
      subs             <- expand table'
      -- Π, ^x : [Γ'; ∆'] τ' ⊢ E2 : [Γ2; ∆2] τ2 ~> e2
      (gam2, t2, f2, cons2, dis2) <- localCtx (extendVarCtx x (CtxSch del' t')) $ infer e2
      -- check  ∆' |= θ(∆_loc)
      tbl <- addDisjointness (applySubstDis subs dloc) emptyTable
      entails del' (constructDel subs tbl (map (translate . univar) tbl))
      -- Γ = Γ1 ∪ Γ2
      let gam  = applySubstGam subs (joinGam gam1 gam2)
      -- ∆ = ∆_glob ∪ ∆2
      let dis  = applySubstDis subs (dglob ++ dis2)
      -- S = S_glob ∪ S2
      let cons = applySubstCons subs (sglob ++ cons2)
      -- θ(e1)
      aFi     <- translType a
      let t1'  = convertPtoS $ multipleSubs subs PosT t1
      f1'     <- substFExpr subs f1
      alph    <- freevarsE f1'
      del1    <- reorder $ constructDel subs table' (toList alph) -- (toList $ freevars t1')
      f1''    <- constructFinalTerm del1 f1'
      -- f = let x : A = θ(e1) in e2
      let f    = I.Letrec (bind (translate x, embed (Just aFi)) (f1'', f2))
      -- result
      return (gam, t2, f, cons, dis)

{-
  Π ⊢ E1 : [Γ1; S1; ∆1] τ1 ~> e1                Π ⊢ E2 : [Γ2; S2; ∆2] τ2 ~> e2
  Π ⊢ E3 : [Γ3; S3; ∆3] τ3 ~> e3                u fresh
  ---------------------------------------------------------------------------------------------
  Π ⊢ If E1 E2 E3 : u [Γ1 ∪ Γ2 ∪ Γ3;
                       S1 ∪ S2 ∪ S3 ∪ (τ1 <: Bool, τ2 <: u, τ3 <: u);
                       ∆1 ∪ ∆2 ∪ ∆3]
        ~> if e1 then e2 else e3
-}
infer (If e1 e2 e3) = do
  (gam1, t1, f1, cons1, dis1) <- infer e1
  (gam2, t2, f2, cons2, dis2) <- infer e2
  (gam3, t3, f3, cons3, dis3) <- infer e3
  uFresh  <- getFreshUni
  let gam  = joinGam gam1 (joinGam gam2 gam3)
  let cons = (t1, mkBoolT) : (t2, mkUni uFresh) : (t3, mkUni uFresh) : (cons1 ++ cons2 ++ cons3)
  let dis  = dis1 ++ dis2 ++ dis3
  return (gam, mkUni uFresh, I.If f1 f2 f3, cons, dis)

{-
  Π ⊢ E1 : [Γ1; S1; ∆1] τ1 ~> e1    Π ⊢ E2 : [Γ2; S2; ∆2] τ2 ~> e2       u fresh
  -------------------------------------------------------------------------------
  Π ⊢ PrimOp Op E1 E2 : u [Γ1 ∪ Γ2; S1 ∪ S2 ∪ (...); ∆1 ∪ ∆2] ~> PrimOp Op e1 e2
-}
infer (PrimOp op e1 e2) = do
  (gam1, t1, f1, cons1, dis1) <- infer e1
  (gam2, t2, f2, cons2, dis2) <- infer e2
  uFresh <- getFreshUni
  let gam = joinGam gam1 gam2
  let dis = dis1 ++ dis2
  case op of
    Arith   _ -> do
      let cons = (mkNumT, mkUni uFresh) : (t1, mkNumT)   : (t2, mkNumT)  : (cons1 ++ cons2)
      return (gam, mkUni uFresh, I.PrimOp op f1 f2, cons, dis)
    Comp    _ -> do
      let cons = (mkBoolT, mkUni uFresh) : (t1, mkNumT)  : (t2, mkNumT)  : (cons1 ++ cons2)
      return (gam, mkUni uFresh, I.PrimOp op f1 f2, cons, dis)
    Logical _ -> do
      let cons = (mkBoolT, mkUni uFresh) : (t1, mkBoolT) : (t2, mkBoolT) : (cons1 ++ cons2)
      return (gam, mkUni uFresh, I.PrimOp op f1 f2, cons, dis)

infer (Pos p tm) = extendSourceLocation p tm $ infer tm

infer a = errThrow [DS "Infer not implemented:", DD a]

-----------------------------------
-- CONSTRUCTING CONSTRAINT TABLE --
-----------------------------------
-- Construct a table from the given subtyping & disjointness constraints
constructTable :: [SubRule] -> [DisRule] -> STcMonad Table
constructTable cons dis = do
  table1 <- addDisjointness dis  emptyTable
  table2 <- addSubtyping    cons table1
  return $ table2

--------------------------------------------------------------------------------
-- Add disjointness constraints to the table
addDisjointness :: [DisRule] -> Table -> STcMonad Table
addDisjointness [] table = return table
addDisjointness ((p1, p2):dis) table = do
  table' <- disjoint p1 p2 table
  addDisjointness dis table'

--------------------------------------------------------------------------------
-- Add subtyping constraints to the table
addSubtyping :: [SubRule] -> Table -> STcMonad Table
addSubtyping cs table = case destruct (initC' cs) table [] of
  Just table' -> return table'
  Nothing     -> errThrow [DS $ "Destructing subtyping constraints is impossible"]

--------------------------------
-- EXPANDING CONSTRAINT TABLE --
--------------------------------
-- Expand a constraint table
expand :: Table -> STcMonad (Subst')
expand []         = return []
expand (e:table) | (not $ null unis) && (not $ null entries) = do -- variable case
  if (univar e) `elem` unis then errThrow [DS $ "Occurs check: cannot construct infinite type."] else do
    sub       <- expand entries
    rest      <- expand (applySubstTable sub ((List.\\) (e:table) entries))
    return (sub ++ rest)
  where
    unis    = hasUnis (lower e ++ upper e ++ disj e)
    entries = getEntries unis table
expand (e:table) | (not $ null unis) && (null entries) = do
  let sub    = [(PosT, univar e, lub' (lower e) (disj e)),
                (NegT, univar e, glb' (upper e) (disj e))]
  rest      <- expand (applySubstTable sub table)
  return (sub ++ rest)
  where
    unis    = hasUnis (lower e ++ upper e)
    entries = getEntries unis table
expand (e:table) | null (lower e) && null (upper e) = do -- no lower/upper bounds
  let sub    = [(PosT, univar e, mkTVar $ translate $ univar e),
                (NegT, univar e, mkTVar $ translate $ univar e)]
  rest      <- expand (applySubstTable sub table)
  return (sub ++ rest)
expand (e:table) | null (lower e) = do -- only an upper bound
  let upp    = glb' (upper e) (disj e)
  let sub    = [(NegT, univar e, upp), (PosT, univar e, upp)]
  rest      <- expand (applySubstTable sub table)
  return (sub ++ rest)
expand (e:table) | null (upper e) = do -- only a lower bound
  let low    = lub' (lower e) (disj e)
  let sub    = [(PosT, univar e, low), (NegT, univar e, low)]
  rest      <- expand (applySubstTable sub table)
  return (sub ++ rest)
expand (e:table) = do -- lower bound and upper bound
  let sub    = [(PosT, univar e, lub' (lower e) (disj e)),
                (NegT, univar e, glb' (upper e) (disj e))]
  rest      <- expand (applySubstTable sub table)
  return (sub ++ rest)

----------------------------------------------------------
-- COMPUTING GREATEST UPPER BOUND AND LEAST LOWER BOUND --
----------------------------------------------------------
-- Compute the least upper bound of two types
lub' :: [PType] -> [PType] -> SType
lub' lst ds = foldr lub mkBotT (disj' (map convertPtoS lst) (map convertPtoS ds))

--------------------------------------------------------------------------------
-- Compute the least upper bound of two types
lub :: SType -> SType -> SType
lub t1                  t2 | t1 == t2     = t1
lub t1                 (In BotT)          = t1
lub (In BotT)           t2                = t2
lub (In (Arr t11 t12)) (In (Arr t21 t22)) = mkArr (glb t11 t21) (lub t12 t22)
lub (In (SRecT l1 t1)) (In (SRecT l2 t2)) | l1 == l2 = mkSRecT l1 (lub t1 t2)
lub (In (And t11 t12))  t2                = if left  == mkTopT then right else
                                            if right == mkTopT then left  else
                                            mkAnd left right
                                              where left  = lub t11 t2
                                                    right = lub t12 t2
lub t1                 (In (And t21 t22)) = if left  == mkTopT then right else
                                            if right == mkTopT then left  else
                                            mkAnd left right
                                              where left  = lub t1 t21
                                                    right = lub t1 t22
lub _ _ = mkTopT

--------------------------------------------------------------------------------
-- Compute the greatest lower bound of a list of types
glb' :: [PType] -> [PType] -> SType
glb' lst ds = foldr glb mkTopT (disj' (map convertPtoS lst) (map convertPtoS ds))

--------------------------------------------------------------------------------
-- Compute the greatest lower bound of two types
glb :: SType -> SType -> SType
glb t1                  t2 | t1 == t2     = t1
glb t1                 (In TopT)          = t1
glb (In TopT)           t2                = t2
glb (In (Arr t11 t12)) (In (Arr t21 t22)) = mkArr (lub t11 t21) (glb t12 t22)
glb (In (SRecT l1 t1)) (In (SRecT l2 t2)) | l1 == l2 = mkSRecT l1 (glb t1 t2)
glb (In (And t11 t12))  t2                = simplifyIntersection $ mkAnd (glb t11 t2) (glb t12 t2)
glb t1                 (In (And t21 t22)) = simplifyIntersection $ mkAnd (glb t1 t21) (glb t1 t22)
glb t1                  t2                = mkAnd t1 t2

--------------------------------------------------------------------------------
-- Subtract the disjointness constraints from a list of types
disj' :: [SType] -> [SType] -> [SType]
disj' bs ds = map (\b -> helper b ds) bs
  where
    helper :: SType -> [SType] -> SType
    helper b []       = b
    helper b (d:rest) = helper (dDiff b d) rest
    dDiff :: SType -> SType -> SType
    dDiff t1                  t2 | t1 == t2     = mkTopT
    dDiff (In TopT)           t                 = mkTopT
    dDiff (In (Arr t11 t12)) (In (Arr _ t22))   = mkArr t11 (dDiff t12 t22)
    dDiff (In (SRecT l1 t1)) (In (SRecT l2 t2)) | l1 == l2 = mkSRecT l1 (dDiff t1 t2)
    dDiff (In (And t11 t12))  t2                = if left  == mkTopT then right else
                                                  if right == mkTopT then left  else
                                                  mkAnd left right
                                                    where left  = dDiff t11 t2
                                                          right = dDiff t12 t2
    dDiff t1                 (In (And t21 t22)) = if left  == mkTopT then right else
                                                  if right == mkTopT then left  else
                                                  mkAnd left right
                                                    where left  = dDiff t1 t21
                                                          right = dDiff t1 t22
    dDiff t1 t2 = t1

------------------------------------------
-- MAKING AND SIMPLIFYING INTERSECTIONS --
------------------------------------------
-- Simplify an intersection type
simplifyIntersection :: SType -> SType
simplifyIntersection ty = convertPtoS $ mkInt $ simplInt (convertStoP ty) []
  where
    simplInt :: PType -> [PType] -> [PType]
    simplInt t lst | t `elem` lst = lst
    simplInt (In (Inl (And t1 t2))) lst = simplInt t2 (simplInt t1 lst)
    simplInt _ lst = lst

--------------------------------------------------------------------------------
-- Make the intersection of a list of types
mkInt :: [PType] -> PType
mkInt []     = mkTopT
mkInt [x]    = x
mkInt (x:xs) = mkAnd x (mkInt xs)

-------------------
-- SUBSTITUTIONS --
-------------------
-- Apply a substitution to a table
applySubstTable :: Subst' -> Table -> Table
applySubstTable []         table = table
applySubstTable (sub:subs) table = applySubstTable subs (substInTable sub table)

--------------------------------------------------------------------------------
-- Apply a substitution to a term context
applySubstGam :: Subst' -> Gam -> Gam
applySubstGam _     EmptyG         = EmptyG
applySubstGam subs (Gamma x p gam) = Gamma x p' gam'
  where
    p'   = replaceVars $ multipleSubs subs NegT p
    gam' = applySubstGam subs gam

--------------------------------------------------------------------------------
-- Apply a substitution to a list of subtyping constraints
applySubstCons :: Subst' -> [SubRule] -> [SubRule]
applySubstCons _    []               = []
applySubstCons subs ((p1, p2): cons) = (p1', p2') : (applySubstCons subs cons)
  where
    p1' = replaceVars $ multipleSubs subs PosT p1
    p2' = replaceVars $ multipleSubs subs NegT p2

--------------------------------------------------------------------------------
-- Apply a substitution to a list of disjointness constraints
applySubstDis :: Subst' -> [DisRule] -> [DisRule]
applySubstDis _    []              = []
applySubstDis subs ((p1, p2): dis) = (p1', p2') : (applySubstDis subs dis)
  where
    p1' = replaceVars $ multipleSubs subs PosT p1
    p2' = replaceVars $ multipleSubs subs PosT p2

--------------------------------------------------------------------------------
-- Apply a substitution to a table
substInTable :: (Polarity, TUni, SType) -> Table -> Table
substInTable _    []    = []
substInTable sub (e:es) = (:) (mkEntry u low upp dis) rest
  where
    u    = univar e
    low  = map (substInPType sub PosT) (lower e)
    upp  = map (substInPType sub NegT) (upper e)
    dis  = map (substInPType sub PosT) (disj e)
    rest = substInTable sub es

--------------------------------------------------------------------------------
-- Apply a substitution to bounds with a given polarity
substInBounds :: Subst' -> Polarity -> [PType] -> [SType]
substInBounds subs pol bs = map (convertPtoS . multipleSubs subs pol) bs

--------------------------------------------------------------------------------
-- Apply multiple substitutions to a type with a given polarity
multipleSubs :: Subst' -> Polarity -> PType -> PType
multipleSubs []     _ ty = ty
multipleSubs (s:ss) p ty = substInPType s p (multipleSubs ss p ty)

--------------------------------------------------------------------------------
-- Apply a substitution to a type with a given polarity
substInPType :: (Polarity, TUni, SType) -> Polarity -> PType -> PType
substInPType (pol1, uni1, t1) pol2 (In (Inr (Uni uni2))) | pol1 == pol2 && uni1 == uni2         = convertStoP t1
substInPType (pol1, uni1, t1) pol2 (In (Inl (TVar a2)))  | pol1 == pol2 && uni1 == translate a2 = convertStoP t1
substInPType _ _   (In (Inr (Uni uni2)))  = mkUni uni2
substInPType _ _   (In (Inl (TVar a)))    = mkTVar a
substInPType _ _   (In (Inl NumT))        = mkNumT
substInPType _ _   (In (Inl BoolT))       = mkBoolT
substInPType _ _   (In (Inl BotT))        = mkBotT
substInPType _ _   (In (Inl TopT))        = mkTopT
substInPType s pol (In (Inl (Arr t1 t2))) = mkArr     (substInPType s (inv pol) t1)
                                                      (substInPType s pol t2)
substInPType s pol (In (Inl (And t1 t2))) = mkAnd     (substInPType s  pol      t1)
                                                      (substInPType s pol t2)
substInPType s pol (In (Inl (SRecT l t))) = mkSRecT l (substInPType s pol t)

--------------------------------------------------------------------------------
-- Apply a substitution to an Fi+ expression
substFExpr :: Subst' -> I.FExpr -> STcMonad I.FExpr
substFExpr [] fe         = return fe
substFExpr s  I.Bot      = return I.Bot
substFExpr s I.Top       = return I.Top
substFExpr s (I.DRec' d) = return $ I.DRec' d
substFExpr s (I.Var tn)  = return $ I.Var tn
substFExpr s (I.LitV i)  = return $ I.LitV i
substFExpr s (I.BoolV b) = return $ I.BoolV b
substFExpr s (I.Anno fe ft)        = I.Anno      <$> substFExpr s fe
                                                 <*> substInFType s PosT ft
substFExpr s (I.App fe1 fe2)       = I.App       <$> substFExpr s fe1
                                                 <*> substFExpr s fe2
substFExpr s (I.Merge fe1 fe2)     = I.Merge     <$> substFExpr s fe1
                                                 <*> substFExpr s fe2
substFExpr s (I.PrimOp op fe1 fe2) = I.PrimOp op <$> substFExpr s fe1
                                                 <*> substFExpr s fe2
substFExpr s (I.If fe1 fe2 fe3)    = I.If        <$> substFExpr s fe1
                                                 <*> substFExpr s fe2
                                                 <*> substFExpr s fe3
substFExpr s (I.Pos sp fe)         = I.Pos sp    <$> substFExpr s fe
substFExpr s (I.TApp fe ft)        = I.TApp      <$> substFExpr s fe
                                                 <*> substInFType s PosT ft
substFExpr s (I.Rec l fe)          = I.Rec l     <$> substFExpr s fe
substFExpr s (I.Lam b)  = do
  (tn, fe) <- unbind b
  fe'      <- substFExpr s fe
  return $ I.Lam (bind tn fe')
substFExpr s (I.DLam b) = do
  ((tn, Embed ft), fe) <- unbind b
  fe'                  <- substFExpr s fe
  ft'                  <- substInFType s PosT ft
  return $ I.DLam (bind (tn, embed ft') fe')
substFExpr s (I.Acc fe l) = do
  fe' <- substFExpr s fe
  return $ I.Acc fe' l
substFExpr s (I.Remove fe l Nothing) = do
  fe' <- substFExpr s fe
  return $ I.Remove fe' l Nothing
substFExpr s (I.Remove fe l (Just ft)) = do
  fe' <- substFExpr s fe
  ft' <- substInFType s PosT ft
  return $ I.Remove fe' l (Just ft')
substFExpr s (I.LamA b)    = do
  ((tn, Embed ft), fe) <- unbind b
  fe'                  <- substFExpr s fe
  ft'                  <- substInFType s PosT ft
  return $ I.LamA (bind (tn, embed ft') fe')
substFExpr s (I.Letrec b)    = do
  ((tn, Embed mft), (fe1, fe2)) <- unbind b
  fe1'                          <- substFExpr s fe1
  fe2'                          <- substFExpr s fe2
  case mft of
    Nothing -> return $ I.Letrec (bind (tn, embed Nothing) (fe1', fe2'))
    Just ft -> substInFType s PosT ft >>= \ft' ->
                return $ I.Letrec (bind (tn, embed (Just ft')) (fe1', fe2'))

--------------------------------------------------------------------------------
-- Apply a substitution to an Fi+ type with a given polarity
substInFType :: Subst' -> Polarity -> I.FType -> STcMonad I.FType
substInFType [] _    ft               = return ft
substInFType _  _    I.NumT           = return I.NumT
substInFType _  _    I.BoolT          = return I.BoolT
substInFType _ _     I.TopT           = return I.TopT
substInFType _  _    I.BotT           = return I.BotT
substInFType _  _   (I.DForall b)     = return $ I.DForall b
substInFType _  _   (I.OpAbs b)       = return $ I.OpAbs b
substInFType s  pol (I.Arr ft1 ft2)   = I.Arr     <$> substInFType s (inv pol) ft1
                                                  <*> substInFType s pol ft2
substInFType s  pol (I.And ft1 ft2)   = I.And     <$> substInFType s pol       ft1
                                                  <*> substInFType s pol ft2
substInFType s  pol (I.SRecT l ft)    = I.SRecT l <$> substInFType s pol ft
substInFType s  pol (I.OpApp ft1 ft2) = I.OpApp   <$> substInFType s pol ft1
                                                  <*> substInFType s pol ft2
substInFType ((pol1,u,ty):[])   pol2 (I.TVar a) | u == translate a && pol1 == pol2 =
  translSType ty >>= \ft -> return ft
substInFType ((pol1,u,ty):subs) pol2 (I.TVar a) | u == translate a && pol1 == pol2 =
  translSType ty >>= \ft -> substInFType subs pol2 ft
substInFType (sub:[])            _   (I.TVar a) = return $ I.TVar a
substInFType (sub:subs)          pol (I.TVar a) = substInFType subs pol (I.TVar a)

---------------------------
-- DESTRUCT DISJOINTNESS --
---------------------------
-- Destruct disjointness constraints between two types and add them to the table
disjoint :: PType -> PType -> Table -> STcMonad Table
disjoint (In (Inr (Uni u))) t table = return $ addDisj u t table
disjoint t (In (Inr (Uni u))) table = return $ addDisj u t table
disjoint (In (Inl (TVar a))) t table = return $ addDisj (translate a) t table
disjoint t (In (Inl (TVar a))) table = return $ addDisj (translate a) t table
disjoint (In (Inl (Arr t1 t2))) (In (Inl (Arr t3 t4))) table = disjoint t2 t4 table
disjoint (In (Inl (SRecT l1 t1))) (In (Inl (SRecT l2 t2))) table | l1 == l2 = disjoint t1 t2 table
disjoint (In (Inl (SRecT l1 _))) (In (Inl (SRecT l2 _))) table | l1 /= l2 = return $ table
disjoint (In (Inl NumT)) (In (Inl (Arr _ _))) table = return $ table
disjoint (In (Inl (Arr _ _))) (In (Inl NumT)) table = return $ table
disjoint (In (Inl NumT)) (In (Inl (SRecT _ _))) table = return $ table
disjoint (In (Inl (SRecT _ _))) (In (Inl NumT)) table = return $ table
disjoint (In (Inl (Arr _ _))) (In (Inl (SRecT _ _))) table = return $ table
disjoint (In (Inl (SRecT _ _))) (In (Inl (Arr _ _))) table = return $ table
disjoint (In (Inl BoolT)) (In (Inl (Arr _ _))) table = return $ table
disjoint (In (Inl (Arr _ _))) (In (Inl BoolT)) table = return $ table
disjoint (In (Inl BoolT)) (In (Inl (SRecT _ _))) table = return $ table
disjoint (In (Inl (SRecT _ _))) (In (Inl BoolT)) table = return $ table
disjoint (In (Inl BoolT)) (In (Inl NumT)) table = return $ table
disjoint (In (Inl NumT)) (In (Inl BoolT)) table = return $ table
disjoint t1 t2 table | topLikeP t1 || topLikeP t2 = return $ table
disjoint (In (Inl (And t1 t2))) t3 table = disjoint t1 t3 table >>= \table' -> disjoint t2 t3 table'
disjoint t1 (In (Inl (And t2 t3))) table = disjoint t1 t2 table >>= \table' -> disjoint t1 t3 table'
disjoint _ _ _ = errThrow [DS $ "Destructing disjointness constraints is impossible"]

---------------------------
-- UNIFICATION ALGORITHM --
---------------------------
-- Initialization function
initC' :: [SubRule] -> [(Queue, SubRule)]
initC' cons = [(EmptyQ, t) | t <- cons]

--------------------------------------------------------------------------------
-- Destruct a subtyping rule
destruct :: [(Queue,SubRule)] -> Table -> [(Queue,SubRule)] -> Maybe Table
destruct [] table _ = Just table
-- add upper and/or lower bounds
destruct (c@(EmptyQ, s):lqc) table seen | containsUni s = destruct (((List.\\) cons seen) ++ lqc) table' (c:seen)
  where (table', cons) = addBounds s table
-- same types
destruct ((EmptyQ, (t1, t2)):lqc) table seen | t1 == t2 = destruct lqc table seen
-- bot and top
destruct ((_,(In (Inl BotT), _)):lqc) table seen = destruct lqc table seen
destruct ((_,(_, In (Inl TopT))):lqc) table seen = destruct lqc table seen
-- first destruct right type
-- push to queue
destruct (c@(q,(a1, In (Inl (Arr a2 a3)))) :lqc) table seen = destruct ((pushType  a2 q,(a1,a3)):lqc) table (c:seen)
destruct (c@(q,(a1, In (Inl (SRecT l a2)))):lqc) table seen = destruct ((pushLabel l  q,(a1,a2)):lqc) table (c:seen)
-- intersection types
destruct (c@(q,(a,  In (Inl (And a1 a2)))) :lqc) table seen = destruct ((q,(a,a1)):(q,(a,a2)):lqc) table (c:seen)
-- then destruct left type
-- take from queue
destruct (c@(QA p q,(In (Inl (Arr a1 a2)),   a)) :lqc) table seen = case destruct [(EmptyQ,(p, a1))] table (c:seen) of
    Just tbl -> destruct ((q,(a2, a))    :lqc) tbl   ((EmptyQ,(p, a1)):c:seen)
    Nothing  -> destruct ((q,(mkTopT, a)):lqc) table (c:seen)
destruct (c@(QL l q,(In (Inl (SRecT l1 a1)), a2)):lqc) table seen | l == l1 = destruct ((q,(a1, a2)) :lqc) table (c:seen)
-- intersection types
destruct (c@(q,(In (Inl (And a1 a2)), a3))  :lqc) table seen = case destruct [(q, (a1, a3))] table (c:seen) of
  Just tbl1 -> case destruct [(q, (a2, a3))] table (c:seen) of
    Just tbl2 -> destruct lqc (mergeTables table tbl1 tbl2) ((q, (a1, a3)):(q, (a2, a3)):seen)
    Nothing   -> Just tbl1
  Nothing -> case destruct [(q, (a2, a3))] table (c:seen) of
    Just tbl2 -> Just tbl2
    Nothing   -> Nothing
destruct x _ _ = DT.trace ("other:   " ++ show x) $ Nothing

--------------------
-- MERGING TABLES --
--------------------
-- Merge two tables, and add the merged version to the given table
mergeTables :: Table -> Table -> Table -> Table
mergeTables old tbl1 tbl2 = addEntries merged old
  where
    new1   = newParts old tbl1
    new2   = newParts old tbl2
    merged = mergeLowerBounds new1 new2
    addEntries :: [Entry] -> Table -> Table
    addEntries []     tbl = tbl
    addEntries (e:es) tbl = addEntries es (addEntry e tbl)

--------------------------------------------------------------------------------
-- Compute the difference between two given tables
newParts :: Table -> Table -> Table
newParts []     table = table
newParts (e:es) table = case getEntry (univar e) table of
  Nothing -> []
  Just e' -> (mkEntry u low upp dis) : (newParts es table')
    where u      = univar e
          low    = (List.\\) (lower e') (lower e)
          upp    = (List.\\) (upper e') (upper e)
          dis    = (List.\\) (disj e')  (disj e)
          table' = List.delete e' table

--------------------------------------------------------------------------------
-- Merge the lower bounds for every variable of two given tables
mergeLowerBounds :: Table -> Table -> Table
mergeLowerBounds []     table = table
mergeLowerBounds (e:es) table = case getEntry (univar e) table of
  Nothing -> e     : (mergeLowerBounds es table)
  Just e' -> entry : (mergeLowerBounds es table')
    where
      low    = [mkInt (lower e ++ lower e')]
      entry  = mkEntry (univar e) low (upper e ++ upper e') (disj e ++ disj e')
      table' = List.delete e' table

--------------------------------------------------------------------------------
-- Add (upper/lower) bounds to the table
addBounds :: SubRule -> Table -> (Table, [(Queue,SubRule)])
addBounds (In (Inr (Uni u1)), In (Inr (Uni u2)))    table = (table', cons)
  where table' = addUpper u1 (mkUni u2) table
        cons   = [(EmptyQ, (t1, mkUni u2)) | t1 <- getLower u1 table]
addBounds (In (Inr (Uni u)), t@(In (Inl (TVar a)))) table = (table', cons)
  where table' = addUpper u t (addDisj (translate a) (mkInt $ getDisj u table) table)
        cons   = [(EmptyQ, (t', t)) | t' <- getLower u table]
addBounds (In (Inr (Uni u)), t) table                     = (addUpper u t table, cons)
  where cons   = [(EmptyQ, (t', t)) | t' <- getLower u table]
addBounds (t@(In (Inl (TVar a))), In (Inr (Uni u))) table = (table', cons)
  where table' = addLower u t (addDisj (translate a) (mkInt $ getDisj u table) table)
        cons   = [(EmptyQ, (t, t')) | t' <- getUpper u table]
addBounds (t, In (Inr (Uni u)))                     table = (addLower u t table, cons)
  where cons   = [(EmptyQ, (t, t')) | t' <- getUpper u table]
addBounds  _                                        table = (table, [])

---------------------------------------
-- SPLIT DISJOINTNESS LOCAL - GLOBAL --
---------------------------------------
-- Split disjointness constraints into a local and a global part
splitDis :: Gam -> [DisRule] -> ([DisRule], [DisRule])
splitDis gam []             = ([], [])
splitDis gam ((p1, p2):dis) = if isGlob then (loc, ((p1, p2):glob))
                                        else (((p1, p2):loc), glob)
  where (loc, glob) = splitDis gam dis
        isGlob      = any (gamContains gam) (findUnis p1 ++ findUnis p2)

--------------------------------------------------------------------------------
-- Split subtyping constraints into a local and a global part
splitCons :: Gam -> [SubRule] -> ([SubRule], [SubRule])
splitCons gam []             = ([], [])
splitCons gam ((p1, p2):dis) = if isGlob then (loc, ((p1, p2):glob))
                                         else (((p1, p2):loc), glob)
  where (loc, glob) = splitCons gam dis
        isGlob      = any (gamContains gam) (findUnis p1 ++ findUnis p2)

--------------------
-- ENTAILMENT LET --
--------------------
-- Check if a type context entails another type context, throw an error if not
entails :: Del -> Del -> STcMonad ()
entails del1  EmptyD              = return ()
entails del1 (Delta name ty del2) = do
  ent     del1 (translate name) ty
  entails del1 del2
  where
    ent :: Del -> TyName -> SType -> STcMonad ()
    ent  EmptyD                    _   _            =
      errThrow [DS "No entailment in letrec."]
    ent (Delta u1 (In (TVar a)) d) u2 (In (TVar b)) =
      if u1 == b && a == u2 then return () else ent d u2 (mkTVar b)
    ent (Delta u1 a d)             u2  b | u1 == u2 =
      case destruct [(EmptyQ, (convertStoP a, convertStoP b))] emptyTable [] of
        Nothing -> if (topLike b) then return () else ent d u2 b
        Just t  -> return ()
    ent (Delta u1 a d)             u2  b = ent d u2 b

-------------------------------------
-- CHECK FOR UNIFICATION VARIABLES --
-------------------------------------
-- Check whether a unification variable gets substituted
containsUni :: SubRule -> Bool
containsUni (In (Inr (Uni u)), _) = True
containsUni (_, In (Inr (Uni u))) = True
containsUni  _                    = False

--------------------------------------------------------------------------------
-- Substitute type variables with unification variables in a given type scheme
findAndSubstVars :: Del -> PType -> STcMonad ([DisRule], PType, [TUni])
findAndSubstVars  EmptyD             ty = return ([], ty, [])
findAndSubstVars (Delta alph st del) ty = do
  (dis', ty', vars') <- findAndSubstVars del ty
  uFresh             <- getFreshUni
  let newDis          = (mkUni uFresh, convertStoP st) : dis'
  let newTy           = replaceTVar (translate alph) uFresh ty'
  return (newDis, newTy, uFresh : vars')

-------------------------------------------
-- PUSHING LABELS AND TYPES TO THE QUEUE --
-------------------------------------------
pushLabel :: Label -> Queue -> Queue
pushLabel l EmptyQ    = QL l EmptyQ
pushLabel l (QL l' q) = QL l' (pushLabel l q)
pushLabel l (QA t q)  = QA t (pushLabel l q)

pushType :: PType -> Queue -> Queue
pushType t EmptyQ    = QA t EmptyQ
pushType t (QL l q)  = QL l (pushType t q)
pushType t (QA t' q) = QA t' (pushType t q)

-----------------------------------
-- TERM CONTEXTS & TYPE CONTEXTS --
-----------------------------------
-- Look up a term variable in the term context
lookupGam' :: Gam -> TmName -> Maybe PType
lookupGam'  EmptyG           _  = Nothing
lookupGam' (Gamma x1 ty gam) x2 | x1 == x2 = case lookupGam' gam x2 of
  Nothing  -> Just ty
  Just ty' -> Just (mkAnd ty ty')
lookupGam' (Gamma _  _  gam) x  = lookupGam' gam x

--------------------------------------------------------------------------------
-- Check if a term context contains the given unification variable
gamContains :: Gam -> TUni -> Bool
gamContains  EmptyG          _ = False
gamContains (Gamma x ty gam) u = u `elem` (findUnis ty) || gamContains gam u

--------------------------------------------------------------------------------
-- Replace type variables in gamma
replaceGam :: TUni -> TUni -> Gam -> Gam
replaceGam _    _  EmptyG          = EmptyG
replaceGam alph u (Gamma x ty gam) = Gamma x (replaceTVar alph u ty) (replaceGam alph u gam)

--------------------------------------------------------------------------------
-- Remove the given term variable from the term context
removeFromGam :: Gam -> TmName -> Gam
removeFromGam  EmptyG          _ = EmptyG
removeFromGam (Gamma x ty gam) y | x == y = removeFromGam gam y
removeFromGam (Gamma x ty gam) y = Gamma x ty (removeFromGam gam y)

--------------------------------------------------------------------------------
-- Look up disjointness requirement in type context
lookupDel :: Del -> TyName -> (Maybe SType, Del)
lookupDel  EmptyD           _  = (Nothing, EmptyD)
lookupDel (Delta u1 ty del) u2 | u1 == u2 = (Just ty, del)
lookupDel (Delta u1 ty del) u  = (t, Delta u1 ty d)
  where (t, d) = lookupDel del u

--------------------------------------------------------------------------------
-- Combine two term contexts into one
joinGam :: Gam -> Gam -> Gam
joinGam EmptyG            gam    = gam
joinGam gam               EmptyG = gam
joinGam (Gamma x ty gam1) gam2   = Gamma x ty (joinGam gam1 gam2)

--------------------------------------------------------------------------------
-- Combine two type contexts into one
joinDel :: Del -> Del -> Del
joinDel EmptyD            del    = del
joinDel del               EmptyD = del
joinDel (Delta x ty del1) del2   = Delta x ty (joinDel del1 del2)

-----------------------------------------
-- REORDERING DISJOINTNESS CONSTRAINTS --
-----------------------------------------
-- Reorder the disjointness requirement so that a variable has been introduced
-- before defining a disjointness constraint with it
reorder :: Del -> STcMonad Del
reorder d = reorderDo [] d
  where
    reorderDo :: [TyName] -> Del -> STcMonad Del
    reorderDo _      EmptyD              = return EmptyD
    reorderDo names (Delta alph t1 cons) =
      if allContained t1 names
        then do
          tail' <- reorderDo (alph:names) cons
          return $ Delta alph t1 tail'
        else reorderDo names (joinDel cons (Delta alph t1 EmptyD))
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
iTcMtoSTcM x = askCtx         >>= \ctx ->
               sCtxtoICtx ctx >>= \ctx' ->
               lift $ lift $ runReaderT (runFreshMT x) ctx'


--------------------------------------
-- CONSTRUCTING FINAL TYPE AND TERM --
--------------------------------------
-- Construct the type context with disjointness requirements from the table
constructDel :: Subst' -> Table -> [TyName] -> Del
constructDel _   _     []     = EmptyD
constructDel sub table (f:fs) = Delta f st (constructDel sub table fs)
  where
    d  = getDisj (translate f) (applySubstTable sub table)
    st = foldr glb mkTopT (map convertPtoS d)

--------------------------------------------------------------------------------
-- Construct the final type by abstracting over the disjointness requirements
constructFinalType :: Del -> SType -> Scheme
constructFinalType  EmptyD          t2 = SType t2
constructFinalType (Delta u t1 sub) t2 = DForall (bind (translate u, Embed t1)
                                                 (constructFinalType sub t2))

--------------------------------------------------------------------------------
-- Construct the final term by abstracting over the disjointness requirements
constructFinalTerm :: Fresh m => Del -> I.FExpr -> m I.FExpr
constructFinalTerm  EmptyD          fe = return $ fe
constructFinalTerm (Delta u t1 sub) fe = do
  ty   <- translSType t1
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

------------------------------------------------------------------------------

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


--------------------------
-- CONVERSION FUNCTIONS --
--------------------------
-- Convert a type scheme to a context type
convertScheme :: Fresh m => Scheme -> m CtxType
convertScheme (SType st)  = return $ CtxSch EmptyD (convertStoP st)
convertScheme (DForall b) = do
  ((alph, Embed t1), a2) <- unbind b
  CtxSch del ty          <- convertScheme a2
  return $ CtxSch (Delta alph t1 del) ty

--------------------------------------------------------------------------------
-- Convert an SType to a PType
convertStoP :: SType -> PType
convertStoP = cata (In . Inl)

--------------------------------------------------------------------------------
-- Convert a PType to an SType
convertPtoS :: PType -> SType
convertPtoS (In (Inl NumT))        = mkNumT
convertPtoS (In (Inl BoolT))       = mkBoolT
convertPtoS (In (Inl BotT))        = mkBotT
convertPtoS (In (Inl TopT))        = mkTopT
convertPtoS (In (Inl (TVar a)))    = mkTVar a
convertPtoS (In (Inl (Arr t1 t2))) = mkArr (convertPtoS t1) (convertPtoS t2)
convertPtoS (In (Inl (And t1 t2))) = mkAnd (convertPtoS t1) (convertPtoS t2)
convertPtoS (In (Inl (SRecT l t))) = mkSRecT l (convertPtoS t)
convertPtoS (In (Inr (Uni u)))     = mkTVar $ translate u

----------------------
-- HELPER FUNCTIONS --
----------------------
-- Reverse the polarity
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
    alg alph uni (Inr (Uni x))  | alph == x             = mkUni uni
    alg alph uni (Inl (TVar x)) | alph == (translate x) = mkUni uni
    alg alph uni  t             = In t

--------------------------------------------------------------------------------
-- Find all unification variables in a list of types
hasUnis :: [PType] -> [TUni]
hasUnis ts = foldr (++) [] (map findUnis ts)

--------------------------------------------------------------------------------
-- Find all unification variables in a given type
findUnis :: PType -> [TUni]
findUnis = cata alg
  where
    alg :: PType' [TUni] -> [TUni]
    alg (Inr (Uni uni)) = [uni]
    alg (Inl ty)        = concat ty

--------------------------------------------------------------------------------
-- Replace variables with fresh unification variables
replaceVars :: PType -> PType
replaceVars (In (Inr (Uni uni2)))  = mkUni uni2
replaceVars (In (Inl (TVar a)))    = mkUni $ translate a
replaceVars (In (Inl NumT))        = mkNumT
replaceVars (In (Inl BoolT))       = mkBoolT
replaceVars (In (Inl BotT))        = mkBotT
replaceVars (In (Inl TopT))        = mkTopT
replaceVars (In (Inl (Arr t1 t2))) = mkArr (replaceVars t1) (replaceVars t2)
replaceVars (In (Inl (And t1 t2))) = mkAnd (replaceVars t1) (replaceVars t2)
replaceVars (In (Inl (SRecT l t))) = mkSRecT l (replaceVars t)
