module Unification
    ( checkSubtyping
    ) where

import qualified Data.List   as List
import           Debug.Trace as DT
import           Syntax

---------------------------------
-- CHECK SUBTYPING CONSTRAINTS --
---------------------------------

checkSubtyping :: Type -> Type -> [Substitution]
checkSubtyping t1 t2 = map expand (possTbls [(EmptyQ, t1, t2)] [] []) -- empty table, empty cache

-----------------------------
-- COMPUTE POSSIBLE TABLES --
-----------------------------

-- Computes a list of possible tables as output from the destruct function
possTbls :: Subs -> Table -> Subs -> [Table]
possTbls []       table _     = [table]
possTbls (s:subs) table cache = result $ destruct s table
  where
    result :: Result -> [Table]
    result  Same           = possTbls subs table (s:cache)
    result (Tab table' cs) = possTbls (((List.\\) cs (s:cache)) ++ subs) table' (s:cache)
    result (Cons cons)     = possTbls (cons ++ subs) table (s:cache)
    result (Branch r1 r2)  = (result r1) ++ (result r2)
    result  Fail           = []

-- The result of a constraint can be the following:
data Result = Same                  -- ignore the constraint
            | Tab    Table  Subs    -- change the table and construct new constraints
            | Cons   Subs           -- destruct into smaller constraints
            | Branch Result Result  -- make a branch, i.e. multiple possible results
            | Fail                  -- the constraints can not be solved

------------------------------------
-- DESTRUCT SUBTYPING CONSTRAINTS --
------------------------------------

-- Takes a subtyping rule and a table
-- Returns a result as described above
destruct :: Sub -> Table -> Result

-- (2) Trivial cases : ignore
-- (2.1) Same types
destruct (EmptyQ, t1, t2) _ | t1 == t2 = Same
-- (2.2) Bottom
destruct (_, Bot, _) _ = Same
-- (2.3) Top
destruct (_, _, t2) _ | toplike t2 = Same
-- (2.4) BCD distributivity A & B <: A and A & B <: B
destruct (EmptyQ, And t1 t2, t3) _ | t1 == t3 || t2 == t3 = Same

-- (3) Add upper and/or lower bounds to the table
destruct c table | containsUni c = occursCheck table c

-- (4) Destruct the right type of the constraint first
-- (4.1) Push type to queue
destruct (q, t1, Arr t2 t3) _ = Cons [(pushType t2 q, t1, t3)]
-- (4.2) Push label to queue
destruct (q, t1, Rec l t2)  _ = Cons [(pushLabel l q, t1, t2)]
-- (4.3) Intersection type
destruct (q, t1, And t2 t3) _ = Cons ((q, t1, t2) : (q, t1, t3) : [])

-- (5) Destruct the left type of the constraint
-- (5.1) Pop type from queue
destruct (QA t q, Arr t1 t2, t3) _ = Cons ((EmptyQ, t, t1) : (q, t2, t3) : [])
-- (5.1) Pop label from queue
destruct (QL l q, Rec l' t1, t2) _ | l == l' = Cons [(q, t1, t2)]
-- (5.3) Intersection types
-- (5.3.1) BCD subtyping function types
destruct (q, And (Arr t1 t2) (Arr t3 t4), t) _ = Branch c1 (Branch c2 c3)
  where
    c1 = Cons [(q, Arr t1 t2, t)]
    c2 = Cons [(q, Arr t3 t4, t)]
    c3 = Cons [(q, Arr (And t1 t3) (And t2 t4), t)]
-- (5.3.2) BCD subtyping record types
destruct (q, And (Rec l1 t1) (Rec l2 t2), t) _ =  Branch c1 (Branch c2 c3)
  where
    c1 = Cons [(q, Rec l1 t1, t)]
    c2 = Cons [(q, Rec l2 t2, t)]
    c3 = if l1 == l2 then Cons [(q, Rec l1 (And t1 t2), t)] else Same
-- (5.3.3) Other intersections
destruct (q, And t1 t2, t3) _ = Branch c1 c2
  where
    c1 = Cons [(q, t1, t3)]
    c2 = Cons [(q, t2, t3)]

-- (6) Reconstruct constraints
-- (6.1) Pop type from queue : Q, t ⊢ u <: t' ==> Q ⊢ u <: t -> t'
destruct (QA t q, Uni u, t')  _ = Cons [(q, Uni u, Arr t t')]
-- (6.2) Pop label from queue : Q, l ⊢ u <: t ==> Q ⊢ u <: {l : t}
destruct (QL l q, Uni u, t)   _ = Cons [(q, Uni u, Rec l t)]
-- (6.3) Unification variable is toplike
destruct (QL _ _, Top, Uni u) _ = Cons [(EmptyQ, Top, Uni u)]
destruct (QA _ _, Top, Uni u) _ = Cons [(EmptyQ, Top, Uni u)]

-- (7) Other cases : fail
destruct _ _ = Fail

-------------------
-- DETECT CYCLES --
-------------------

-- a cycle consists of a list of unification variables
type Cycle = [TUni]

-- The occurs check properly deals with cycles in the subtyping constraints
occursCheck :: Table -> Sub -> Result
occursCheck table (q, Uni u, t) =
  -- (1) t has no unification vars => add bounds to the table
  if List.null unis then Tab table' cons'
    -- (2) t has unification vars including u => instantiate u with Top
    else if List.elem u unis then tableTop
      -- (3) t has unification vars but no cycle => add bounds to the table
      else if empty cycles then Tab table' cons'
        -- (4) t has unification vars including cycle => instantiate the
        -- unification variables in turn with Top
        else constructBranches table' cycles
  where
    unis            = List.nub $ findUnis t
    (table', cons') = addBounds (q, Uni u, t) table
    tableTop        = Tab (substTop u table') [(q, Top, replaceTop u t)]
    cycles          = map (\ux -> detectCycle [ux] table') unis

occursCheck table (q, t, Uni u) =
  -- (1) t has no unification vars => add bounds to the table
  if List.null unis then Tab table' cons'
    -- (2) t has unification vars including u => instantiate u with Top
    else if List.elem u unis then tableTop
      -- (3) t has unification vars but no cycle => add bounds to the table
      else if empty cycles then Tab table' cons'
        -- (4) t has unification vars including cycle => instantiate the
        -- unification variables in turn with Top
        else constructBranches table' cycles
  where
    unis            = List.nub $ findUnis t
    (table', cons') = addBounds (q, t, Uni u) table
    tableTop        = Tab (substTop u table') [(q, replaceTop u t, Top)]
    cycles          = map (\ux -> detectCycle [ux] table') unis

-- Construct branches for a list of cycles of unification vars
constructBranches :: Table -> [Cycle] -> Result
constructBranches table [c]    = constructBranch table c
constructBranches table (c:cs) = Branch (constructBranch table c) (constructBranches table cs)

-- Construct branches for a cycle (i.e. a list of unification variables)
-- by instantiating them in turn with Top
constructBranch :: Table -> Cycle -> Result
constructBranch table [u]    = Tab table' ((EmptyQ, Top, Uni u) : consTable table')
  where
    table' = substTop u table
constructBranch table (u:us) = Branch result' (constructBranch table us)
  where
    result' = Tab table' cons'
    table' = substTop u table
    cons'  = (EmptyQ, Top, Uni u) : consTable table'

-- Detect a cycle in a table
detectCycle :: [TUni] -> Table -> Cycle
detectCycle acc@(u:us) table = concat $ map go (findAllUnis u table)
  where
    go :: TUni -> Cycle
    go = \ux -> if List.elem ux acc
                then DT.trace "-------CYCLE-------" $ acc
                else detectCycle (ux:acc) table

--------------------------------
-- EXPANDING CONSTRAINT TABLE --
--------------------------------
-- Expand a constraint table
expand :: Table -> Substitution
-- base case
expand []         = []
-- variable case
expand (e:es) | (not $ null unis) && (not $ null entries) = sub ++ rest
  where
    unis    = hasUnis (lower e ++ upper e)
    entries = getEntries unis es
    sub     = expand entries
    rest    = expand (applySubstTable sub ((List.\\) (e:es) entries))
expand (e:es) | (not $ null unis) && (null entries) = sub ++ rest
  where
    unis    = hasUnis (lower e ++ upper e)
    entries = getEntries unis es
    sub     = [(uni e, PosT, lub $ lower e),
               (uni e, NegT, glb $ upper e)]
    rest    = expand $ applySubstTable sub es
-- no lower/upper bounds
expand (e:es) | null (lower e) && null (upper e) = sub ++ rest
  where
    sub  = [(uni e, PosT, Var $ uni e),
            (uni e, NegT, Var $ uni e)]
    rest = expand $ applySubstTable sub es
-- only an upper bound
expand (e:es) | null (lower e) = sub ++ rest
  where
    sub  = [(uni e, PosT, glb $ upper e), (uni e, NegT, glb $ upper e)]
    rest = expand $ applySubstTable sub es
-- only a lower bound
expand (e:es) | null (upper e) = sub ++ rest
  where
    sub  = [(uni e, PosT, lub $ lower e), (uni e, NegT, lub $ lower e)]
    rest = expand $ applySubstTable sub es
-- lower bound and upper bound
expand (e:es) = sub ++ rest
  where
    sub  = [(uni e, PosT, lub $ lower e), (uni e, NegT, glb $ upper e)]
    rest = expand $ applySubstTable sub es

----------------
-- EDIT TABLE --
----------------

-- Add (upper/lower) bounds to the table
addBounds :: Sub -> Table -> (Table, [Sub])
addBounds (_, Uni u1, Uni u2) table = (addUpper u1 (Uni u2) table, cons)
  -- all lower bounds should be a subtype of the new upper bound
  where cons   = [(EmptyQ, t1, Uni u2) | t1 <- getLower u1 table]
addBounds (_, Uni u,  t)      table = (addUpper u t table, cons)
  -- all lower bounds should be a subtype of the new upper bound
  where cons   = [(EmptyQ, t', t) | t' <- getLower u table]
addBounds (_, t,      Uni u)  table = (addLower u t table, cons)
  -- all upper bounds should be a subtype of the new lower bound
  where cons   = [(EmptyQ, t, t') | t' <- getUpper u table]
addBounds  _            table = (table, [])

-- Get the lower bounds from the table for a unification variable
getLower :: TUni -> Table -> [Type]
getLower u []     = []
getLower u (e:es) | uni e == u = lower e
getLower u (e:es) = getLower u es

-- Get the upper bounds from a table for a unification variable
getUpper :: TUni -> Table -> [Type]
getUpper u []     = []
getUpper u (e:es) | uni e == u = upper e
getUpper u (e:es) = getUpper u es

-- Add a lower bound to the table for a unification variable
addLower :: TUni -> Type -> Table -> Table
addLower u ty []     = [Entry u [ty] []]
addLower u ty (e:es) | u == uni e = Entry u (ty : lower e) (upper e) : es
addLower u ty (e:es) = e : addLower u ty es

-- Add an upper bound to the table for a unification variable
addUpper :: TUni -> Type -> Table -> Table
addUpper u ty []     = [Entry u [] [ty]]
addUpper u ty (e:es) | u == uni e = Entry u (lower e) (ty : upper e) : es
addUpper u ty (e:es) = e : addUpper u ty es

-- get the entries for a given list of unification variables
getEntries :: [TUni] -> Table -> [Entry]
getEntries []     table = []
getEntries (u:us) table = (e ++ es)
  where
    e  = filter (\entry -> uni entry == u) table
    es = getEntries us table

-- Find all unification variables in the upper and lower bounds of a unification variable
findAllUnis :: TUni -> Table -> [TUni]
findAllUnis u table = List.nub $ concat $ map findUnis (getLower u table ++ getUpper u table)

-- Find all the constraints currently included in the given table
consTable :: Table -> Subs
consTable []     = []
consTable (e:es) = go (lower e) (upper e) ++ consTable es
  where
    go :: [Type] -> [Type] -> Subs
    go []         _    = []
    go (low:lows) upps = map (\upp -> (EmptyQ, low, upp)) upps ++ go lows upps

-------------------
-- SUBSTITUTIONS --
-------------------

-- Substitute a unification variable with Top in a table
substTop :: TUni -> Table -> Table
substTop u []     = []
substTop u (e:es) | uni e == u = Entry u [Top] [] : substTop u es
substTop u (e:es) = e' : substTop u es
  where
    e' = Entry (uni e) low upp
    low = map (replaceTop u) (lower e)
    upp = map (replaceTop u) (upper e)

-- Apply a substitution to a table
applySubstTable :: Substitution -> Table -> Table
applySubstTable []         table = table
applySubstTable (sub:subs) table = applySubstTable subs (substInTable sub table)

-- Apply a substitution to a table
substInTable :: (TUni, Polarity, Type) -> Table -> Table
substInTable _    []    = []
substInTable sub (e:es) = Entry (uni e) low upp : substInTable sub es
  where
    low  = map (substInType sub PosT) (lower e)
    upp  = map (substInType sub NegT) (upper e)
    rest = substInTable sub es

-- Apply a substitution to a type with a given polarity
substInType :: (TUni, Polarity, Type) -> Polarity -> Type -> Type
substInType (u1, pol1, t1) pol2 (Uni u2) | pol1 == pol2 && u1 == u2 = t1
substInType (u1, pol1, t1) pol2 (Var a2) | pol1 == pol2 && u1 == a2 = t1
substInType s pol (Arr t1 t2) = Arr (substInType s (inv pol) t1)
                                    (substInType s pol t2)
substInType s pol (And t1 t2) = And (substInType s pol t1)
                                    (substInType s pol t2)
substInType s pol (Rec l t)   = Rec l (substInType s pol t)
substInType _ _ t = t

----------------------------
-- UPPER AND LOWER BOUNDS --
----------------------------

-- Compute the least upper bound of a list of types
lub :: [Type] -> Type
lub = foldr lub' Bot

-- Compute the least upper bound of two types
lub' :: Type -> Type -> Type
lub' t1             t2           | t1 == t2 = t1
lub' t1             Bot          = t1
lub' Bot            t2           = t2
lub' (Arr t11 t12) (Arr t21 t22) = Arr (glb' t11 t21) (lub' t12 t22)
lub' (Rec l1 t1)   (Rec l2 t2)   | l1 == l2 = Rec l1 (lub' t1 t2)
lub' (And t11 t12)  t2           = if left  == Top then right else
                                   if right == Top then left  else
                                   And left right
                     where left  = lub' t11 t2
                           right = lub' t12 t2
lub'  t1           (And t21 t22) = if left  == Top then right else
                                   if right == Top then left  else
                                   And left right
                     where left  = lub' t1 t21
                           right = lub' t1 t22
lub' _ _ = Top

-- Compute the greatest lower bound of a list of types
glb :: [Type] -> Type
glb = foldr glb' Top

-- Compute the greatest lower bound of two types
glb' :: Type -> Type -> Type
-- BCD subtyping
glb' (Arr t11 t12) (Arr t21 t22) = Arr (glb' t11 t21) (glb' t12 t22)
glb' (Rec l1 t1)   (Rec l2 t2)   | l1 == l2 = Rec l1 (glb' t1 t2)
-- simplify intersections e.g. A & B & A & C & B = A & B & C
glb' (And t11 t12)  t2           = simplify $ And (glb' t11 t2) (glb' t12 t2)
glb' t1            (And t21 t22) = simplify $ And (glb' t1 t21) (glb' t1 t22)
glb' t1             t2           = And t1 t2

------------------------------------
-- SIMPLIFYING INTERSECTION TYPES --
------------------------------------

-- Simplify an intersection type
simplify :: Type -> Type
simplify ty = mkInt $ simplInt ty []
  where
    simplInt :: Type -> [Type] -> [Type]
    simplInt t           lst | t `elem` lst = lst
    simplInt (And t1 t2) lst = simplInt t2 (simplInt t1 lst)
    simplInt _           lst = lst
    mkInt :: [Type] -> Type

    mkInt []     = Top
    mkInt [x]    = x
    mkInt (x:xs) = And x (mkInt xs)

----------------------
-- HELPER FUNCTIONS --
----------------------

-- Toplike types are those types that are isomorphic to top
toplike :: Type -> Bool
toplike Top         = True
toplike (And t1 t2) = toplike t1 && toplike t2
toplike (Arr _   t) = toplike t
toplike (Rec _ t)   = toplike t
toplike _           = False

-- Check whether a subtyping rule contains a unification variable
containsUni :: Sub -> Bool
containsUni (EmptyQ, Uni u, _) = True
containsUni (EmptyQ, _, Uni u) = True
containsUni  _                 = False

-- Find all unification variables in a type
findUnis :: Type -> [TUni]
findUnis (Uni u)     = [u]
findUnis (Arr t1 t2) = (findUnis t1) ++ (findUnis t2)
findUnis (And t1 t2) = (findUnis t1) ++ (findUnis t2)
findUnis (Rec _ t)   = findUnis t
findUnis _           = []

-- Find all unification variables in a list of types
hasUnis :: [Type] -> [TUni]
hasUnis ts = foldr (++) [] (map findUnis ts)

-- Replace a unification variable in a type with top
replaceTop :: TUni -> Type -> Type
replaceTop u1 (Uni u2)   | u1 == u2 = Top
replaceTop u (Arr t1 t2) = Arr (replaceTop u t1) (replaceTop u t2)
replaceTop u (And t1 t2) = And (replaceTop u t1) (replaceTop u t2)
replaceTop u (Rec l t)   = Rec l (replaceTop u t)
replaceTop _ t           = t

-- Check whether a list of lists is empty
empty :: [[a]] -> Bool
empty []   = True
empty [[]] = True
empty _    = False

inv :: Polarity -> Polarity
inv PosT = NegT
inv NegT = PosT

-- TODO: proof strategy

-- [C] = { Theta | |= Theta(C)}
-- forall c, c'. (c >-> c') => [c] = [c']
-- forall c, c1, c2. (c >-> c1) and (c >-> c2) => [c] = [c1] and [c] = [c2]

-- zie paper Inferring Algebraic Effects (3.2, Theorem 3.3)


-- \usepackage{stmaryrd}
-- \begin{equation}
--   \llbracket     1 \rrbracket       \quad
-- \end{equation}
