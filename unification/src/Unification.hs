module Unification
    ( checkSubtyping
    ) where

import qualified Data.List   as List
import           Debug.Trace as DT
import           Syntax
import           Util

---------------------------------
-- CHECK SUBTYPING CONSTRAINTS --
---------------------------------

checkSubtyping :: Type -> Type -> [Substitution]
checkSubtyping t1 t2 = DT.trace ("tables: " ++ show tbls) $ map expand tbls
  where tbls = possTbls [(EmptyQ, t1, t2)] [] [] -- empty table, empty cache

-----------------------------
-- COMPUTE POSSIBLE TABLES --
-----------------------------

-- Computes a list of possible tables as output from the destruct function
possTbls :: Subs -> Table -> Subs -> [Table]
possTbls []       table _     = [table]
possTbls (s:subs) table cache = DT.trace ("result:  " ++ show (destruct s table)) $ interpret $ destruct s table
  where
    interpret :: Result -> [Table]
    interpret  Same              = possTbls subs table (s:cache)
    interpret (Tab table' cons') = possTbls (((List.\\) cons' (s:cache)) ++ subs) table' (s:cache)
    interpret (Cons cons)        = possTbls (cons ++ subs) table (s:cache)
    interpret (Branch r1 r2)     = interpret r1 ++ interpret r2
    interpret  Fail              = []

-- The result of a constraint can be the following:
data Result = Same                  -- ignore the constraint
            | Tab    Table  Subs    -- change the table and construct new constraints
            | Cons   Subs           -- destruct into smaller constraints
            | Branch Result Result  -- make a branch, i.e. multiple possible results
            | Fail                  -- the constraints can not be solved
            deriving (Eq, Show)

------------------------------------
-- DESTRUCT SUBTYPING CONSTRAINTS --
------------------------------------

-- Takes a subtyping rule and a table
-- Returns a result as described above
destruct :: Sub -> Table -> Result

-- (1) Trivial cases : ignore
-- (1.1) Same types
destruct (EmptyQ, c1, c2) _ | isPrim c1 && isPrim c2 && c1 == c2 = Same
-- (1.2) Bottom
destruct (_, Bot, c) _  | isPrim c = Same
-- (1.3) Top
destruct (_, _, c) _ | toplike c = Same
-- -- (1.4) BCD distributivity A & B <: A and A & B <: B
-- destruct (EmptyQ, And t1 t2, t3) _ | t1 == t3 || t2 == t3 = Same

-- (2) Add upper and/or lower bounds to the table
destruct c table | containsUni c = occursCheck table c

-- (3) Destruct the right type of the constraint first
-- (3.1) Push type to queue
destruct (q, t1, Arr t2 t3) _ = Cons [(pushType t2 q, t1, t3)]
-- (3.2) Push label to queue
destruct (q, t1, Rec l t2)  _ = Cons [(pushLabel l q, t1, t2)]
-- (3.3) Intersection type
destruct (q, t1, And t2 t3) _ = Cons ((q, t1, t2) : (q, t1, t3) : [])

-- (4) Destruct the left type of the constraint
-- (4.1) Pop type from queue
destruct (QA t q, Arr t1 t2, c3) _ | isPrim c3 = Cons ((EmptyQ, t, t1) : (q, t2, c3) : [])
-- (4.2) Pop label from queue
destruct (QL l q, Rec l' t1, c2) _ | isPrim c2 = if l == l' then Cons [(q, t1, c2)] else Fail
-- (4.3) Intersection types
destruct (q, And t1 t2, c) _ | isPrim c = Branch br1 (Branch br2 br3)
  where
    br1 = Cons [(q, t1, c)]
    br2 = Cons [(q, t2, c)]
    br3 = Cons ((q, t1, c) : (q, t2, c) : [])

-- (5) Reconstruct constraints
-- (5.1) Pop type from queue : Q, t ⊢ u <: t' ==> Q ⊢ u <: t -> t'
--                             Q, l ⊢ u <: t ==> Q ⊢ u <: {l : t}
destruct (q, Uni u, c)  _ | isPrim c = Cons [(EmptyQ, Uni u, expandType q c)]
-- (5.3) Unification variable is toplike
destruct (QL _ _, Top, Uni u) _ = Cons [(EmptyQ, Top, Uni u)]
destruct (QA _ _, Top, Uni u) _ = Cons [(EmptyQ, Top, Uni u)]
-- (5.4) Q ⊢ c <: u
destruct (QL _ _, c, Uni u) _ | isPrim c = Cons [(EmptyQ, Top, Uni u)] -- Fail
destruct (QA _ _, c, Uni u) _ | isPrim c = Cons [(EmptyQ, Top, Uni u)] -- Fail

-- (6) Other cases : fail
-- (6.1) Q ⊢ c1 <: c2
destruct (_, c1, c2) _ | isPrim c1 && isPrim c2 && c1 /= c2 = Fail
-- (6.2) t1 -> t2 <: c
destruct (EmptyQ, Arr _ _, c) _ | isPrim c = Fail
-- (6.3) {l : t} <: c
destruct (EmptyQ, Rec _ _, c) _ | isPrim c = Fail
-- (6.4) t1 -> t2 <: {l : t}
destruct (QL _ _, Arr _ _, c) _ | isPrim c = Fail
-- (6.5) {l : t} <: t1 -> t2
destruct (QA _ _, Rec _ _, c) _ | isPrim c = Fail
-- (6.6) Q ⊢ Top <: c
destruct (_, t, c) _ | isPrim c && toplike t && (not $ toplike c) = Fail
-- (6.7) Q ⊢ c <: c
destruct (QA _ _, c1, c2) _ | isPrim c1 && isPrim c2 = Fail
destruct (QL _ _, c1, c2) _ | isPrim c1 && isPrim c2 = Fail


destruct s _ = DT.trace ("OTHER......    " ++ show s) $ Fail

-------------------
-- DETECT CYCLES --
-------------------

-- a cycle consists of a list of unification variables
type Cycle = [TUni]

-- The occurs check properly deals with cycles in the subtyping constraints
occursCheck :: Table -> Sub -> Result
occursCheck table (q, And t1 t2, Uni u2) | elem (Uni u2) (elemInt (And t1 t2)) = Same
occursCheck table (q, And t1 t2, Uni u2) | elem (Uni u2) (elemInt (And t1 t2))  = Same
occursCheck table (q, Uni u1, And (Uni u2) t) | u1 == u2 = occursCheck table (q, Uni u1, t)
occursCheck table (q, Uni u1, And t (Uni u2)) | u1 == u2 = occursCheck table (q, Uni u1, t)
occursCheck table c@(q, Uni u, t) =
  -- (1) t has no unification vars => add bounds to the table
  if List.null unis then Tab table' cons'
    -- (2) t has unification vars including u => instantiate u with Top
    else if List.elem u unis then tableTop
      -- (3) t has unification vars but no cycle => add bounds to the table
      else if empty cycles then Tab table' cons'
        -- (4) t has unification vars including cycle => instantiate the
        -- unification variables in turn with Top
        else DT.trace ("cycles: " ++ show cycles ++ "\nconstop1  " ++ show consTop) $ constructBranches table cycles c
  where
    unis            = List.nub $ findUnis t
    (table', cons') = addBounds (q, Uni u, t) table
    consTop         = (q, Top, replaceTop u t) : [(EmptyQ, Top, t) | t <- getUpper u table']
    tableTop        = Tab (substTop u table') consTop
    cycles          = map (\ux -> detectCycle [ux] table') unis

occursCheck table c@(q, t, Uni u) =
  -- (1) t has no unification vars => add bounds to the table
  if List.null unis then Tab table' cons'
    -- (2) t has unification vars including u => instantiate u with Top
    else if List.elem u unis then tableTop
      -- (3) t has unification vars but no cycle => add bounds to the table
      else if empty cycles then Tab table' cons'
        -- (4) t has unification vars including cycle => instantiate the
        -- unification variables in turn with Top
        else DT.trace ("cycles: " ++ show cycles ++ "\nconstop2  " ++ show consTop) $ constructBranches table cycles c
  where
    unis            = List.nub $ findUnis t
    (table', cons') = addBounds (q, t, Uni u) table
    consTop         = (q, Top, replaceTop u t) : [(EmptyQ, Top, t) | t <- getUpper u table']
    tableTop        = Tab (substTop u table') consTop
    cycles          = map (\ux -> detectCycle [ux] table') unis

-- Construct branches for a list of cycles of unification vars
constructBranches :: Table -> [Cycle] -> Sub -> Result
constructBranches table [cyc]      c = constructBranch table cyc c
constructBranches table (cyc:cycs) c = Branch (constructBranch table cyc c) (constructBranches table cycs c)

-- Construct branches for a cycle (i.e. a list of unification variables)
-- by instantiating them in turn with Top
constructBranch :: Table -> Cycle -> Sub -> Result
constructBranch tab [] c = Tab table cons
  where
    (table, cons)  = addBounds c tab
constructBranch tab [u] c@(q, t1, t2) = DT.trace ("CONS : " ++ show cons') $ Tab table' cons'
  where
    (table, _) = addBounds c tab
    cons1      = [(EmptyQ, Top, Uni u)]
    cons2      = [(EmptyQ, Top, t) | t <- getUpper u table]
    cons3      = [(substTopQueue u q, substTopType u t1, substTopType u t2)]
    table'     = substTop u table
    cons'      = cons1 ++ cons2 ++ cons3 ++ consTable table'
constructBranch tab (u:us) c@(q, t1, t2) = DT.trace ("CONS : " ++ show cons') $ Branch result' (constructBranch tab us (q, t1, t2))
  where
    (table, _) = addBounds c tab
    cons1      = [(EmptyQ, Top, Uni u)]
    cons2      = [(EmptyQ, Top, t) | t <- getUpper u table]
    cons3      = [(substTopQueue u q, substTopType u t1, substTopType u t2)]
    result'    = Tab table' cons'
    table'     = substTop u table
    cons'      = cons1 ++ cons2 ++ cons3 ++ consTable table'

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
expand (e:es) | null (lower e) && null (upper e) = sub ++ rest
  where
    sub  = [(uni e, PosT, Var $ uni e),
            (uni e, NegT, Var $ uni e)]
    rest = expand $ applySubstTable sub es

expand (e:es) = sub ++ rest
  where
    sub     = if null $ lower e
              then [(uni e, PosT, glb $ upper e), (uni e, NegT, glb $ upper e)]
              else if null $ upper e
                   then [(uni e, PosT, lub $ lower e), (uni e, NegT, lub $ lower e)]
                   else [(uni e, PosT, lub $ lower e), (uni e, NegT, glb $ upper e)]
    rest    = expand $ applySubstTable sub es

----------------
-- EDIT TABLE --
----------------

-- Add (upper/lower) bounds to the table
addBounds :: Sub -> Table -> (Table, Subs)
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

----------------------------
-- UPPER AND LOWER BOUNDS --
----------------------------

-- Compute the least upper bound of a list of types
lub :: [Type] -> Type
-- lub []     = Top -- TODO
lub [t]    = t
lub (t:ts) = lub' t (lub ts)

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
-- glb []     = Bot -- TODO
glb [t]    = t
glb (t:ts) = glb' t (glb ts)

-- Compute the greatest lower bound of two types
glb' :: Type -> Type -> Type
glb' t1             t2           | t1 == t2 = t1
glb' t1             Top          = t1
glb' Top            t2           = t2
glb' (Arr t11 t12) (Arr t21 t22) = Arr (lub' t11 t21) (glb' t12 t22)
glb' (Rec l1 t1)   (Rec l2 t2)   | l1 == l2 = Rec l1 (glb' t1 t2)
glb' (And t11 t12)  t2           = simplify $ And (glb' t11 t2) (glb' t12 t2)
glb' t1            (And t21 t22) = simplify $ And (glb' t1 t21) (glb' t1 t22)
glb' t1             t2           = And t1 t2
-- -- equal types
-- glb' t1            t2            | t1 == t2 = t1
-- -- BCD subtyping
-- glb' (Arr t11 t12) (Arr t21 t22) = Arr (glb' t11 t21) (glb' t12 t22)
-- glb' (Rec l1 t1)   (Rec l2 t2)   | l1 == l2 = Rec l1 (glb' t1 t2)
-- -- simplify intersections e.g. A & B & A & C & B = A & B & C
-- glb' (And t11 t12)  t2           = simplify $ And (glb' t11 t2) (glb' t12 t2)
-- glb' t1            (And t21 t22) = simplify $ And (glb' t1 t21) (glb' t1 t22)
-- glb' t1             t2           = And t1 t2
