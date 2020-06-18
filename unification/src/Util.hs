module Util where

import           Data.List

import           Syntax

------------------------------------
-- SIMPLIFYING INTERSECTION TYPES --
------------------------------------

-- Simplify an intersection type
simplify :: Type -> Type
simplify ty = mkInt $ nub $ elemInt ty

elemInt :: Type -> [Type]
elemInt (And t1 t2) = elemInt t1 ++ elemInt t2
elemInt t           = [t]

mkInt :: [Type] -> Type
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

expandType :: Queue -> Type -> Type
expandType EmptyQ t     = t
expandType (QA t1 q) t2 = Arr t1 (expandType q t2)
expandType (QL l  q) t2 = Rec l  (expandType q t2)

-- Check whether a list of lists is empty
empty :: [[a]] -> Bool
empty []  = True
empty lst = foldr (&&) True (map null lst)

-- Inverse a polarity
inv :: Polarity -> Polarity
inv PosT = NegT
inv NegT = PosT

-- Check whether a type is primitive
isPrim :: Type -> Bool
isPrim Bool    = True
isPrim Nat     = True
isPrim (Var _) = True
isPrim Bot     = True
isPrim (Uni _) = True
isPrim _       = False

-------------------
-- SUBSTITUTIONS --
-------------------

-- Substitute a unification variable with Top in a table
substTop :: TUni -> Table -> Table
substTop _ []     = []
substTop u (e:es) | uni e == u = Entry u [Top] [] : substTop u es
substTop u (e:es) = e' : substTop u es
  where
    e' = Entry (uni e) low upp
    low = map (replaceTop u) (lower e)
    upp = map (replaceTop u) (upper e)

substTopQueue :: TUni -> Queue -> Queue
substTopQueue _ EmptyQ   = EmptyQ
substTopQueue u (QL l q) = QL l (substTopQueue u q)
substTopQueue u (QA t q) = QA (substTopType u t) (substTopQueue u q)

substTopType :: TUni -> Type -> Type
substTopType u1 (Uni u2)    | u1 == u2 = Top
substTopType u  (Arr t1 t2) = Arr (substTopType u t1) (substTopType u t2)
substTopType u  (And t1 t2) = And (substTopType u t1) (substTopType u t2)
substTopType u  (Rec l t)   = Rec l (substTopType u t)
substTopType _   t          = t

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


-- Apply a substitution to a subtyping constraint
applySubst :: Substitution -> Type -> Type -> (Type, Type)
applySubst []     t1 t2 = (t1, t2)
applySubst (s:ss) t1 t2 = applySubst ss (substInType s PosT t1) (substInType s NegT t2)
