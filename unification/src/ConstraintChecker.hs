module ConstraintChecker where

import           Syntax
import           Util

import           Debug.Trace as DT

constant :: Type -> Bool
constant Bot     = True
constant Nat     = True
constant Bool    = True
constant (Var _) = True
constant _       = False

uni2var :: Type -> Type
uni2var (Uni u)     = Var u
uni2var (Arr t1 t2) = Arr (uni2var t1) (uni2var t2)
uni2var (And t1 t2) = And (uni2var t1) (uni2var t2)
uni2var (Rec l t)   = Rec l (uni2var t)
uni2var t           = t

constraintCheck :: Type -> Type -> Bool
constraintCheck t1 t2 = check $ (EmptyQ, uni2var t1, uni2var t2)

check :: Sub -> Bool
check (_, t, Top)            = True
check (q, t, And t1 t2)      = check (q, t, t1) && check (q, t, t2)
check (q, t, Arr t1 t2)      = check (pushType t1 q, t, t2)
check (q, t, Rec l t1)       = check (pushLabel l q, t, t1)
check (EmptyQ, c1, c2)       | isPrim c1 && isPrim c2 && c1 == c2 = True
check (_, Bot, c)            | isPrim c = True
check (QA t q, Arr t1 t2, c) | isPrim c = check (EmptyQ, t, t1) && check (q, t2, c)
check (QL l q, Rec l1 t1, c) | isPrim c && l == l1 = check (q, t1, c)
check (q, And t1 t2, c)      | isPrim c = check (q, t1, c) || check (q, t2, c)
check  sub                   = DT.trace ("ConstraintChecker sub:  " ++ show sub) $ False
