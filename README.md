# Type Inference for Disjoint Intersection types

## Aim
This code presents a type inference algorithm for a calculus with disjoint intersection types and a merge operator, BCD subtyping and (disjoint) polymorphism.
An intersection of two types `A` and `B`, denoted `A&B`, is the type of all values that have at the same time type `A` and type `B`.
A merge operator `,,` introduces intersection types at the term level, for instance `(5.0 ,, true) : (Double & Bool)`.
They can be used in operations as follows:
```
(5.0 ,, true) +  3.0   = 8.0
(5.0 ,, true) OR false = true
```
This is similar to a tuple, except that with merges, projections are implicit.
In order to avoid ambiguity, for instance as in `(5.0 ,, 3.0) + 1.0 = ???`, the types in intersections can not overlap and thus should be disjoint, denoted by `A*B`.

BCD subtyping expresses the distributivity of intersection over function types and record types. For example, `(A -> B_1) & (A -> B_2) <: A -> (B_1 & B_2)`.
Parametric disjoint polymorphism includes disjointness requirements in type abstractions. For example `forall (A * Double). A & Double`.

## Algorithm
The algorithm can be found in the [inference](inference) folder.
