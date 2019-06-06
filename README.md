# Type_Inference_PHiDI

## Build and Run

This project can be built with
[stack](https://docs.haskellstack.org/en/stable/README/) version 1.9.

```
stack build
stack ghci
```

## Usage

* Main program
```
stack ghci
main 
> main = true ,, 3
Fi+ term:         Merge (BoolV True) (LitV 3.0)
Source type:      SType (And BoolT NumT)
Fi+ type:         And BoolT NumT
Typing result
: (Bool & Double)

Evaluation result
=> <Pair>
```
* Testing soundness
```
stack ghci
test_soundness
```
* Testing completeness
```
stack ghci
test_completeness
```
* Testing principality
```
stack ghci
test_principality
```
Testing this property is future work.
