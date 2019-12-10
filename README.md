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
Typing result
: (Bool & Double)

Elaborated term
~~>  True ,, 3.0

Evaluation result
=> <Pair>
```

```
stack ghci
main
> main = let ^f = 5 in (\x -> x) ^f
Typing result
: Double

Elaborated term
~~>  let f = 5.0 in (λ(x) . x : (Double → Double) : (Double → Double)) f

Evaluation result
=> <Pair>
```

```
stack ghci
main
> main = letrec ^f : Double  = 5 in (\x -> x) ^f
Typing result
: Double

Elaborated term
~~> letrec f : Double = 5.0
    in  (λ(x) . x : (Double → Double) : (Double → Double)) f

Evaluation result
=> 5.0
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

## Code

The code for testing properties can be found in [Test.hs](impl/src/SEDEL/Test.hs).
