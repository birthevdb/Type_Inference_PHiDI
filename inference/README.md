# Type Inference for Disjoint Intersection types

## Dependencies

- [stack](https://docs.haskellstack.org/en/stable/README/) >= 1.9

## Building

```shell
$ stack build
```

## Usage

The interpreter can be launched with

```shell
$ stack run
```

You can evaluate PHiDI expressions and get information about
their type.

```shell
> true ,, 3
Typing result
: (Bool & Int)

Elaborated term
~~>  True ,, 3.0

Evaluation result
=> <Pair>
```

## Syntax

### Types

- Int: `Int`
- Top: `Top`
- Bottom: `Bot`
- Arrow: `Int -> Bool`
- Record: `{label : Int}`
- Intersection: `Top & Int`
- Type variable: `X`
- Boolean: `Bool`
- Forall: `forall (X * Top) . X -> X`

### Expressions

- Literal
    ```
    3.14
    ```
- Top
    ```
    ()
    ```
- Lambda variable
    ```
    x
    ```
- Let variable
    ```
    ^x
    ```
- Lambda
    ```
    \x -> x + 5
    \_ -> true
    ```
- Application
    ```
    (\x -> x) 3
    ```
- Record construction
    ```
    {label = 3.0}
    ```
- Record extraction
    ```
    {label = 3.0} . label
    ```
- Merge
    ```
    3.0 ,, true
    ```
- Letrec
    ```
    let ^id : forall (X * Top) . X -> X = \v -> v in ^id 5
    ```
- Boolean literal
    ```
    true
    false
    ```
- Primitive operations
    ```
    2 * 4
    4 / 2
    3 + 1
    5 - 0
    3 > 1
    1 < 2
    3 == 2
    4 /= 5
    true && false
    false || true
    ```
    An example:
    ```
    let ^pos : (Int -> Bool) = \x -> x == 0 || x > 0 in ^pos 1.5
    ```
- If
    ```
    (\x -> if x < 0 then false else true) (0.0 - 3)
    ```

## More examples

The examples in the map [examples](examples) can be run with

```shell
$ stack test
```
This tests whether the inferred type for the given term is as expected.
Some more examples:

```
> main = \x -> x x
Typing result
: (∀(u*Top) . (∀(u1*Top) . ((u & (u → u1)) → u1)))

Elaborated term
~~> Λ(u * Top)
    . Λ(u1 * Top)
      . λ(x) . (x : ((u → u1) → u1)) x : (((u → u1) & ((u → u1) → u1)) → u1)

Evaluation result
=> <lambda>
```

```
> main = (\x -> x x) (\x -> x x)
1:8:
Occurs check: cannot construct infinite type.
In the expression:
(λ(x) . x x) (λ(x) . x x)
```

```
> main = (\x -> x) ,, (\x -> x)
Typing result
: (∀(u*Top) . (∀(u1*u) . ((u1 → u1) & (u → u))))

Elaborated term
~~> Λ(u * Top) . Λ(u1 * u) . λ(x) . x : (u1 → u1) ,, λ(x) . x : (u → u)

Evaluation result
=> <Pair>
```
