# “Polymorphic Hindley-Milner for Disjoint Intersection types

## Dependencies

- [stack](https://docs.haskellstack.org/en/stable/README/) >= 1.9

## Building

```shell
$ stack build
```

## Usage

The interpreter can be launched with

```shell
$ stack ghci
```

In the interpreter, the main loop can be started with

```shell
> main
```

In the main loop, you can evaluate PHiDI expressions and get information about
their type. You need to write your expressions in the form `main = expression`.

```shell
> main = true ,, 3
Typing result
: (Bool & Double)

Elaborated term
~~>  True ,, 3.0

Evaluation result
=> <Pair>
```

## Syntax

### Types

- Int: `Double`
- Top: `Top`
- Bottom: `Bot`
- Arrow: `Double -> Bool`
- Record: `{label : Double}`
- Intersection: `Top & Double`
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
    main = let ^pos : (Double -> Bool) = \x -> x == 0 || x > 0 in ^pos 1.5
    ```
- If
    ```
    main = (\x -> if x < 0 then false else true) (0.0 - 3)
    ```

<!--
## Tests

### Testing soundness

```
stack ghci
test_soundness
```

### Testing completeness

```
stack ghci
test_completeness
```

### Testing principality

```
stack ghci
test_principality
```

Testing this property is future work.
-->
