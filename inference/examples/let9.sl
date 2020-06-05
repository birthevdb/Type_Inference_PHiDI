--> Int

let ^f : forall (A * Top). forall (B * A). A -> B -> (A & B -> Int) -> Int = \x -> \y -> \g -> g (x ,, y) in ^f 1 2 (\x -> x)
