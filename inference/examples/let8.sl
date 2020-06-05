--> forall (A * Int) . A -> Int

let ^id : Int -> Int = \x -> x in ((\z -> (\x -> \y -> ^id (x ,, y)) z 2))
