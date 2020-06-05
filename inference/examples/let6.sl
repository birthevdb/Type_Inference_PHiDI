--> forall (A * Int) . A -> Int

let ^id : Int -> Int = \x -> x in (\x -> \y -> ^id (x ,, y)) 1
