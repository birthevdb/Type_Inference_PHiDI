--> forall (A * Top) . forall (B * A) . A -> B -> A & B

let ^id : forall (A * Top). A -> A  = \x -> x in \x -> \y -> ^id (x ,, y)
