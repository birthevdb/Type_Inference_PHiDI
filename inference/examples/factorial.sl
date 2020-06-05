--> Int

let ^fac : (Int -> Int) = (\x -> if x < 1 then 1 else x * (^fac (x - 1))) in ^fac 5
