--> Int

let ^f : Int -> Int = (\x -> (let ^y : Int = x-1 in ^y)) in 5
