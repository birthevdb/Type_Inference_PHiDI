--> Int

let ^f : Int -> Int = (\x -> if (x > 0) then 0 else (let ^y : Int = (x - 1) in ^f ^y)) in ^f 5
