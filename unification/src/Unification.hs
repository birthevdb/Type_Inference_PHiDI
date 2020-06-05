module Unification
    ( someFunc
    ) where

someFunc :: IO ()
someFunc = putStrLn "someFunc"


-- destruct
-- multiple solutions
-- occurs check


-- proof strategy

-- [C] = { Theta | |= Theta(C)}
-- forall c, c'. (c >-> c') => [c] = [c']
-- forall c, c1, c2. (c >-> c1) and (c >-> c2) => [c] = [c1] and [c] = [c2]

-- zie papaer Inferring Algebraic Effects (3.2, Theorem 3.3)


-- \usepackage{stmaryrd}
-- \begin{equation}
--   \llbracket     1 \rrbracket       \quad
-- \end{equation}
