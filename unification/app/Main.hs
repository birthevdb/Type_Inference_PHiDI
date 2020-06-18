module Main where

import           System.Environment (getArgs)
import           System.Exit

import           Parser
import           Unification

parseInput :: IO ()
parseInput = do
  putStrLn "Type your subtyping constraint:"
  l1 <- getLine
  putStrLn "<:"
  l2 <- getLine
  case (parseType l1, parseType l2) of
    (Left err1, Left err2) -> do
      putStrLn err1
      putStrLn err2
      exitWith (ExitFailure 1)
    (Left err1, _) -> do
      putStrLn err1
      exitWith (ExitFailure 1)
    (_, Left err2) -> do
      putStrLn err2
      exitWith (ExitFailure 1)
    (Right t1, Right t2) -> do
      putStrLn $ show $ checkSubtyping t1 t2
      return ()


main :: IO ()
main = parseInput
