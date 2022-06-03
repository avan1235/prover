module Util where

import Debug.Trace (trace)
import qualified Data.Map as Map

debug :: Show a => a -> String -> a
debug o name = trace (name ++ " = " ++ show o) o

-- debug o _ = o

update :: Eq a => (a -> b) -> a -> b -> a -> b
update f a b x
  | x == a = b
  | otherwise = f x

partitions :: [a] -> [[[a]]]
partitions [] = [[]]
partitions (x : xs) = [[x] : yss | yss <- partitions xs] ++ [(x : ys) : yss | (ys : yss) <- partitions xs]

cartProd :: Int -> [a] -> Map.Map Int [[a]]
cartProd n xs = Map.fromAscList $ map key [1..n]
  where
    key x = (x, go x)
    go 0 = [[]]
    go n = [x : y | x <- xs, y <- ys]
      where
        ys = go (n - 1)

-- all possible ways to split n into the sum of strictly positive integers
catalan :: Int -> [[Int]]
catalan n = map (map length) $ partitions [1 .. n]

-- alternating merge of two (potentially infinite) lists
merge :: [a] -> [a] -> [a]
merge [] bs = bs
merge (a : as) bs = a : merge bs as

-- alternating merge of a (potentially infinite) list of (potentially infinite) lists
merges :: [[a]] -> [a]
merges = foldr merge []

-- collect all functions from a finite list to a (potentially infinite) list
functions :: Eq a => [a] -> [b] -> [a -> b]
functions [] _ = [undefined]
functions (a : as) bs = merges [[update f a b | f <- functions as bs] | b <- bs]
