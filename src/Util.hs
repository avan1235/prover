module Util where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace (trace)
import Data.List (delete, intercalate, sort)

debug :: Show a => a -> String -> a
debug o name = trace (name ++ " = " ++ show o) o

debugIOLines :: Show a => Int -> [a] -> IO ()
debugIOLines n xs = do
  putStr $ intercalate "\n" $ map show $ take n xs

update :: Ord a => Map.Map a b -> a -> b -> Map.Map a b
update f a b = Map.insert a b f

merge :: [a] -> [a] -> [a]
merge [] bs = bs
merge (a : as) bs = a : merge bs as

merges :: [[a]] -> [a]
merges = foldr merge []

functions :: Ord a => [a] -> [b] -> [Map.Map a b]
functions [] _ = [Map.empty]
functions (a : as) bs = merges [[update f a b | f <- functions as bs] | b <- bs]

prefixes :: [a] -> [[a]]
prefixes xs = drop 1 $ foldr f [[]] xs
  where
    f x acc = [] : map (x :) acc

ordNub :: Ord a => [a] -> [a]
ordNub = go Set.empty
  where
    go _ [] = []
    go acc (x : xs) =
      if Set.member x acc
        then go acc xs
        else x : go (Set.insert x acc) xs
