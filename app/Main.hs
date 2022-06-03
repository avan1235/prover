{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main where

-- import Formula (tautology)
-- import Parser (parseString)
-- import System.IO (isEOF)

-- main :: IO ()
-- main = do
--   eof <- isEOF
--   if eof
--     then return ()
--     else do
--       line <- getLine
--       let phi = parseString line
--       let res = tautology phi
--       if res
--         then putStrLn "1"
--         else putStrLn "0"

import Formula (test)

main :: IO ()
main = do
  print test