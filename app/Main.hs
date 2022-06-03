{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main where

import Parser (parseString)
import System.IO (isEOF)

prover :: p -> Bool
prover _ = True

main :: IO ()
main = do
  eof <- isEOF
  if eof
    then return ()
    else do
      line <- getLine
      let phi = parseString line
      let res = prover phi
      if res
        then putStrLn "1"
        else putStrLn "0"