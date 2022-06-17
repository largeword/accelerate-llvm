-- |
-- Module      : nofib-llvm-native
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
{-# LANGUAGE TypeApplications #-}
module Main where

import Data.Array.Accelerate as A
-- import Data.Array.Accelerate.Test.NoFib
import Data.Array.Accelerate.LLVM.Native

main :: IO ()
-- main = nofib runN
main = print $ run @Native $ complex (use $ fromList (Z:.10) [1 :: Int ..])

complex :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
complex xs = let as = A.map (* 2)             xs
                 bs = A.map (+ 3)             xs
                 cs = A.map (\a -> bs ! I1 a) as
                 ds = A.map (\b -> as ! I1 b) bs
              in T2 cs ds



