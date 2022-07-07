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
{-# LANGUAGE ViewPatterns #-}
module Main where

import Data.Array.Accelerate as A
import Data.Array.Accelerate.Trafo
import Data.Array.Accelerate.Interpreter
-- import Data.Array.Accelerate.Test.NoFib
import Data.Array.Accelerate.LLVM.Native
import Data.Array.Accelerate.LLVM.Native.Operation

main :: IO ()
-- main = nofib runN
main = do
  -- Currently, SLV is broken and it removes permutes!
  -- putStrLn $ test @UniformScheduleFun @NativeKernel $ \xs ys -> A.permute @DIM2 @DIM1 @Int (+) xs (const $ Just_ $ I1 0) ys
  -- putStrLn $ test @UniformScheduleFun @NativeKernel $ A.reverse @Int
  print $ run @Native $ zippies (use $ fromList (Z:.10) [1 :: Int ..])

-- See the TODO in Solve.hs: the combination of the current naive cost function and not splitting them there,
-- causes us to make 2 clusters here (even without the zipWith), with the second one consisting of two unrelated maps. Luckily, they
-- do have the same size, so it works out fine for Native :)
complex :: Acc (Vector Int) -> Acc (Vector Int)
complex xs = let as = A.map (* 2)             xs
                 bs = A.map (+ 3)             xs
                 cs = A.map (\a -> bs ! I1 a) as
                 ds = A.map (\b -> as ! I1 b) bs
              in A.zipWith (+) cs ds

-- the map correctly doesn't get fused into the zip and reverse kernel
zippies :: Acc (Vector Int) -> Acc (Vector Int)
zippies (A.map (*2) -> xs) = A.zipWith6 (\a b c d e f -> a + b + c + d + e + f)
  xs
  xs
  xs
  xs
  (A.reverse xs)
  xs

