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
import Data.Array.Accelerate.Trafo
import Data.Array.Accelerate.Interpreter
-- import Data.Array.Accelerate.Test.NoFib
import Data.Array.Accelerate.LLVM.Native
import Data.Array.Accelerate.LLVM.Native.Operation

main :: IO ()
-- main = nofib runN
main = do
  -- print $ test @UniformScheduleFun @InterpretKernel $ complex (use $ fromList (Z:.10) [1 :: Int ..])
  print $ run @Native $ complex (use $ fromList (Z:.10) [1 :: Int ..])

-- See the TODO in Solve.hs: the combination of the current naive cost function and not splitting them there,
-- causes us to make 2 clusters here, with the second one consisting of two unrelated maps. Luckily, they
-- do have the same size, so it works out fine for Native :)
complex :: Acc (Vector Int) -> Acc (Vector Int)
complex xs = let as = A.map (* 2)             xs
                 bs = A.map (+ 3)             xs
                 cs = A.map (\a -> bs ! I1 a) as
                 ds = A.map (\b -> as ! I1 b) bs
              in A.zipWith (+) cs ds



