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
{-# LANGUAGE FlexibleContexts #-}
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
  -- Currently, it seems that operations with a SoA array input (i.e. a map or backpermute over an array of pairs) crash
  
  -- Currently, SLV is broken and it removes permutes!
  -- putStrLn $ test @UniformScheduleFun @NativeKernel $ \xs ys -> A.permute @DIM2 @DIM1 @Int (+) xs (const $ Just_ $ I1 0) ys
  putStrLn $ test @UniformScheduleFun @NativeKernel $ foo
  print $ run @Native $ foo (use $ fromList (Z:.10) [1 :: Int ..])

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

reverses :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
reverses xs = let
  xs' = A.reverse xs
  a   = A.zip xs xs'
  b   = A.reverse a
  (c, d) = A.unzip b
  in T2 c (A.reverse d)


foo :: Acc (Vector Int) -> Acc (Vector (Int, Int))
foo =  A.map (\x -> T2 (x-1) (x+1))

-- A version of awhile that generates more code, as we duplicate the condition, but this allows it to fuse the condition into the body
awhileFuse :: Arrays a 
           => (Acc a -> Acc (Scalar Bool))    -- ^ keep evaluating while this returns 'True'
           -> (Acc a -> Acc a)                -- ^ function to apply
           -> Acc a                           -- ^ initial value
           -> Acc a
awhileFuse c f x = asnd $ A.awhile c' f' x'
  where
    x' = T2 (c x) x
    c' (T2 cond _) = cond
    f' (T2 _ value) = let value' = f value in T2 (c value') value'
