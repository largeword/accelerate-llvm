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
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Data.Array.Accelerate as A
import Data.Array.Accelerate.Trafo
import Data.Array.Accelerate.Interpreter
-- import Data.Array.Accelerate.Test.NoFib
import Data.Array.Accelerate.LLVM.Native
import Data.Array.Accelerate.LLVM.Native.Operation
import Criterion.Main
import Control.Monad
import Prelude ()
import qualified Prelude as Prelude

main :: Prelude.IO ()
-- main = nofib runN
main = do
  -- Currently, SLV is broken and it removes permutes!
  -- putStrLn $ test @UniformScheduleFun @NativeKernel $ \xs ys -> A.permute @DIM2 @DIM1 @Int (+) xs (const $ Just_ $ I1 0) ys
  Prelude.putStrLn $ test @UniformScheduleFun @NativeKernel $ -- backpermute @_ @_ @Float (I2 2 10) (\(I2 x y) -> I2 y x) . backpermute (I2 10 10) (\(I2 x y) -> I2 y x)
    -- \a b -> let I2 k m = shape a 
    --             I2 _ n = shape b 
    --         in sum $ backpermute (I3 k m n) (\(I3 p q r) -> I3 p r q) $ zipWith ((*) @(Exp Float)) (replicate (I3 All_ All_ n) a) (replicate (I3 k All_ All_) b)
    futharkbadaccelerategood
  -- print $ flip linearIndexArray 0 . Prelude.fst $ runN @Native $ diagonal (use $ fromList (Z:.1024) [1 :: Int ..])
  -- print $ flip linearIndexArray 0 . Prelude.fst $ runN @Native $ diagonal' (use $ fromList (Z:.1024) [1 :: Int ..])

  -- benchmarking:
  -- defaultMain 
  --   [ --benchsize 1
  --   -- , benchsize 32
  --   -- , benchsize 64
  --   --  benchsize (1024*1024*32)      
  --   ]
  where 
    xs n = fromList (Z:.n) $ Prelude.map (`Prelude.mod` (n `div` 2)) [1 :: Int ..]
    benchsize n = bgroup (Prelude.show n)
      -- we force the result by indexing into a result array and forcing that number. 
      -- some benchmarks return two arrays, so we simply index in the first one
      -- [ env (return (xs n, flip linearIndexArray 0 . Prelude.fst . runN @Native complex    )) $ (\ ~(xs, p) -> bench "complex    " $ nf p xs) 
      -- , env (return (xs n, flip linearIndexArray 0 . Prelude.fst . runN @Native complex'   )) $ (\ ~(xs, p) -> bench "complex'   " $ nf p xs) 
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native complexAdd )) $ (\ ~(xs, p) -> bench "complexAdd " $ nf p xs) 
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native complexAdd')) $ (\ ~(xs, p) -> bench "complexAdd'" $ nf p xs)         
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native singleLoop )) $ (\ ~(xs, p) -> bench "singleLoop " $ nf p xs)         
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native singleLoop')) $ (\ ~(xs, p) -> bench "singleLoop'" $ nf p xs) 
      [ env (return (xs n, flip linearIndexArray 0 . Prelude.fst . runN @Native diagonal   )) $ (\ ~(xs, p) -> bench "diagonal   " $ nf p xs) 
      , env (return (xs n, flip linearIndexArray 0 . Prelude.fst . runN @Native diagonal'  )) $ (\ ~(xs, p) -> bench "diagonal'  " $ nf p xs) 
      ]

----------------------------BENCHMARKS------------------------------
-- complex      from the ILP example
-- complexAdd   a variation on complex, where the results are zipWith-ed together
-- singleLoop   from the introduction
-- diagonal     two maps, fused diagonally
--------------------------------------------------------------------

complex :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
complex xs = 
  let as = A.map (* 2)             xs
      bs = A.map (+ 3)             xs
      cs = A.map (\a -> bs ! I1 a) as
      ds = A.map (\b -> as ! I1 b) bs
  in T2 cs ds

complex' :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
complex' xs = 
  let as = A.map (* 2)             $ xs
      bs = A.map (+ 3)             $ barrier xs
      cs = A.map (\a -> bs ! I1 a) $ barrier as
      ds = A.map (\b -> as ! I1 b) $ barrier bs
    in T2 cs ds


complexAdd :: Acc (Vector Int) -> Acc (Vector Int)
complexAdd xs = 
  let as = A.map (* 2)             xs
      bs = A.map (+ 3)             xs
      cs = A.map (\a -> bs ! I1 a) as
      ds = A.map (\b -> as ! I1 b) bs
    in A.zipWith (+) cs ds

complexAdd' :: Acc (Vector Int) -> Acc (Vector Int)
complexAdd' xs = 
  let as = A.map (* 2)             $ xs
      bs = A.map (+ 3)             $ barrier xs
      cs = A.map (\a -> bs ! I1 a) $ barrier as
      ds = A.map (\b -> as ! I1 b) $ barrier bs
    in A.zipWith (+) cs ds

singleLoop :: Acc (Vector Int) -> Acc (Vector Int)
singleLoop as =
  let bs = A.reverse  as
      cs = A.map (+1) as
      ds = A.map (*2) cs
  in  A.zipWith3 (\b c d -> b + c + d) bs cs ds

-- mimicking delayed arrays: One cluster computing @cs@, and one with the zipWith3 that has @bs@ and @ds@ vertically fused.
singleLoop' :: Acc (Vector Int) -> Acc (Vector Int)
singleLoop' as =
  let bs = A.reverse  $ barrier $ as
      cs = A.map (+1) $ barrier $ as
      ds = A.map (*2) $ barrier $ cs
  in  A.zipWith3 (\b c d -> b + c + d) bs cs ds

-- something that showcases the use of awhileFuse, but sadly we also need something like fold to be implemented to make this work
mapWhilePositive :: Acc (Vector Int) -> Acc (Vector Int)
mapWhilePositive = awhileFuse (fold1 (A.&&) . A.map (A.> 0)) (A.map (\x -> x-1))

diagonal :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
diagonal xs = let ys = A.map (+2) xs in T2 ys (A.map (+3) ys)

diagonal' :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
diagonal' xs = let ys = A.map (+2) xs in T2 ys (A.map (+3) $ barrier ys)

futharkbadaccelerategood :: Acc (Vector Int) -> Acc (Vector Int, Vector Int)
futharkbadaccelerategood = complex . map (*4)




barrier :: Elt a => Acc (Vector a) -> Acc (Vector a)
barrier xs = generate (shape xs) (xs A.!)


--------------------------------------------------------

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


foo :: Acc (Vector Int) -> Acc (Vector Int)
foo = A.map (\(T2 a b) -> a + b) . A.map (\x -> T2 (x-1) (x+1))

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

------------------


-- new example to replace 'complex': needs to be easy, but have at least two local optima

-- example xs =
--   let as = map (+1) xs
--       bs = map (*2) xs
--   in permute (+) (\i -> i/2) as bs
