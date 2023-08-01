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
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies #-}
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
import Prelude (Show(..), IO, )
import qualified Prelude as Prelude
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve
import Data.Array.Accelerate.Data.Bits
import Data.Array.Accelerate.Unsafe

main :: IO ()
main = do
  -- benchmarking:
  -- defaultMain $ Prelude.map benchOption [minBound :: Objective .. maxBound]

  -- problem: just combining the lists (taking True over False) as now only works if the backpermute isn't rank changing
  -- need to actually keep track of which array, which dimension, we need at which point.. stacking directions (the clean solution from paper) seems easiest tbh
  -- main problems with that approach: 1. could break bunch of stuff, 2. direction bounds get wide af
  -- Ah, alternatively: I'll just make each 'False' loopsize the right rank using the depth in bcan2: trimming the outermost loops
  -- or adding 0s on the outermost loops.
  Prelude.print $ runNWithObj @Native ArrayReadsWrites $ quicksort $ use $ fromList (Z :. 5) [100::Int, 200, 3, 5, 4]
  where
    benchOption obj = bgroup (show obj)
      [ benchProgram "diagonal " diagonal  obj
      , benchProgram "diagonal'" diagonal' obj
      , benchProgram "complex" complex obj
      , benchProgram "complex'" complex' obj
      , benchProgram "complexAdd" complexAdd obj
      , benchProgram "complexAdd'" complexAdd' obj
      , benchProgram "singleLoop" singleLoop obj
      , benchProgram "singleLoop'" singleLoop' obj
      , benchProgram "futharkbadaccelerategood" futharkbadaccelerategood obj
      , benchProgram "reverses" reverses obj
      ]
    benchProgram str pr obj = env (return $ runNWithObj @Native obj pr) $ \p -> bgroup str
      [ benchsize 32         p
      , benchsize (32*32)    p
      , benchsize (32*32*32) p
      ]
    xs n = fromList (Z:.n) $ Prelude.map (`Prelude.mod` (n `div` 2)) [1 :: Int ..]
    benchsize n p = env (return $ xs n) $ \xs -> bench (show n) $ nf p xs
      -- we force the result by indexing into a result array and forcing that number. 
      -- some benchmarks return two arrays, so we simply index in the first one
      -- [ env (return (xs n, flip linearIndexArray 0 . Prelude.fst . runN @Native complex    )) $ (\ ~(xs, p) -> bench "complex    " $ nf p xs) 
      -- , env (return (xs n, flip linearIndexArray 0 . Prelude.fst . runN @Native complex'   )) $ (\ ~(xs, p) -> bench "complex'   " $ nf p xs) 
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native complexAdd )) $ (\ ~(xs, p) -> bench "complexAdd " $ nf p xs) 
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native complexAdd')) $ (\ ~(xs, p) -> bench "complexAdd'" $ nf p xs)         
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native singleLoop )) $ (\ ~(xs, p) -> bench "singleLoop " $ nf p xs)         
      -- , env (return (xs n, flip linearIndexArray 0               . runN @Native singleLoop')) $ (\ ~(xs, p) -> bench "singleLoop'" $ nf p xs) 
      -- [ bench "diagonal   " $ nf (flip linearIndexArray 0 . Prelude.fst . p) xs) 
      -- , bench "diagonal'  " $ nf (flip linearIndexArray 0 . Prelude.fst . p) xs) 
      -- ]

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


vertical :: Acc (Vector Int) -> Acc (Vector Int)
vertical xs = let ys = A.map (+2) xs in A.map (+3) ys

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





quicksort :: Ord a => Acc (Vector a) -> Acc (Vector a)
quicksort input = result
  where
    -- Initially, we have one segment, namely the whole array
    initialFlags = scatter (fill (I1 1) 0 ++ fill (I1 1) (length input)) emptyFlags fullFlags
    emptyFlags   = fill (I1 (1 + length input)) False_
    fullFlags    = fill (I1 2) True_

    -- We stop when each segment contains just one element, as segments of
    -- one element are sorted.
    T2 result _ = awhile condition step $ T2 input initialFlags

type State a =
  ( Vector a      -- Values
  , Vector Bool   -- Head flags, denoting the starting points of the unsorted segments
  )

step :: Ord a => Acc (State a) -> Acc (State a)
step (T2 values headFlags) = (T2 values' headFlags')
  where
    -- Per element, the pivot of the segment of that element
    -- For each segment, we just take the first element as pivot
    pivots = propagateSegmentHead headFlags values

    -- Find which elements are larger than the pivot
    isLarger = zipWith (>=) values pivots

    -- Propagate the start index of a segment to all elements
    startIndex = propagateSegmentHead headFlags (generate (shape values) unindex1)

    -- Compute the offsets to which the elements must be moved using a scan
    indicesLarger, indicesSmaller :: Acc (Vector Int)
    indicesLarger  = map (\x -> x - 1) $ postscanSegHead (+) headFlags $ map (? (1, 0)) isLarger
    indicesSmaller = map (\x -> x - 1) $ postscanSegHead (+) headFlags $ map (? (0, 1)) isLarger

    -- Propagate the number of smaller elements to each segment
    -- This is needed as an offset for the larger elements
    countSmaller :: Acc (Vector Int)
    countSmaller = map (+1) $ propagateSegmentLast headFlags indicesSmaller

    -- Compute the new indices of the elements
    permutation = zipWith5 partitionPermuteIndex isLarger startIndex indicesSmaller indicesLarger countSmaller

    -- Perform the permutation
    values' = scatter permutation (fill (shape values) undef) values

    -- Update the head flags for the next iteration (the 'recursive call' in a traditional implementation)
    -- Mark new section starts at:
    --  * the position of the pivot
    --  * the position of the pivot + 1
    headFlags' =
      let
          f :: Int -> Exp Bool -> Exp Int -> Exp Int -> Exp (Maybe DIM1)
          f inc headF start countSmall =
            headF ? (Just_ (I1 $ start + countSmall + constant inc), Nothing_)

          writes :: Int -> Acc (Vector (Maybe DIM1))
          writes inc = zipWith3 (f inc) headFlags startIndex countSmaller
      in
      -- Note that (writes 1) may go out of bounds of the values array.
      -- We made the headFlags array one larger, such that this gives no problems.
      writeFlags (writes 0) $ writeFlags (writes 1) $ headFlags

-- Checks whether all segments have length 1. If that is the case, then the
-- loop may terminate.
--
condition :: Elt a => Acc (State a) -> Acc (Scalar Bool)
condition (T2 _ headFlags) = map not $ fold (&&) True_ headFlags

-- Finds the new index of an element of the list, as the result of the
-- partition
--
partitionPermuteIndex :: Exp Bool -> Exp Int -> Exp Int -> Exp Int -> Exp Int -> Exp Int
partitionPermuteIndex isLarger start indexIfSmaller indexIfLarger countSmaller =
  start + (isLarger ? (countSmaller + indexIfLarger, indexIfSmaller))

-- Given head flags, propagates the value of the head to all elements in
-- the segment
--
propagateSegmentHead
    :: Elt a
    => Acc (Vector Bool)
    -> Acc (Vector a)
    -> Acc (Vector a)
propagateSegmentHead headFlags values
  = map fst
  $ postscanl f (T2 undef True_)
  $ zip values headFlags
  where
    f left (T2 rightValue rightFlag) =
      if rightFlag
         then T2 rightValue True_
         else left

-- Given head flags, propagates the value of the head to all elements in
-- the segment
--
propagateSegmentLast
    :: Elt a
    => Acc (Vector Bool)
    -> Acc (Vector a)
    -> Acc (Vector a)
propagateSegmentLast headFlags values
  = map fst
  $ reverse
  $ postscanl f (T2 undef True_)
  $ reverse
  $ zip values
  $ tail headFlags
  where
    f (T2 leftValue leftFlag) right =
      if leftFlag
         then T2 leftValue True_
         else right

-- Segmented postscan, where the segments are defined with head flags
--
postscanSegHead
    :: Elt a
    => (Exp a -> Exp a -> Exp a)
    -> Acc (Vector Bool)
    -> Acc (Vector a)
    -> Acc (Vector a)
postscanSegHead f headFlags values
  = map fst
  $ postscanl g (T2 undef True_)
  $ zip values headFlags
  where
    g (T2 leftValue leftFlag) (T2 rightValue rightFlag)
      = T2
          (rightFlag ? (rightValue, f leftValue rightValue))
          (leftFlag .|. rightFlag)

-- Writes True to the specified indices in a flags arrays
--
writeFlags
    :: Acc (Vector (Maybe DIM1))
    -> Acc (Vector Bool)
    -> Acc (Vector Bool)
writeFlags writes flags = permute const flags (writes !) (fill (shape writes) True_)
