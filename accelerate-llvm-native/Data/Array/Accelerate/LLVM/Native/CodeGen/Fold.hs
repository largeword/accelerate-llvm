{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE RankNTypes          #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Fold
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Fold
  where

-- accelerate
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Analysis.Shape
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Type

import Data.Array.Accelerate.LLVM.Native.CodeGen.Base


import LLVM.General.AST
import LLVM.General.AST.Global

import LLVM.General.Quote.LLVM

-- standard library
import GHC.Conc


-- Reduce an array along the innermost dimension
--
mkFold
    :: forall t aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFold aenv f z a
  -- Either (1) multidimensional fold; or
  --        (2) only using one CPU, so just execute sequentially
  | numCapabilities == 1 || expDim (undefined::Exp aenv sh) > 0
  = mkFold' aenv f z a

  -- Parallel foldAll
  | otherwise
  = mkFoldAll' aenv f z a


-- Reduce an array along the innermost dimension. The innermost dimension must
-- not be empty.
--
mkFold1
    :: forall t aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFold1 aenv f a
  -- Either (1) multidimensional fold; or
  --        (2) only using one CPU, so just execute sequentially
  | numCapabilities == 1 || expDim (undefined::Exp aenv sh) > 0
  = mkFold1' aenv f a

  -- Parallel foldAll
  | otherwise
  = mkFold1All' aenv f a


-- Multidimensional reduction
-- --------------------------

-- Reduce a multidimensional array. Threads sequentially reduce along the
-- innermost dimensions, so don't need to communicate. Each thread is given a
-- range of innermost dimensions to iterate over, given by [start,end).
--
-- > fold start end = iter start (start * n)
-- >   where
-- >     iter sh sz
-- >       | sh >= end       = return ()
-- >       | otherwise       = do
-- >           let next = sz + n
-- >           writeArray out sh (reduce indexArray c z sz next)
-- >           iter (sh+1) next
--
mkFold'
    :: forall t aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFold' aenv combine seed IRDelayed{..} = do
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      arrOut                    = arrayData  (undefined::Array sh e) "out"
      paramOut                  = arrayParam (undefined::Array sh e) "out"
      intType                   = (typeOf (integralType :: IntegralType Int))
      paramStride               = [Parameter intType "ix.stride" []]

      ty_acc                    = llvmOfTupleType (eltType (undefined::e))
  seed' <- seed
  k <- [llgM|
  define void @fold (
    $params:(paramGang) ,
    $params:(paramStride),
    $params:(paramOut) ,
    $params:(paramEnv)
    ) {
      entry:
        %firstSeg = mul $type:(intType) $opr:(start), %ix.stride
        br label %for

      for:
        for $type:(intType) %sh in $opr:(start) to $opr:(end) with $type:(intType) %firstSeg as %sz {
          for.entry:
            %next = add $type:(intType) %sz, %ix.stride
            br label %reduce
          reduce:
            for $type:(intType) %j in %sz to %next with $types:(ty_acc) $oprs:(seed') as %x {
                $bbsM:("y" .=. delayedLinearIndex ("j" :: [Operand]))
                $bbsM:("z" .=. (combine ("x" :: Name) ("y" :: Name)))
                $bbsM:(execRet (return "z"))
            }
            $bbsM:(exec (writeArray arrOut "sh" ("x" :: Name)))
            ret $type:(intType) %next
        }
      end:
        ret void
    }
  |]
  return $ [Kernel k]

-- Reduce a non-empty array to a single element. Since there is no seed element
-- provided, initialise the loop accumulator with the first element of the
-- array.
--
mkFold1'
    :: forall t aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFold1' aenv combine IRDelayed{..} = do
  let
      (start, end, paramGang)   = gangParam
      paramEnv                  = envParam aenv
      arrOut                    = arrayData  (undefined::Array sh e) "out"
      paramOut                  = arrayParam (undefined::Array sh e) "out"
      paramStride               = [Parameter (typeOf (integralType :: IntegralType Int)) "ix.stride" []]

      n                         = local "ix.stride"
      ty_acc                    = llvmOfTupleType (eltType (undefined::e))
      intType                   = (typeOf (integralType :: IntegralType Int))
  k <- [llgM|
  define void @fold (
    $params:(paramGang) ,
    $params:(paramStride),
    $params:(paramOut) ,
    $params:(paramEnv)
    ) {
      entry:
        %firstSeg = mul $type:(intType) $opr:(start), $opr:(n)
        br label %for

      for:
        for $type:(intType) %sh in $opr:(start) to $opr:(end) with $type:(intType) %firstSeg as %sz {
          for.entry:
            %next = add $type:(intType) %sz, $opr:(n)
            %start = add $type:(intType) %sz, 1
          br label %nextblock
            $bbsM:("seed" .=. delayedLinearIndex ("sz" :: [Operand]))
          reduce:
            for $type:(intType) %j in %start to %next with $types:(ty_acc) %seed as %x {
                $bbsM:("y" .=. delayedLinearIndex ("j" :: [Operand]))
                $bbsM:("z" .=. (combine ("x" :: Name) ("y" :: Name)))
                $bbsM:(execRet (return "z"))
            }
            $bbsM:(exec (writeArray arrOut "sh" ("x" :: Name)))
            ret $type:(intType) %next
        }
      end:
        ret void
    }
  |]
  return $ [Kernel k]

-- Reduction to scalar
-- -------------------

-- Reduce an array to a single element, with all threads cooperating.
--
-- Since reductions consume arrays that have been fused into them, fold in a
-- multi-threaded context requires two passes. At an example, take vector
-- dot-product:
--
-- > dotp xs ys = fold (+) 0 (zipWith (*) xs ys)
--
--   1. The first pass reads in the fused array data, in this case corresponding
--   to the function (\i -> (xs!i) * (ys!i)).
--
--   2. The second pass just reads the manifest data from the first step
--   directly and reduces the array. This second step is just done by a single
--   thread.
--
mkFoldAll'
    :: forall t aenv sh e. (Shape sh, Elt e)    -- really have sh ~ Z
    => Gamma aenv
    -> IRFun2    aenv (e -> e -> e)
    -> IRExp     aenv e
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFoldAll' aenv combine seed IRDelayed{..} =
  let
      -- inputs
      (start, end, paramGang)   = gangParam
      (tid, paramId)            = gangId
      paramEnv                  = envParam aenv

      -- intermediate result of first step
      paramTmp  = arrayParam (undefined::Vector e) "tmp"
      arrTmp    = arrayData  (undefined::Vector e) "tmp"

      -- output array from final step
      paramOut  = arrayParam (undefined::Scalar e) "out"
      arrOut    = arrayData  (undefined::Scalar e) "out"

      ty_acc    = llvmOfTupleType (eltType (undefined::e))
      zero      = constOp (num int 0)

      manifestLinearIndex [i]   = readArray arrTmp i
      manifestLinearIndex _     = $internalError "makeFoldAll" "expected single expression"
  in do
  [k1] <- makeKernel "foldAll" (paramGang ++ paramTmp ++ paramOut ++ paramEnv) $ do
            r <- reduce ty_acc manifestLinearIndex combine seed start end
            writeArray arrOut zero r
            return_
  [k2] <- makeKernel "fold1" (paramGang ++ paramId ++ paramTmp ++ paramEnv) $ do
            r <- reduce1 ty_acc delayedLinearIndex combine start end
            writeArray arrTmp tid r
            return_
  return [k1,k2]


-- Reduce an array to a single element, without a starting value.
--
-- This is just the second phase of the operation, which takes the manifest
-- array of partial summations from each thread and reduces them to a single
-- value.
--
mkFold1All'
    :: forall t aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun2 aenv (e -> e -> e)
    -> IRDelayed aenv (Array (sh:.Int) e)
    -> CodeGen [Kernel t aenv (Array sh e)]
mkFold1All' aenv combine IRDelayed{..} =
  let
      -- inputs
      (start, end, paramGang)   = gangParam
      (tid, paramId)            = gangId
      paramEnv                  = envParam aenv

      -- intermediate result of first step
      paramTmp  = arrayParam (undefined::Vector e) "tmp"
      arrTmp    = arrayData  (undefined::Vector e) "tmp"

      -- output array from final step
      paramOut  = arrayParam (undefined::Scalar e) "out"
      arrOut    = arrayData  (undefined::Scalar e) "out"

      ty_acc    = llvmOfTupleType (eltType (undefined::e))
      zero      = constOp (num int 0)

      manifestLinearIndex [i]   = readArray arrTmp i
      manifestLinearIndex _     = $internalError "makeFoldAll" "expected single expression"
  in do
  [k1] <- makeKernel "foldAll" (paramGang ++ paramTmp ++ paramOut ++ paramEnv) $ do
            r <- reduce1 ty_acc manifestLinearIndex combine start end
            writeArray arrOut zero r
            return_
  [k2] <- makeKernel "fold1" (paramGang ++ paramId ++ paramTmp ++ paramEnv) $ do
            r <- reduce1 ty_acc delayedLinearIndex combine start end
            writeArray arrTmp tid r
            return_
  return [k1,k2]


-- Reduction loops
-- ---------------

-- Sequentially reduce all elements between the start and end indices, using the
-- provided seed element, combination function, and function to retrieve each
-- element.
--
-- > reduce indexArray c z start end = iter start z
-- >   where
-- >     iter i acc
-- >       | i >= end        = acc
-- >       | otherwise       = iter (i+1) (acc `c` indexArray i)
--
reduce :: [Type]                                        -- Type of the accumulator
       -> ([Operand] -> CodeGen [Operand])              -- read an element of the array
       -> ([Operand] -> [Operand] -> CodeGen [Operand]) -- combine elements
       -> CodeGen [Operand]                             -- seed
       -> Operand                                       -- starting array index
       -> Operand                                       -- final index
       -> CodeGen [Operand]                             -- reduction
reduce ty get combine seed start end = do
  z <- seed
  iterFromTo start end ty z $ \i acc -> combine acc =<< get [i]


-- Sequential reduction loop over a non-empty sequence. The condition is not
-- checked.
--
reduce1 :: [Type]
        -> ([Operand] -> CodeGen [Operand])              -- read an element of the array
        -> ([Operand] -> [Operand] -> CodeGen [Operand]) -- combine elements
        -> Operand                                       -- starting array index
        -> Operand                                       -- final index
        -> CodeGen [Operand]                             -- reduction
reduce1 ty get combine start end = do
  start' <- add int start (constOp $ num int 1)
  reduce ty get combine (get [start]) start' end

