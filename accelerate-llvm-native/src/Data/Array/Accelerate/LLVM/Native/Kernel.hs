{-# LANGUAGE GADTs             #-}
{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Accelerate
-- Copyright   : [2014..2022] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Kernel (
  NativeKernel(..)
) where

-- accelerate

import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Backend
import Data.Array.Accelerate.Lifetime
import Data.Array.Accelerate.LLVM.Native.Operation
import Data.Array.Accelerate.LLVM.Native.Compile.Cache
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Base
import LLVM.AST.Type.Function
import Data.ByteString.Short                                        ( ShortByteString )
import System.FilePath                                              ( FilePath, (<.>) )
import Control.DeepSeq
import Data.Typeable
import Foreign.LibFFI
import Foreign.Ptr

data NativeKernel env where
  NativeKernel
    :: Result f ~ ()
    => { kernelId       :: {-# UNPACK #-} !UID
       , kernelFunction :: !(Lifetime (FunPtr f))
       , kernelSize     :: !(KernelSize sh env f)
       }
    -> NativeKernel env

data KernelSize sh env f where
  -- Kernels are started with an inclusive lower and exclusive upper bound
  KernelSizeDynamic
    :: ShapeR sh
    -> ExpVars env sh
    -> KernelSize sh env (MarshalScalars sh (MarshalScalars sh (MarshalFun env)))

  -- Kernels are started with ids within the range 0 (inclusive) to n (exclusive)
  KernelSizeIds
    :: ExpVar env Int -- n
    -> KernelSize sh env (Int -> MarshalFun env)

instance NFData (KernelSize sh env f) where
  rnf (KernelSizeDynamic shr vars) = rnfShapeR shr `seq` rnfVars rnfScalarType vars
  rnf (KernelSizeIds var)          = rnfVar rnfScalarType var

instance NFData' NativeKernel where
  rnf' (NativeKernel !_ fn sz) = unsafeGetValue fn `seq` rnf sz

instance IsKernel NativeKernel where
  type KernelOperation NativeKernel = NativeOp

  -- compileKernel :: Env AccessGroundR env -> Cluster (KernelOperation NativeKernel) args -> Args env args -> NativeKernel env
  -- TODO: Implement compileKernel
  -- Not sure if this type is actually good.
  compileKernel = undefined
