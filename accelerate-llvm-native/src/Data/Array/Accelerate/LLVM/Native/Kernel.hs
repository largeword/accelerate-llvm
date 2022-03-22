{-# LANGUAGE GADTs             #-}
{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE TypeFamilies      #-}
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
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Backend
import Data.Array.Accelerate.Lifetime
import Data.Array.Accelerate.LLVM.Native.Operation
import Data.Array.Accelerate.LLVM.Native.Compile.Cache
import Data.ByteString.Short                                        ( ShortByteString )
import System.FilePath                                              ( FilePath, (<.>) )
import Control.DeepSeq
import Foreign.LibFFI
import Foreign.Ptr

data NativeKernel env = NativeKernel
  { kernelId       :: {-# UNPACK #-} !UID
  , kernelFunction :: !(Lifetime (FunPtr (MarshalFun (MarshalFun env))))
  }

type family MarshalArg a where
  MarshalArg (Var' e) = e
  MarshalArg (Buffer e) = Ptr e

type family MarshalFun env where
  MarshalFun () = ()
  MarshalFun (env, t) = MarshalArg t -> MarshalFun env

instance NFData' NativeKernel where
  rnf' (NativeKernel !_ fn) = unsafeGetValue fn `seq` ()

instance IsKernel NativeKernel where
  type KernelOperation NativeKernel = NativeOp

  -- compileKernel :: Cluster (KernelOperation NativeKernel) args -> Args env args -> NativeKernel env
  -- TODO: Implement compileKernel
  -- Not sure if this type is actually good.
  compileKernel = undefined
