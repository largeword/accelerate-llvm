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
  NativeKernel(..),
  NativeKernelMetadata(..),
  KernelType
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
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Lifetime
import Data.Array.Accelerate.Pretty.Schedule

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.Native.State
import Data.Array.Accelerate.LLVM.Native.Operation
import Data.Array.Accelerate.LLVM.Native.Compile.Cache
import Data.Array.Accelerate.LLVM.Native.CodeGen
import Data.Array.Accelerate.LLVM.Native.Compile
import Data.Array.Accelerate.LLVM.Native.Link
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.Execute.Marshal
import qualified LLVM.AST                                           as LLVM
import LLVM.AST.Type.Function
import Data.ByteString.Short                                        ( ShortByteString )
import System.FilePath                                              ( FilePath, (<.>) )
import System.IO.Unsafe
import Control.DeepSeq
import Data.Typeable
import Foreign.LibFFI
import Foreign.Ptr
import Prettyprinter
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Representation

data NativeKernel env where
  NativeKernel
    :: { kernelId       :: {-# UNPACK #-} !UID
       , kernelFunction :: !(Lifetime (FunPtr (KernelType env)))
       }
    -> NativeKernel env

instance NFData' NativeKernel where
  rnf' (NativeKernel !_ fn) = unsafeGetValue fn `seq` ()

newtype NativeKernelMetadata f =
  NativeKernelMetadata { kernelArgsSize :: Int }

instance NFData' NativeKernelMetadata where
  rnf' (NativeKernelMetadata sz) = rnf sz

instance IsKernel NativeKernel where
  type KernelOperation NativeKernel = NativeOp
  type KernelMetadata  NativeKernel = NativeKernelMetadata

  compileKernel env cluster args = unsafePerformIO $ evalLLVM defaultTarget $ do
    module' <- codegen uid env cluster args
    obj <- compile uid module'
    funPtr <- link obj
    return $ NativeKernel uid funPtr
    where
      uid = hashOperation cluster args

  kernelMetadata kernel = NativeKernelMetadata $ sizeOfEnv kernel

instance PrettyKernel NativeKernel where
  prettyKernel = PrettyKernelFun go
    where
      go :: OpenKernelFun NativeKernel env t -> Adoc
      go (KernelFunLam _ f) = go f
      go (KernelFunBody kernel) = viaShow $ kernelId kernel
