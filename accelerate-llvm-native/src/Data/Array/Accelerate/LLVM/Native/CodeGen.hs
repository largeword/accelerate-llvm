{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen (
  codegen
) where

-- accelerate
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Eval
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.LiveVars
import Data.Array.Accelerate.Error

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.Compile.Cache
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment hiding ( Empty )
import Data.Array.Accelerate.LLVM.Native.Operation
-- import Data.Array.Accelerate.LLVM.Native.CodeGen.Skeleton
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.CodeGen.Fold
import Data.Array.Accelerate.LLVM.Native.CodeGen.FoldSeg
import Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
import Data.Array.Accelerate.LLVM.Native.CodeGen.Map
import Data.Array.Accelerate.LLVM.Native.CodeGen.Permute
import Data.Array.Accelerate.LLVM.Native.CodeGen.Scan
import Data.Array.Accelerate.LLVM.Native.CodeGen.Stencil
import Data.Array.Accelerate.LLVM.Native.CodeGen.Transform
import Data.Array.Accelerate.LLVM.Native.Target
import Control.DeepSeq
import Data.Typeable

import LLVM.AST.Type.Representation
import LLVM.AST.Type.Module
import LLVM.AST.Type.Function
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import LLVM.AST.Type.AddrSpace (defaultAddrSpace)

codegen :: UID -> Env AccessGroundR env -> Cluster NativeOp args -> Args env args -> LLVM Native (Module (KernelType env))
codegen uid env cluster args = case clusterOperations cluster args of
  ClusterOperations _ lhs [ApplyOperation operation args]
    | Just Refl <- leftHandSideIsVoid lhs
    , NGenerate <- operation
    , argF :>: argOut@(ArgArray _ (ArrayR shr _) sh _) :>: ArgsNil <- args
    -> mkGenerate uid "generate" env argOut argF
    | otherwise
    -> internalError "Cannot compile this operation yet"
  _ -> internalError "Cannot compile this kernel yet"

codegenN :: UID -> Env AccessGroundR env -> Cluster NativeOp args -> Args env args -> LLVM Native (Module (KernelType env))
codegenN uid env cluster args = case clusterOperations cluster args of
  ClusterOperations extra lhs operations -> let
    (envTp, extractEnv, gamma) = bindEnv env
    in
    codeGenFunction uid "cluster" (LLVM.Lam (PtrPrimType envTp defaultAddrSpace) "env") $ do
      extractEnv
      undefined
