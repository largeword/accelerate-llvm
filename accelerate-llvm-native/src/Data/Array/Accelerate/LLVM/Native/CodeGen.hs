{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

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
import qualified Data.Array.Accelerate.AST.Environment as Env
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
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.IR (Operands (..), IROP (..))
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.LLVM.CodeGen.Sugar (app1)
import Data.Array.Accelerate.LLVM.CodeGen.Exp (llvmOfFun1)

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
    -- the type, code and gamma for the array-level environment
    (envTp, extractEnv, gamma) = bindEnv env
    in
    codeGenFunction uid "cluster" (LLVM.Lam (PtrPrimType envTp defaultAddrSpace) "env") $ do
      extractEnv

      -- TODO: declare the vertically fused variables
      undefined extra lhs gamma

      -- TODO: read from input buffers, making a version of 
      undefined operations gamma

      -- TODO: generate code bodies
      sequence_ $ undefined <$> operations

      -- TODO: write outputs
      undefined operations

codegenEval :: Cluster NativeOp args
            -> Args env args
            -> Gamma env
            -> CodeGen Native ()
codegenEval c = evalCluster loopheader c
  where
    -- inspect the cluster and decide what the loopy structure around this loopbody should be,
    -- i.e. the number of dimension (nested loops) and bounds
    loopheader loopbody = _ c



instance EvalOp NativeOp where
  type EvalMonad NativeOp = CodeGen Native
  type Index NativeOp = Operands Int
  type Embed' NativeOp = Operands
  type EnvF NativeOp = GroundOperand

  -- don't need to be in the monad!
  indexsh vars gamma = pure $ aprjParameters (unsafeToExpVars vars) gamma
  indexsh' vars gamma = pure $ aprjParameters vars gamma

  subtup SubTupRskip _ = OP_Unit
  subtup SubTupRkeep x = x
  subtup (SubTupRpair a b) (OP_Pair x y) = OP_Pair (subtup @NativeOp a x) (subtup @NativeOp b y)

  -- the backendarg2 is superfluous in readInput
  -- the scalartypes guarantee that there is always only one buffer. Same for the unsafeCoerce!
  writeOutput tp ~(TupRsingle buf) gamma i x = writeBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i) (op tp x)
  readInput tp ~(TupRsingle buf) gamma _ i = ir tp <$> readBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i)

  evalOp i NMap gamma (Push (Push (Push Env.Empty (BAE _ NOTHING)) (BAE (Value' x (Shape' shr sh)) NOTHING)) (BAE f NOTHING)) 
    = Push Env.Empty . FromArg . flip Value' (Shape' shr sh) <$> app1 (llvmOfFun1 @Native f gamma) x
  evalOp i NBackpermute gamma x = error "todo"
  evalOp i NGenerate gamma (Push (Push Env.Empty (BAE (Shape' shr sh) NOTHING)) (BAE f NOTHING))
    -- TODO: given linear index and total shape, compute multidimensional index. 
    -- Alternatively, change index structure to something else instead of Operands Int, to allow nested loops and thus fewer index computations
    = Push Env.Empty . FromArg . flip Value' (Shape' shr sh) <$> app1 (llvmOfFun1 @Native f gamma) (_ i sh) 
  evalOp i NPermute gamma x = _

instance TupRmonoid Operands where
  pair' = OP_Pair
  unpair' (OP_Pair x y) = (x, y)
  injL x p = OP_Pair x (proofToOp p)
  injR x p = OP_Pair (proofToOp p) x

proofToOp :: TupUnitsProof a -> Operands a
proofToOp OneUnit = OP_Unit
proofToOp (MoreUnits x y) = OP_Pair (proofToOp x) (proofToOp y)

unsafeToExpVars :: GroundVars env sh -> ExpVars env sh
unsafeToExpVars TupRunit = TupRunit
unsafeToExpVars (TupRpair l r) = TupRpair (unsafeToExpVars l) (unsafeToExpVars r)
unsafeToExpVars (TupRsingle (Var g idx)) = case g of
  GroundRbuffer _ -> error "unsafeToExpVars on a buffer"
  GroundRscalar t -> TupRsingle (Var t idx)

