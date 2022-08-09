{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

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
import Data.Array.Accelerate.Representation.Shape (empty, shapeType, ShapeR(..))
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
import Data.Array.Accelerate.LLVM.CodeGen.Sugar (app1, IRBuffer (IRBuffer), IROpenFun2 (app2))
import Data.Array.Accelerate.LLVM.CodeGen.Exp (llvmOfFun1, intOfIndex, llvmOfFun2)
import Data.Array.Accelerate.Trafo.Desugar (ArrayDescriptor(..))
import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic (ifThenElse, isJust, when, fromJust, eq)
import LLVM.AST.Type.Name
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.Constant (constant)
import Data.Array.Accelerate.Analysis.Match (matchShapeR)
import Data.Array.Accelerate.Trafo.Exp.Substitution (compose)
import Data.Array.Accelerate.Array.Buffer (readBuffers)
import LLVM.Internal.FFI.LLVMCTypes (libFunc__printf)
import Data.Array.Accelerate.AST.Operation (groundToExpVar)
import qualified Debug.Trace

-- TODO: this is still singlethreaded
-- TODO: add 'dimsPerIter' to backendargs, add a counter for depth to the Index type, replace imapNestFromTo with a stack of iterFromTo's 
--       that each contain two calls to evalCluster (before and after recursive loop) as well as a recursive loop (with the obvious base case).
codegen :: UID
            -> Env AccessGroundR env
            -> Cluster NativeOp args
            -> Args env args
            -> LLVM Native (Module (KernelType env))
codegen uid env c args = loopheader $ evalCluster c args gamma
  where
    (argTp, extractEnv, workstealIndex, workstealActiveThreads, gamma) = bindHeaderEnv env
    loopheader loopbody = codeGenFunction uid "name_of_a_fused_cluster" (LLVM.Lam argTp "arg") $
      do
        extractEnv
        loopsize c gamma args $ \(shr, sh) ->
          workstealChunked shr workstealIndex workstealActiveThreads sh $ \ix i -> loopbody (i, multidim' shr ix)

-- inspect the cluster and decide what the loopy structure around this loopbody should be,
-- i.e. the number of dimension (nested loops) and bounds. Might need to give this access to
-- the static cluster info later, but hopefully just the 'BackendCluster' is enough.
-- For now, this simply finds an Input or Output and uses its shape. When we add backpermute, need to rethink this function.
-- This function also fails for the specific case of a vertically fused generate into permute: That cluster has no inputs nor outputs,
-- but the vertically fused away array does need to be fully computed. This gets solved automatically when we add backpermutes and pick any in-order argument
loopsize :: forall env args r. Cluster NativeOp args -> Gamma env -> Args env args -> (forall sh. (ShapeR sh, Operands sh) -> r) -> r
loopsize (Cluster _ (Cluster' io _)) gamma args k = go io args
  where
    go :: ClusterIO a i o -> Args env a -> r
    go Empty                  ArgsNil                              = k (ShapeRz, OP_Unit)
    go (Input _)            (ArgArray _ (ArrayR shr _) sh _ :>: _) = k (shr, aprjParameters (unsafeToExpVars sh) gamma)
    go (Output{}) (ArgArray _ (ArrayR shr _) sh _ :>: _)           = k (shr, aprjParameters (unsafeToExpVars sh) gamma)
    go (Trivial _)          (ArgArray _ (ArrayR shr _) sh _ :>: _) = k (shr, aprjParameters (unsafeToExpVars sh) gamma)
    go (Vertical _ (ArrayR shr _) _) (ArgVar sh :>: _)             = k (shr, aprjParameters                  sh  gamma)
    go (MutPut io')           (_ :>: args') = go io' args'
    go (ExpPut io')           (_ :>: args') = go io' args'
    go (VarPut io')           (_ :>: args') = go io' args'
    go (FunPut io')           (_ :>: args') = go io' args'


instance EvalOp NativeOp where
  type EvalMonad NativeOp = CodeGen Native
  -- linear and multidim index. The latter has 'trust me, this is the right shape' levels of type safety, but trust me. It is the right shape.
  type Index NativeOp = (Operands Int, [Operands Int])
  type Embed' NativeOp = Operands
  type EnvF NativeOp = GroundOperand

  -- don't need to be in the monad!
  indexsh vars gamma = pure $ aprjParameters (unsafeToExpVars vars) gamma
  indexsh' vars gamma = pure $ aprjParameters vars gamma

  subtup SubTupRskip _ = OP_Unit
  subtup SubTupRkeep x = x
  subtup (SubTupRpair a b) (OP_Pair x y) = OP_Pair (subtup @NativeOp a x) (subtup @NativeOp b y)

  -- the scalartypes guarantee that there is always only one buffer. Same for the unsafeCoerce from (Buffers e) to (Buffer e)
  writeOutput tp sh ~(TupRsingle buf) gamma (i,_) x = writeBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i) (op tp x)
  readInput :: forall e env sh. ScalarType e -> GroundVars env sh -> GroundVars env (Buffers e) -> Gamma env -> BackendClusterArg2 NativeOp env (In sh e) -> (Operands Int, [Operands Int]) -> CodeGen Native (Operands e)
  readInput tp sh ~(TupRsingle buf) gamma NoBP                             (i, _) = ir tp <$> readBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i)
  readInput tp sh ~(TupRsingle buf) gamma (BP shr1 (shr2 :: ShapeR sh2) f) (_,ix) = do
    sh2 <- app1 (llvmOfFun1 @Native f gamma) $ multidim shr1 ix
    let sh' = unsafeCoerce @(GroundVars env sh) @(GroundVars env sh2) sh -- "trust me", the shapeR in the BP should match the shape of the buffer
    let sh'' = aprjParameters (groundToExpVar (shapeType shr2) sh') gamma
    i <- intOfIndex shr2 sh'' sh2
    ir tp <$> readBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i)

  evalOp _ NMap gamma (Push (Push (Push Env.Empty (BAE _ _)) (BAE (Value' x (Shape' shr sh)) _)) (BAE f _))
    = Push Env.Empty . FromArg . flip Value' (Shape' shr sh) <$> app1 (llvmOfFun1 @Native f gamma) x
  evalOp _ NBackpermute gamma (Push (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE (Value' x _) _)) _)
    = pure $ Push Env.Empty $ FromArg $ Value' x $ Shape' shr sh
  evalOp i NGenerate gamma (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE f NoBP))
    = Push Env.Empty . FromArg . flip Value' (Shape' shr sh) <$> app1 (llvmOfFun1 @Native f gamma) (multidim shr $ snd i)
  evalOp i NGenerate gamma (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE f (BP shrO shrI idxTransform)))
    | Just Refl <- matchShapeR shrI shr
    = Push Env.Empty . FromArg . flip Value' (Shape' shr sh) <$> app1 (llvmOfFun1 @Native (compose f idxTransform) gamma) (multidim shrO $ snd i)
    | otherwise = error "bp shapeR doesn't match generate's output"
  -- For Permute, we ignore all the BP info here and simply assume that there is none
  evalOp i NPermute gamma (Push (Push (Push (Push (Push Env.Empty
    (BAE (Value' x (Shape' shrx shx))           _)) -- input
    (BAE (flip (llvmOfFun1 @Native) gamma -> f) _)) -- index function
    (BAE (ArrayDescriptor shrl shl bufl, lty)   _)) -- lock
    (BAE (ArrayDescriptor shrt sht buft, tty)   _)) -- target
    (BAE (flip (llvmOfFun2 @Native) gamma -> c) _)) -- combination function
    = do
        ix' <- app1 f (multidim shrx $ snd i)
        -- project element onto the destination array and (atomically) update
        -- when (isJust ix') $ do
        do
          ix <- fromJust ix'
          let sht' = aprjParameters (unsafeToExpVars sht) gamma
          j <- intOfIndex shrt sht' ix

          -- atomically gamma (ArgArray Mut (ArrayR shrl lty) shl bufl) j $ do
          do
            y <- readArray TypeInt gamma (ArgArray Mut (ArrayR shrt tty) sht buft) j
            r <- app2 c x y
            writeArray TypeInt gamma (ArgArray Mut (ArrayR shrt tty) sht buft) j r
        return Env.Empty
  evalOp i NScanl1 gamma args = error "todo" -- need to switch the 'imapNestFromTo' to something else

multidim :: ShapeR sh -> [Operands Int] -> Operands sh
multidim ShapeRz [] = OP_Unit
multidim (ShapeRsnoc shr) (i:is) = OP_Pair (multidim shr is) i
multidim _ _ = error "shouldn't have trusted me"

multidim' :: ShapeR sh -> Operands sh -> [Operands Int]
multidim' ShapeRz OP_Unit = []
multidim' (ShapeRsnoc shr) (OP_Pair sh i) = i : multidim' shr sh

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


