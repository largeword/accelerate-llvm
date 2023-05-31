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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen 
-- (
--   codegen
--   ) 
  where

-- accelerate
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape (shapeType, ShapeR(..))
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Partitioned as P
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Eval
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.LiveVars
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.Compile.Cache
import Data.Array.Accelerate.LLVM.CodeGen.Environment hiding ( Empty )
import Data.Array.Accelerate.LLVM.Native.Operation
-- import Data.Array.Accelerate.LLVM.Native.CodeGen.Skeleton
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.Target
import Data.Typeable

import LLVM.AST.Type.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified LLVM.AST.Type.Function as LLVM
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.IR (Operands (..), IROP (..))
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.LLVM.CodeGen.Sugar (app1, IROpenFun2 (app2))
import Data.Array.Accelerate.LLVM.CodeGen.Exp (llvmOfFun1, intOfIndex, llvmOfFun2)
import Data.Array.Accelerate.Trafo.Desugar (ArrayDescriptor(..))
import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic ( fromJust, isJust, when, ifThenElse, nothing, just )
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
import Data.Array.Accelerate.Analysis.Match (matchShapeR)
import Data.Array.Accelerate.Trafo.Exp.Substitution (compose)
import Data.Array.Accelerate.AST.Operation (groundToExpVar)
import LLVM.AST.Type.Constant (Constant(..))
import LLVM.AST.Type.Operand (Operand(..))
import Data.Array.Accelerate.LLVM.Native.CodeGen.Permute (atomically)
import Control.Monad.State (StateT(..), lift, evalStateT, execStateT)
import qualified Data.Map as M
import Data.Array.Accelerate.AST.LeftHandSide (Exists (Exists), lhsToTupR)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Label)
import Data.Array.Accelerate.LLVM.CodeGen.Constant (undefs, constant)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP(..), BackendCluster)
import Data.Coerce (coerce)

-- TODO: add 'dimsPerIter' to backendargs, add a counter for depth to the Index type, replace imapNestFromTo with a stack of iterFromTo's 
--       that each contain two calls to evalCluster (before and after recursive loop) as well as a recursive loop.

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
        -- loopExit <- newBlock "loop.exit"
        loopBot <- newBlock "cluster.bot"
        _ <- beginBlock "cluster.init"
        extractEnv
        (acc, _, _) <- execStateT (evalCluster (toOnlyAcc c) args gamma Init) (mempty, undefined, undefined)
        -- loopBody <- beginBlock "loop.body"
        -- let acc = (mempty, loopBody)
        loopsize c gamma args $ \(shr, sh) ->
          workstealChunked shr workstealIndex workstealActiveThreads sh $ \ix i -> do
            loopTop <- beginBlock "cluster.top"
            evalStateT (loopbody (i, multidim' shr ix)) (acc, loopTop, loopBot)
            setBlock loopBot
        -- s <- get
        -- Debug.Trace.trace (show s) $ setBlock loopExit


-- inspect the cluster and decide what the loopy structure around this loopbody should be,
-- i.e. the number of dimension (nested loops) and bounds. Might need to give this access to
-- the static cluster info later, but hopefully just the 'BackendCluster' is enough.
-- For now, this simply finds an Input or Output and uses its shape. When we add backpermute, need to rethink this function.
-- This function also fails for the specific case of a vertically fused generate into permute: That cluster has no inputs nor outputs,
-- but the vertically fused away array does need to be fully computed. This gets solved automatically when we add backpermutes and pick any in-order argument

-- plan: look at all arguments that are in left2right or right2left order. Each gives a shape and shapeR.
-- These should join smoothly: The outermost sizes should match, and then just recurse. If one iteration
-- size is smaller than the other, just take the bigger one: that simply means that the smaller one is before or after the nested loop.
loopsize :: forall env args r. Cluster NativeOp args -> Gamma env -> Args env args -> (forall sh. (ShapeR sh, Operands sh) -> r) -> r
-- todo: hardcoded iteration space
loopsize (Cluster _ (Cluster' io _)) gamma args k = k (ShapeRsnoc $ ShapeRsnoc ShapeRz, OP_Pair (OP_Pair OP_Unit $ constant (TupRsingle scalarTypeInt) 2) $ constant (TupRsingle scalarTypeInt) 512) --error "TODO" -- need to do some fiddling, consider e.g. backpermute.fold where we need to do the output of the backpermute, with the inner dimension of the fold on top. Use the 'onOp' for this!
  -- where
  --   go :: ClusterIO a i o -> Args env a -> r
  --   go Empty                  ArgsNil                              = k (ShapeRz, OP_Unit)
  --   go (Input _)            (ArgArray _ (ArrayR shr _) sh _ :>: _) = k (shr, aprjParameters (unsafeToExpVars sh) gamma)
  --   go (Output{}) (ArgArray _ (ArrayR shr _) sh _ :>: _)           = k (shr, aprjParameters (unsafeToExpVars sh) gamma)
  --   go (Trivial _)          (ArgArray _ (ArrayR shr _) sh _ :>: _) = k (shr, aprjParameters (unsafeToExpVars sh) gamma)
  --   go (Vertical _ (ArrayR shr _) _) (ArgVar sh :>: _)             = k (shr, aprjParameters                  sh  gamma)
  --   go (MutPut io')           (_ :>: args') = go io' args'
  --   go (ExpPut io')           (_ :>: args') = go io' args'
  --   go (VarPut io')           (_ :>: args') = go io' args'
  --   go (FunPut io')           (_ :>: args') = go io' args'

type Accumulator = (M.Map Label (Exists Operands), Block, Block)

instance EvalOp NativeOp where
  type EvalMonad NativeOp = StateT Accumulator (CodeGen Native) -- should be a ReaderT
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

  -- the scalartypes guarantee that there is always only one buffer, and that the unsafeCoerce from (Buffers e) to (Buffer e) is safe
  writeOutput tp sh ~(TupRsingle buf) gamma (i,_) x = lift $ writeBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i) (op tp x)
  readInput :: forall e env sh. ScalarType e -> GroundVars env sh -> GroundVars env (Buffers e) -> Gamma env -> BackendClusterArg2 NativeOp env (In sh e) -> (Operands Int, [Operands Int]) -> StateT Accumulator (CodeGen Native) (Operands e)
  readInput tp sh ~(TupRsingle buf) gamma NoBP                             (i, _) = lift $ ir tp <$> readBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i)
  readInput tp sh ~(TupRsingle buf) gamma (BP shr1 (shr2 :: ShapeR sh2) f) (_,ix) = lift $ do
    sh2 <- app1 (llvmOfFun1 @Native f gamma) $ multidim shr1 ix
    let sh' = unsafeCoerce @(GroundVars env sh) @(GroundVars env sh2) sh -- "trust me", the shapeR in the BP should match the shape of the buffer
    let sh'' = aprjParameters (groundToExpVar (shapeType shr2) sh') gamma
    i <- intOfIndex shr2 sh'' sh2
    ir tp <$> readBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i)

  evalOp  :: (Operands Int, [Operands Int])
          -> Label
          -> NativeOp args
          -> Gamma env
          -> BackendArgEnv NativeOp env (InArgs args)
          -> StateT Accumulator (CodeGen Native) (Env (FromArg' NativeOp env) (OutArgs args))
  evalOp _ _ NMap gamma (Push (Push (Push Env.Empty (BAE _ _)) (BAE (Value' x (Shape' shr sh)) _)) (BAE f _))
    = lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr sh) <$> app1 (llvmOfFun1 @Native f gamma) x
  evalOp _ _ NBackpermute _ (Push (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE (Value' x _) _)) _)
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' x $ Shape' shr sh
  evalOp i _ NGenerate gamma (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE f NoBP))
    = lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr sh) <$> app1 (llvmOfFun1 @Native f gamma) (multidim shr $ snd i)
  evalOp i _ NGenerate gamma (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE f (BP shrO shrI idxTransform)))
    | Just Refl <- matchShapeR shrI shr
    = lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr sh) <$> app1 (llvmOfFun1 @Native (compose f idxTransform) gamma) (multidim shrO $ snd i)
    | otherwise = error "bp shapeR doesn't match generate's output"
  -- For Permute, we ignore all the BP info here and simply assume that there is none
  evalOp i _ NPermute gamma (Push (Push (Push (Push (Push Env.Empty
    (BAE (Value' x (Shape' shrx _))           _)) -- input
    (BAE (flip (llvmOfFun1 @Native) gamma -> f) _)) -- index function
    (BAE (ArrayDescriptor shrl shl bufl, lty)   _)) -- lock
    (BAE (ArrayDescriptor shrt sht buft, tty)   _)) -- target
    (BAE (flip (llvmOfFun2 @Native) gamma -> c) _)) -- combination function
    = lift $ do
        ix' <- app1 f (multidim shrx $ snd i)
        -- project element onto the destination array and (atomically) update
        when (isJust ix') $ do
          let ix = fromJust ix'
          let sht' = aprjParameters (unsafeToExpVars sht) gamma
          j <- intOfIndex shrt sht' ix

          atomically gamma (ArgArray Mut (ArrayR shrl lty) shl bufl) j $ do
            y <- readArray TypeInt gamma (ArgArray Mut (ArrayR shrt tty) sht buft) j
            r <- app2 c x y
            writeArray TypeInt gamma (ArgArray Mut (ArrayR shrt tty) sht buft) j r
        pure Env.Empty
  evalOp i l NScanl1 gamma (Push (Push _ (BAE (Value' x sh) _)) (BAE f' _))
    | f <- llvmOfFun2 @Native f' gamma
    , Lam (lhsToTupR -> ty) _ <- f'
    = StateT $ \(acc, _, _) -> do
        let Exists (unsafeCoerce @(Operands _) @(Operands (PrimMaybe _)) -> y) = acc M.! l
        z <- ifThenElse (maybeTy ty, isJust y) (just <$> app2 f (fromJust y) x) (pure $ just x)
        bot <- getBlock
        _ <- phi' (maybeTy ty) bot y [(nothing (undefs ty), top), (z, bot)]
        pure (Push Env.Empty $ FromArg (Value' (fromJust z) sh), (acc, _, _))
    | otherwise = error "f' not lam"
  evalOp i l NFold1 gamma args = error "todo"
  evalOp i l NFold2 gamma args = error "todo"

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


maybeTy :: TypeR a -> TypeR (PrimMaybe a)
maybeTy ty = TupRpair (TupRsingle scalarTypeWord8) (TupRpair TupRunit ty)









-- initialiseAccumulator :: Cluster NativeOp args -> CodeGen Native Accumulator
-- initialiseAccumulator (Cluster _ (Cluster' _ P.None)) = mempty
-- initialiseAccumulator (Cluster _ (Cluster' _ (Bind lhs op l ast))) = do
--   acc <- initialiseAccumulator ast
--   case op of
--     NMap         -> return acc
--     NBackpermute -> return acc
--     NGenerate    -> return acc
--     NPermute     -> return acc
--     NFold1 -> undefined
--     NFold2 -> undefined
--     NScanl1 -> 
newtype JustAccumulator a b = JA (a b)
data InitOrPhi = Init | Phi

instance EvalOp (JustAccumulator NativeOp) where
  type EvalMonad (JustAccumulator NativeOp) = StateT Accumulator (CodeGen Native) -- should be a ReaderT
  type Index (JustAccumulator NativeOp) = InitOrPhi
  type Embed' (JustAccumulator NativeOp) = TypeR
  type EnvF (JustAccumulator NativeOp) = GroundOperand

  indexsh  vars _ = pure $ mapTupR varType $ unsafeToExpVars vars
  indexsh' vars _ = pure $ mapTupR varType vars

  subtup SubTupRskip _ = TupRunit
  subtup SubTupRkeep x = x
  subtup (SubTupRpair a b) (TupRpair x y) = TupRpair (subtup @(JustAccumulator NativeOp) a x) (subtup @(JustAccumulator NativeOp) b y)
  subtup _ _ = error "subtup-pair with non-pair TypeR"

  readInput ty _ _ _ _ _ = pure $ TupRsingle ty
  writeOutput _ _ _ _ _ _ = pure ()

  evalOp Init l (JA NScanl1) _ (Push (Push _ (BAE (Value' _ sh) _)) (BAE f _))
    | Lam (lhsToTupR -> ty) _ <- f
    = StateT $ \(acc, i) -> do
        thing <- fresh ty
        pure (Push Env.Empty $ FromArg (Value' undefined sh), (M.insert l (Exists thing) acc, i))
  evalOp Init _ (JA NMap) _ (Push (Push (Push Env.Empty (BAE _ _)) (BAE (Value' x (Shape' shr sh)) _)) (BAE _ _))
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' undefined (Shape' shr sh)
  evalOp Init _ (JA NBackpermute) _ (Push (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE (Value' x _) _)) _)
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' x $ Shape' shr sh
  evalOp Init _ (JA NGenerate) _ (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE _ _))
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' undefined (Shape' shr sh)
  -- For Permute, we ignore all the BP info here and simply assume that there is none

  evalOp Phi l (JA NScanl1) _ (Push (Push _ (BAE (Value' _ sh) _)) (BAE f _))
    | Lam (lhsToTupR -> ty) _ <- f
    = StateT $ \(acc, i) -> do
        _
 
  evalOp _ _ (JA op) _ _ = undefined


instance MakesILP op => MakesILP (JustAccumulator op) where
  type BackendVar (JustAccumulator op) = BackendVar op
  type BackendArg (JustAccumulator op) = BackendArg op
  newtype BackendClusterArg (JustAccumulator op) a = BCAJA (BackendClusterArg op a)
  mkGraph (JA op) = undefined -- do not want to run the ILP solver again!
  -- probably just never running anything here

-- invariant: EnvF (JustAccumulator op) == envF op
-- uses unsafeCoerce!
instance (StaticClusterAnalysis op) => StaticClusterAnalysis (JustAccumulator op) where
  newtype BackendClusterArg2 (JustAccumulator op) x y = BCA2JA (BackendClusterArg2 op x y)
  onOp a b c d   = coerce @(BackendArgs        op _ _) @(BackendArgs        (JustAccumulator op) _ _) $ onOp (coerce a) (coerce b) (coerce c) (unsafeCoerce d)
  def      x y z = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ def x (unsafeCoerce y) (coerce z)
  valueToIn    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ valueToIn $ coerce x
  valueToOut   x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ valueToOut $ coerce x
  inToValue    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ inToValue $ coerce x
  outToValue   x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ outToValue $ coerce x
  outToSh      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ outToSh $ coerce x
  shToOut      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shToOut $ coerce x
  shToValue    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shToValue $ coerce x
  varToValue   x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ varToValue $ coerce x
  varToSh      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ varToSh $ coerce x
  shToVar      x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shToVar $ coerce x
  shrinkOrGrow x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ shrinkOrGrow $ coerce x
  addTup       x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ addTup $ coerce x
  unitToVar    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ unitToVar $ coerce x
  varToUnit    x = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ varToUnit $ coerce x

deriving instance (Eq (BackendClusterArg2 op x y)) => Eq (BackendClusterArg2 (JustAccumulator op) x y)

instance TupRmonoid TypeR where

toOnlyAcc :: Cluster op args -> Cluster (JustAccumulator op) args
toOnlyAcc (Cluster bc (Cluster' io ast)) = Cluster (go2 bc) (Cluster' io $ go ast)
  where
    go :: ClusterAST op env args' -> ClusterAST (JustAccumulator op) env args'
    go P.None = P.None
    go (Bind lhs op l ast') = Bind lhs (JA op) l (go ast')
    go2 :: BackendCluster op args -> BackendCluster (JustAccumulator op) args
    go2 ArgsNil = ArgsNil
    go2 (bca :>: args) = BCAJA bca :>: go2 args
