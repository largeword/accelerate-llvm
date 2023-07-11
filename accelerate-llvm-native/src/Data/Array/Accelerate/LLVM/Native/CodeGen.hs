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
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}

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
import Data.Array.Accelerate.Representation.Shape (shapeType, ShapeR(..), rank)
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
import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic ( when, ifThenElse, just, add, lt, mul, eq, fromJust, isJust )
import Data.Array.Accelerate.Analysis.Match (matchShapeR)
import Data.Array.Accelerate.Trafo.Exp.Substitution (compose)
import Data.Array.Accelerate.AST.Operation (groundToExpVar)
import Data.Array.Accelerate.LLVM.Native.CodeGen.Permute (atomically)
import Control.Monad.State (StateT(..), lift, evalStateT, execStateT)
import qualified Data.Map as M
import Data.Array.Accelerate.AST.LeftHandSide (Exists (Exists), lhsToTupR)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Label)
import Data.Array.Accelerate.LLVM.CodeGen.Constant (constant, boolean)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP(..), BackendCluster)
import Data.Coerce (coerce)
import Data.Functor.Compose
import qualified Control.Monad as Prelude
import Data.Bifunctor (Bifunctor(..))
import Data.Array.Accelerate.LLVM.CodeGen.Loop (iter, while)
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
import qualified Debug.Trace




codegen :: UID
        -> Env AccessGroundR env
        -> Cluster NativeOp args
        -> Args env args
        -> LLVM Native (Module (KernelType env))
codegen uid env c@(Cluster _ (Cluster' cIO cAST)) args = 
  codeGenFunction uid "fused_cluster_name" (LLVM.Lam argTp "arg") $ do
    extractEnv
    workstealLoop workstealIndex workstealActiveThreads (op scalarTypeInt32 $ constant (TupRsingle scalarTypeInt32) 3) $ \_ -> do
      acc <- execStateT (evalCluster (toOnlyAcc c) args gamma ()) mempty
      body acc
      retval_ $ boolean True
    where
      (argTp, extractEnv, workstealIndex, workstealActiveThreads, gamma) = bindHeaderEnv env
      body :: Accumulated -> CodeGen Native ()
      body initialAcc = loopsize c gamma args $ \(shr', flipShape shr' -> sh') ->
        let go :: ShapeR sh -> Operands sh -> (Int, Operands Int, [Operands Int]) -> StateT Accumulated (CodeGen Native) ()
            go ShapeRz OP_Unit _ = pure ()
            go (ShapeRsnoc shr) (OP_Pair sh sz) ix = iter' sz ix $ \i@(d,lin,is) -> do
              recurLin <- lift $ mul numType lin (firstOrZero shr sh)
              go shr sh (d+1, recurLin, is)
              let ba = makeBackendArg @NativeOp args gamma c
              newInputs <- evalI @NativeOp i cIO args ba gamma
              outputs <- evalAST @NativeOp i cAST gamma newInputs
              evalO @NativeOp i cIO args gamma outputs
        in case (shr', sh') of
          -- (ShapeRz,_) -> error "tiny cluster"
          -- (ShapeRsnoc shr', OP_Pair sh' sz) -> 
          (shr', sh') ->
            evalStateT (go shr' sh' (1, constant typerInt 0, [])) initialAcc
      iter' :: Operands Int
            -> (Int, Operands Int, [Operands Int])
            -> ((Int, Operands Int, [Operands Int]) -> StateT Accumulated (CodeGen Native) ()) -> StateT Accumulated (CodeGen Native) ()
      iter' size (d, linearI, outerI) body = StateT $ \accMap ->
        operandsMapToPairs accMap $ \(accR, toR, fromR) ->
          ((),) . fromR <$> iter
                              (TupRpair typerInt typerInt)
                              accR
                              (OP_Pair (constant typerInt 0) linearI)
                              (toR accMap)
                              (\(OP_Pair i _) -> lt singleType i size)
                              (\(OP_Pair i l) -> OP_Pair <$> add numType (constant typerInt 1) i <*> add numType (constant typerInt 1) l)
                              (\(OP_Pair i l) -> fmap (toR . snd) . runStateT (body (d, l, i:outerI)) . fromR)

-- We use some unsafe coerces in the context of the accumulators. 
-- Some, in this function, are very local. Others, like in evalOp, 
-- just deal with the assumption that the specific operand stored at index l indeed belongs to operation l.
operandsMapToPairs
  :: Accumulated
  -> (forall accR. ( TypeR accR
     , Accumulated -> Operands accR
     , Operands accR -> Accumulated) -> r)
  -> r
operandsMapToPairs acc k
  = case existentialStuff of
    (Exists accR, toR, fromR) -> k ( accR
                                   , unsafeUnExists . toR . map (fst.snd) . M.toList
                                   , M.fromList . zip labels . fromR . Exists)
  where
  (labels, (_, existentialStuff)) = second (second (foldr
      (\(Exists newR) (Exists accR, toR, fromR) ->
        ( Exists (TupRpair newR accR)
        , \(Exists this : rest') -> case toR rest' of Exists rest -> Exists $ OP_Pair this rest
        , \(Exists hastobepair) -> case unsafeCoerce hastobepair of OP_Pair this rest -> (Exists this, Exists newR) : fromR (Exists rest)))
      (   Exists TupRunit
        , \[] -> Exists OP_Unit
        , const [])) -- should always get "Exists OP_Unit" as argument
    . unzip)
    . unzip
    $ M.toList acc
  unsafeUnExists :: Exists f -> f a
  unsafeUnExists (Exists fa) = unsafeCoerce fa

-- type family ShapeMinus big small where
--   ShapeMinus sh () = sh
--   ShapeMinus (sh, Int) (sh', Int) = ShapeMinus sh sh'

firstOrZero :: ShapeR sh -> Operands sh -> Operands Int
firstOrZero ShapeRz _ = constant typerInt 0
firstOrZero ShapeRsnoc{} (OP_Pair _ i) = i

type family ShapePlus a b where
  ShapePlus sh () = sh
  ShapePlus sh (sh', Int) = ShapePlus (sh, Int) sh'

flipShape :: forall sh. ShapeR sh -> Operands sh -> Operands sh
flipShape shr sh = go shr sh OP_Unit
  where
    go :: ShapeR sh' -> Operands sh' -> Operands sh'' -> Operands (ShapePlus sh' sh'')
    go ShapeRz OP_Unit sh = unsafeCoerce sh
    go (ShapeRsnoc shr) (OP_Pair sh i) sh' = go shr sh (OP_Pair sh' i)

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
loopsize (Cluster _ (Cluster' io _)) gamma = go io
  -- k (ShapeRsnoc $ ShapeRsnoc ShapeRz, OP_Pair (OP_Pair OP_Unit $ constant typerInt 16) $ constant typerInt 16) 
  --error "TODO" 
  -- need to do some fiddling, consider e.g. backpermute.fold where we need to do the output of the backpermute,
  -- with the inner dimension of the fold on top. Use the 'onOp' for this!
  where
    go :: ClusterIO a i o -> Args env a -> (forall sh. (ShapeR sh, Operands sh) -> r) -> r
    go Empty ArgsNil k = k (ShapeRz, OP_Unit)
    go (Input io')                     (ArgArray _ (ArrayR shr _) sh _ :>: args') k = go io' args' $ \x -> combine x (shr, aprjParameters (unsafeToExpVars sh) gamma) k
    go (Output _ _ _ io')              (ArgArray _ (ArrayR shr _) sh _ :>: args') k = go io' args' $ \x -> combine x (shr, aprjParameters (unsafeToExpVars sh) gamma) k
    go (Trivial io')                   (ArgArray _ (ArrayR shr _) sh _ :>: args') k = go io' args' $ \x -> combine x (shr, aprjParameters (unsafeToExpVars sh) gamma) k
    go (Vertical _ (ArrayR shr _) io') (ArgVar sh                      :>: args') k = go io' args' $ \x -> combine x (shr, aprjParameters                  sh  gamma) k
    go (MutPut io')                    (_                              :>: args') k = go io' args' k
    go (ExpPut io')                    (_                              :>: args') k = go io' args' k
    go (VarPut io')                    (_                              :>: args') k = go io' args' k
    go (FunPut io')                    (_                              :>: args') k = go io' args' k

    combine :: (ShapeR sh1, Operands sh1) -> (ShapeR sh2, Operands sh2) -> (forall sh. (ShapeR sh, Operands sh) -> r) -> r
    combine x y k = combine' x y k k
    combine' :: (ShapeR sh1, Operands sh1) -> (ShapeR sh2, Operands sh2) -> (forall sh. (ShapeR sh, Operands sh) -> r) -> (forall sh. (ShapeR sh, Operands sh) -> r) -> r
    combine' (ShapeRz,_) sh2 kl kr = kr sh2
    combine' sh1 (ShapeRz,_) kl kr = kl sh1
    combine' (ShapeRsnoc shr1, OP_Pair sh1 n1) (ShapeRsnoc shr2, OP_Pair sh2 n2) kl kr =
      combine' (shr1, sh1) (shr2, sh2) 
        (\(shr,sh) -> kl (ShapeRsnoc shr, OP_Pair sh n1))
        (\(shr,sh) -> kr (ShapeRsnoc shr, OP_Pair sh n2))


type Accumulated = M.Map Label (Exists Operands, Exists TypeR)
-- type Accumulator = (Accumulated, Block, Block)

instance EvalOp NativeOp where
  type EvalMonad NativeOp = StateT Accumulated (CodeGen Native) -- should be a ReaderT
  -- dimension and linear and multidim index. The last has 'trust me, this is the right shape' levels of type safety, but trust me. It is the right shape.
  type Index NativeOp = (Int, Operands Int, [Operands Int])
  type Embed' NativeOp = Compose Maybe Operands
  type EnvF NativeOp = GroundOperand

  -- don't need to be in the monad!
  indexsh vars gamma = pure . CJ $ aprjParameters (unsafeToExpVars vars) gamma
  indexsh' vars gamma = pure . CJ $ aprjParameters vars gamma

  subtup _ CN = CN
  subtup SubTupRskip (CJ _) = CJ OP_Unit
  subtup SubTupRkeep (CJ x) = CJ x
  subtup (SubTupRpair a b) (CJ (OP_Pair x y)) = CJ $ OP_Pair ((\(CJ z)->z) $ subtup @NativeOp a $ CJ x) ((\(CJ z)->z) $ subtup @NativeOp b $ CJ y)

  -- the scalartypes guarantee that there is always only one buffer, and that the unsafeCoerce from (Buffers e) to (Buffer e) is safe
  writeOutput tp sh ~(TupRsingle buf) gamma (d,i,_) = \case
    CN -> pure ()
    CJ x -> lift $ Prelude.when (sh `isAtDepth` d) $ writeBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i) (op tp x)
  readInput :: forall e env sh. ScalarType e -> GroundVars env sh -> GroundVars env (Buffers e) -> Gamma env -> BackendClusterArg2 NativeOp env (In sh e) -> (Int, Operands Int, [Operands Int]) -> StateT Accumulated (CodeGen Native) (Compose Maybe Operands e)
  readInput _ sh _ gamma _ (d,_,_) | not $ sh `isAtDepth` d = pure CN
  readInput _ _ _ _ (BCAN2 _ d) (d',_,_) | d /= d = pure CN
  readInput tp sh ~(TupRsingle buf) gamma (BCAN2 Nothing _)                                 (d,i, _) =
    lift $ CJ . ir tp <$> readBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i)
  readInput tp sh ~(TupRsingle buf) gamma (BCAN2 (Just (BP shr1 (shr2 :: ShapeR sh2) f)) _) (d,_,ix) =
    lift $ CJ . ir tp <$> do
      sh2 <- app1 (llvmOfFun1 @Native f gamma) $ multidim shr1 ix
      let sh' = unsafeCoerce @(GroundVars env sh) @(GroundVars env sh2) sh -- "trust me", the shapeR in the BP should match the shape of the buffer
      let sh'' = aprjParameters (groundToExpVar (shapeType shr2) sh') gamma
      i <- intOfIndex shr2 sh'' sh2
      readBuffer tp TypeInt (aprjBuffer (unsafeCoerce buf) gamma) (op TypeInt i)

  evalOp  :: (Int, Operands Int, [Operands Int])
          -> Label
          -> NativeOp args
          -> Gamma env
          -> BackendArgEnv NativeOp env (InArgs args)
          -> StateT Accumulated (CodeGen Native) (Env (FromArg' NativeOp env) (OutArgs args))
  -- evalOp _ _ _ _ _ = error "todo: add depth checks to all matches"
  evalOp (d,_,_) _ NMap gamma (Push (Push (Push Env.Empty (BAE _ _)) (BAE (Value' x' (Shape' shr sh)) (BCAN2 _ d'))) (BAE f _))
    = lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr sh) <$> case x' of
      CJ x | d == d' -> CJ <$> app1 (llvmOfFun1 @Native f gamma) x
      _   -> pure CN
  evalOp _ _ NBackpermute _ (Push (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE (Value' x _) _)) _)
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' x $ Shape' shr sh
  evalOp (d',_,is) _ NGenerate gamma (Push (Push Env.Empty (BAE (Shape' shr ~(CJ sh)) _)) (BAE f (BCAN2 Nothing d)))
    | shr `isAtDepth'` d = lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr (CJ sh)) . CJ <$> app1 (llvmOfFun1 @Native f gamma) (multidim shr is)
    | d' == d = error "how come we didn't hit the case above?"
    | otherwise        = pure $ Push Env.Empty $ FromArg $ Value' CN (Shape' shr (CJ sh))
  evalOp (d',_,is) _ NGenerate gamma (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE f (BCAN2 (Just (BP shrO shrI idxTransform)) d)))
    | not $ shr `isAtDepth'` d
    = pure $ Push Env.Empty $ FromArg $ flip Value' (Shape' shr sh) CN
    | d' /= d = error "huh"
    | Just Refl <- matchShapeR shrI shr
    = lift $ Push Env.Empty . FromArg . flip Value' (Shape' shr sh) . CJ <$> app1 (llvmOfFun1 @Native (compose f idxTransform) gamma) (multidim shrO is)
    | otherwise = error "bp shapeR doesn't match generate's output"
  -- For Permute, we ignore all the BP info here and simply assume that there is none
  evalOp (d',_,is) _ NPermute gamma (Push (Push (Push (Push (Push Env.Empty
    (BAE (Value' x' (Shape' shrx _))           (BCAN2 _ d))) -- input
    (BAE (flip (llvmOfFun1 @Native) gamma -> f) _)) -- index function
    (BAE (ArrayDescriptor shrl shl bufl, lty)   _)) -- lock
    (BAE (ArrayDescriptor shrt sht buft, tty)   _)) -- target
    (BAE (flip (llvmOfFun2 @Native) gamma -> c) _)) -- combination function
    | CJ x <- x'
    = lift $ do
        ix' <- app1 f (multidim shrx is)
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
    | d == d' = error "case above?"
    | otherwise = pure Env.Empty
  evalOp (d',_,~(inner:_)) l NScanl1 gamma (Push (Push _ (BAE (Value' x' sh) (BCAN2 Nothing d))) (BAE f' _))
    | f <- llvmOfFun2 @Native f' gamma
    , Lam (lhsToTupR -> ty :: TypeR e) _ <- f'
    , CJ x <- x'
    , d == d'
    = StateT $ \acc -> do
        let (Exists (unsafeCoerce @(Operands _) @(Operands e) -> accX), eTy) = acc M.! l
        z <- ifThenElse (ty, eq singleType inner (constant typerInt 0)) (pure x) (app2 f accX x) -- note: need to apply the accumulator as the _left_ argument to the function
        pure (Push Env.Empty $ FromArg (Value' (CJ z) sh), M.adjust (const (Exists z, eTy)) l acc)
    | otherwise = pure $ Push Env.Empty $ FromArg (Value' CN sh)
  evalOp _ _ NScanl1 gamma (Push (Push _ (BAE (Value' x' sh) (BCAN2 (Just (BP{})) d))) (BAE f' _)) = error "backpermuted scan"
  evalOp i l NFold1 gamma args = error "todo: fold1"
  evalOp (d',_,~(inner:_)) l NFold2 gamma (Push (Push _ (BAE (Value' x' sh@(Shape' (ShapeRsnoc shr') ~(CJ (OP_Pair sh' _)))) (BCAN2 Nothing d))) (BAE f' _))
    | f <- llvmOfFun2 @Native f' gamma
    , Lam (lhsToTupR -> ty :: TypeR e) _ <- f'
    , CJ x <- x'
    , d == d'
    = StateT $ \acc -> do
        let (Exists (unsafeCoerce @(Operands _) @(Operands e) -> accX), eTy) = acc M.! l
        z <- ifThenElse (ty, eq singleType inner (constant typerInt 0)) (pure x) (app2 f accX x) -- note: need to apply the accumulator as the _left_ argument to the function
        pure (Push Env.Empty $ FromArg (Value' (CJ z) (Shape' shr' (CJ sh'))), M.adjust (const (Exists z, eTy)) l acc)
    | f <- llvmOfFun2 @Native f' gamma
    , Lam (lhsToTupR -> ty :: TypeR e) _ <- f'
    , d == d'+1 -- the fold was in the iteration above; we grab the result from the accumulator now
    = StateT $ \acc -> do
        let (Exists (unsafeCoerce @(Operands _) @(Operands e) -> x), _) = acc M.! l
        pure (Push Env.Empty $ FromArg (Value' (CJ x) (Shape' shr' (CJ sh'))), acc)
    | otherwise = pure $ Push Env.Empty $ FromArg (Value' CN (Shape' shr' (CJ sh')))
  evalOp _ _ NFold2 _ _ = error "backpermuted fold1"

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

instance (TupRmonoid f) => TupRmonoid (Compose Maybe f) where
  pair' (Compose l) (Compose r) = Compose $ pair' <$> l <*> r
  unpair' (Compose p) = maybe (CN, CN) (bimap CJ CJ . unpair') p
  injL (Compose x) p = Compose $ (`injL` p) <$> x
  injR (Compose x) p = Compose $ (`injR` p) <$> x

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

instance EvalOp (JustAccumulator NativeOp) where
  type EvalMonad (JustAccumulator NativeOp) = StateT Accumulated (CodeGen Native) -- should be a ReaderT
  type Index (JustAccumulator NativeOp) = ()
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

  evalOp () l (JA NScanl1) _ (Push (Push _ (BAE (Value' ty sh) _)) (BAE f _))
    = StateT $ \acc -> do
        let thing = zeroes ty
        pure (Push Env.Empty $ FromArg (Value' undefined sh), M.insert l (Exists thing, Exists ty) acc)
  evalOp () l (JA NFold2) _ (Push (Push _ (BAE (Value' ty sh) _)) (BAE f _))
    = StateT $ \acc -> do
        let thing = zeroes ty
        pure (Push Env.Empty $ FromArg (Value' undefined undefined), M.insert l (Exists thing, Exists ty) acc)
  evalOp () _ (JA NMap) _ (Push (Push (Push Env.Empty (BAE _ _)) (BAE (Value' x (Shape' shr sh)) _)) (BAE _ _))
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' undefined (Shape' shr sh)
  evalOp () _ (JA NBackpermute) _ (Push (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE (Value' x _) _)) _)
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' x $ Shape' shr sh
  evalOp () _ (JA NGenerate) _ (Push (Push Env.Empty (BAE (Shape' shr sh) _)) (BAE _ _))
    = lift $ pure $ Push Env.Empty $ FromArg $ Value' undefined (Shape' shr sh)
  -- For Permute, we ignore all the BP info here and simply assume that there is none


  evalOp _ _ (JA op) _ _ = undefined


instance MakesILP op => MakesILP (JustAccumulator op) where
  type BackendVar (JustAccumulator op) = BackendVar op
  type BackendArg (JustAccumulator op) = BackendArg op
  newtype BackendClusterArg (JustAccumulator op) a = BCAJA (BackendClusterArg op a)
  mkGraph (JA op) = undefined -- do not want to run the ILP solver again!
  finalize = undefined
  labelLabelledArg = undefined
  getClusterArg = undefined
  encodeBackendClusterArg = undefined
  -- probably just never running anything here
  -- this is really just here because MakesILP is a superclass


instance (StaticClusterAnalysis op, EnvF (JustAccumulator op) ~ EnvF op) => StaticClusterAnalysis (JustAccumulator op) where
  newtype BackendClusterArg2 (JustAccumulator op) x y = BCA2JA (BackendClusterArg2 op x y)
  onOp a b c d   = coerce @(BackendArgs        op _ _) @(BackendArgs        (JustAccumulator op) _ _) $ onOp (coerce a) (coerce b) (coerce c) d
  def      x y z = coerce @(BackendClusterArg2 op _ _) @(BackendClusterArg2 (JustAccumulator op) _ _) $ def x y (coerce z)
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


toOnlyAcc :: Cluster op args -> Cluster (JustAccumulator op) args
toOnlyAcc (Cluster bc (Cluster' io ast)) = Cluster (go2 bc) (Cluster' io $ go ast)
  where
    go :: ClusterAST op env args' -> ClusterAST (JustAccumulator op) env args'
    go P.None = P.None
    go (Bind lhs op l ast') = Bind lhs (JA op) l (go ast')
    go2 :: BackendCluster op args -> BackendCluster (JustAccumulator op) args
    go2 ArgsNil = ArgsNil
    go2 (bca :>: args) = BCAJA bca :>: go2 args

pattern CJ :: f a -> Compose Maybe f a
pattern CJ x = Compose (Just x)
pattern CN :: Compose Maybe f a
pattern CN = Compose Nothing
{-# COMPLETE CJ,CN #-}

-- Does this Vars contain exactly `x` variables, i.e., is `sh` `x`-dimensional?
isAtDepth :: Vars f x sh -> Int -> Bool
isAtDepth vs x = x == depth vs
  where
    depth :: Vars x y z -> Int
    depth TupRunit = 0
    depth (TupRpair l r) = depth l + depth r
    depth TupRsingle{} = 1

isAtDepth' :: ShapeR sh -> Int -> Bool
isAtDepth' vs x = x == rank vs

typerInt :: TypeR Int
typerInt = TupRsingle scalarTypeInt

zeroes :: TypeR a -> Operands a
zeroes TupRunit = OP_Unit
zeroes (TupRpair l r) = OP_Pair (zeroes l) (zeroes r)
zeroes ty@(TupRsingle t) = case t of
  VectorScalarType _ -> error "todo"
  SingleScalarType (NumSingleType t) -> case t of
    IntegralNumType t -> case t of
      TypeInt    -> constant ty 0
      TypeInt8   -> constant ty 0
      TypeInt16  -> constant ty 0
      TypeInt32  -> constant ty 0
      TypeInt64  -> constant ty 0
      TypeWord   -> constant ty 0
      TypeWord8  -> constant ty 0
      TypeWord16 -> constant ty 0
      TypeWord32 -> constant ty 0
      TypeWord64 -> constant ty 0
    FloatingNumType t -> case t of
      TypeHalf   -> constant ty 0
      TypeFloat  -> constant ty 0
      TypeDouble -> constant ty 0

