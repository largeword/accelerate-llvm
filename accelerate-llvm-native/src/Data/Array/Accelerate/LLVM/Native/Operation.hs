{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Accelerate
-- Copyright   : [2014..2022] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Operation
  where

-- accelerate

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Analysis.Hash.Operation
import Data.Array.Accelerate.Backend
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Array.Accelerate.Eval


import qualified Data.Set as Set
import Data.Array.Accelerate.AST.Environment (weakenId, weakenEmpty, (.>) )
import Data.Array.Accelerate.Representation.Array (ArrayR(..))
import Data.Array.Accelerate.Trafo.Var (DeclareVars(..), declareVars)
import Data.Array.Accelerate.Representation.Ground (buffersR, typeRtoGroundsR)
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Trafo.Operation.Substitution (aletUnique, alet, weaken, LHS (..), mkLHS)
import Data.Array.Accelerate.Representation.Shape (ShapeR (..), shapeType, rank)
import Data.Array.Accelerate.Representation.Type (TypeR, TupR (..))
import Data.Array.Accelerate.Type (scalarType, Word8, scalarTypeWord8, scalarTypeInt)
import Data.Array.Accelerate.Analysis.Match
import Data.Maybe (isJust)
import Data.Array.Accelerate.Interpreter (InOut (..))
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import Lens.Micro
import qualified Data.Map as M
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Desugar (desugarAlloc)
import Data.Array.Accelerate.Trafo.Substitution (Sink'(..))

import qualified Debug.Trace
import GHC.Stack

data NativeOp t where
  NMap         :: NativeOp (Fun' (s -> t)    -> In sh s -> Out sh  t -> ())
  NBackpermute :: NativeOp (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ())
  NGenerate    :: NativeOp (Fun' (sh -> t)              -> Out sh  t -> ())
  NPermute     :: NativeOp (Fun' (e -> e -> e)
                            -> Mut sh' e
                            -> Mut sh' Word8
                            -> Fun' (sh -> PrimMaybe sh')
                            -> In sh e
                            -> ())
  -- this one covers ScanDim, ScanP1 and ScanP2. Only ScanP1's second output argument will be used for the partial reductions,
  -- the others will simply get SLV'd away.
  NScanl1      :: NativeOp (Fun' (e -> e -> e) 
                         -> In (sh, Int) e 
                         -> Out (sh, Int) e -- the local scan result
                         -> Out (sh, Int) e -- the local fold result
                         -> ())
  NFold1       :: NativeOp (Fun' (e -> e -> e) -- segmented
                         -> In (sh, Int) e
                         -> Out (sh, Int) e
                         -> ())
  NFold2       :: NativeOp (Fun' (e -> e -> e) -- sequential
                         -> In (sh, Int) e
                         -> Out sh e
                         -> ())

instance PrettyOp NativeOp where
  prettyOp NMap         = "map"
  prettyOp NBackpermute = "backpermute"
  prettyOp NGenerate    = "generate"
  prettyOp NPermute     = "permute"
  prettyOp NScanl1      = "scanl1"
  prettyOp NFold1       = "fold-1"
  prettyOp NFold2       = "fold-2"

instance NFData' NativeOp where
  rnf' !_ = ()

instance DesugarAcc NativeOp where
  mkMap         a b c   = Exec NMap         (a :>: b :>: c :>:       ArgsNil)
  mkBackpermute a b c   = Exec NBackpermute (a :>: b :>: c :>:       ArgsNil)
  mkGenerate    a b     = Exec NGenerate    (a :>: b :>:             ArgsNil)
  mkScan LeftToRight f Nothing i o
    -- If multidimensional, simply NScanl1.
    -- Otherwise, NScanl1 followed by NScanl1 on the reductions, followed by a replicate on that result and then zipWith the first result.
    = error "todo"
  -- right to left is conceptually easy once we already have order variables for backpermute. 
  -- Exclusive scans (changing array size) are weirder, require an extra 'cons' primitive
  mkScan _ _ _ _ _ = error "todo" 
  mkPermute     a b@(ArgArray _ (ArrayR shr _) sh _) c d
    | DeclareVars lhs w lock <- declareVars $ buffersR $ TupRsingle scalarTypeWord8
    = Debug.Trace.trace "hello??" $ aletUnique lhs 
        (Alloc shr scalarTypeWord8 $ groundToExpVar (shapeType shr) sh)
        $ alet LeftHandSideUnit
          (Exec NGenerate ( -- The old pipeline used a 'memset 0' instead, which sounds faster...
                ArgFun (Lam (LeftHandSideWildcard (shapeType shr)) $ Body $ Const scalarTypeWord8 0)
            :>: ArgArray Out (ArrayR shr (TupRsingle scalarTypeWord8)) (weakenVars w sh) (lock weakenId) 
            :>: ArgsNil))
          (Exec NPermute (
                weaken w a 
            :>: weaken w b 
            :>: ArgArray Mut (ArrayR shr (TupRsingle scalarTypeWord8)) (weakenVars w sh) (lock weakenId) 
            :>: weaken w c 
            :>: weaken w d 
            :>: ArgsNil))
  -- we desugar a Fold with seed element into a Fold1 followed by a map which prepends the seed
  -- copied verbatim from Interpreter; this should probably be in the shared implementation except for the part where it doesn't work on 0-size arrays
  -- Will need to figure out how to solve that before we ship it, as long as we keep the conditional out of the loop. 
  -- Potentially generating multiple versions, as we do currently? With the new fusion, that might result in an exponential amount of variations in the number of folds per cluster...
  -- TODO
  mkFold a@(ArgFun f) (Just (ArgExp seed)) b@(ArgArray In (ArrayR _ tp) _ _) c@(ArgArray _ arr' sh' _)
    | DeclareVars lhsTemp wTemp kTemp <- declareVars $ buffersR tp =
      aletUnique lhsTemp (desugarAlloc arr' $ fromGrounds sh') $
        alet LeftHandSideUnit
          (mkFold (weaken wTemp a) Nothing (weaken wTemp b) (ArgArray Out arr' (weakenVars wTemp sh') (kTemp weakenId))) $
          case mkLHS tp of
            LHS lhs vars ->
              mkMap
                (ArgFun $ 
                  Lam lhs $ Body $ (\f -> apply2 tp f (weakenThroughReindex wTemp reindexExp $ 
                    weakenE weakenEmpty seed) (expVars vars)) $ weakenThroughReindex wTemp reindexExp f)
                (ArgArray In arr' (weakenVars wTemp sh') (kTemp weakenId))
                (weaken wTemp c)
  mkFold (a :: Arg env (Fun' (e -> e -> e))) Nothing b@(ArgArray In arr@(ArrayR shr tp) _ _) c
    | DeclareVars lhsSize (wSize :: env :> env') kSize <- declareVars . typeRtoGroundsR $ TupRsingle scalarTypeInt
    , DeclareVars lhsTemp (wTemp :: env' :> env'') kTemp <- declareVars $ buffersR tp =
      let w = wTemp .> wSize in
      case shr of
        ShapeRsnoc ShapeRz -> aletUnique lhsSize (Compute $ Const scalarTypeInt 2) $ -- magic constant 2; TODO change into `size/workstealsize` rounded up
          let sh = TupRpair TupRunit (kSize weakenId) in
          aletUnique lhsTemp (desugarAlloc (ArrayR shr tp) $ fromGrounds sh) $ 
            let tmpArrArg :: Modifier m -> Arg env'' (m ((),Int) e)
                tmpArrArg m = ArgArray m arr (weakenVars wTemp sh) (kTemp weakenId)
            in alet LeftHandSideUnit
              (Exec NFold1 $ weaken w a :>: weaken w b :>: tmpArrArg Out :>: ArgsNil)
              (Exec NFold2 $ weaken w a :>: tmpArrArg In :>: weaken w c :>: ArgsNil)
        _ -> -- single-kernel multidim reduction
          Exec NFold2 $ a :>: b :>: c :>: ArgsNil

instance SimplifyOperation NativeOp where
  detectCopy _          NMap         = detectMapCopies
  detectCopy matchVars' NBackpermute = detectBackpermuteCopies matchVars'
  detectCopy _ _                     = const []

instance SLVOperation NativeOp where
  slvOperation NGenerate    = defaultSlvGenerate    NGenerate
  slvOperation NMap         = defaultSlvMap         NMap
  slvOperation NBackpermute = defaultSlvBackpermute NBackpermute
  slvOperation _ = Nothing

instance EncodeOperation NativeOp where
  encodeOperation NMap         = intHost $(hashQ ("Map" :: String))
  encodeOperation NBackpermute = intHost $(hashQ ("Backpermute" :: String))
  encodeOperation NGenerate    = intHost $(hashQ ("Generate" :: String))
  encodeOperation NPermute     = intHost $(hashQ ("Permute" :: String))
  encodeOperation NScanl1      = intHost $(hashQ ("Scanl1" :: String))
  encodeOperation NFold1       = intHost $(hashQ ("Fold-1" :: String))
  encodeOperation NFold2       = intHost $(hashQ ("Fold-2" :: String))

-- -3 can't fuse with anything, -2 for 'left to right', -1 for 'right to left', n for 'unpredictable, see computation n' (currently only backpermute)
data NativeILPVar = Order InOut  Label 
                  -- 0 means maximal parallelism; each thread only gets 1 element, e.g. output of the first stage of 1-dimensional fold
                  -- 1 is segmented along the innermost dimension into nthreads equal parts, e.g. input of the first stage of 1-dimensional fold
                  -- 2 is one row for each thread
                  -- 3 is segmented along the second dimension, e.g. input of a fused folddim followed by first stage of 1-dimensional fold
                  -- 4 is 2 dimensions per thread, etc
                  -- note that this is about _logical_ threads; if there are less physical ones present then they will perform work stealing, so this is really the (minimum) size of each bucket in the work stealing queue
                  | Dims InOut Label
  deriving (Eq, Ord, Show)
pattern InDir, OutDir, InDims, OutDims :: Label -> Graph.Var NativeOp
pattern InDir   l = BackendSpecific (Order  InArr l)
pattern OutDir  l = BackendSpecific (Order OutArr l)
pattern InDims  l = BackendSpecific (Dims   InArr l)
pattern OutDims l = BackendSpecific (Dims  OutArr l)


-- TODO: factor out more common parts of mkGraph
-- TODO: do the TODO's in here, and also do them in the Interpreter
-- TODO: enforce that all buffers that together make up an array (say, as input of a Map) all have the same order
instance MakesILP NativeOp where
  type BackendVar NativeOp = NativeILPVar
  type BackendArg NativeOp = Int -- the Order, to ensure that multiple uses of the same array in different orders get separate array reads
  data BackendClusterArg NativeOp a = None

  mkGraph NBackpermute (_ :>: L (ArgArray In (ArrayR shrI _) _ _) (_, lIns) :>: L (ArgArray Out (ArrayR shrO _) _ _)_ :>: ArgsNil) l@(Label i _) =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> c (InDir l) .==. int i 
          -- .+. timesN (int 3 .+. c (OutDir l)) 
          -- When we switch to gather, like in the paper, we need to add this term.
          -- 4 + dir is always positive, and this is exactly why we (elsewhere) define `n` as `5+(size nodes)`
          -- problem: this clashes with the assumption in 'inputConstraints' and 'finalise' that orders are at most n,
          -- so if we want this we need to change inputConstraints and finalise
        )-- <> c (InDims l) .+. int (rank shrO) .==. c (OutDims l) .+. int (rank shrI))
      (defaultBounds l)
  mkGraph NGenerate _ l =
    Graph.Info
      mempty
      mempty
      (defaultBounds l)
  mkGraph NMap (_ :>: L _ (_, lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> c (InDir  l) .==. c (OutDir  l)
        <> c (InDims l) .==. c (OutDims l))
      (defaultBounds l)
  mkGraph NPermute (_ :>: L _ (_, lTargets) :>: L _ (_, lLocks) :>: _ :>: L _ (_, lIns) :>: ArgsNil) l =
    Graph.Info
      ( mempty & infusibleEdges .~ Set.map (-?> l) (lTargets <> lLocks)) -- add infusible edges from the producers of target and lock arrays to the permute
      (    inputConstraints l lIns
        <> c (OutDir l) .==. int (-3)) -- Permute cannot fuse with its consumer
      ( lower (-2) (InDir l)) -- default lowerbound for the input, but not for the output (as we set it to -3)
  mkGraph NScanl1 (_ :>: L _ (_, lIns) :>: _ :>: _ :>: ArgsNil) l =
    error "todo"
  mkGraph NFold1 (_ :>: L _ (_, lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> c (InDir   l) .==. c (OutDir l)
        <> c (InDims  l) .==. int 1
        <> c (OutDims l) .==. int 0)
      (defaultBounds l)
  mkGraph NFold2 (_ :>: L _ (_, lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> c (InDir  l) .==. c (OutDir l)
        <> c (InDims l) .==. int 2 .+. c (OutDims l)) -- Difference of 2, because a full dimension is reduced
      (defaultBounds l)

  labelLabelledArg :: M.Map (BackendVar NativeOp) Int -> Label -> LabelledArg env a -> LabelledArgOp NativeOp env a
  labelLabelledArg vars l (L x@(ArgArray In  _ _ _) y) = LOp x y $ vars M.! Order InArr  l
  labelLabelledArg vars l (L x@(ArgArray Out _ _ _) y) = LOp x y $ vars M.! Order OutArr l
  labelLabelledArg _ _ (L x y) = LOp x y 0
  getClusterArg :: LabelledArgOp NativeOp env a -> BackendClusterArg NativeOp a
  getClusterArg _ = None
  -- For each label: If the output is manifest, then its direction is negative (i.e. not in a backpermuted order)
  finalize = mempty-- foldMap $ \l -> timesN (manifest l) .>. c (OutDir l)

  encodeBackendClusterArg None = intHost $(hashQ ("None" :: String))

inputConstraints :: HasCallStack => Label -> Labels -> Constraint NativeOp
inputConstraints l = foldMap $ \lIn -> 
                timesN (fused lIn l) .>=. c (InDir  l) .-. c (OutDir  lIn)
    <> (-1) .*. timesN (fused lIn l) .<=. c (InDir  l) .-. c (OutDir  lIn)
    <>          timesN (fused lIn l) .>=. c (InDims l) .-. c (OutDims lIn)
    <> (-1) .*. timesN (fused lIn l) .<=. c (InDims l) .-. c (OutDims lIn)

defaultBounds :: Label -> Bounds NativeOp
defaultBounds l = lower (-2) (InDir l) <> lower (-2) (OutDir l) <> lower 0 (InDims l) <> lower 0 (OutDims l)


instance NFData' (BackendClusterArg NativeOp) where
  rnf' !_ = ()

instance ShrinkArg (BackendClusterArg NativeOp) where
  shrinkArg _ None = None
  deadArg None = None

instance StaticClusterAnalysis NativeOp where
  data BackendClusterArg2 NativeOp env arg where
    BP :: ShapeR sh1 -> ShapeR sh2 -> Fun env (sh1 -> sh2) -> BackendClusterArg2 NativeOp env arg
    NoBP :: BackendClusterArg2 NativeOp env arg
  def _ _ _ = NoBP
  justUnit  = NoBP
  valueToIn    = bpid
  valueToOut   = bpid
  inToValue    = bpid
  outToValue   = bpid
  outToSh      = bpid
  shToOut      = bpid
  shToValue    = bpid
  varToValue   = bpid
  varToSh      = bpid
  shToVar      = bpid
  shrinkOrGrow = bpid
  addTup       = bpid
  -- onOp propagates the backpermute information from the outputs to the inputs of each operation
  onOp NMap (bp :>: ArgsNil) _ _ = NoBP :>: bpid bp :>: bp :>: ArgsNil
  onOp NBackpermute (bp@(BP shr1 shr2 g) :>: ArgsNil) (ArgFun f :>: ArgArray In (ArrayR shrI _) _ _ :>: ArgArray Out (ArrayR shrO _) _ _ :>: ArgsNil) _
    | Just Refl <- matchShapeR shrO shr2  = NoBP :>: BP shr1 shrI (compose f g) :>: bp :>: ArgsNil
    | otherwise = error "BP shapeR doesn't match backpermute output shape"
  onOp NBackpermute (NoBP           :>: ArgsNil) (ArgFun f :>: ArgArray In (ArrayR shrI _) _ _ :>: ArgArray Out (ArrayR shrO _) _ _ :>: ArgsNil) _
                                          = NoBP :>: BP shrO shrI f             :>: NoBP           :>: ArgsNil    
  onOp NGenerate (bp :>: ArgsNil) _ _ = bpid bp :>: bp :>: ArgsNil -- storing the bp in the function argument. Probably not required, could just take it from the array one during codegen
  onOp NPermute ArgsNil _ _ = NoBP :>: NoBP :>: NoBP :>: NoBP :>: NoBP :>: ArgsNil
  onOp NFold1 (bp :>: ArgsNil) _ _ = NoBP :>: fold1bp bp :>: bp :>: ArgsNil
  onOp NFold2 (bp :>: ArgsNil) _ _ = NoBP :>: fold2bp bp :>: bp :>: ArgsNil
  onOp _ _ _ _ = error "todo"

bpid :: BackendClusterArg2 NativeOp env arg -> BackendClusterArg2 NativeOp env arg'
bpid NoBP = NoBP
bpid (BP a b c) = BP a b c

fold1bp :: BackendClusterArg2 NativeOp env (Out sh e) -> BackendClusterArg2 NativeOp env (In sh e)
fold1bp NoBP = NoBP
fold1bp (BP shr1 shr2 g) = BP shr1 shr2 $ error "todo: multiply the innermost (outer constructor) dimension by the workstealsize" g

fold2bp :: BackendClusterArg2 NativeOp env (Out sh e) -> BackendClusterArg2 NativeOp env (In (sh,Int) e)
fold2bp NoBP = NoBP
fold2bp (BP shr1 shr2 g) = BP (ShapeRsnoc shr1) (ShapeRsnoc shr2) $ error "todo: ignore the innermost index, apply the function, then add the index again" g



instance Eq (BackendClusterArg2 NativeOp env arg) where
  NoBP == NoBP = True
  (BP shr1 shr2 f) == (BP shr1' shr2' f')
    | Just Refl <- matchShapeR shr1 shr1'
    , Just Refl <- matchShapeR shr2 shr2'
    = isJust $ matchOpenFun f f'
  _ == _ = False


shrToTypeR :: ShapeR sh -> TypeR sh
shrToTypeR ShapeRz = TupRunit
shrToTypeR (ShapeRsnoc shr) = TupRpair (shrToTypeR shr) (TupRsingle scalarType)
