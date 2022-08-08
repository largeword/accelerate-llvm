{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

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


import Data.Set (Set)
import qualified Data.Set as Set
import Data.Array.Accelerate.AST.Partitioned (OutArgsOf)
import Data.Array.Accelerate.AST.Environment (Val, weakenId)
import Data.Array.Accelerate.Representation.Array (ArrayR(..))
import Data.Array.Accelerate.Trafo.Var (DeclareVars(..), declareVars, identity)
import Data.Array.Accelerate.Representation.Ground (buffersR)
import Data.Array.Accelerate.Trafo.Desugar (desugarAlloc)
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Trafo.Exp.Substitution (weakenVars)
import Data.Array.Accelerate.Trafo.Operation.Substitution (aletUnique, alet, weaken)
import Data.Array.Accelerate.Representation.Shape (ShapeR (..), shapeType)
import Data.Array.Accelerate.Representation.Type (TypeR, TupR (..))
import Data.Array.Accelerate.Type (scalarType, Word8, scalarTypeWord8)
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Trafo.Substitution (compose)
import Data.Maybe (isJust)
import Data.Array.Accelerate.Interpreter (InOut (..))
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import Lens.Micro
import qualified Debug.Trace
import qualified Data.Map as M


data NativeOp op where
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

instance PrettyOp NativeOp where
  prettyOp NMap         = "map"
  prettyOp NBackpermute = "backpermute"
  prettyOp NGenerate    = "generate"
  prettyOp NPermute     = "permute"
  prettyOp NScanl1      = "scanl1"

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

-- -3 can't fuse with anything, -2 for 'left to right', -1 for 'right to left', n for 'unpredictable, see computation n' (currently only backpermute)
data NativeILPVar = Order InOut  Label
  deriving (Eq, Ord)
pattern InDir, OutDir :: Label -> Graph.Var NativeOp
pattern InDir  l = BackendSpecific (Order  InArr l)
pattern OutDir l = BackendSpecific (Order OutArr l)


-- TODO: factor out more common parts of mkGraph
-- TODO: do the TODO's in here, and also do them in the Interpreter
-- TODO: enforce that all buffers that together make up an array (say, as input of a Map) all have the same order
instance MakesILP NativeOp where
  type BackendVar NativeOp = NativeILPVar
  type BackendArg NativeOp = Int -- the Order, to ensure that multiple uses of the same array in different orders get separate array reads
  data BackendClusterArg NativeOp a = None

  mkGraph NBackpermute (_ :>: L _ (_, lIns) :>: _ :>: ArgsNil) l@(Label i _) =
    Graph.Info
      mempty
      (    inputConstraints l lIns
        <> c (InDir l) .==. int i) -- TODO: incorporate the order of the output here too: InDir l .==. int i .+. nTimes (OutDir l) --- actually, maybe there is no need? Think about this another two times :)
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
        <> c (InDir l) .==. c (OutDir l))
      (defaultBounds l)
  mkGraph NPermute (_ :>: L _ (_, lTargets) :>: L _ (_, lLocks) :>: _ :>: L _ (_, lIns) :>: ArgsNil) l =
    Graph.Info
      ( mempty & infusibleEdges .~ Set.map (-?> l) (lTargets <> lLocks)) -- add infusible edges from the producers of target and lock arrays to the permute
      (    inputConstraints l lIns
        <> c (OutDir l) .==. int (-3)) -- Permute cannot fuse with its consumer
      ( lower (-2) (InDir l)) -- default lowerbound for the input, but not for the output (as we set it to -3)
  mkGraph NScanl1 (_ :>: L _ (_, lIns) :>: _ :>: _ :>: ArgsNil) l =
    undefined

  labelLabelledArg vars l (L x@(ArgArray In  _ _ _) y) = LOp x y $ vars M.! Order InArr  l
  labelLabelledArg vars l (L x@(ArgArray Out _ _ _) y) = LOp x y $ vars M.! Order OutArr l
  labelLabelledArg _ _ (L x y) = LOp x y 0
  getClusterArg _ = None
  -- For each label: If the output is manifest, then its direction is negative (i.e. not in a backpermuted order)
  finalize = foldMap $ \l -> timesN (manifest l) .>. c (OutDir l)

  encodeBackendClusterArg None = intHost $(hashQ ("None" :: String))

inputConstraints :: Label -> Labels -> Constraint NativeOp
inputConstraints l = foldMap $ \lIn ->
                timesN (fused lIn l) .>=. c (InDir l) .-. c (OutDir lIn)
    <> (-1) .*. timesN (fused lIn l) .<=. c (InDir l) .-. c (OutDir lIn)

defaultBounds :: Label -> Bounds NativeOp
defaultBounds l = lower (-2) (InDir l) <> lower (-2) (OutDir l) 


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
  onOp NMap (BP a b c :>: ArgsNil) _ _ = NoBP :>: BP a b c :>: BP a b c :>: ArgsNil
  onOp NMap (NoBP     :>: ArgsNil) _ _ = NoBP :>: NoBP     :>: NoBP     :>: ArgsNil
  onOp NBackpermute (BP shr1 shr2 g :>: ArgsNil) (ArgFun f :>: ArgArray In (ArrayR shrI _) _ _ :>: ArgArray Out (ArrayR shrO _) _ _ :>: ArgsNil) _
    | Just Refl <- matchShapeR shrO shr2  = NoBP :>: BP shr1 shrI (compose f g) :>: BP shr1 shr2 g :>: ArgsNil
    | otherwise = error "BP shapeR doesn't match backpermute output shape"
  onOp NBackpermute (NoBP           :>: ArgsNil) (ArgFun f :>: ArgArray In (ArrayR shrI _) _ _ :>: ArgArray Out (ArrayR shrO _) _ _ :>: ArgsNil) _
                                          = Debug.Trace.trace "making bp" $ NoBP :>: BP shrO shrI f             :>: NoBP           :>: ArgsNil    
  onOp NGenerate (BP a b c :>: ArgsNil) _ _ = BP a b c :>: BP a b c :>: ArgsNil -- storing the bp in the function argument. Probably not required, could just take it from the array one during codegen
  onOp NGenerate (NoBP     :>: ArgsNil) _ _ = NoBP     :>: NoBP     :>: ArgsNil
  onOp NPermute ArgsNil _ _ = NoBP :>: NoBP :>: NoBP :>: NoBP :>: NoBP :>: ArgsNil
  onOp _ _ _ _ = error "todo"

bpid :: BackendClusterArg2 NativeOp env arg -> BackendClusterArg2 NativeOp env arg'
bpid NoBP = NoBP
bpid (BP a b c) = BP a b c

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
