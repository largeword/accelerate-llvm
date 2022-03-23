{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
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

module Data.Array.Accelerate.LLVM.Native.Operation (
  NativeOp(..)
) where

-- accelerate

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Backend
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels

import Data.Set (Set)
import qualified Data.Set as Set


data NativeOp op where
  NMap         :: NativeOp (Fun' (s -> t)    -> In sh s -> Out sh  t -> ())
  NBackpermute :: NativeOp (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ())
  NGenerate    :: NativeOp (Fun' (sh -> t)              -> Out sh  t -> ())
  NPermute     :: NativeOp (Fun' (e -> e -> e)
                            -> Mut sh' e
                            -> Fun' (sh -> PrimMaybe sh')
                            -> In sh e
                            -> ())

instance PrettyOp NativeOp where
  prettyOp NMap         = "map"
  prettyOp NBackpermute = "backpermute"
  prettyOp NGenerate    = "generate"
  prettyOp NPermute     = "permute"

instance NFData' NativeOp where
  rnf' !_ = ()

instance DesugarAcc NativeOp where
  mkMap         a b c   = Exec NMap         (a :>: b :>: c :>:       ArgsNil)
  mkBackpermute a b c   = Exec NBackpermute (a :>: b :>: c :>:       ArgsNil)
  mkGenerate    a b     = Exec NGenerate    (a :>: b :>:             ArgsNil)
  mkPermute     a b c d = Exec NPermute     (a :>: b :>: c :>: d :>: ArgsNil)

instance SimplifyOperation NativeOp where
  detectCopy _          NMap         = detectMapCopies
  detectCopy matchVars' NBackpermute = detectBackpermuteCopies matchVars'
  detectCopy _ _                     = const []

instance SLVOperation NativeOp where
  slvOperation NGenerate    = defaultSlvGenerate    NGenerate
  slvOperation NMap         = defaultSlvMap         NMap
  slvOperation NBackpermute = defaultSlvBackpermute NBackpermute
  slvOperation _ = Nothing


-- No fusion at all
noFusion :: Set Label -> Label -> Information NativeOp
noFusion inputs l = 
  mempty{_graphI = 
    mempty{_infusibleEdges = 
      Set.map (-?> l) inputs}}
  

instance MakesILP NativeOp where
  type BackendVar NativeOp = ()
  type BackendArg NativeOp = ()
  data BackendClusterArg NativeOp a = None
  
  mkGraph NMap (_ :>: L _ (_, lIns) :>: _ :>: ArgsNil) = noFusion lIns
  mkGraph NBackpermute (_ :>: L _ (_, lIns) :>: _ :>: ArgsNil) = noFusion lIns
  mkGraph NGenerate _ = const mempty
  mkGraph NPermute (_ :>: _ :>: _ :>: L _ (_, lIns) :>: ArgsNil) = noFusion lIns

  labelLabelledArg _ _ (L x y) = LOp x y ()
  getClusterArg _ = None
  finalize = const mempty
