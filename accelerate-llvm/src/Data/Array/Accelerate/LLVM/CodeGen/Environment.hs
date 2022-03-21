{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Environment
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Environment
  ( module Data.Array.Accelerate.LLVM.CodeGen.Environment, Env(..) )
  where

import Data.String
import Text.Printf

import Data.Array.Accelerate.AST.Exp                            ( shapeExpVars )
import Data.Array.Accelerate.AST.Environment                    ( Env(..), prj' )
import Data.Array.Accelerate.AST.Operation                      ( ExpVar, ExpVars, GroundVar, GroundR(..), Arg(..), bufferImpossible )
import Data.Array.Accelerate.AST.Idx                            ( Idx )
import Data.Array.Accelerate.AST.Var                            ( Var(..) )
import Data.Array.Accelerate.Error                              ( internalError )
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Array

import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Sugar

import LLVM.AST.Type.Operand

import GHC.Stack


-- Scalar environment
-- ==================

-- | An environment for local scalar expression bindings, encoded at the value
-- level as a heterogenous snoc list, and on the type level as nested tuples.
--
type Val = Env Operand

prj :: Idx env t -> Val env -> Operand t
prj = prj'

-- Ground environment
-- =================

-- | A mapping between the environment index of a free scalar or buffer variable and the
-- Name of that variable to be used in the generated code.
--
-- This simply compresses the indices into a continuous range, rather than
-- directly using the integer equivalent of the de Bruijn index. Thus, the
-- result is still sensitive to the order of let bindings, but not of any
-- intermediate (unused) free array variables.
--
type Gamma = Env GroundOperand

data GroundOperand t where
  GroundOperandParam  :: Operand t  -> GroundOperand t
  GroundOperandBuffer :: IRBuffer t -> GroundOperand (Buffer t)

-- Projection of a scalar from the ground environment using a de Bruijn index.
--
aprjParameter :: HasCallStack => ExpVar genv t -> Gamma genv -> Operand t
aprjParameter (Var tp idx) env =
  case prj' idx env of
    GroundOperandParam x  -> x
    GroundOperandBuffer _ -> bufferImpossible tp

aprjParameters :: HasCallStack => ExpVars genv t -> Gamma genv -> Operands t
aprjParameters (TupRsingle var) env = ir (varType var) $ aprjParameter var env
aprjParameters (TupRpair v1 v2) env = OP_Pair (aprjParameters v1 env) (aprjParameters v2 env)
aprjParameters TupRunit         _   = OP_Unit

-- Projection of a buffer from the ground environment using a de Bruijn index.
-- This returns the operand of pointer to the buffer and its address space and
-- volatility.
--
aprjBuffer :: HasCallStack => GroundVar genv (Buffer t) -> Gamma genv -> IRBuffer t
aprjBuffer (Var (GroundRbuffer _) idx) env =
  case prj' idx env of
    GroundOperandBuffer buffer -> buffer
    GroundOperandParam _       -> internalError "Scalar impossible"
aprjBuffer (Var (GroundRscalar tp) _) _ = bufferImpossible tp

{-
-- | Construct the array environment index, will be used by code generation to
-- map free array variable indices to names in the generated code.
--
makeGamma :: IntMap (Idx' aenv) -> Gamma aenv
makeGamma = snd . IM.mapAccum (\n ix -> (n+1, toAval n ix)) 0
  where
    toAval :: Int -> Idx' aenv -> (Label, Idx' aenv)
    toAval n ix = (fromString (printf "fv%d" n), ix)
-}

arraySize :: HasCallStack => Arg genv (m sh e) -> Gamma genv -> Operands sh
arraySize (ArgArray _ (ArrayR shr _) sh _) = aprjParameters $ shapeExpVars shr sh
