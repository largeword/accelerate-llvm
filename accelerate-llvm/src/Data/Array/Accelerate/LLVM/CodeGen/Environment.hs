{-# LANGUAGE GADTs                #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
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
  ( Env(..)
  , Val, prj
  , Gamma, GroundOperand(..), AccessGroundR(..)
  , aprjParameter, aprjParameters, aprjBuffer
  , arraySize
  , MarshalArg, MarshalFun, MarshalFun', MarshalEnv
  , marshalScalarArg
  -- , scalarParameter, ptrParameter
  , bindParameters, bindEnv, envType
  )
  where

import Data.String

import Data.Array.Accelerate.AST.Environment                    ( Env(..), prj' )
import Data.Array.Accelerate.AST.Operation                      hiding (Parameter)
import Data.Array.Accelerate.AST.Idx                            ( Idx )
import Data.Array.Accelerate.Error                              ( internalError )
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.CodeGen.Monad

import LLVM.AST.Type.AddrSpace
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Function                                   as LLVM
import LLVM.AST.Type.Global
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Name
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation

import GHC.Stack
import Data.Typeable


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

arraySize :: HasCallStack => Arg genv (m sh e) -> Gamma genv -> Operands sh
arraySize (ArgArray _ (ArrayR shr _) sh _) = aprjParameters $ shapeExpVars shr sh

type family MarshalArg a where
  MarshalArg (Buffer e) = Ptr (ScalarArrayDataR e)
  MarshalArg e = e

-- | Converts a typed environment into a function type.
-- For instance, (((), Int), Float) is converted to Int -> Float -> ().
-- The accumulating parameter 'r' is needed as the type would be in reverse
-- order without such accumulator.
--
type MarshalFun env = MarshalFun' env ()
type family MarshalFun' env r where
  MarshalFun' () r = r
  MarshalFun' (env, t) r = MarshalFun' env (MarshalArg t -> r)

type family MarshalEnv env where
  MarshalEnv (env, t) = (MarshalEnv env, MarshalArg t)
  MarshalEnv ()       = ()

envType :: Env AccessGroundR env -> TupR PrimType (MarshalEnv env)
envType Empty = TupRunit
envType (Push env (AccessGroundRscalar tp))
  | Refl <- marshalScalarArg tp = envType env `TupRpair` TupRsingle (ScalarPrimType tp)
envType (Push env (AccessGroundRbuffer _ (SingleScalarType tp)))
  | SingleArrayDict <- singleArrayDict tp 
  = envType env `TupRpair` TupRsingle (PtrPrimType (ScalarPrimType $ SingleScalarType tp) defaultAddrSpace)
envType (Push env (AccessGroundRbuffer _ (VectorScalarType (VectorType n tp))))
  = envType env `TupRpair` TupRsingle (PtrPrimType (ScalarPrimType $ SingleScalarType tp) defaultAddrSpace)

bindEnv
  :: forall arch env. Env AccessGroundR env
  -> ( PrimType (Struct (MarshalEnv env))
     , CodeGen arch ()
     , Gamma env
     )
bindEnv environment =
  let (gen, gamma, _, _) = go id environment in (envTp, gen, gamma)
  where
    envTp = StructPrimType False $ envType environment
    operandEnv = LocalReference (PrimType (PtrPrimType envTp defaultAddrSpace)) "env"
    go :: (forall t. TupleIdx (MarshalEnv env') t -> TupleIdx (MarshalEnv env) t)
       -> Env AccessGroundR env'
       -> ( CodeGen arch ()
          , Gamma env'
          , Int -- Next fresh scalar variable index
          , Int -- Next fresh buffer variable index
          )
    go _ Empty = (return (), Empty, 0, 0)
    go toTupleIdx (Push env (AccessGroundRscalar tp))
      | Refl <- marshalScalarArg tp = 
        ( instr_ (downcast $
            namePtr := GetStructElementPtr (ScalarPrimType tp) operandEnv (toTupleIdx $ TupleIdxRight TupleIdxSelf)
          ) 
          >> instr_ (downcast $
            name := Load tp NonVolatile operandPtr
          )
          >> codegen
        , gamma `Push` GroundOperandParam operand
        , freshScalar + 1
        , freshBuffer
        )
      where
        (codegen, gamma, freshScalar, freshBuffer) = go (toTupleIdx . TupleIdxLeft) env
        operand = LocalReference (PrimType $ ScalarPrimType tp) name
        operandPtr = LocalReference (PrimType $ PtrPrimType (ScalarPrimType tp) defaultAddrSpace) namePtr
        name = fromString $ "param." ++ show freshScalar
        namePtr = fromString $ "param." ++ show freshScalar ++ ".ptr"
    go toTupleIdx (Push env (AccessGroundRbuffer m (tp :: ScalarType t))) =
      ( instr_ (downcast $
          namePtr := GetStructElementPtr ptrType operandEnv (toTupleIdx $ TupleIdxRight TupleIdxSelf)
        )
        >> instr_ (downcast $
          name := LoadPtr NonVolatile operandPtr
        )
        >> codegen
      , gamma `Push` GroundOperandBuffer irbuffer
      , freshScalar
      , freshBuffer + 1
      )
      where
        (codegen, gamma, freshScalar, freshBuffer) = go (toTupleIdx . TupleIdxLeft) env
        operand = LocalReference (PrimType ptrType) name
        operandPtr = LocalReference (PrimType $ PtrPrimType ptrType defaultAddrSpace) namePtr
        prefix = case m of
          In  -> "in."
          Out -> "out."
          Mut -> "mut."
        name = fromString $ prefix ++ show freshBuffer
        namePtr = fromString $ prefix ++ show freshBuffer ++ ".ptr"
        irbuffer :: IRBuffer t
        irbuffer = IRBuffer (Just (operand, defaultAddrSpace, NonVolatile)) Nothing
        ptrType :: PrimType (MarshalArg (Buffer t))
        ptrType = case tp of
          SingleScalarType t
            | SingleArrayDict <- singleArrayDict t -> PtrPrimType (ScalarPrimType tp) defaultAddrSpace
          VectorScalarType (VectorType _ t) -> PtrPrimType (ScalarPrimType $ SingleScalarType t) defaultAddrSpace

bindParameters
  :: Env AccessGroundR env
  -> ( Result t :~: Result (MarshalFun' env t)
     , GlobalFunctionDefinition t -> GlobalFunctionDefinition (MarshalFun' env t)
     , Gamma env
     )
bindParameters env = (eq, fun, gamma)
  where
    (eq, fun, gamma, _, _) = bindParameters' env

bindParameters'
  :: forall env t. Env AccessGroundR env
  -> ( Result t :~: Result (MarshalFun' env t)
     , GlobalFunctionDefinition t -> GlobalFunctionDefinition (MarshalFun' env t)
     , Gamma env
     , Int -- Next fresh scalar variable index
     , Int -- Next fresh buffer variable index
     -- TODO: Should we have separate indices for in, mut and out buffers?
     )
bindParameters' Empty = (Refl, id, Empty, 0, 0)
bindParameters' (Push env (AccessGroundRscalar tp :: AccessGroundR s))
  | (eq, fun, gamma, nextScalar, nextBuffer) <- bindParameters' env =
  let
    operand = LocalReference (PrimType $ ScalarPrimType tp) name
    name = fromString $ "param." ++ show nextScalar

    -- Not sure why, but it seems GHC gets confused if we pattern match for
    -- 's ~ MarshalArg s' on toplevel, hence we do that nested here.
    --
    tp' :: ScalarType (MarshalArg s)
    name' :: Name (MarshalArg s)
    (tp', name')
      | Refl <- marshalScalarArg @s tp = (tp, name)
  in
    ( case eq of Refl -> Refl -- Again, we need to pattern match nested
    , \b -> fun $ LLVM.Lam (ScalarPrimType tp') name' b
    , gamma `Push` GroundOperandParam operand
    , nextScalar + 1
    , nextBuffer
    )
bindParameters' (Push env (AccessGroundRbuffer m tp))
  | (eq, fun, gamma, nextScalar, nextBuffer) <- bindParameters' env =
  let
    operand = LocalReference (PrimType ptrType) name
    prefix = case m of
      In  -> "in."
      Out -> "out."
      Mut -> "mut."
    name = fromString $ prefix ++ show nextBuffer
    irbuffer = IRBuffer (Just (operand, defaultAddrSpace, NonVolatile)) Nothing
    ptrType = case tp of
      SingleScalarType t
        | SingleArrayDict <- singleArrayDict t -> PtrPrimType (ScalarPrimType tp) defaultAddrSpace
      VectorScalarType (VectorType _ t) -> PtrPrimType (ScalarPrimType $ SingleScalarType t) defaultAddrSpace
  in
    ( case eq of Refl -> Refl -- Again, we need to pattern match nested
    , \b -> fun $ LLVM.Lam ptrType name b
    , gamma `Push` GroundOperandBuffer irbuffer
    , nextScalar
    , nextBuffer + 1
    )

marshalScalarArg :: ScalarType t -> t :~: MarshalArg t
-- Pattern match to prove that 't' is not a buffer
marshalScalarArg (VectorScalarType _) = Refl
marshalScalarArg (SingleScalarType (NumSingleType (IntegralNumType tp))) = case tp of
  TypeInt    -> Refl
  TypeInt8   -> Refl
  TypeInt16  -> Refl
  TypeInt32  -> Refl
  TypeInt64  -> Refl
  TypeWord   -> Refl
  TypeWord8  -> Refl
  TypeWord16 -> Refl
  TypeWord32 -> Refl
  TypeWord64 -> Refl
marshalScalarArg (SingleScalarType (NumSingleType (FloatingNumType tp))) = case tp of
  TypeHalf   -> Refl
  TypeFloat  -> Refl
  TypeDouble -> Refl
