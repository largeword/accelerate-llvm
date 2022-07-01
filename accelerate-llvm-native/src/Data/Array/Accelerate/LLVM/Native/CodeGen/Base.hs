{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Base
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Base
  where

import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Profile
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.Compile.Cache
import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )
import Data.Array.Accelerate.LLVM.Native.Foreign                    ()
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Primitive.Vec

import LLVM.AST.Type.Representation
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Name
import LLVM.AST.Type.Module
import LLVM.AST.Type.AddrSpace
import qualified LLVM.AST.Global                                    as LLVM
import qualified LLVM.AST.Type                                      as LLVM

import Data.String
import qualified Data.ByteString.Short.Char8                        as S8

-- The struct passed as argument to a call contains:
--   * An integer to denote the index of the next chunk to be started
--   * An integer to denote the number of threads currently working on this task
--   * Padding to assure that the environment is aligned by 2 cache lines
--     (The size of the header is now 2 cache lines)
--
-- The integers are incremented with atomic instructions.
type Header = Vec 32 Int32

headerType :: PrimType Header
headerType = ScalarPrimType scalarType

type KernelType env = Ptr (Struct (Header, Struct (MarshalEnv env))) -> Bool

bindHeaderEnv
  :: forall env. Env AccessGroundR env
  -> ( PrimType (Ptr (Struct (Header, Struct (MarshalEnv env))))
     , CodeGen Native ()
     , Operand (Ptr Int32)
     , Operand (Ptr Int32)
     , Gamma env
     )
bindHeaderEnv env = 
  ( argTp
  , do
      instr_ $ downcast $ nameHeader := GetStructElementPtr headerType arg (TupleIdxLeft TupleIdxSelf)
      instr_ $ downcast $ nameIndex := GetVecElementPtr TypeInt32 header (integral TypeInt32 0)
      instr_ $ downcast $ nameActiveThreads := GetVecElementPtr TypeInt32 header (integral TypeInt32 1)
      instr_ $ downcast $ "env" := GetStructElementPtr envTp arg (TupleIdxRight TupleIdxSelf)
      extractEnv
  , LocalReference (PrimType $ PtrPrimType (ScalarPrimType scalarType) defaultAddrSpace) nameIndex
  , LocalReference (PrimType $ PtrPrimType (ScalarPrimType scalarType) defaultAddrSpace) nameActiveThreads
  , gamma
  )
  where
    argTp = PtrPrimType (StructPrimType False (TupRsingle headerType `TupRpair` TupRsingle envTp)) defaultAddrSpace
    (envTp, extractEnv, gamma) = bindEnv env

    nameHeader = "header"
    nameIndex = "worksteal.index"
    nameActiveThreads = "worksteal.activethreads"

    arg = LocalReference (PrimType argTp) "arg"
    header = LocalReference (PrimType (PtrPrimType headerType defaultAddrSpace)) nameHeader
