{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
  where

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Partitioned

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.Compile.Cache

import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop

import LLVM.AST.Type.Function                                       as LLVM
import LLVM.AST.Type.Global
import LLVM.AST.Type.Name
import LLVM.AST.Type.Module

import Data.Typeable

mkGenerate
    :: forall genv sh e.
       UID
    -> Label
    -> Env AccessGroundR genv
    -> Arg genv (Out sh e)
    -> Arg genv (Fun' (sh -> e))
    -> LLVM Native (Module (MarshalScalars sh (MarshalScalars sh (MarshalFun genv))))
mkGenerate uid name env array@(ArgArray _ (ArrayR shr _) _ _) fun
  | (Refl, bindRange, start, end) <- bindWorkRange @sh @(MarshalFun genv) shr
  , (Refl, bindEnv, gamma) <- bindParameters @genv @() env
  = codeGenFunction uid "generate" (bindRange . bindEnv) $ do
      return ()

  -- bindRange $ bindEnv $ LLVM.Body VoidType name body
{-
-- Construct a new array by applying a function to each index. Each thread
-- processes multiple adjacent elements.
--
mkGenerate
    :: UID
    -> Gamma aenv
    -> ArrayR (Array sh e)
    -> IRFun1  Native aenv (sh -> e)
    -> CodeGen Native      (IROpenAcc Native aenv (Array sh e))
mkGenerate uid aenv repr apply =
  let
      (start, end, paramGang)   = gangParam (arrayRshape repr)
      (arrOut, paramOut)        = mutableArray repr "out"
      paramEnv                  = envParam aenv
      shOut                     = irArrayShape arrOut
  in
  makeOpenAcc uid "generate" (paramGang ++ paramOut ++ paramEnv) $ do

    imapNestFromTo (arrayRshape repr) start end shOut $ \ix i -> do
      r <- app1 apply ix                        -- apply generator function
      writeArray TypeInt arrOut i r             -- store result
-}
