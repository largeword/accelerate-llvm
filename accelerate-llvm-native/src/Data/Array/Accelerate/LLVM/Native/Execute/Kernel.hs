{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute.Kernel
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute.Kernel where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Array.Unique
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Lifetime
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.LLVM.CodeGen.Environment       ( MarshalArg, marshalScalarArg )
import Data.Array.Accelerate.LLVM.Native.Kernel
import Data.Array.Accelerate.LLVM.Native.Execute.Marshal
import Data.Primitive.Vec

import Control.Concurrent

import Foreign.Ptr
import Foreign.Marshal.Alloc
import Foreign.Storable
import Data.Typeable

foreign import ccall "dynamic"  
  callKernelPtr :: FunPtr (Ptr () -> IO ()) -> Ptr () -> IO ()

callKernel :: forall env f. Val env -> NativeKernelMetadata f -> KernelFun NativeKernel f -> SArgs env f -> IO ()
callKernel env (NativeKernelMetadata envSize) fun args =
  -- Allocate memory to store the arguments to the function.
  -- Align by 2 cache lines.
  allocaBytesAligned envSize (cacheLineSize * 2) $ \envPtr -> do
    putStrLn "Trying to launch kernel"
    let
      go :: Int -> OpenKernelFun NativeKernel kenv f' -> SArgs env f' -> IO ()
      go cursor (KernelFunBody (NativeKernel _ funLifetime)) ArgsNil
        | cursor == envSize =
          withLifetime funLifetime $ \funPtr -> do
            let ptr' = castFunPtrToPtr funPtr :: Ptr Int8
            let ptr'' = plusPtr ptr' 11 :: Ptr Int8
            putStrLn "Starting"
            print (funPtr, envPtr)
            a <- callKernelPtr (castFunPtr funPtr) nullPtr -- (castPtr envPtr)
            putStrLn "Done!"
        | otherwise = internalError "Cursor and size do not match. callKernel and sizeOfEnv might be inconsistent."
      go cursor (KernelFunLam argR fun') (arg :>: args') = do
        let (align, size) = alignmentAndSizeOfArgument argR
        let aligned = makeAligned cursor align
        let ptr = plusPtr envPtr aligned
        withArg env argR ptr arg $ go (aligned + size) fun' args'

    go 0 fun args


-- Writes the argument to the struct. This function is in the with-resource style,
-- to ensure that the arguments stay live while executing the kernel.
--
withArg :: Val env -> KernelArgR t s -> Ptr (MarshalArg s) -> SArg env t -> IO () -> IO ()
withArg env (KernelArgRbuffer _ _) ptr (SArgBuffer _ var) action = do
  let Buffer ua = prj (varIdx var) env
  withUniqueArrayPtr ua $ \bufferPtr -> do
    poke ptr bufferPtr
    action
withArg env (KernelArgRscalar (SingleScalarType tp)) ptr (SArgScalar var) action
  | SingleDict <- singleDict tp
  , Refl <- marshalScalarArg (SingleScalarType tp) = do
    let value = prj (varIdx var) env
    poke ptr value
    action
withArg env (KernelArgRscalar (VectorScalarType (VectorType _ (tp :: SingleType u)))) ptr (SArgScalar var) action
  | SingleDict <- singleDict tp = do
    let
      ptr' :: Ptr u
      ptr' = castPtr ptr
      value = prj (varIdx var) env
      go :: Int -> [u] -> IO ()
      go _ [] = return ()
      go i (v:vs) = do
        pokeElemOff ptr' i v
        go (i + 1) vs
    go 0 $ listOfVec value
    action

cacheLineSize :: Int
cacheLineSize = 64
