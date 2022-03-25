{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : LLVM.AST.Type.Module
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module LLVM.AST.Type.Module
  where

import LLVM.AST.Type.Downcast
import qualified LLVM.AST                                 as LLVM
import qualified LLVM.AST.DataLayout                      as LLVM
import LLVM.AST.Type.Global

import Data.ByteString.Short


-- | A compiled module consists of a number of global functions (kernels). The
-- module additionally includes a map from the callable function definitions to
-- the metadata for that function.
--
data Module a
  = Module { moduleName             :: ShortByteString
           , moduleSourceFileName   :: ShortByteString
           , moduleDataLayout       :: Maybe LLVM.DataLayout
           , moduleTargetTriple     :: Maybe ShortByteString
           , moduleMain             :: GlobalFunctionDefinition a
           , moduleOtherDefinitions :: [LLVM.Definition]
           }

instance Downcast (Module t) LLVM.Module where
  downcast (Module name source dataLayout target main other) = LLVM.Module name source dataLayout target (LLVM.GlobalDefinition (downcast main) : other)

