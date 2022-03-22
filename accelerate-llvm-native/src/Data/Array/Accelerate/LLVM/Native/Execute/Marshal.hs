{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute.Marshal
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute.Marshal
  where

-- accelerate
import Data.Array.Accelerate.Array.Unique
import Data.Array.Accelerate.Array.Buffer

-- libraries
import qualified Foreign.LibFFI                                 as FFI

marshalInt :: Int -> FFI.Arg
marshalInt = FFI.argInt

marshalBuffer :: Buffer t -> FFI.Arg
marshalBuffer (Buffer ua) = FFI.argPtr $ unsafeUniqueArrayPtr ua

