{-# LANGUAGE CPP             #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE RecordWildCards #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Execute.Environment
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@nvidia.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Execute.Environment (

  Async(..), Aval(..), Event, Stream,
  aprj, after, wait, streaming,

) where

-- accelerate
import Data.Array.Accelerate.AST

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Array.Accelerate.LLVM.PTX.Execute.Event             ( Event )
import Data.Array.Accelerate.LLVM.PTX.Execute.Stream            ( Stream )
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Event   as Event
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Stream  as Stream

-- standard library
import Control.Monad.State

#include "accelerate.h"


-- Asynchronous kernel execution
-- -----------------------------

-- Arrays with an associated CUDA Event that will be signalled once the
-- computation has completed.
--
data Async a = Async {-# UNPACK #-} !Event !a


-- Valuation for an environment of array computations
--
data Aval env where
  Aempty :: Aval ()
  Apush  :: Aval env -> Async t -> Aval (env, t)


-- Projection of a value from a valuation using a de Bruijn index.
--
aprj :: Idx env t -> Aval env -> Async t
aprj ZeroIdx       (Apush _   x) = x
aprj (SuccIdx idx) (Apush val _) = aprj idx val
aprj _             _             = INTERNAL_ERROR(error) "aprj" "inconsistent valuation"


-- All work submitted to the given stream will occur after the asynchronous
-- event for the given array has been fulfilled. Synchronisation is performed
-- efficiently on the device. This function returns immediately.
--
after :: MonadIO m => Stream -> Async a -> m a
after stream (Async event arr) = liftIO $ Event.after event stream >> return arr


-- Block the calling thread until the event for the given array computation
-- is recorded.
--
wait :: MonadIO m => Async a -> m a
wait (Async e x) = liftIO $ Event.block e >> return x


-- Execute the given computation in a unique execution stream.
--
streaming
    :: (Stream -> LLVM PTX a)
    -> (Async a -> LLVM PTX b)
    -> LLVM PTX b
streaming first second = do
  PTX{..} <- gets llvmTarget
  Stream.streaming ptxContext ptxStreamReservoir first (\e a -> second (Async e a))

