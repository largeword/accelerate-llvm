{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Native.Loop
-- Copyright   : [2014..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Loop
  where

-- accelerate
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape                   hiding ( eq )

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic                as A
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop            as Loop

import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )

import LLVM.AST.Type.Representation
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Atomic
import LLVM.AST.Type.Instruction.Volatile
import qualified LLVM.AST.Type.Instruction.RMW as RMW

-- | A standard 'for' loop, that steps from the start to end index executing the
-- given function at each index.
--
imapFromTo
    :: Operands Int                                   -- ^ starting index (inclusive)
    -> Operands Int                                   -- ^ final index (exclusive)
    -> (Operands Int -> CodeGen Native ())            -- ^ apply at each index
    -> CodeGen Native ()
imapFromTo start end body =
  Loop.imapFromStepTo start (liftInt 1) end body


-- | Generate a series of nested 'for' loops which iterate between the start and
-- end indices of a given hyper-rectangle. LLVM is very good at vectorising
-- these kinds of nested loops, but not so good at vectorising the flattened
-- representation utilising to/from index.
--
imapNestFromTo
    :: ShapeR sh
    -> Operands sh                                          -- ^ initial index (inclusive)
    -> Operands sh                                          -- ^ final index (exclusive)
    -> Operands sh                                          -- ^ total array extent
    -> (Operands sh -> Operands Int -> CodeGen Native ())   -- ^ apply at each index
    -> CodeGen Native ()
imapNestFromTo shr start end extent body =
  go shr start end body'
  where
    body' ix = body ix =<< intOfIndex shr extent ix

    go :: ShapeR t -> Operands t -> Operands t -> (Operands t -> CodeGen Native ()) -> CodeGen Native ()
    go ShapeRz OP_Unit OP_Unit k
      = k OP_Unit

    go (ShapeRsnoc shr') (OP_Pair ssh ssz) (OP_Pair esh esz) k
      = go shr' ssh esh
      $ \sz      -> imapFromTo ssz esz
      $ \i       -> k (OP_Pair sz i)


{--
-- TLM: this version (seems to) compute the corresponding linear index as it
--      goes. We need to compare it against the above implementation to see if
--      there are any advantages.
--
imapNestFromTo'
    :: forall sh. Shape sh
    => Operands sh
    -> Operands sh
    -> Operands sh
    -> (Operands sh -> Operands Int -> CodeGen Native ())
    -> CodeGen Native ()
imapNestFromTo' start end extent body = do
  startl <- intOfIndex extent start
  void $ go (eltType @sh) start end extent (int 1) startl body'
  where
    body' :: Operands (EltRepr sh) -> Operands Int -> CodeGen Native (Operands Int)
    body' ix l = body ix l >> add numType (int 1) l

    go :: TupleType t
       -> Operands t
       -> Operands t
       -> Operands t
       -> Operands Int
       -> Operands Int
       -> (Operands t -> Operands Int -> CodeGen Native (Operands Int))
       -> CodeGen Native (Operands Int)
    go TypeRunit OP_Unit OP_Unit OP_Unit _delta l k
      = k OP_Unit l

    go (TypeRpair tsh tsz) (OP_Pair ssh ssz) (OP_Pair esh esz) (OP_Pair exh exz) delta l k
      | TypeRscalar t <- tsz
      , Just Refl     <- matchScalarType t (scalarType :: ScalarType Int)
      = do
          delta' <- mul numType delta exz
          go tsh ssh esh exh delta' l $ \sz ll -> do
            Loop.iterFromStepTo ssz (int 1) esz ll $ \i l' ->
              k (OP_Pair sz i) l'
            add numType ll delta'

    go _ _ _ _ _ _ _
      = $internalError "imapNestFromTo'" "expected shape with Int components"
--}

{--
-- | Generate a series of nested 'for' loops which iterate between the start and
-- end indices of a given hyper-rectangle. LLVM is very good at vectorising
-- these kinds of nested loops, but not so good at vectorising the flattened
-- representation utilising to/from index.
--
imapNestFromStepTo
    :: forall sh. Shape sh
    => Operands sh                                    -- ^ initial index (inclusive)
    -> Operands sh                                    -- ^ steps
    -> Operands sh                                    -- ^ final index (exclusive)
    -> Operands sh                                    -- ^ total array extent
    -> (Operands sh -> Operands Int -> CodeGen Native ())   -- ^ apply at each index
    -> CodeGen Native ()
imapNestFromStepTo start steps end extent body =
  go (eltType @sh) start steps end (body' . IR)
  where
    body' ix = body ix =<< intOfIndex extent ix

    go :: TupleType t -> Operands t -> Operands t -> Operands t -> (Operands t -> CodeGen Native ()) -> CodeGen Native ()
    go TypeRunit OP_Unit OP_Unit OP_Unit k
      = k OP_Unit

    go (TypeRpair tsh tsz) (OP_Pair ssh ssz) (OP_Pair sts stz) (OP_Pair esh esz) k
      | TypeRscalar t <- tsz
      , Just Refl     <- matchScalarType t (scalarType :: ScalarType Int)
      = go tsh ssh sts esh
      $ \sz      -> Loop.imapFromStepTo ssz stz esz
      $ \i       -> k (OP_Pair sz i)

    go _ _ _ _ _
      = $internalError "imapNestFromTo" "expected shape with Int components"
--}

-- | Iterate with an accumulator between the start and end index, executing the
-- given function at each.
--
iterFromTo
    :: TypeR a
    -> Operands Int                                       -- ^ starting index (inclusive)
    -> Operands Int                                       -- ^ final index (exclusive)
    -> Operands a                                         -- ^ initial value
    -> (Operands Int -> Operands a -> CodeGen Native (Operands a))    -- ^ apply at each index
    -> CodeGen Native (Operands a)
iterFromTo tp start end seed body =
  Loop.iterFromStepTo tp start (liftInt 1) end seed body

workstealLoop
    :: Operand (Ptr Int32)
    -> Operand (Ptr Int32)
    -> Operand Int32
    -> (Operand Int32 -> CodeGen Native ())
    -> CodeGen Native ()
workstealLoop counter activeThreads size doWork = do
  start    <- newBlock "worksteal.start"
  work     <- newBlock "worksteal.loop.work"
  exit     <- newBlock "worksteal.exit"
  exitLast <- newBlock "worksteal.exit.last"
  finished <- newBlock "worksteal.finished"

  -- Check whether there might be work for us
  initialCounter <- instr' $ Load scalarType NonVolatile counter
  initialCondition <- lt singleType (OP_Int32 initialCounter) (OP_Int32 size)
  cbr initialCondition start finished

  setBlock start
  -- Might be work for us!
  -- First mark that this thread is doing work.
  atomicAdd Acquire activeThreads (integral TypeInt32 1)
  startIndex <- atomicAdd Unordered counter (integral TypeInt32 1)
  startCondition <- lt singleType (OP_Int32 startIndex) (OP_Int32 size)
  cbr startCondition work exit

  setBlock work
  indexName <- freshLocalName
  let index = LocalReference type' indexName

  -- Already claim the next work, to hide the latency of the atomic instruction
  nextIndex <- atomicAdd Unordered counter (integral TypeInt32 1)

  doWork index
  condition <- lt singleType (OP_Int32 nextIndex) (OP_Int32 size)

  -- Append the phi node to the start of the 'work' block.
  -- We can only do this now, as we need to have 'nextIndex', and know the
  -- exit block of 'doWork'.
  currentBlock <- getBlock
  phi1 work indexName [(startIndex, start), (nextIndex, currentBlock)]

  cbr condition work exit

  setBlock exit
  -- Decrement activeThreads
  remaining <- atomicAdd Release activeThreads (integral TypeInt32 (-1))
  -- If 'activeThreads' was 1 (now 0), then all work is definitely done.
  -- Note that there may be multiple threads returning true here.
  -- It is guaranteed that at least one thread returns true.
  allDone <- eq singleType (OP_Int32 remaining) (liftInt32 1)
  retval_ $ op BoolPrimType allDone

  setBlock finished
  -- Work was already finished
  retval_ $ boolean False

workstealChunked :: ShapeR sh -> Operand (Ptr Int32) -> Operand (Ptr Int32) -> Operands sh -> (Operands sh -> Operands Int -> CodeGen Native ()) -> CodeGen Native ()
workstealChunked shr counter activeThreads sh doWork = do
  let chunkSz = chunkSize shr
  chunkCounts <- chunkCount shr sh chunkSz
  chunkCnt <- shapeSize shr chunkCounts
  chunkCnt' :: Operand Int32 <- instr' $ Trunc boundedType boundedType $ op TypeInt chunkCnt

  workstealLoop counter activeThreads chunkCnt' $ \chunkLinearIndex -> do
    chunkLinearIndex' <- instr' $ Ext boundedType boundedType chunkLinearIndex
    chunkIndex <- indexOfInt shr chunkCounts (OP_Int chunkLinearIndex')
    start <- chunkStart shr chunkSz chunkIndex
    end <- chunkEnd shr sh chunkSz start

    imapNestFromTo shr start end sh doWork

chunkSize :: ShapeR sh -> sh
chunkSize ShapeRz = ()
chunkSize (ShapeRsnoc ShapeRz) = ((), 1024 * 16)
chunkSize (ShapeRsnoc (ShapeRsnoc ShapeRz)) = (((), 64), 64)
chunkSize (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc ShapeRz))) = ((((), 16), 16), 32)
chunkSize (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc (ShapeRsnoc sh)))) = ((((go sh, 8), 8), 16), 16)
  where
    go :: ShapeR sh' -> sh'
    go ShapeRz = ()
    go (ShapeRsnoc sh') = (go sh', 1)

chunkCount :: ShapeR sh -> Operands sh -> sh -> CodeGen Native (Operands sh)
chunkCount ShapeRz OP_Unit () = return OP_Unit
chunkCount (ShapeRsnoc shr) (OP_Pair sh sz) (chunkSh, chunkSz) = do
  counts <- chunkCount shr sh chunkSh
  
  -- Compute ceil(sz / chunkSz), as
  -- (sz + chunkSz - 1) `quot` chunkSz
  sz' <- add numType sz (liftInt $ chunkSz - 1)
  count <- A.quot TypeInt sz' $ liftInt chunkSz

  return $ OP_Pair counts count

chunkStart :: ShapeR sh -> sh -> Operands sh -> CodeGen Native (Operands sh)
chunkStart ShapeRz () OP_Unit = return OP_Unit
chunkStart (ShapeRsnoc shr) (chunkSh, chunkSz) (OP_Pair sh sz) = do
  ixs <- chunkStart shr chunkSh sh
  ix <- mul numType sz $ liftInt chunkSz
  return $ OP_Pair ixs ix

chunkEnd
  :: ShapeR sh
  -> Operands sh -- Array sizee
  -> sh          -- Chunk size
  -> Operands sh -- Chunk start
  -> CodeGen Native (Operands sh) -- Chunk end
chunkEnd ShapeRz OP_Unit () OP_Unit = return OP_Unit
chunkEnd (ShapeRsnoc shr) (OP_Pair sh0 sz0) (sh1, sz1) (OP_Pair sh2 sz2) = do
  sh3 <- chunkStart shr sh1 sh2
  sz3 <- add numType sz2 $ liftInt sz1
  sz3' <- A.min singleType sz3 sz0
  return $ OP_Pair sh3 sz3'

atomicAdd :: MemoryOrdering -> Operand (Ptr Int32) -> Operand Int32 -> CodeGen Native (Operand Int32)
atomicAdd ordering ptr increment = do
  instr' $ AtomicRMW numType NonVolatile RMW.Add ptr increment (CrossThread, ordering)
