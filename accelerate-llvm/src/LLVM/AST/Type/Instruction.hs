{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : LLVM.AST.Type.Instruction
-- Copyright   : [2015..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module LLVM.AST.Type.Instruction
  where

import LLVM.AST.Type.Constant                             ( Constant(ScalarConstant) )
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Function
import LLVM.AST.Type.InlineAssembly
import LLVM.AST.Type.Name
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation

import LLVM.AST.Type.Instruction.Atomic                   ( Atomicity, MemoryOrdering )
import LLVM.AST.Type.Instruction.Compare                  ( Ordering(..) )
import LLVM.AST.Type.Instruction.RMW                      ( RMWOperation )
import LLVM.AST.Type.Instruction.Volatile                 ( Volatility )

import qualified LLVM.AST.Constant                        as LLVM ( Constant(GlobalReference, Int) )
import qualified LLVM.AST.CallingConvention               as LLVM
import qualified LLVM.AST.FloatingPointPredicate          as FP
import qualified LLVM.AST.Instruction                     as LLVM
import qualified LLVM.AST.IntegerPredicate                as IP
import qualified LLVM.AST.Operand                         as LLVM ( Operand(..), CallableOperand )
import qualified LLVM.AST.ParameterAttribute              as LLVM ( ParameterAttribute )
import qualified LLVM.AST.RMWOperation                    as LLVM ( RMWOperation )
import qualified LLVM.AST.Type                            as LLVM ( Type(..) )
#if !MIN_VERSION_llvm_hs_pure(15,0,0)
import qualified LLVM.AST.AddrSpace                       as LLVM
#endif

import Data.Array.Accelerate.AST                          ( PrimBool )
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Primitive.Vec

import Prelude                                            hiding ( Ordering(..), quot, rem, div, isNaN, tail )


-- | Non-terminating instructions
--
--  * <http://llvm.org/docs/LangRef.html#binary-operations>
--
--  * <http://llvm.org/docs/LangRef.html#bitwise-binary-operations>
--
--  * <http://llvm.org/docs/LangRef.html#vector-operations>
--
--  * <http://llvm.org/docs/LangRef.html#aggregate-operations>
--
--  * <http://llvm.org/docs/LangRef.html#memory-access-and-addressing-operations>
--
--  * <http://llvm.org/docs/LangRef.html#other-operations>
--
data Instruction a where
  -- Binary Operations
  -- -----------------

  -- <http://llvm.org/docs/LangRef.html#add-instruction>
  -- <http://llvm.org/docs/LangRef.html#fadd-instruction>
  --
  Add             :: NumType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#sub-instruction>
  -- <http://llvm.org/docs/LangRef.html#fsub-instruction>
  --
  Sub             :: NumType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#mul-instruction>
  -- <http://llvm.org/docs/LangRef.html#fmul-instruction>
  --
  Mul             :: NumType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#udiv-instruction>
  -- <http://llvm.org/docs/LangRef.html#sdiv-instruction>
  --
  Quot            :: IntegralType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#urem-instruction>
  -- <http://llvm.org/docs/LangRef.html#srem-instruction>
  --
  Rem             :: IntegralType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#fdiv-instruction>
  --
  Div             :: FloatingType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#shl-instruction>
  --
  ShiftL          :: IntegralType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#lshr-instruction>
  --
  ShiftRL         :: IntegralType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#ashr-instruction>
  --
  ShiftRA         :: IntegralType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  -- Bitwise Binary Operations
  -- -------------------------

  -- <http://llvm.org/docs/LangRef.html#and-instruction>
  --
  BAnd            :: IntegralType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  LAnd            :: Operand Bool
                  -> Operand Bool
                  -> Instruction Bool

  -- <http://llvm.org/docs/LangRef.html#or-instruction>
  --
  BOr             :: IntegralType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  LOr             :: Operand Bool
                  -> Operand Bool
                  -> Instruction Bool

  -- <http://llvm.org/docs/LangRef.html#xor-instruction>
  --
  BXor            :: IntegralType a
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  LNot            :: Operand Bool
                  -> Instruction Bool

  -- Vector Operations
  -- -----------------

  -- <http://llvm.org/docs/LangRef.html#extractelement-instruction>
  --
  ExtractElement  :: Int32  -- TupleIdx (ProdRepr (Vec n a)) a
                  -> Operand (Vec n a)
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#insertelement-instruction>
  --
  InsertElement   :: Int32  -- TupleIdx (ProdRepr (Vec n a)) a
                  -> Operand (Vec n a)
                  -> Operand a
                  -> Instruction (Vec n a)

  -- ShuffleVector

  -- Aggregate Operations
  -- --------------------

  -- <http://llvm.org/docs/LangRef.html#extractvalue-instruction>
  --
  ExtractValue    :: PrimType t
                  -> TupleIdx tup t
                  -> Operand (Struct tup)
                  -> Instruction t

  -- <http://llvm.org/docs/LangRef.html#insertvalue-instruction>
  -- InsertValue

  -- Memory Access and Addressing Operations
  -- ---------------------------------------

  -- <http://llvm.org/docs/LangRef.html#alloca-instruction>
  -- Alloca

  -- <http://llvm.org/docs/LangRef.html#load-instruction>
  --
  Load            :: ScalarType a
                  -> Volatility
                  -> Operand (Ptr a)
                  -> Instruction a

  LoadPtr         :: Volatility
                  -> Operand (Ptr (Ptr a))
                  -> Instruction (Ptr a)

  -- <http://llvm.org/docs/LangRef.html#store-instruction>
  --
  Store           :: Volatility
                  -> Operand (Ptr a)
                  -> Operand a
                  -> Instruction ()

  -- <http://llvm.org/docs/LangRef.html#getelementptr-instruction>
  --
  GetElementPtr   :: ScalarType a
                  -> Operand (Ptr a)
                  -> [Operand i]
                  -> Instruction (Ptr a)

  GetStructElementPtr
                  :: PrimType t
                  -> Operand (Ptr (Struct a))
                  -> TupleIdx a t
                  -> Instruction (Ptr t)

  GetVecElementPtr
                  :: IntegralType i
                  -> Operand (Ptr (Vec n t))
                  -> Operand i
                  -> Instruction (Ptr t)

  -- <http://llvm.org/docs/LangRef.html#i-fence>
  --
  Fence           :: Atomicity
                  -> Instruction ()

  -- <http://llvm.org/docs/LangRef.html#cmpxchg-instruction>
  --
  CmpXchg         :: IntegralType a
                  -> Volatility
                  -> Operand (Ptr a)
                  -> Operand a                  -- expected value
                  -> Operand a                  -- replacement value
                  -> Atomicity                  -- on success
                  -> MemoryOrdering             -- on failure (see docs for restrictions)
                  -> Instruction (Struct (a, Bool))

  -- <http://llvm.org/docs/LangRef.html#atomicrmw-instruction>
  --
  AtomicRMW       :: NumType a
                  -> Volatility
                  -> RMWOperation
                  -> Operand (Ptr a)
                  -> Operand a
                  -> Atomicity
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#trunc-to-instruction>
  --
  Trunc           :: BoundedType a        -- precondition: BitSize a > BitSize b
                  -> BoundedType b
                  -> Operand a
                  -> Instruction b

  IntToBool       :: IntegralType a
                  -> Operand a
                  -> Instruction Bool

  -- <http://llvm.org/docs/LangRef.html#fptrunc-to-instruction>
  --
  FTrunc          :: FloatingType a       -- precondition: BitSize a > BitSize b
                  -> FloatingType b
                  -> Operand a
                  -> Instruction b

  -- <http://llvm.org/docs/LangRef.html#zext-to-instruction>
  -- <http://llvm.org/docs/LangRef.html#sext-to-instruction>
  --
  Ext             :: BoundedType a        -- precondition: BitSize a < BitSize b
                  -> BoundedType b
                  -> Operand a
                  -> Instruction b

  BoolToInt       :: IntegralType a
                  -> Operand Bool
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#fpext-to-instruction>
  --
  FExt            :: FloatingType a       -- precondition: BitSize a < BitSize b
                  -> FloatingType b
                  -> Operand a
                  -> Instruction b

  BoolToFP        :: FloatingType a
                  -> Operand Bool
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#fptoui-to-instruction>
  -- <http://llvm.org/docs/LangRef.html#fptosi-to-instruction>
  --
  FPToInt         :: FloatingType a
                  -> IntegralType b
                  -> Operand a
                  -> Instruction b

  -- <http://llvm.org/docs/LangRef.html#uitofp-to-instruction>
  -- <http://llvm.org/docs/LangRef.html#sitofp-to-instruction>
  --
  IntToFP         :: IntegralType a
                  -> FloatingType b
                  -> Operand a
                  -> Instruction b

  -- <http://llvm.org/docs/LangRef.html#bitcast-to-instruction>
  --
  BitCast         :: ScalarType b         -- precondition: BitSize a == BitSize b
                  -> Operand a
                  -> Instruction b

  PtrCast         :: PrimType (Ptr b)     -- precondition: same address space
                  -> Operand (Ptr a)
                  -> Instruction (Ptr b)

  -- PtrToInt
  -- IntToPtr
  -- AddrSpaceCast

  -- Other Operations
  -- ----------------

  -- <http://llvm.org/docs/LangRef.html#icmp-instruction>
  -- <http://llvm.org/docs/LangRef.html#fcmp-instruction>
  --
  -- We treat non-scalar types as signed/unsigned integer values.
  --
  Cmp             :: SingleType a
                  -> Ordering
                  -> Operand a
                  -> Operand a
                  -> Instruction Bool

  IsNaN           :: FloatingType a
                  -> Operand a
                  -> Instruction Bool

  -- <http://llvm.org/docs/LangRef.html#phi-instruction>
  --
  Phi             :: PrimType a
                  -> [(Operand a, Label)]
                  -> Instruction a

  -- <http://llvm.org/docs/LangRef.html#call-instruction>
  --
  Call            :: Function (Either InlineAssembly Label) t
                  -> Arguments t
                  -> [Either GroupID FunctionAttribute]
                  -> Instruction (Result t)

  -- <http://llvm.org/docs/LangRef.html#select-instruction>
  --
  Select          :: SingleType a
                  -> Operand Bool
                  -> Operand a
                  -> Operand a
                  -> Instruction a

  -- VAArg
  -- LandingPad


-- | Instances of instructions may be given a name, allowing their results to be
-- referenced as Operands. Instructions returning void (e.g. function calls)
-- don't need names.
--
data Named ins a where
  (:=) :: Name a -> ins a -> Named ins a
  Do   :: ins ()          -> Named ins ()


-- | Convert to llvm-hs
--
instance Downcast (Instruction a) LLVM.Instruction where
  downcast = \case
    Add t x y             -> add t (downcast x) (downcast y)
    Sub t x y             -> sub t (downcast x) (downcast y)
    Mul t x y             -> mul t (downcast x) (downcast y)
    Quot t x y            -> quot t (downcast x) (downcast y)
    Rem t x y             -> rem t (downcast x) (downcast y)
    Div _ x y             -> LLVM.FDiv fmf (downcast x) (downcast y) md
    ShiftL _ x i          -> LLVM.Shl nsw nuw (downcast x) (downcast i) md
    ShiftRL _ x i         -> LLVM.LShr exact (downcast x) (downcast i) md
    ShiftRA _ x i         -> LLVM.AShr exact (downcast x) (downcast i) md
    BAnd _ x y            -> LLVM.And (downcast x) (downcast y) md
    LAnd x y              -> LLVM.And (downcast x) (downcast y) md
    BOr _ x y             -> LLVM.Or (downcast x) (downcast y) md
    LOr x y               -> LLVM.Or (downcast x) (downcast y) md
    BXor _ x y            -> LLVM.Xor (downcast x) (downcast y) md
    LNot x                -> LLVM.Xor (downcast x) (LLVM.ConstantOperand (LLVM.Int 1 1)) md
    InsertElement i v x   -> LLVM.InsertElement (downcast v) (downcast x) (constant i) md
    ExtractElement i v    -> LLVM.ExtractElement (downcast v) (constant i) md
    ExtractValue _ i s    -> extractStruct i s
#if MIN_VERSION_llvm_hs_pure(15,0,0)
    Load t v p            -> LLVM.Load (downcast v) (downcast t) (downcast p) atomicity alignment md
    LoadPtr v p           -> LLVM.Load (downcast v) (downcast $ typeOf p) (downcast p) atomicity alignment md
    GetElementPtr t n i   -> LLVM.GetElementPtr inbounds (downcast t) (downcast n) (downcast i) md
    GetStructElementPtr _ n i -> case typeOf n of
      (PrimType (PtrPrimType t@(StructPrimType _ tp) _)) ->
                             LLVM.GetElementPtr inbounds (downcast t) (downcast n) [constant (0 :: Int), constant (fromIntegral $ tupleIdxToInt tp i :: Int32)] md
      _ -> internalError "Struct ptr impossible"
    GetVecElementPtr _ n i -> case typeOf n of
      (PrimType (PtrPrimType t _)) ->
        LLVM.GetElementPtr inbounds (downcast t) (downcast n) [constant (0 :: Int), downcast i] md
      _ -> internalError "Ptr impossible"
#else
    Load _ v p            -> LLVM.Load (downcast v) (downcast p) atomicity alignment md
    LoadPtr v p           -> LLVM.Load (downcast v) (downcast p) atomicity alignment md
    GetElementPtr _ n i   -> LLVM.GetElementPtr inbounds (downcast n) (downcast i) md
    GetStructElementPtr _ n i -> case typeOf n of
      PrimType (PtrPrimType (StructPrimType _ tp) _) ->
                             LLVM.GetElementPtr inbounds (downcast n) [constant (0 :: Int), constant (fromIntegral $ tupleIdxToInt tp i :: Int32)] md
      _ -> internalError "Struct ptr impossible"
    GetVecElementPtr _ n i -> LLVM.GetElementPtr inbounds (downcast n) [constant (0 :: Int), downcast i] md
#endif
    Store v p x           -> LLVM.Store (downcast v) (downcast p) (downcast x) atomicity alignment md
    Fence a               -> LLVM.Fence (downcast a) md
    CmpXchg _ v p x y a m -> cmpXchg (downcast v) (downcast p) (downcast x) (downcast y) (downcast a) (downcast m) md
    AtomicRMW t v f p x a -> atomicRMW (downcast v) (downcast (t,f)) (downcast p) (downcast x) (downcast a) md
    Trunc _ t x           -> LLVM.Trunc (downcast x) (downcast t) md
    IntToBool _ x         -> LLVM.Trunc (downcast x) (LLVM.IntegerType 1) md
    FTrunc _ t x          -> LLVM.FPTrunc (downcast x) (downcast t) md
    Ext a b x             -> ext a b (downcast x)
    BoolToInt a x         -> LLVM.ZExt (downcast x) (downcast a) md
    BoolToFP x a          -> LLVM.UIToFP (downcast a) (downcast x) md
    FExt _ t x            -> LLVM.FPExt (downcast x) (downcast t) md
    FPToInt _ b x         -> float2int b (downcast x)
    IntToFP a b x         -> int2float a b (downcast x)
    BitCast t x           -> LLVM.BitCast (downcast x) (downcast t) md
    PtrCast t x           -> LLVM.BitCast (downcast x) (downcast t) md
    Phi t e               -> LLVM.Phi (downcast t) (downcast e) md
    Select _ p x y        -> LLVM.Select (downcast p) (downcast x) (downcast y) md
    IsNaN _ x             -> isNaN (downcast x)
    Cmp t p x y           -> cmp t p (downcast x) (downcast y)
    Call f args a         -> call f args a

    where
      nsw :: Bool       -- no signed wrap
      nsw = False

      nuw :: Bool       -- no unsigned wrap
      nuw = False

      exact :: Bool     -- does not lose any information
      exact = False

      inbounds :: Bool
      inbounds = True

      atomicity :: Maybe LLVM.Atomicity
      atomicity = Nothing

      alignment :: Word32
      alignment = 0

      fmf :: LLVM.FastMathFlags
#if MIN_VERSION_llvm_hs_pure(6,0,0)
      fmf = LLVM.FastMathFlags
              { LLVM.allowReassoc    = True
              , LLVM.noNaNs          = True
              , LLVM.noInfs          = True
              , LLVM.noSignedZeros   = True
              , LLVM.allowReciprocal = True
              , LLVM.allowContract   = True
              , LLVM.approxFunc      = True
              }
#else
      fmf = LLVM.UnsafeAlgebra -- allow everything
#endif

      -- LLVM 13 added optional alignment parameters. These behave differently from
      -- the alignment in the load and store instructions though. An alignment of 0
      -- here means that the alignment is the same as the size of the type, while an
      -- alignment of 0 in those instructions means that the alignment is defined by
      -- the ABI.
      --
      cmpXchg   :: Bool -> LLVM.Operand -> LLVM.Operand -> LLVM.Operand -> LLVM.Atomicity -> LLVM.MemoryOrdering -> LLVM.InstructionMetadata -> LLVM.Instruction
      atomicRMW :: Bool -> LLVM.RMWOperation -> LLVM.Operand -> LLVM.Operand -> LLVM.Atomicity -> LLVM.InstructionMetadata -> LLVM.Instruction
#if MIN_VERSION_llvm_hs_pure(13,0,0)
      cmpXchg volatile address expected replacement atomicity' failureMemoryOrdering metadata =
        LLVM.CmpXchg volatile address expected replacement alignment atomicity' failureMemoryOrdering metadata
      atomicRMW volatile rmwOperation address value atomicity' metadata =
        LLVM.AtomicRMW volatile rmwOperation address value alignment atomicity' metadata
#else
      cmpXchg volatile address expected replacement atomicity' failureMemoryOrdering metadata =
        LLVM.CmpXchg volatile address expected replacement atomicity' failureMemoryOrdering metadata
      atomicRMW volatile rmwOperation address value atomicity' metadata =
        LLVM.AtomicRMW volatile rmwOperation address value atomicity' metadata
#endif

      md :: LLVM.InstructionMetadata
      md = []

      constant :: IsScalar a => a -> LLVM.Operand
      constant x = downcast (ConstantOperand (ScalarConstant scalarType x))

      add :: NumType a -> LLVM.Operand -> LLVM.Operand -> LLVM.Instruction
      add IntegralNumType{} x y = LLVM.Add nsw nuw x y md
      add FloatingNumType{} x y = LLVM.FAdd fmf    x y md

      sub :: NumType a -> LLVM.Operand -> LLVM.Operand -> LLVM.Instruction
      sub IntegralNumType{} x y = LLVM.Sub nsw nuw x y md
      sub FloatingNumType{} x y = LLVM.FSub fmf    x y md

      mul :: NumType a -> LLVM.Operand -> LLVM.Operand -> LLVM.Instruction
      mul IntegralNumType{} x y = LLVM.Mul nsw nuw x y md
      mul FloatingNumType{} x y = LLVM.FMul fmf    x y md

      quot :: IntegralType a -> LLVM.Operand -> LLVM.Operand -> LLVM.Instruction
      quot t x y
        | signed t  = LLVM.SDiv exact x y md
        | otherwise = LLVM.UDiv exact x y md

      rem :: IntegralType a -> LLVM.Operand -> LLVM.Operand -> LLVM.Instruction
      rem t x y
        | signed t  = LLVM.SRem x y md
        | otherwise = LLVM.URem x y md

      extractStruct :: TupleIdx s t -> Operand (Struct s) -> LLVM.Instruction
      extractStruct ix s = LLVM.ExtractValue (downcast s) [fromIntegral int] md
        where
          int = case typeOf s of
            PrimType (StructPrimType _ tuple) -> tupleIdxToInt tuple ix
            _ -> internalError "Struct impossible"

      ext :: BoundedType a -> BoundedType b -> LLVM.Operand -> LLVM.Instruction
      ext a (downcast -> b) x
        | signed a  = LLVM.SExt x b md
        | otherwise = LLVM.ZExt x b md

      float2int :: IntegralType b -> LLVM.Operand -> LLVM.Instruction
      float2int t@(downcast -> t') x
        | signed t  = LLVM.FPToSI x t' md
        | otherwise = LLVM.FPToUI x t' md

      int2float :: IntegralType a -> FloatingType b -> LLVM.Operand -> LLVM.Instruction
      int2float a (downcast -> b) x
        | signed a  = LLVM.SIToFP x b md
        | otherwise = LLVM.UIToFP x b md

      isNaN :: LLVM.Operand -> LLVM.Instruction
      isNaN x = LLVM.FCmp FP.UNO x x md

      cmp :: SingleType a -> Ordering -> LLVM.Operand -> LLVM.Operand -> LLVM.Instruction
      cmp t p x y =
        case t of
          NumSingleType FloatingNumType{} -> LLVM.FCmp (fp p) x y md
          _ | signed t                    -> LLVM.ICmp (si p) x y md
            | otherwise                   -> LLVM.ICmp (ui p) x y md
        where
          fp :: Ordering -> FP.FloatingPointPredicate
          fp EQ = FP.OEQ
          fp NE = FP.ONE
          fp LT = FP.OLT
          fp LE = FP.OLE
          fp GT = FP.OGT
          fp GE = FP.OGE

          si :: Ordering -> IP.IntegerPredicate
          si EQ = IP.EQ
          si NE = IP.NE
          si LT = IP.SLT
          si LE = IP.SLE
          si GT = IP.SGT
          si GE = IP.SGE

          ui :: Ordering -> IP.IntegerPredicate
          ui EQ = IP.EQ
          ui NE = IP.NE
          ui LT = IP.ULT
          ui LE = IP.ULE
          ui GT = IP.UGT
          ui GE = IP.UGE

      call :: Function (Either InlineAssembly Label) t -> Arguments t -> [Either GroupID FunctionAttribute] -> LLVM.Instruction
#if MIN_VERSION_llvm_hs_pure(15,0,0)
      call f args as = LLVM.Call tail LLVM.C [] fun_ty target (travArgs args) (downcast as) md
#else
      call f args as = LLVM.Call tail LLVM.C []        target (travArgs args) (downcast as) md
#endif
        where
          trav :: Function (Either InlineAssembly Label) t
               -> ( [LLVM.Type]                                 -- argument types
                  , Maybe LLVM.TailCallKind                     -- calling kind
                  , LLVM.Type                                   -- return type
                  , LLVM.CallableOperand                        -- function name or inline assembly
                  )
          trav (Body u k o) =
            case o of
              Left asm -> ([], downcast k, downcast u, Left  (downcast (LLVM.FunctionType ret argt False, asm)))
#if MIN_VERSION_llvm_hs_pure(15,0,0)
              Right n  -> ([], downcast k, downcast u, Right (LLVM.ConstantOperand (LLVM.GlobalReference (downcast n))))
#else
              Right n  -> ([], downcast k, downcast u, Right (LLVM.ConstantOperand (LLVM.GlobalReference ptr_fun_ty (downcast n))))
#endif
          trav (Lam t _ l)  =
            let (ts, k, r, n) = trav l
            in  (downcast t : ts, k, r, n)

          travArgs :: Arguments t -> [(LLVM.Operand, [LLVM.ParameterAttribute])]
          travArgs (ArgumentsCons operand attrs args') = (downcast operand, attrs) : travArgs args'
          travArgs ArgumentsNil = []

          (argt, tail, ret, target) = trav f
          fun_ty                          = LLVM.FunctionType ret argt False
#if !MIN_VERSION_llvm_hs_pure(15,0,0)
          ptr_fun_ty                      = LLVM.PointerType fun_ty (LLVM.AddrSpace 0)
#endif


instance Downcast (i a) i' => Downcast (Named i a) (LLVM.Named i') where
  downcast (x := op) = downcast x LLVM.:= downcast op
  downcast (Do op)   = LLVM.Do (downcast op)


instance TypeOf Instruction where
  typeOf = \case
    Add _ x _             -> typeOf x
    Sub _ x _             -> typeOf x
    Mul _ x _             -> typeOf x
    Quot _ x _            -> typeOf x
    Rem _ x _             -> typeOf x
    Div _ x _             -> typeOf x
    ShiftL _ x _          -> typeOf x
    ShiftRL _ x _         -> typeOf x
    ShiftRA _ x _         -> typeOf x
    BAnd _ x _            -> typeOf x
    BOr _ x _             -> typeOf x
    BXor _ x _            -> typeOf x
    LAnd x _              -> typeOf x
    LOr x _               -> typeOf x
    LNot x                -> typeOf x
    ExtractElement _ x    -> typeOfVec x
    InsertElement _ x _   -> typeOf x
    ExtractValue t _ _    -> PrimType t
    Load t _ _            -> scalar t
    LoadPtr _ x           -> case typeOf x of
      PrimType (PtrPrimType t _) -> PrimType t
      _ -> internalError "Ptr impossible"
    Store{}               -> VoidType
    GetElementPtr _ x _   -> typeOf x
    GetStructElementPtr t x _ -> case typeOf x of
      PrimType (PtrPrimType _ addr) -> PrimType $ PtrPrimType t addr
      _ -> internalError "Ptr impossible"
    GetVecElementPtr _ x _ -> case typeOf x of
      PrimType (PtrPrimType (ScalarPrimType (VectorScalarType (VectorType _ tp))) addr)
        -> PrimType $ PtrPrimType (ScalarPrimType $ SingleScalarType tp) addr
      _ -> internalError "Vec ptr impossible"
    Fence{}               -> VoidType
    CmpXchg t _ _ _ _ _ _ -> PrimType . StructPrimType False $ ScalarPrimType (SingleScalarType (NumSingleType (IntegralNumType t))) `pair` primType
    AtomicRMW _ _ _ _ x _ -> typeOf x
    FTrunc _ t _          -> floating t
    FExt _ t _            -> floating t
    Trunc _ t _           -> bounded t
    Ext _ t _             -> bounded t
    FPToInt _ t _         -> integral t
    IntToFP _ t _         -> floating t
    IntToBool _ _         -> type'
    BoolToInt t _         -> integral t
    BoolToFP t _          -> floating t
    BitCast t _           -> scalar t
    PtrCast t _           -> PrimType t
    Cmp{}                 -> type'
    IsNaN{}               -> type'
    Phi t _               -> PrimType t
    Select _ _ x _        -> typeOf x
    Call f _ _            -> fun f
    where
      typeOfVec :: HasCallStack => Operand (Vec n a) -> Type a
      typeOfVec x
        | PrimType p          <- typeOf x
        , ScalarPrimType s    <- p
        , VectorScalarType v  <- s
        , VectorType _ t      <- v
        = PrimType (ScalarPrimType (SingleScalarType t))
        --
        | otherwise
        = internalError "unexpected evaluation"

      scalar :: ScalarType a -> Type a
      scalar = PrimType . ScalarPrimType

      single :: SingleType a -> Type a
      single = scalar . SingleScalarType

      floating :: FloatingType a -> Type a
      floating = single . NumSingleType . FloatingNumType

      integral :: IntegralType a -> Type a
      integral = single . NumSingleType . IntegralNumType

      pair :: PrimType a -> PrimType b -> TupR PrimType (a, b)
      pair a b = TupRsingle a `TupRpair` TupRsingle b

      bounded :: BoundedType a -> Type a
      bounded (IntegralBoundedType t) = integral t

      fun :: Function kind a -> Type (Result a)
      fun (Lam _ _ l)  = fun l
      fun (Body t _ _) = t

