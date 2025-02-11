-- |
-- Module: Covenant.Prim
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, farseen@mlabs.city, sean@mlabs.city
--
-- Contains definitions relating to Plutus primitive functions in Covenant
-- programs.
--
-- @since 1.0.0
module Covenant.Prim
  ( OneArgFunc (..),
    TwoArgFunc (..),
    ThreeArgFunc (..),
    SixArgFunc (..),
    typeOfOneArgFunc,
    typeOfTwoArgFunc,
    typeOfThreeArgFunc,
    typeOfSixArgFunc,
  )
where

import Covenant.Constant
  ( TyExpr
      ( TyBoolean,
        TyByteString,
        TyInteger,
        TyList,
        TyPair,
        TyPlutusData,
        TyString,
        TyUnit
      ),
  )
import Test.QuickCheck (Arbitrary (arbitrary), elements)

-- | All one-argument primitives provided by Plutus.
--
-- @since 1.0.0
data OneArgFunc
  = LengthOfByteString
  | Sha2_256
  | Sha3_256
  | Blake2b_256
  | EncodeUtf8
  | DecodeUtf8
  | FstPair
  | SndPair
  | HeadList
  | TailList
  | NullList
  | MapData
  | ListData
  | IData
  | BData
  | UnConstrData
  | UnMapData
  | UnListData
  | UnIData
  | UnBData
  | SerialiseData
  | MkNilData
  | MkNilPairData
  | BLS12_381_G1_neg
  | BLS12_381_G1_compress
  | BLS12_381_G1_uncompress
  | BLS12_381_G2_neg
  | BLS12_381_G2_compress
  | BLS12_381_G2_uncompress
  | Keccak_256
  | Blake2b_244
  | ComplementByteString
  | CountSetBits
  | FindFirstSetBit
  | Ripemd_160
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | Does not shrink.
--
-- @since 1.0.0
instance Arbitrary OneArgFunc where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    elements
      [ LengthOfByteString,
        Sha2_256,
        Sha3_256,
        Blake2b_256,
        EncodeUtf8,
        DecodeUtf8,
        FstPair,
        SndPair,
        HeadList,
        TailList,
        NullList,
        MapData,
        ListData,
        IData,
        BData,
        UnConstrData,
        UnMapData,
        UnListData,
        UnIData,
        UnBData,
        SerialiseData,
        MkNilData,
        MkNilPairData,
        BLS12_381_G1_neg,
        BLS12_381_G1_compress,
        BLS12_381_G1_uncompress,
        BLS12_381_G2_neg,
        BLS12_381_G2_compress,
        BLS12_381_G2_uncompress,
        Keccak_256,
        Blake2b_244,
        ComplementByteString,
        CountSetBits,
        FindFirstSetBit,
        Ripemd_160
      ]

-- | All two-argument primitives provided by Plutus.
--
-- @since 1.0.0
data TwoArgFunc
  = AddInteger
  | SubtractInteger
  | MultiplyInteger
  | DivideInteger
  | QuotientInteger
  | RemainderInteger
  | ModInteger
  | EqualsInteger
  | LessThanInteger
  | LessThanEqualsInteger
  | AppendByteString
  | ConsByteString
  | IndexByteString
  | EqualsByteString
  | LessThanByteString
  | LessThanEqualsByteString
  | AppendString
  | EqualsString
  | ChooseUnit
  | Trace
  | MkCons
  | ConstrData
  | EqualsData
  | MkPairData
  | BLS12_381_G1_add
  | BLS12_381_G1_scalarMul
  | BLS12_381_G1_equal
  | BLS12_381_G1_hashToGroup
  | BLS12_381_G2_add
  | BLS12_381_G2_scalarMul
  | BLS12_381_G2_equal
  | BLS12_381_G2_hashToGroup
  | BLS12_381_millerLoop
  | BLS12_381_mulMlResult
  | BLS12_381_finalVerify
  | ByteStringToInteger
  | ReadBit
  | ReplicateByte
  | ShiftByteString
  | RotateByteString
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | Does not shrink.
--
-- @since 1.0.0
instance Arbitrary TwoArgFunc where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    elements
      [ AddInteger,
        SubtractInteger,
        MultiplyInteger,
        DivideInteger,
        QuotientInteger,
        RemainderInteger,
        ModInteger,
        EqualsInteger,
        LessThanInteger,
        LessThanEqualsInteger,
        AppendByteString,
        ConsByteString,
        IndexByteString,
        EqualsByteString,
        LessThanByteString,
        LessThanEqualsByteString,
        AppendString,
        EqualsString,
        ChooseUnit,
        Trace,
        MkCons,
        ConstrData,
        EqualsData,
        MkPairData,
        BLS12_381_G1_add,
        BLS12_381_G1_scalarMul,
        BLS12_381_G1_equal,
        BLS12_381_G1_hashToGroup,
        BLS12_381_G2_add,
        BLS12_381_G2_scalarMul,
        BLS12_381_G2_equal,
        BLS12_381_G2_hashToGroup,
        BLS12_381_millerLoop,
        BLS12_381_mulMlResult,
        BLS12_381_finalVerify,
        ByteStringToInteger,
        ReadBit,
        ReplicateByte,
        ShiftByteString,
        RotateByteString
      ]

-- | All three-argument primitives provided by Plutus.
--
-- @since 1.0.0
data ThreeArgFunc
  = VerifyEd25519Signature
  | VerifyEcdsaSecp256k1Signature
  | VerifySchnorrSecp256k1Signature
  | IfThenElse
  | ChooseList
  | CaseList
  | IntegerToByteString
  | AndByteString
  | OrByteString
  | XorByteString
  | WriteBits
  | ExpModInteger
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | Does not shrink.
--
-- @since 1.0.0
instance Arbitrary ThreeArgFunc where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    elements
      [ VerifyEd25519Signature,
        VerifyEcdsaSecp256k1Signature,
        VerifySchnorrSecp256k1Signature,
        IfThenElse,
        ChooseList,
        CaseList,
        IntegerToByteString,
        AndByteString,
        OrByteString,
        XorByteString,
        WriteBits,
        ExpModInteger
      ]

-- | All six-argument primitives provided by Plutus.
--
-- @since 1.0.0
data SixArgFunc
  = ChooseData
  | CaseData
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | Does not shrink.
--
-- @since 1.0.0
instance Arbitrary SixArgFunc where
  {-# INLINEABLE arbitrary #-}
  arbitrary = elements [ChooseData, CaseData]

-- | Maps one-argument functions to their input and output types.
-- Returns a tuple of (arg type, result type).
--
-- @since 1.0.0
typeOfOneArgFunc :: OneArgFunc -> (TyExpr, TyExpr)
typeOfOneArgFunc = \case
  LengthOfByteString -> (TyByteString, TyInteger)
  Sha2_256 -> (TyByteString, TyByteString)
  Sha3_256 -> (TyByteString, TyByteString)
  Blake2b_256 -> (TyByteString, TyByteString)
  EncodeUtf8 -> (TyString, TyByteString)
  DecodeUtf8 -> (TyByteString, TyString)
  FstPair -> (TyPair TyPlutusData TyPlutusData, TyPlutusData)
  SndPair -> (TyPair TyPlutusData TyPlutusData, TyPlutusData)
  HeadList -> (TyList TyPlutusData, TyPlutusData)
  TailList -> (TyList TyPlutusData, TyList TyPlutusData)
  NullList -> (TyList TyPlutusData, TyBoolean)
  MapData -> (TyList (TyPair TyPlutusData TyPlutusData), TyPlutusData)
  ListData -> (TyList TyPlutusData, TyPlutusData)
  IData -> (TyInteger, TyPlutusData)
  BData -> (TyByteString, TyPlutusData)
  UnConstrData -> (TyPlutusData, TyPair TyInteger (TyList TyPlutusData))
  UnMapData -> (TyPlutusData, TyList (TyPair TyPlutusData TyPlutusData))
  UnListData -> (TyPlutusData, TyList TyPlutusData)
  UnIData -> (TyPlutusData, TyInteger)
  UnBData -> (TyPlutusData, TyByteString)
  SerialiseData -> (TyPlutusData, TyByteString)
  MkNilData -> (TyUnit, TyList TyPlutusData)
  MkNilPairData -> (TyUnit, TyList (TyPair TyPlutusData TyPlutusData))
  BLS12_381_G1_neg -> (TyByteString, TyByteString)
  BLS12_381_G1_compress -> (TyByteString, TyByteString)
  BLS12_381_G1_uncompress -> (TyByteString, TyByteString)
  BLS12_381_G2_neg -> (TyByteString, TyByteString)
  BLS12_381_G2_compress -> (TyByteString, TyByteString)
  BLS12_381_G2_uncompress -> (TyByteString, TyByteString)
  Keccak_256 -> (TyByteString, TyByteString)
  Blake2b_244 -> (TyByteString, TyByteString) -- TODO: Fix typo in Prim.hs to Blake2b_224
  ComplementByteString -> (TyByteString, TyByteString)
  CountSetBits -> (TyByteString, TyInteger)
  FindFirstSetBit -> (TyByteString, TyInteger)
  Ripemd_160 -> (TyByteString, TyByteString)

-- | Maps two-argument functions to their input and output types.
-- Returns a tuple of (arg1 type, arg2 type, return type).
--
-- @since 1.0.0
typeOfTwoArgFunc :: TwoArgFunc -> (TyExpr, TyExpr, TyExpr)
typeOfTwoArgFunc = \case
  AddInteger -> (TyInteger, TyInteger, TyInteger)
  SubtractInteger -> (TyInteger, TyInteger, TyInteger)
  MultiplyInteger -> (TyInteger, TyInteger, TyInteger)
  DivideInteger -> (TyInteger, TyInteger, TyInteger)
  QuotientInteger -> (TyInteger, TyInteger, TyInteger)
  RemainderInteger -> (TyInteger, TyInteger, TyInteger)
  ModInteger -> (TyInteger, TyInteger, TyInteger)
  EqualsInteger -> (TyInteger, TyInteger, TyBoolean)
  LessThanInteger -> (TyInteger, TyInteger, TyBoolean)
  LessThanEqualsInteger -> (TyInteger, TyInteger, TyBoolean)
  AppendByteString -> (TyByteString, TyByteString, TyByteString)
  ConsByteString -> (TyInteger, TyByteString, TyByteString)
  IndexByteString -> (TyByteString, TyInteger, TyInteger)
  EqualsByteString -> (TyByteString, TyByteString, TyBoolean)
  LessThanByteString -> (TyByteString, TyByteString, TyBoolean)
  LessThanEqualsByteString -> (TyByteString, TyByteString, TyBoolean)
  AppendString -> (TyString, TyString, TyString)
  EqualsString -> (TyString, TyString, TyBoolean)
  ChooseUnit -> (TyUnit, TyPlutusData, TyPlutusData)
  Trace -> (TyString, TyPlutusData, TyPlutusData)
  MkCons -> (TyPlutusData, TyList TyPlutusData, TyList TyPlutusData)
  ConstrData -> (TyInteger, TyList TyPlutusData, TyPlutusData)
  EqualsData -> (TyPlutusData, TyPlutusData, TyBoolean)
  MkPairData -> (TyPlutusData, TyPlutusData, TyPair TyPlutusData TyPlutusData)
  BLS12_381_G1_add -> (TyByteString, TyByteString, TyByteString)
  BLS12_381_G1_scalarMul -> (TyInteger, TyByteString, TyByteString)
  BLS12_381_G1_equal -> (TyByteString, TyByteString, TyBoolean)
  BLS12_381_G1_hashToGroup -> (TyByteString, TyByteString, TyByteString)
  BLS12_381_G2_add -> (TyByteString, TyByteString, TyByteString)
  BLS12_381_G2_scalarMul -> (TyInteger, TyByteString, TyByteString)
  BLS12_381_G2_equal -> (TyByteString, TyByteString, TyBoolean)
  BLS12_381_G2_hashToGroup -> (TyByteString, TyByteString, TyByteString)
  BLS12_381_millerLoop -> (TyByteString, TyByteString, TyByteString)
  BLS12_381_mulMlResult -> (TyByteString, TyByteString, TyByteString)
  BLS12_381_finalVerify -> (TyByteString, TyByteString, TyBoolean)
  ByteStringToInteger -> (TyBoolean, TyByteString, TyInteger)
  ReadBit -> (TyByteString, TyInteger, TyBoolean)
  ReplicateByte -> (TyInteger, TyInteger, TyByteString)
  ShiftByteString -> (TyByteString, TyInteger, TyByteString)
  RotateByteString -> (TyByteString, TyInteger, TyByteString)

-- | Maps three-argument functions to their input and output types.
-- Returns a tuple of (arg1 type, arg2 type, arg3 type, return type).
--
-- @since 1.0.0
typeOfThreeArgFunc :: ThreeArgFunc -> (TyExpr, TyExpr, TyExpr, TyExpr)
typeOfThreeArgFunc = \case
  VerifyEd25519Signature -> (TyByteString, TyByteString, TyByteString, TyBoolean)
  VerifyEcdsaSecp256k1Signature -> (TyByteString, TyByteString, TyByteString, TyBoolean)
  VerifySchnorrSecp256k1Signature -> (TyByteString, TyByteString, TyByteString, TyBoolean)
  IfThenElse -> (TyBoolean, TyPlutusData, TyPlutusData, TyPlutusData)
  ChooseList -> (TyList TyPlutusData, TyPlutusData, TyPlutusData, TyPlutusData)
  CaseList -> (TyList TyPlutusData, TyPlutusData, TyPair TyPlutusData (TyList TyPlutusData), TyPlutusData)
  IntegerToByteString -> (TyBoolean, TyInteger, TyInteger, TyByteString)
  AndByteString -> (TyBoolean, TyByteString, TyByteString, TyByteString)
  OrByteString -> (TyBoolean, TyByteString, TyByteString, TyByteString)
  XorByteString -> (TyBoolean, TyByteString, TyByteString, TyByteString)
  WriteBits -> (TyByteString, TyList TyInteger, TyBoolean, TyByteString)
  ExpModInteger -> (TyInteger, TyInteger, TyInteger, TyInteger)

-- | Maps six-argument functions to their input and output types.
-- Returns a tuple of (arg1 type, arg2 type, arg3 type, .. arg6 type, return type).
--
-- @since 1.0.0
typeOfSixArgFunc :: SixArgFunc -> (TyExpr, TyExpr, TyExpr, TyExpr, TyExpr, TyExpr, TyExpr)
typeOfSixArgFunc = \case
  ChooseData -> (TyPlutusData, TyPlutusData, TyPlutusData, TyPlutusData, TyPlutusData, TyPlutusData, TyPlutusData)
  CaseData ->
    ( TyPlutusData,
      TyPair TyInteger (TyList TyPlutusData),
      TyList (TyPair TyPlutusData TyPlutusData),
      TyList TyPlutusData,
      TyInteger,
      TyByteString,
      TyPlutusData
    )
