{-# LANGUAGE PatternSynonyms #-}

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
    typeOneArgFunc,
    TwoArgFunc (..),
    typeTwoArgFunc,
    ThreeArgFunc (..),
    typeThreeArgFunc,
    SixArgFunc (..),
    typeSixArgFunc,
  )
where

import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index (count0, ix0, ix1)
import Covenant.Type
  ( AbstractTy,
    CompT (CompT),
    ValT (ThunkT),
    boolT,
    byteStringT,
    comp0,
    comp1,
    comp2,
    dataT,
    g1T,
    g2T,
    integerT,
    listT,
    mlResultT,
    stringT,
    tyvar,
    unitT,
    (-*-),
    pattern ReturnT,
    pattern (:--:>),
  )
import Test.QuickCheck (Arbitrary (arbitrary), elements)

-- | All one-argument primitives provided by Plutus.
--
-- = Note
--
-- We exclude the @MkNilData@ and @MkNilPairData@ primitives from this list for
-- several reasons. For clarity, we list these below. Firstly, the reason why
-- these primitives still exist at all is historical: Plutus now has the ability
-- to directly \'lift\' empty list constants into itself. Secondly, while these
-- primitives /could/ still be used instead of direct lifts, there is never a
-- reason to prefer them, as they are less efficient than embedding a constant
-- directly. Thirdly, their naive typings would end up with overdetermined type
-- variables - consider the typing of @MkNilData@:
--
-- @forall a . () -> ![a]@
--
-- For all of these reasons, we do not represent these primitives in the ASG.
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

-- | Produce the type of a single-argument primop.
--
-- @since 1.0.0
typeOneArgFunc :: OneArgFunc -> CompT AbstractTy
typeOneArgFunc = \case
  LengthOfByteString -> comp0 $ byteStringT :--:> ReturnT integerT
  Sha2_256 -> hashingT
  Sha3_256 -> hashingT
  Blake2b_256 -> hashingT
  EncodeUtf8 -> comp0 $ stringT :--:> ReturnT byteStringT
  DecodeUtf8 -> comp0 $ byteStringT :--:> ReturnT stringT
  FstPair ->
    comp2 $
      (tyvar (S Z) ix0 -*- tyvar (S Z) ix1)
        :--:> ReturnT (tyvar Z ix0)
  SndPair ->
    comp2 $
      (tyvar (S Z) ix0 -*- tyvar (S Z) ix1)
        :--:> ReturnT (tyvar Z ix1)
  HeadList ->
    comp1 $ list0 (tyvar (S Z) ix0) :--:> ReturnT (tyvar Z ix0)
  TailList ->
    comp1 $
      list0 (tyvar (S Z) ix0)
        :--:> ReturnT (listT count0 (tyvar (S Z) ix0))
  NullList ->
    comp1 $ list0 (tyvar (S Z) ix0) :--:> ReturnT boolT
  MapData ->
    comp0 $ list0 (dataT -*- dataT) :--:> ReturnT dataT
  ListData -> comp0 $ list0 dataT :--:> ReturnT dataT
  IData -> comp0 $ integerT :--:> ReturnT dataT
  BData -> comp0 $ byteStringT :--:> ReturnT dataT
  UnConstrData -> comp0 $ dataT :--:> ReturnT (integerT -*- list0 dataT)
  UnMapData -> comp0 $ dataT :--:> ReturnT (list0 (dataT -*- dataT))
  UnListData -> comp0 $ dataT :--:> ReturnT (list0 dataT)
  UnIData -> comp0 $ dataT :--:> ReturnT integerT
  UnBData -> comp0 $ dataT :--:> ReturnT byteStringT
  SerialiseData -> comp0 $ dataT :--:> ReturnT byteStringT
  BLS12_381_G1_neg -> comp0 $ g1T :--:> ReturnT g1T
  BLS12_381_G1_compress -> comp0 $ g1T :--:> ReturnT byteStringT
  BLS12_381_G1_uncompress -> comp0 $ byteStringT :--:> ReturnT g1T
  BLS12_381_G2_neg -> comp0 $ g2T :--:> ReturnT g2T
  BLS12_381_G2_compress -> comp0 $ g2T :--:> ReturnT byteStringT
  BLS12_381_G2_uncompress -> comp0 $ byteStringT :--:> ReturnT g2T
  Keccak_256 -> hashingT
  Blake2b_244 -> hashingT
  ComplementByteString -> comp0 $ byteStringT :--:> ReturnT byteStringT
  CountSetBits -> comp0 $ byteStringT :--:> ReturnT integerT
  FindFirstSetBit -> comp0 $ byteStringT :--:> ReturnT integerT
  Ripemd_160 -> hashingT
  where
    list0 :: ValT AbstractTy -> ValT AbstractTy
    list0 = listT count0
    hashingT :: CompT AbstractTy
    hashingT = CompT count0 $ byteStringT :--:> ReturnT byteStringT

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

-- | Produce the type of a two-argument primop.
--
-- @since 1.0.0
typeTwoArgFunc :: TwoArgFunc -> CompT AbstractTy
typeTwoArgFunc = \case
  AddInteger -> combineT integerT
  SubtractInteger -> combineT integerT
  MultiplyInteger -> combineT integerT
  DivideInteger -> combineT integerT
  QuotientInteger -> combineT integerT
  RemainderInteger -> combineT integerT
  ModInteger -> combineT integerT
  EqualsInteger -> compareT integerT
  LessThanInteger -> compareT integerT
  LessThanEqualsInteger -> compareT integerT
  AppendByteString -> combineT byteStringT
  ConsByteString -> comp0 $ integerT :--:> byteStringT :--:> ReturnT byteStringT
  IndexByteString -> comp0 $ byteStringT :--:> integerT :--:> ReturnT integerT
  EqualsByteString -> compareT byteStringT
  LessThanByteString -> compareT byteStringT
  LessThanEqualsByteString -> compareT byteStringT
  AppendString -> combineT stringT
  EqualsString -> compareT stringT
  ChooseUnit -> comp1 $ unitT :--:> tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)
  Trace -> comp1 $ stringT :--:> tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)
  MkCons ->
    comp1 $
      tyvar Z ix0
        :--:> listT count0 (tyvar (S Z) ix0)
        :--:> ReturnT (tyvar Z ix0)
  ConstrData -> comp0 $ integerT :--:> listT count0 dataT :--:> ReturnT dataT
  EqualsData -> compareT dataT
  MkPairData -> comp0 $ dataT :--:> dataT :--:> ReturnT (dataT -*- dataT)
  BLS12_381_G1_add -> combineT g1T
  BLS12_381_G1_scalarMul -> comp0 $ integerT :--:> g1T :--:> ReturnT g1T
  BLS12_381_G1_equal -> compareT g1T
  BLS12_381_G1_hashToGroup -> comp0 $ byteStringT :--:> byteStringT :--:> ReturnT g1T
  BLS12_381_G2_add -> combineT g2T
  BLS12_381_G2_scalarMul -> comp0 $ integerT :--:> g2T :--:> ReturnT g2T
  BLS12_381_G2_equal -> compareT g2T
  BLS12_381_G2_hashToGroup -> comp0 $ byteStringT :--:> byteStringT :--:> ReturnT g2T
  BLS12_381_millerLoop -> comp0 $ g1T :--:> g2T :--:> ReturnT mlResultT
  BLS12_381_mulMlResult -> combineT mlResultT
  BLS12_381_finalVerify -> comp0 $ mlResultT :--:> mlResultT :--:> ReturnT boolT
  ByteStringToInteger -> comp0 $ boolT :--:> byteStringT :--:> ReturnT integerT
  ReadBit -> comp0 $ byteStringT :--:> integerT :--:> ReturnT boolT
  ReplicateByte -> comp0 $ integerT :--:> integerT :--:> ReturnT byteStringT
  ShiftByteString -> comp0 $ byteStringT :--:> integerT :--:> ReturnT byteStringT
  RotateByteString -> comp0 $ byteStringT :--:> integerT :--:> ReturnT byteStringT
  where
    combineT :: ValT AbstractTy -> CompT AbstractTy
    combineT t = comp0 $ t :--:> t :--:> ReturnT t
    compareT :: ValT AbstractTy -> CompT AbstractTy
    compareT t = comp0 $ t :--:> t :--:> ReturnT boolT

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

-- | Produce the type of a three-argument primop.
--
-- @since 1.0.0
typeThreeArgFunc :: ThreeArgFunc -> CompT AbstractTy
typeThreeArgFunc = \case
  VerifyEd25519Signature -> signatureT
  VerifyEcdsaSecp256k1Signature -> signatureT
  VerifySchnorrSecp256k1Signature -> signatureT
  IfThenElse ->
    comp1 $
      boolT
        :--:> tyvar Z ix0
        :--:> tyvar Z ix0
        :--:> ReturnT (tyvar Z ix0)
  ChooseList ->
    comp2 $
      listT count0 (tyvar (S Z) ix0)
        :--:> tyvar Z ix1
        :--:> tyvar Z ix1
        :--:> ReturnT (tyvar Z ix1)
  CaseList ->
    comp2 $
      tyvar Z ix1
        :--:> ThunkT
          ( comp0 $
              tyvar (S Z) ix0
                :--:> listT count0 (tyvar (S (S Z)) ix0)
                :--:> ReturnT (tyvar (S Z) ix1)
          )
        :--:> listT count0 (tyvar (S Z) ix0)
        :--:> ReturnT (tyvar Z ix1)
  IntegerToByteString ->
    comp0 $
      boolT :--:> integerT :--:> integerT :--:> ReturnT byteStringT
  AndByteString -> bitwiseT
  OrByteString -> bitwiseT
  XorByteString -> bitwiseT
  WriteBits ->
    comp0 $
      byteStringT
        :--:> listT count0 integerT
        :--:> boolT
        :--:> ReturnT byteStringT
  ExpModInteger ->
    comp0 $
      integerT
        :--:> integerT
        :--:> integerT
        :--:> ReturnT integerT
  where
    signatureT :: CompT AbstractTy
    signatureT =
      comp0 $
        byteStringT
          :--:> byteStringT
          :--:> byteStringT
          :--:> ReturnT boolT
    bitwiseT :: CompT AbstractTy
    bitwiseT =
      comp0 $
        boolT
          :--:> byteStringT
          :--:> byteStringT
          :--:> ReturnT byteStringT

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

-- | Produce the type of a six-argument primop.
--
-- @since 1.0.0
typeSixArgFunc :: SixArgFunc -> CompT AbstractTy
typeSixArgFunc = \case
  ChooseData ->
    comp1 $
      dataT
        :--:> tyvar Z ix0
        :--:> tyvar Z ix0
        :--:> tyvar Z ix0
        :--:> tyvar Z ix0
        :--:> tyvar Z ix0
        :--:> ReturnT (tyvar Z ix0)
  CaseData ->
    comp1 $
      ThunkT (comp0 $ integerT :--:> listT count0 dataT :--:> ReturnT (tyvar (S Z) ix0))
        :--:> ThunkT (comp0 $ listT count0 (dataT -*- dataT) :--:> ReturnT (tyvar (S Z) ix0))
        :--:> ThunkT (comp0 $ listT count0 dataT :--:> ReturnT (tyvar (S Z) ix0))
        :--:> ThunkT (comp0 $ integerT :--:> ReturnT (tyvar (S Z) ix0))
        :--:> ThunkT (comp0 $ byteStringT :--:> ReturnT (tyvar (S Z) ix0))
        :--:> dataT
        :--:> ReturnT (tyvar Z ix0)
