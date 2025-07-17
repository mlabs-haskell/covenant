-- |
-- Module: Covenant.Prim
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, sean@mlabs.city
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
import Covenant.Index (ix0, ix1)
import Covenant.Type
  ( AbstractTy,
    CompT (Comp0, Comp1, Comp2),
    CompTBody (ReturnT, (:--:>)),
    ValT (ThunkT),
    boolT,
    byteStringT,
    dataType1T,
    dataType2T,
    dataTypeT,
    g1T,
    g2T,
    integerT,
    mlResultT,
    stringT,
    tyvar,
    unitT,
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
-- directly.
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
  | -- | @since 1.1.0
    FstPair
  | -- | @since 1.1.0
    SndPair
  | -- | @since 1.1.0
    HeadList
  | -- | @since 1.1.0
    TailList
  | -- | @since 1.1.0
    NullList
  | -- | @since 1.1.0
    MapData
  | -- | @since 1.1.0
    ListData
  | -- | @since 1.1.0
    IData
  | -- | @since 1.1.0
    BData
  | -- | @since 1.1.0
    UnConstrData
  | -- | @since 1.1.0
    UnMapData
  | -- | @since 1.1.0
    UnListData
  | -- | @since 1.1.0
    UnIData
  | -- | @since 1.1.0
    UnBData
  | -- | @since 1.1.0
    SerialiseData
  | BLS12_381_G1_neg
  | BLS12_381_G1_compress
  | BLS12_381_G1_uncompress
  | BLS12_381_G2_neg
  | BLS12_381_G2_compress
  | BLS12_381_G2_uncompress
  | Keccak_256
  | Blake2b_224
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
        Blake2b_224,
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
  LengthOfByteString -> Comp0 $ byteStringT :--:> ReturnT integerT
  Sha2_256 -> hashingT
  Sha3_256 -> hashingT
  Blake2b_256 -> hashingT
  EncodeUtf8 -> Comp0 $ stringT :--:> ReturnT byteStringT
  DecodeUtf8 -> Comp0 $ byteStringT :--:> ReturnT stringT
  FstPair -> Comp2 $ pairT aT bT :--:> ReturnT aT
  SndPair -> Comp2 $ pairT aT bT :--:> ReturnT bT
  HeadList -> Comp1 $ listT aT :--:> ReturnT aT
  TailList -> Comp1 $ listT aT :--:> ReturnT (listT aT)
  NullList -> Comp1 $ listT aT :--:> ReturnT boolT
  MapData -> Comp0 $ listT (pairT dataT dataT) :--:> ReturnT dataT
  ListData -> Comp0 $ listT dataT :--:> ReturnT dataT
  IData -> Comp0 $ integerT :--:> ReturnT dataT
  BData -> Comp0 $ byteStringT :--:> ReturnT dataT
  UnConstrData -> Comp0 $ dataT :--:> ReturnT (pairT integerT (listT dataT))
  UnMapData -> Comp0 $ dataT :--:> ReturnT (listT (pairT dataT dataT))
  UnListData -> Comp0 $ dataT :--:> ReturnT (listT dataT)
  UnIData -> Comp0 $ dataT :--:> ReturnT integerT
  UnBData -> Comp0 $ dataT :--:> ReturnT byteStringT
  SerialiseData -> Comp0 $ dataT :--:> ReturnT byteStringT
  BLS12_381_G1_neg -> Comp0 $ g1T :--:> ReturnT g1T
  BLS12_381_G1_compress -> Comp0 $ g1T :--:> ReturnT byteStringT
  BLS12_381_G1_uncompress -> Comp0 $ byteStringT :--:> ReturnT g1T
  BLS12_381_G2_neg -> Comp0 $ g2T :--:> ReturnT g2T
  BLS12_381_G2_compress -> Comp0 $ g2T :--:> ReturnT byteStringT
  BLS12_381_G2_uncompress -> Comp0 $ byteStringT :--:> ReturnT g2T
  Keccak_256 -> hashingT
  Blake2b_224 -> hashingT
  ComplementByteString -> Comp0 $ byteStringT :--:> ReturnT byteStringT
  CountSetBits -> Comp0 $ byteStringT :--:> ReturnT integerT
  FindFirstSetBit -> Comp0 $ byteStringT :--:> ReturnT integerT
  Ripemd_160 -> hashingT
  where
    hashingT :: CompT AbstractTy
    hashingT = Comp0 $ byteStringT :--:> ReturnT byteStringT

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
  | -- | @since 1.1.0
    MkCons
  | -- | @since 1.1.0
    ConstrData
  | -- | @since 1.1.0
    EqualsData
  | -- | @since 1.1.0
    MkPairData
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
  ConsByteString -> Comp0 $ integerT :--:> byteStringT :--:> ReturnT byteStringT
  IndexByteString -> Comp0 $ byteStringT :--:> integerT :--:> ReturnT integerT
  EqualsByteString -> compareT byteStringT
  LessThanByteString -> compareT byteStringT
  LessThanEqualsByteString -> compareT byteStringT
  AppendString -> combineT stringT
  EqualsString -> compareT stringT
  ChooseUnit -> Comp1 $ unitT :--:> aT :--:> ReturnT aT
  Trace -> Comp1 $ stringT :--:> aT :--:> ReturnT aT
  MkCons -> Comp1 $ aT :--:> listT aT :--:> ReturnT (listT aT)
  ConstrData -> Comp0 $ integerT :--:> listT dataT :--:> ReturnT dataT
  EqualsData -> compareT dataT
  MkPairData -> Comp0 $ dataT :--:> dataT :--:> ReturnT (pairT dataT dataT)
  BLS12_381_G1_add -> combineT g1T
  BLS12_381_G1_scalarMul -> Comp0 $ integerT :--:> g1T :--:> ReturnT g1T
  BLS12_381_G1_equal -> compareT g1T
  BLS12_381_G1_hashToGroup -> Comp0 $ byteStringT :--:> byteStringT :--:> ReturnT g1T
  BLS12_381_G2_add -> combineT g2T
  BLS12_381_G2_scalarMul -> Comp0 $ integerT :--:> g2T :--:> ReturnT g2T
  BLS12_381_G2_equal -> compareT g2T
  BLS12_381_G2_hashToGroup -> Comp0 $ byteStringT :--:> byteStringT :--:> ReturnT g2T
  BLS12_381_millerLoop -> Comp0 $ g1T :--:> g2T :--:> ReturnT mlResultT
  BLS12_381_mulMlResult -> combineT mlResultT
  BLS12_381_finalVerify -> Comp0 $ mlResultT :--:> mlResultT :--:> ReturnT boolT
  ByteStringToInteger -> Comp0 $ boolT :--:> byteStringT :--:> ReturnT integerT
  ReadBit -> Comp0 $ byteStringT :--:> integerT :--:> ReturnT boolT
  ReplicateByte -> Comp0 $ integerT :--:> integerT :--:> ReturnT byteStringT
  ShiftByteString -> Comp0 $ byteStringT :--:> integerT :--:> ReturnT byteStringT
  RotateByteString -> Comp0 $ byteStringT :--:> integerT :--:> ReturnT byteStringT
  where
    combineT :: ValT AbstractTy -> CompT AbstractTy
    combineT t = Comp0 $ t :--:> t :--:> ReturnT t
    compareT :: ValT AbstractTy -> CompT AbstractTy
    compareT t = Comp0 $ t :--:> t :--:> ReturnT boolT

-- | All three-argument primitives provided by Plutus.
--
-- @since 1.0.0
data ThreeArgFunc
  = VerifyEd25519Signature
  | VerifyEcdsaSecp256k1Signature
  | VerifySchnorrSecp256k1Signature
  | IfThenElse
  | -- | @since 1.1.0
    ChooseList
  | -- | @since 1.1.0
    CaseList
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
  IfThenElse -> Comp1 $ boolT :--:> aT :--:> aT :--:> ReturnT aT
  ChooseList -> Comp2 $ listT aT :--:> bT :--:> bT :--:> ReturnT bT
  CaseList ->
    Comp2 $
      bT
        :--:> ThunkT (Comp0 $ aTOuter :--:> listT aTOuter :--:> ReturnT bTOuter)
        :--:> listT aT
        :--:> ReturnT bT
  IntegerToByteString ->
    Comp0 $
      boolT :--:> integerT :--:> integerT :--:> ReturnT byteStringT
  AndByteString -> bitwiseT
  OrByteString -> bitwiseT
  XorByteString -> bitwiseT
  WriteBits ->
    Comp0 $
      byteStringT :--:> listT integerT :--:> boolT :--:> ReturnT byteStringT
  ExpModInteger ->
    Comp0 $
      integerT
        :--:> integerT
        :--:> integerT
        :--:> ReturnT integerT
  where
    signatureT :: CompT AbstractTy
    signatureT =
      Comp0 $
        byteStringT
          :--:> byteStringT
          :--:> byteStringT
          :--:> ReturnT boolT
    bitwiseT :: CompT AbstractTy
    bitwiseT =
      Comp0 $
        boolT
          :--:> byteStringT
          :--:> byteStringT
          :--:> ReturnT byteStringT

-- | All six-argument primitives provided by Plutus.
--
-- @since 1.1.0
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
-- @since 1.1.0
instance Arbitrary SixArgFunc where
  {-# INLINEABLE arbitrary #-}
  arbitrary = elements [ChooseData, CaseData]

-- | Produce the type of a six-argument primop.
--
-- @since 1.1.0
typeSixArgFunc :: SixArgFunc -> CompT AbstractTy
typeSixArgFunc = \case
  ChooseData ->
    Comp1 $
      dataT
        :--:> aT
        :--:> aT
        :--:> aT
        :--:> aT
        :--:> aT
        :--:> ReturnT aT
  CaseData ->
    Comp1 $
      ThunkT (Comp0 $ integerT :--:> listT dataT :--:> ReturnT aTOuter)
        :--:> ThunkT (Comp0 $ listT (pairT dataT dataT) :--:> ReturnT aTOuter)
        :--:> ThunkT (Comp0 $ listT dataT :--:> ReturnT aTOuter)
        :--:> ThunkT (Comp0 $ integerT :--:> ReturnT aTOuter)
        :--:> ThunkT (Comp0 $ byteStringT :--:> ReturnT aTOuter)
        :--:> dataT
        :--:> ReturnT aT

-- Helpers

dataT :: ValT AbstractTy
dataT = dataTypeT "Data"

listT :: ValT AbstractTy -> ValT AbstractTy
listT = dataType1T "List"

pairT :: ValT AbstractTy -> ValT AbstractTy -> ValT AbstractTy
pairT = dataType2T "Pair"

aT :: ValT AbstractTy
aT = tyvar Z ix0

aTOuter :: ValT AbstractTy
aTOuter = tyvar (S Z) ix0

bT :: ValT AbstractTy
bT = tyvar Z ix1

bTOuter :: ValT AbstractTy
bTOuter = tyvar (S Z) ix1
