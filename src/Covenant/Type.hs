{-# LANGUAGE PatternSynonyms #-}

module Covenant.Type
  ( AbsTy (..),
    BuiltinValT (..),
    ValT (..),
    CompT (..),
    typeOneArgFunc,
    typeTwoArgFunc,
    typeThreeArgFunc,
    typeSixArgFunc,
    typeConstant,
  )
where

import Covenant.Constant
  ( AConstant
      ( ABoolean,
        AByteString,
        AData,
        AList,
        APair,
        AString,
        AUnit,
        AnInteger
      ),
  )
import Covenant.Prim
  ( OneArgFunc
      ( BData,
        BLS12_381_G1_compress,
        BLS12_381_G1_neg,
        BLS12_381_G1_uncompress,
        BLS12_381_G2_compress,
        BLS12_381_G2_neg,
        BLS12_381_G2_uncompress,
        Blake2b_244,
        Blake2b_256,
        ComplementByteString,
        CountSetBits,
        DecodeUtf8,
        EncodeUtf8,
        FindFirstSetBit,
        FstPair,
        HeadList,
        IData,
        Keccak_256,
        LengthOfByteString,
        ListData,
        MapData,
        MkNilData,
        MkNilPairData,
        NullList,
        Ripemd_160,
        SerialiseData,
        Sha2_256,
        Sha3_256,
        SndPair,
        TailList,
        UnBData,
        UnConstrData,
        UnIData,
        UnListData,
        UnMapData
      ),
    SixArgFunc (CaseData, ChooseData),
    ThreeArgFunc
      ( AndByteString,
        CaseList,
        ChooseList,
        ExpModInteger,
        IfThenElse,
        IntegerToByteString,
        OrByteString,
        VerifyEcdsaSecp256k1Signature,
        VerifyEd25519Signature,
        VerifySchnorrSecp256k1Signature,
        WriteBits,
        XorByteString
      ),
    TwoArgFunc
      ( AddInteger,
        AppendByteString,
        AppendString,
        BLS12_381_G1_add,
        BLS12_381_G1_equal,
        BLS12_381_G1_hashToGroup,
        BLS12_381_G1_scalarMul,
        BLS12_381_G2_add,
        BLS12_381_G2_equal,
        BLS12_381_G2_hashToGroup,
        BLS12_381_G2_scalarMul,
        BLS12_381_finalVerify,
        BLS12_381_millerLoop,
        BLS12_381_mulMlResult,
        ByteStringToInteger,
        ChooseUnit,
        ConsByteString,
        ConstrData,
        DivideInteger,
        EqualsByteString,
        EqualsData,
        EqualsInteger,
        EqualsString,
        IndexByteString,
        LessThanByteString,
        LessThanEqualsByteString,
        LessThanEqualsInteger,
        LessThanInteger,
        MkCons,
        MkPairData,
        ModInteger,
        MultiplyInteger,
        QuotientInteger,
        ReadBit,
        RemainderInteger,
        ReplicateByte,
        RotateByteString,
        ShiftByteString,
        SubtractInteger,
        Trace
      ),
  )
import Data.Vector qualified as Vector

data AbsTy = AbsTyOne | AbsTyTwo
  deriving stock (Eq, Show)

data BuiltinValT
  = UnitT
  | BoolT
  | IntegerT
  | StringT
  | ByteStringT
  | BLS12_381_G1_ElementT
  | BLS12_381_G2_ElementT
  | BLS12_381_MlResultT
  | DataT
  | ListT ValT
  | PairT ValT ValT
  deriving stock (Eq, Show)

pattern (:*:) :: ValT -> ValT -> BuiltinValT
pattern t1 :*: t2 <- PairT t1 t2
  where
    t1 :*: t2 = PairT t1 t2

data ValT
  = BValT BuiltinValT
  | TyInstValT AbsTy
  | Thunk CompT
  deriving stock (Eq, Show)

absTyOne :: ValT
absTyOne = TyInstValT AbsTyOne

absTyTwo :: ValT
absTyTwo = TyInstValT AbsTyTwo

data CompT
  = Fun ValT CompT
  | Return ValT
  deriving stock (Eq, Show)

pattern (:-->) :: ValT -> CompT -> CompT
pattern x :--> f <- Fun x f
  where
    x :--> f = Fun x f

infixr 1 :-->

pattern (::-->) :: BuiltinValT -> CompT -> CompT
pattern x ::--> f <- Fun (BValT x) f
  where
    x ::--> f = Fun (BValT x) f

infixr 1 ::-->

pattern (:--:>) :: ValT -> ValT -> CompT
pattern x :--:> y <- Fun x (Return y)
  where
    x :--:> y = Fun x (Return y)

infixr 1 :--:>

pattern (::--:>) :: BuiltinValT -> ValT -> CompT
pattern x ::--:> y <- Fun (BValT x) (Return y)
  where
    x ::--:> y = Fun (BValT x) (Return y)

infixr 1 ::--:>

pattern (::--::>) :: BuiltinValT -> BuiltinValT -> CompT
pattern x ::--::> y <- Fun (BValT x) (Return (BValT y))
  where
    x ::--::> y = Fun (BValT x) (Return (BValT y))

infixr 1 ::--::>

typeOneArgFunc :: OneArgFunc -> CompT
typeOneArgFunc = \case
  LengthOfByteString -> ByteStringT ::--::> IntegerT
  Sha2_256 -> hashingT
  Sha3_256 -> hashingT
  Blake2b_256 -> hashingT
  EncodeUtf8 -> StringT ::--::> ByteStringT
  DecodeUtf8 -> ByteStringT ::--::> StringT
  FstPair -> (absTyOne :*: absTyTwo) ::--:> absTyOne
  SndPair -> (absTyOne :*: absTyTwo) ::--:> absTyTwo
  HeadList -> ListT absTyOne ::--:> absTyOne
  TailList -> ListT absTyOne ::--::> ListT absTyOne
  NullList -> ListT absTyOne ::--::> BoolT
  IData -> IntegerT ::--::> DataT
  BData -> ByteStringT ::--::> DataT
  ListData -> dataListT ::--::> DataT
  MapData -> dataMapT ::--::> DataT
  UnIData -> DataT ::--::> IntegerT
  UnBData -> DataT ::--::> ByteStringT
  UnConstrData -> DataT ::--::> (BValT IntegerT :*: BValT dataListT)
  UnListData -> DataT ::--::> dataListT
  UnMapData -> DataT ::--::> dataMapT
  SerialiseData -> DataT ::--::> ByteStringT
  MkNilData -> UnitT ::--::> dataListT
  MkNilPairData -> UnitT ::--::> (BValT DataT :*: BValT DataT)
  BLS12_381_G1_neg -> BLS12_381_G1_ElementT ::--::> BLS12_381_G1_ElementT
  BLS12_381_G1_compress -> BLS12_381_G1_ElementT ::--::> ByteStringT
  BLS12_381_G1_uncompress -> ByteStringT ::--::> BLS12_381_G1_ElementT
  BLS12_381_G2_neg -> BLS12_381_G2_ElementT ::--::> BLS12_381_G2_ElementT
  BLS12_381_G2_compress -> BLS12_381_G2_ElementT ::--::> ByteStringT
  BLS12_381_G2_uncompress -> ByteStringT ::--::> BLS12_381_G2_ElementT
  Keccak_256 -> hashingT
  Blake2b_244 -> hashingT
  ComplementByteString -> ByteStringT ::--::> ByteStringT
  CountSetBits -> ByteStringT ::--::> IntegerT
  FindFirstSetBit -> ByteStringT ::--::> IntegerT
  Ripemd_160 -> hashingT
  where
    hashingT :: CompT
    hashingT = ByteStringT ::--::> ByteStringT

typeTwoArgFunc :: TwoArgFunc -> CompT
typeTwoArgFunc = \case
  AddInteger -> combineOpT IntegerT
  SubtractInteger -> combineOpT IntegerT
  MultiplyInteger -> combineOpT IntegerT
  DivideInteger -> combineOpT IntegerT
  QuotientInteger -> combineOpT IntegerT
  RemainderInteger -> combineOpT IntegerT
  ModInteger -> combineOpT IntegerT
  EqualsInteger -> cmpT IntegerT
  LessThanInteger -> cmpT IntegerT
  LessThanEqualsInteger -> cmpT IntegerT
  AppendByteString -> combineOpT ByteStringT
  ConsByteString -> IntegerT ::--> ByteStringT ::--::> ByteStringT
  IndexByteString -> ByteStringT ::--> IntegerT ::--::> IntegerT
  EqualsByteString -> cmpT ByteStringT
  LessThanByteString -> cmpT ByteStringT
  LessThanEqualsByteString -> cmpT ByteStringT
  AppendString -> combineOpT StringT
  EqualsString -> cmpT StringT
  ChooseUnit -> UnitT ::--> absTyOne :--:> absTyOne
  Trace -> StringT ::--> absTyOne :--:> absTyOne
  MkCons -> absTyOne :--> ListT absTyOne ::--::> ListT absTyOne
  ConstrData -> IntegerT ::--> dataListT ::--::> DataT
  EqualsData -> cmpT DataT
  MkPairData -> DataT ::--> DataT ::--::> (BValT DataT :*: BValT DataT)
  BLS12_381_G1_add -> combineOpT BLS12_381_G1_ElementT
  BLS12_381_G1_scalarMul ->
    IntegerT
      ::--> BLS12_381_G1_ElementT
      ::--::> BLS12_381_G1_ElementT
  BLS12_381_G1_equal -> cmpT BLS12_381_G1_ElementT
  BLS12_381_G1_hashToGroup ->
    ByteStringT
      ::--> ByteStringT
      ::--::> BLS12_381_G1_ElementT
  BLS12_381_G2_add -> combineOpT BLS12_381_G2_ElementT
  BLS12_381_G2_scalarMul ->
    IntegerT
      ::--> BLS12_381_G2_ElementT
      ::--::> BLS12_381_G2_ElementT
  BLS12_381_G2_equal -> cmpT BLS12_381_G2_ElementT
  BLS12_381_G2_hashToGroup ->
    ByteStringT
      ::--> ByteStringT
      ::--::> BLS12_381_G2_ElementT
  BLS12_381_mulMlResult -> combineOpT BLS12_381_MlResultT
  BLS12_381_millerLoop ->
    BLS12_381_G1_ElementT
      ::--> BLS12_381_G2_ElementT
      ::--::> BLS12_381_MlResultT
  BLS12_381_finalVerify -> cmpT BLS12_381_MlResultT
  ByteStringToInteger -> BoolT ::--> ByteStringT ::--::> IntegerT
  ReadBit -> ByteStringT ::--> IntegerT ::--::> BoolT
  ReplicateByte -> IntegerT ::--> IntegerT ::--::> ByteStringT
  RotateByteString -> ByteStringT ::--> IntegerT ::--::> ByteStringT
  ShiftByteString -> ByteStringT ::--> IntegerT ::--::> ByteStringT
  where
    combineOpT :: BuiltinValT -> CompT
    combineOpT t = t ::--> (t ::--::> t)
    cmpT :: BuiltinValT -> CompT
    cmpT t = t ::--> (t ::--::> BoolT)

typeThreeArgFunc :: ThreeArgFunc -> CompT
typeThreeArgFunc = \case
  VerifyEd25519Signature -> verifyT
  VerifyEcdsaSecp256k1Signature -> verifyT
  VerifySchnorrSecp256k1Signature -> verifyT
  IfThenElse -> BoolT ::--> absTyOne :--> absTyOne :--:> absTyOne
  ChooseList -> ListT absTyOne ::--> absTyTwo :--> absTyTwo :--:> absTyTwo
  CaseList -> absTyTwo :--> handleCons :--> ListT absTyOne ::--:> absTyTwo
  IntegerToByteString -> BoolT ::--> IntegerT ::--> IntegerT ::--::> ByteStringT
  AndByteString -> bitOpT
  OrByteString -> bitOpT
  XorByteString -> bitOpT
  WriteBits -> ByteStringT ::--> IntegerT ::--> BoolT ::--::> ByteStringT
  ExpModInteger -> IntegerT ::--> IntegerT ::--> IntegerT ::--::> IntegerT
  where
    handleCons :: ValT
    handleCons = Thunk (absTyOne :--> ListT absTyOne ::--:> absTyTwo)
    bitOpT :: CompT
    bitOpT = BoolT ::--> (ByteStringT ::--> (ByteStringT ::--::> ByteStringT))
    verifyT :: CompT
    verifyT = ByteStringT ::--> (ByteStringT ::--> (ByteStringT ::--::> BoolT))

typeSixArgFunc :: SixArgFunc -> CompT
typeSixArgFunc = \case
  ChooseData ->
    DataT
      ::--> absTyOne
      :--> absTyOne
      :--> absTyOne
      :--> absTyOne
      :--> absTyOne
      :--:> absTyOne
  CaseData ->
    handleConstr
      :--> handleMap
      :--> handleList
      :--> handleInteger
      :--> handleByteString
      :--> DataT
      ::--:> absTyOne
    where
      handleConstr :: ValT
      handleConstr = Thunk (IntegerT ::--> (dataListT ::--:> absTyOne))
      handleMap :: ValT
      handleMap = Thunk (dataMapT ::--:> absTyOne)
      handleList :: ValT
      handleList = Thunk (dataListT ::--:> absTyOne)
      handleInteger :: ValT
      handleInteger = Thunk (IntegerT ::--:> absTyOne)
      handleByteString :: ValT
      handleByteString = Thunk (ByteStringT ::--:> absTyOne)

typeConstant :: AConstant -> ValT
typeConstant =
  BValT . \case
    AUnit -> UnitT
    ABoolean _ -> BoolT
    AnInteger _ -> IntegerT
    AByteString _ -> ByteStringT
    AString _ -> StringT
    APair x y -> PairT (typeConstant x) (typeConstant y)
    AList xs -> ListT $ case Vector.length xs of
      0 -> absTyOne
      _ -> typeConstant . Vector.head $ xs
    AData _ -> DataT

-- Helpers

dataListT :: BuiltinValT
dataListT = ListT (BValT DataT)

dataMapT :: BuiltinValT
dataMapT = ListT (BValT (BValT DataT :*: BValT DataT))
