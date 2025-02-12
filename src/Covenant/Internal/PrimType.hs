module Covenant.Internal.PrimType
  ( typeOfOneArgFunc,
    typeOfTwoArgFunc,
    typeOfThreeArgFunc,
    typeOfSixArgFunc,
  )
where

import Covenant.Constant
  ( TyExpr
      ( TyBLS12_381G1Element,
        TyBLS12_381G2Element,
        TyBLS12_381PairingMLResult,
        TyBoolean,
        TyByteString,
        TyInteger,
        TyList,
        TyPair,
        TyPlutusData,
        TyString,
        TyUnit
      ),
  )
import Covenant.Internal.ASGNode (TyASGNode (ATyExpr, ATyLam), TyLam (TyLam))
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
    ThreeArgFunc (AndByteString, CaseList, ChooseList, ExpModInteger, IfThenElse, IntegerToByteString, OrByteString, VerifyEcdsaSecp256k1Signature, VerifyEd25519Signature, VerifySchnorrSecp256k1Signature, WriteBits, XorByteString),
    TwoArgFunc (AddInteger, AppendByteString, AppendString, BLS12_381_G1_add, BLS12_381_G1_equal, BLS12_381_G1_hashToGroup, BLS12_381_G1_scalarMul, BLS12_381_G2_add, BLS12_381_G2_equal, BLS12_381_G2_hashToGroup, BLS12_381_G2_scalarMul, BLS12_381_finalVerify, BLS12_381_millerLoop, BLS12_381_mulMlResult, ByteStringToInteger, ChooseUnit, ConsByteString, ConstrData, DivideInteger, EqualsByteString, EqualsData, EqualsInteger, EqualsString, IndexByteString, LessThanByteString, LessThanEqualsByteString, LessThanEqualsInteger, LessThanInteger, MkCons, MkPairData, ModInteger, MultiplyInteger, QuotientInteger, ReadBit, RemainderInteger, ReplicateByte, RotateByteString, ShiftByteString, SubtractInteger, Trace),
  )

-- | Maps one-argument functions to their input and output types.
-- Returns a tuple of (arg type, result type).
--
-- @since 1.0.0
typeOfOneArgFunc :: OneArgFunc -> (TyASGNode, TyASGNode)
typeOfOneArgFunc =
  liftTy <$> \case
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
    BLS12_381_G1_neg -> (TyBLS12_381G1Element, TyBLS12_381G1Element)
    BLS12_381_G1_compress -> (TyBLS12_381G1Element, TyByteString)
    BLS12_381_G1_uncompress -> (TyByteString, TyBLS12_381G1Element)
    BLS12_381_G2_neg -> (TyBLS12_381G2Element, TyBLS12_381G2Element)
    BLS12_381_G2_compress -> (TyBLS12_381G2Element, TyByteString)
    BLS12_381_G2_uncompress -> (TyByteString, TyBLS12_381G2Element)
    Keccak_256 -> (TyByteString, TyByteString)
    Blake2b_244 -> (TyByteString, TyByteString) -- TODO: Fix typo in Prim.hs to Blake2b_224
    ComplementByteString -> (TyByteString, TyByteString)
    CountSetBits -> (TyByteString, TyInteger)
    FindFirstSetBit -> (TyByteString, TyInteger)
    Ripemd_160 -> (TyByteString, TyByteString)
  where
    liftTy :: (TyExpr, TyExpr) -> (TyASGNode, TyASGNode)
    liftTy (t1, t2) = (ATyExpr t1, ATyExpr t2)

-- | Maps two-argument functions to their input and output types.
-- Returns a tuple of (arg1 type, arg2 type, return type).
--
-- @since 1.0.0
typeOfTwoArgFunc :: TwoArgFunc -> (TyASGNode, TyASGNode, TyASGNode)
typeOfTwoArgFunc =
  liftTy <$> \case
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
    BLS12_381_G1_add -> (TyBLS12_381G1Element, TyBLS12_381G1Element, TyBLS12_381G1Element)
    BLS12_381_G1_scalarMul -> (TyInteger, TyBLS12_381G1Element, TyBLS12_381G1Element)
    BLS12_381_G1_equal -> (TyBLS12_381G1Element, TyBLS12_381G1Element, TyBoolean)
    BLS12_381_G1_hashToGroup -> (TyByteString, TyByteString, TyBLS12_381G1Element)
    BLS12_381_G2_add -> (TyBLS12_381G2Element, TyBLS12_381G2Element, TyBLS12_381G2Element)
    BLS12_381_G2_scalarMul -> (TyInteger, TyBLS12_381G2Element, TyBLS12_381G2Element)
    BLS12_381_G2_equal -> (TyBLS12_381G2Element, TyBLS12_381G2Element, TyBoolean)
    BLS12_381_G2_hashToGroup -> (TyByteString, TyByteString, TyBLS12_381G2Element)
    BLS12_381_millerLoop -> (TyBLS12_381G1Element, TyBLS12_381G2Element, TyBLS12_381PairingMLResult)
    BLS12_381_mulMlResult -> (TyBLS12_381PairingMLResult, TyBLS12_381PairingMLResult, TyBLS12_381PairingMLResult)
    BLS12_381_finalVerify -> (TyBLS12_381PairingMLResult, TyBLS12_381PairingMLResult, TyBoolean)
    ByteStringToInteger -> (TyBoolean, TyByteString, TyInteger)
    ReadBit -> (TyByteString, TyInteger, TyBoolean)
    ReplicateByte -> (TyInteger, TyInteger, TyByteString)
    ShiftByteString -> (TyByteString, TyInteger, TyByteString)
    RotateByteString -> (TyByteString, TyInteger, TyByteString)
  where
    liftTy :: (TyExpr, TyExpr, TyExpr) -> (TyASGNode, TyASGNode, TyASGNode)
    liftTy (t1, t2, t3) = (ATyExpr t1, ATyExpr t2, ATyExpr t3)

-- | Maps three-argument functions to their input and output types.
-- Returns a tuple of (arg1 type, arg2 type, arg3 type, return type).
--
-- @since 1.0.0
typeOfThreeArgFunc :: ThreeArgFunc -> (TyASGNode, TyASGNode, TyASGNode, TyASGNode)
typeOfThreeArgFunc =
  liftTy <$> \case
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
  where
    liftTy :: (TyExpr, TyExpr, TyExpr, TyExpr) -> (TyASGNode, TyASGNode, TyASGNode, TyASGNode)
    liftTy (t1, t2, t3, t4) = (ATyExpr t1, ATyExpr t2, ATyExpr t3, ATyExpr t4)

-- | Maps six-argument functions to their input and output types.
-- Returns a tuple of (arg1 type, arg2 type, arg3 type, .. arg6 type, return type).
--
-- @since 1.0.0
typeOfSixArgFunc :: SixArgFunc -> (TyASGNode, TyASGNode, TyASGNode, TyASGNode, TyASGNode, TyASGNode, TyASGNode)
typeOfSixArgFunc = \case
  ChooseData ->
    ( ATyExpr TyPlutusData,
      ATyExpr TyPlutusData,
      ATyExpr TyPlutusData,
      ATyExpr TyPlutusData,
      ATyExpr TyPlutusData,
      ATyExpr TyPlutusData,
      ATyExpr TyPlutusData
    )
  CaseData ->
    ( -- Int -> [Data] -> a
      ATyLam $
        TyLam
          (ATyExpr TyInteger)
          (ATyLam $ TyLam (ATyExpr (TyList TyPlutusData)) (ATyExpr TyUnit)),
      -- (Data, Data) -> a
      ATyLam $ TyLam (ATyExpr (TyPair TyPlutusData TyPlutusData)) (ATyExpr TyUnit),
      -- [Data] -> a
      ATyLam $ TyLam (ATyExpr (TyList TyPlutusData)) (ATyExpr TyUnit),
      -- Data -> a
      ATyLam $ TyLam (ATyExpr TyPlutusData) (ATyExpr TyUnit),
      -- Int -> a
      ATyLam $ TyLam (ATyExpr TyInteger) (ATyExpr TyUnit),
      -- ByteString -> a
      ATyLam $ TyLam (ATyExpr TyByteString) (ATyExpr TyUnit),
      -- a
      ATyExpr TyUnit
    )
