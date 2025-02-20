{-# LANGUAGE PatternSynonyms #-}

module Covenant.ASGNode
  ( TypeError (..),
    Id (..),
    typeId,
    Arg (..),
    Bound (..),
    Ref (..),
    typeRef,
    CompNode,
    ValNode,
    ASGNode,
    typeASGNode,
  )
where

import Control.Monad ((>=>))
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.HashCons (MonadHashCons (lookupRef))
import Control.Monad.Reader (MonadReader (local))
import Covenant.Constant (AConstant)
import Covenant.Ledger (LedgerAccessor, LedgerDestructor)
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
import Covenant.Type
  ( AbsTy (AbsTy),
    BuiltinT
      ( BLS12_381_G1_ElementT,
        BLS12_381_G2_ElementT,
        BLS12_381_MlResultT,
        BoolT,
        ByteStringT,
        DataT,
        IntegerT,
        ListT,
        PairT,
        StringT,
        UnitT
      ),
    CompT (ForallT, FunT, ReturnT),
    ValT (AbsT, BValT, ThunkT),
    pattern (:--:>),
    pattern (:-->),
    pattern (::--::>),
    pattern (::--:>),
    pattern (::-->),
  )
import Data.Kind (Type)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Word (Word64)

-- | @since 1.0.0
data TypeError
  = -- | The specified 'Id' doesn't refer to any 'ASGNode'. Under normal
    -- circumstances, this error cannot arise; it is only possible when 'Id's are
    -- being improperly reused outside of their enclosing 'MonadHashCons'
    -- computation.
    BrokenIdReference Id
  | -- Attempt to forall a value type.
    ForallValType ValT
  | -- Attempt to return a computation type.
    ReturnCompType CompT
  | -- Attempt to force a computation type.
    ForceCompType CompT
  | -- Attempt to bind an expression of computation type.
    LetBindingCompType CompT
  | -- Attempt to use a value type as a @let@ body.
    LetBodyValType ValT
  deriving stock (Eq, Show)

-- | A unique identifier for a node in a Covenant program.
--
-- @since 1.0.0
newtype Id = Id Word64
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Bounded,
      -- | Needed for internal reasons, even though this type class is terrible.
      --
      -- @since 1.0.0
      Enum
    )
    via Word64
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

typeId ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError TypeError m) =>
  Id -> m (Either CompT ValT)
typeId i =
  lookupRef i >>= \case
    Nothing -> throwError . BrokenIdReference $ i
    Just asgNode -> pure . typeASGNode $ asgNode

data Arg = Arg ValT Word64
  deriving stock (Eq, Ord, Show)

data Bound = Bound ValT Word64
  deriving stock (Eq, Ord, Show)

-- | A general reference in a Covenant program. This is one of the following:
--
-- * A computation, represented by its unique 'Id';
-- * A function argument, represented by an 'Arg'; or
-- * A @let@-bound variable, represented by a 'Bound'.
--
-- @since 1.0.0
data Ref = AnArg Arg | AnId Id | ABound Bound
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

typeRef ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError TypeError m) =>
  Ref -> m (Either CompT ValT)
typeRef = \case
  AnArg (Arg t _) -> pure . pure $ t
  AnId i -> typeId i
  ABound (Bound t _) -> pure . pure $ t

data Primitive
  = Prim1 OneArgFunc
  | Prim2 TwoArgFunc
  | Prim3 ThreeArgFunc
  | Prim6 SixArgFunc
  deriving stock (Eq, Ord, Show)

typePrimitive :: Primitive -> CompT
typePrimitive = \case
  Prim1 p -> typeOneArg p
  Prim2 p -> typeTwoArg p
  Prim3 p -> typeThreeArg p
  Prim6 p -> typeSixArg p

data CompNode
  = TyAbsInternal Id
  | LamInternal (Vector ValT) Id
  | BuiltinInternal Primitive
  | LetInternal ValT Ref Id
  | ForceInternal Ref
  | ReturnInternal Ref
  deriving stock (Eq, Ord, Show)

newtype TyInsts = TyInsts (Vector (Maybe ValT))

freshInst :: TyInsts -> TyInsts
freshInst (TyInsts v) = TyInsts . Vector.cons Nothing $ v

typeCompNode ::
  forall (m :: Type -> Type).
  (MonadHashCons Id ASGNode m, MonadError TypeError m, MonadReader TyInsts m) =>
  CompNode -> m CompT
typeCompNode = \case
  TyAbsInternal i ->
    local freshInst $
      typeId i >>= \case
        Left compT -> pure . ForallT $ compT
        Right t -> throwError . ForallValType $ t
  LamInternal argTs i -> _
  BuiltinInternal p -> pure . typePrimitive $ p
  LetInternal bindingT binding body ->
    typeRef binding >>= \case
      Left t -> throwError . LetBindingCompType $ t
      Right valT ->
        typeId body >>= \case
          Left compT -> unify bindingT valT compT
          Right t -> throwError . LetBodyValType $ t
  ForceInternal r ->
    typeRef r >>= \case
      Left t -> throwError . ForceCompType $ t
      Right (ThunkT compT) -> pure compT
      Right t -> throwError . ForceNonThunk $ t
  ReturnInternal r ->
    typeRef r >>= \case
      Left t -> throwError . ReturnCompType $ t
      Right valT -> pure . ReturnT $ valT

data ValNode
  = LitInternal AConstant
  | ThunkInternal Id
  | AppInternal Id (Vector Ref)
  | LedgerAccessInternal LedgerAccessor Ref
  | LedgerDestructInternal LedgerDestructor Id Ref
  deriving stock (Eq, Ord, Show)

data ASGNode = ACompNode CompT CompNode | AValNode ValT ValNode
  deriving stock (Eq, Ord, Show)

typeASGNode :: ASGNode -> Either CompT ValT
typeASGNode = \case
  ACompNode t _ -> Left t
  AValNode t _ -> Right t

-- Helpers

typeOneArg :: OneArgFunc -> CompT
typeOneArg = \case
  LengthOfByteString -> ByteStringT ::--::> IntegerT
  Sha2_256 -> ByteStringT ::--::> ByteStringT
  Sha3_256 -> ByteStringT ::--::> ByteStringT
  Blake2b_256 -> ByteStringT ::--::> ByteStringT
  EncodeUtf8 -> StringT ::--::> ByteStringT
  DecodeUtf8 -> ByteStringT ::--::> StringT
  FstPair ->
    ForallT . ForallT $ PairT absOuter absInner ::--:> absOuter
  SndPair ->
    ForallT . ForallT $ PairT absOuter absInner ::--:> absInner
  HeadList ->
    ForallT $ ListT absInner ::--:> absInner
  TailList ->
    ForallT $ ListT absInner ::--::> ListT absInner
  NullList ->
    ForallT $ ListT absInner ::--::> BoolT
  MapData ->
    ListT (BValT . PairT (BValT DataT) . BValT $ DataT) ::--::> DataT
  ListData ->
    ListT (BValT DataT) ::--::> DataT
  IData -> IntegerT ::--::> DataT
  BData -> ByteStringT ::--::> DataT
  UnConstrData ->
    DataT ::--::> PairT (BValT IntegerT) (BValT (ListT (BValT DataT)))
  UnMapData ->
    DataT ::--::> ListT (BValT (PairT (BValT DataT) . BValT $ DataT))
  UnListData ->
    DataT ::--::> ListT (BValT DataT)
  UnIData -> DataT ::--::> IntegerT
  UnBData -> DataT ::--::> ByteStringT
  SerialiseData -> DataT ::--::> ByteStringT
  -- Note (Koz, 20/02/2025): Technically both of these are functions in Plutus
  -- Core, which take a unit argument. This was needed as a workaround for a
  -- lack of nullary functions, but since we can be a bit more honest, this is
  -- really just a way of making these lazy constants. Thus, we use `ReturnT` as
  -- their type. It means they can't be applied to anything, but then again,
  -- it's not like it makes a tonne of sense to do so anyway.
  MkNilData -> ReturnT . BValT . ListT . BValT $ DataT
  MkNilPairData ->
    ReturnT . BValT . ListT . BValT . PairT (BValT DataT) . BValT $ DataT
  BLS12_381_G1_neg -> BLS12_381_G1_ElementT ::--::> BLS12_381_G1_ElementT
  BLS12_381_G1_compress -> BLS12_381_G1_ElementT ::--::> ByteStringT
  BLS12_381_G1_uncompress -> ByteStringT ::--::> BLS12_381_G1_ElementT
  BLS12_381_G2_neg -> BLS12_381_G2_ElementT ::--::> BLS12_381_G2_ElementT
  BLS12_381_G2_compress -> BLS12_381_G2_ElementT ::--::> ByteStringT
  BLS12_381_G2_uncompress -> ByteStringT ::--::> BLS12_381_G2_ElementT
  Keccak_256 -> ByteStringT ::--::> ByteStringT
  Blake2b_244 -> ByteStringT ::--::> ByteStringT
  ComplementByteString -> ByteStringT ::--::> ByteStringT
  CountSetBits -> ByteStringT ::--::> IntegerT
  FindFirstSetBit -> ByteStringT ::--::> IntegerT
  Ripemd_160 -> ByteStringT ::--::> ByteStringT

typeTwoArg :: TwoArgFunc -> CompT
typeTwoArg = \case
  AddInteger -> IntegerT ::--> IntegerT ::--::> IntegerT
  SubtractInteger -> IntegerT ::--> IntegerT ::--::> IntegerT
  MultiplyInteger -> IntegerT ::--> IntegerT ::--::> IntegerT
  DivideInteger -> IntegerT ::--> IntegerT ::--::> IntegerT
  QuotientInteger -> IntegerT ::--> IntegerT ::--::> IntegerT
  RemainderInteger -> IntegerT ::--> IntegerT ::--::> IntegerT
  ModInteger -> IntegerT ::--> IntegerT ::--::> IntegerT
  EqualsInteger -> IntegerT ::--> IntegerT ::--::> BoolT
  LessThanInteger -> IntegerT ::--> IntegerT ::--::> BoolT
  LessThanEqualsInteger -> IntegerT ::--> IntegerT ::--::> BoolT
  AppendByteString -> ByteStringT ::--> ByteStringT ::--::> ByteStringT
  ConsByteString -> IntegerT ::--> ByteStringT ::--::> ByteStringT
  IndexByteString -> ByteStringT ::--> IntegerT ::--::> ByteStringT
  EqualsByteString -> ByteStringT ::--> ByteStringT ::--::> BoolT
  LessThanByteString -> ByteStringT ::--> ByteStringT ::--::> BoolT
  LessThanEqualsByteString -> ByteStringT ::--> ByteStringT ::--::> BoolT
  AppendString -> StringT ::--> StringT ::--::> StringT
  EqualsString -> StringT ::--> StringT ::--::> BoolT
  ChooseUnit -> ForallT (UnitT ::--> absInner :--:> absInner)
  Trace -> ForallT (StringT ::--> absInner :--:> absInner)
  MkCons -> ForallT (absInner :--> ListT absInner ::--::> ListT absInner)
  ConstrData -> IntegerT ::--> ListT (BValT DataT) ::--::> DataT
  EqualsData -> DataT ::--> DataT ::--::> BoolT
  MkPairData -> DataT ::--> DataT ::--::> PairT (BValT DataT) (BValT DataT)
  BLS12_381_G1_add ->
    BLS12_381_G1_ElementT ::--> BLS12_381_G1_ElementT ::--::> BLS12_381_G1_ElementT
  BLS12_381_G1_scalarMul ->
    IntegerT ::--> BLS12_381_G1_ElementT ::--::> BLS12_381_G1_ElementT
  BLS12_381_G1_equal ->
    BLS12_381_G1_ElementT ::--> BLS12_381_G1_ElementT ::--::> BoolT
  BLS12_381_G1_hashToGroup ->
    ByteStringT ::--> ByteStringT ::--::> BLS12_381_G1_ElementT
  BLS12_381_G2_add ->
    BLS12_381_G2_ElementT ::--> BLS12_381_G2_ElementT ::--::> BLS12_381_G2_ElementT
  BLS12_381_G2_scalarMul ->
    IntegerT ::--> BLS12_381_G2_ElementT ::--::> BLS12_381_G2_ElementT
  BLS12_381_G2_equal ->
    BLS12_381_G2_ElementT ::--> BLS12_381_G2_ElementT ::--::> BoolT
  BLS12_381_G2_hashToGroup ->
    ByteStringT ::--> ByteStringT ::--::> BLS12_381_G2_ElementT
  BLS12_381_millerLoop ->
    BLS12_381_G1_ElementT ::--> BLS12_381_G2_ElementT ::--::> BLS12_381_MlResultT
  BLS12_381_mulMlResult ->
    BLS12_381_MlResultT ::--> BLS12_381_MlResultT ::--::> BLS12_381_MlResultT
  BLS12_381_finalVerify ->
    BLS12_381_MlResultT ::--> BLS12_381_MlResultT ::--::> BoolT
  ByteStringToInteger -> BoolT ::--> ByteStringT ::--::> IntegerT
  ReadBit -> ByteStringT ::--> IntegerT ::--::> BoolT
  ReplicateByte -> IntegerT ::--> IntegerT ::--::> ByteStringT
  ShiftByteString -> ByteStringT ::--> IntegerT ::--::> ByteStringT
  RotateByteString -> ByteStringT ::--> IntegerT ::--::> ByteStringT

typeThreeArg :: ThreeArgFunc -> CompT
typeThreeArg = \case
  VerifyEd25519Signature ->
    ByteStringT ::--> ByteStringT ::--> ByteStringT ::--::> ByteStringT
  VerifyEcdsaSecp256k1Signature ->
    ByteStringT ::--> ByteStringT ::--> ByteStringT ::--::> ByteStringT
  VerifySchnorrSecp256k1Signature ->
    ByteStringT ::--> ByteStringT ::--> ByteStringT ::--::> ByteStringT
  -- Note (Koz, 20/02/2025): This is strict in both branches. Only use this if you
  -- are absolutely, totally sure you don't mind evaluating both branches.
  IfThenElse ->
    ForallT (BoolT ::--> absInner :--> absInner :--:> absInner)
  ChooseList ->
    ForallT . ForallT $ ListT absOuter ::--> absInner :--> absInner :--:> absInner
  CaseList ->
    ForallT . ForallT $ absInner :--> ThunkT (absOuter :--> ListT absOuter ::--:> absInner) :--> ListT absOuter ::--:> absInner
  IntegerToByteString -> BoolT ::--> IntegerT ::--> IntegerT ::--::> ByteStringT
  AndByteString -> BoolT ::--> ByteStringT ::--> ByteStringT ::--::> ByteStringT
  OrByteString -> BoolT ::--> ByteStringT ::--> ByteStringT ::--::> ByteStringT
  XorByteString -> BoolT ::--> ByteStringT ::--> ByteStringT ::--::> ByteStringT
  WriteBits ->
    ByteStringT ::--> ListT (BValT IntegerT) ::--> BoolT ::--::> ByteStringT
  ExpModInteger -> IntegerT ::--> IntegerT ::--> IntegerT ::--::> IntegerT

typeSixArg :: SixArgFunc -> CompT
typeSixArg = \case
  ChooseData ->
    ForallT $
      DataT
        ::--> absInner
        :--> absInner
        :--> absInner
        :--> absInner
        :--> absInner
        :--:> absInner
  CaseData ->
    ForallT $
      ThunkT (IntegerT ::--> ListT (BValT DataT) ::--:> absInner)
        :--> ThunkT (ListT (BValT (PairT (BValT DataT) (BValT DataT))) ::--:> absInner)
        :--> ThunkT (ListT (BValT DataT) ::--:> absInner)
        :--> ThunkT (IntegerT ::--:> absInner)
        :--> ThunkT (ByteStringT ::--:> absInner)
        :--> DataT
        ::--:> absInner

absOuter :: ValT
absOuter = AbsT . AbsTy $ 1

absInner :: ValT
absInner = AbsT . AbsTy $ 0
