{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

-- |
-- Module: Covenant.ASG
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, sean@mlabs.city
--
-- JSON serialization and deserialization utilities for the ASG.
--
-- = Note on Sum Type Encoding:
--
-- Unless otherwise noted, a Haskell sum type like:
--    @data Foo = Bar | Baz Int@
-- Is encoded to JSON using {tag: <CTOR NAME>, fields: [<Arg1>, <Arg2>, <ArgN>]}
--
-- This is the form used for all Haskell sum types which do NOT have `LabelOptic` instances. For those with
-- field names given by those instances, the `fields` part of the encoded sum is not an array of
-- arguments, but an object with names that correspond to the label optics. (The comments for each
-- function make clear which types are encoded in which way.)
-- @since 1.3.0
module Covenant.JSON where

import Control.Monad (foldM, unless, void)
import Control.Monad.Error.Class (MonadError)
import Control.Monad.HashCons (HashConsT, MonadHashCons (lookupRef))
import Control.Monad.Reader (local)
import Control.Monad.Reader.Class (MonadReader)
import Control.Monad.Trans (MonadTrans (lift))
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.Reader (ReaderT)
import Covenant.ASG
  ( ASG,
    ASGBuilder,
    ASGEnv,
    ASGNode,
    Arg,
    CompNodeInfo,
    CovenantError,
    Id,
    Ref,
    ValNodeInfo,
    app',
    builtin1,
    builtin2,
    builtin3,
    builtin6,
    cata,
    dataConstructor,
    err,
    force,
    lam,
    lit,
    match,
    runASGBuilder,
    thunk,
  )
import Covenant.Constant (AConstant (ABoolean, AByteString, AString, AUnit, AnInteger))
import Covenant.Data (BBFError, DatatypeInfo, mkDatatypeInfo, primBaseFunctorInfos)
import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index (Count, Index, intCount, intIndex)
import Covenant.Internal.KindCheck (checkDataDecls)
import Covenant.Internal.Strategy (InternalStrategy (InternalAssocMapStrat, InternalListStrat, InternalOpaqueStrat, InternalPairStrat))
import Covenant.Internal.Term (ASGNode (ACompNode, AValNode, AnError), Arg (Arg), CompNodeInfo (Builtin1Internal, Builtin2Internal, Builtin3Internal, Builtin6Internal, ForceInternal, LamInternal), CovenantTypeError, Id (Id), Ref (AnArg, AnId), ValNodeInfo (AppInternal, CataInternal, DataConstructorInternal, LitInternal, MatchInternal, ThunkInternal))
import Covenant.Internal.Type (AbstractTy (BoundAt), CompT (CompT), CompTBody (CompTBody), ConstructorName (ConstructorName), DataDeclaration (OpaqueData), ValT (BuiltinFlat, ThunkT))
import Covenant.Prim (OneArgFunc (BData, BLS12_381_G1_compress, BLS12_381_G1_neg, BLS12_381_G1_uncompress, BLS12_381_G2_compress, BLS12_381_G2_neg, BLS12_381_G2_uncompress, Blake2b_224, Blake2b_256, ComplementByteString, CountSetBits, DecodeUtf8, EncodeUtf8, FindFirstSetBit, FstPair, HeadList, IData, Keccak_256, LengthOfByteString, ListData, MapData, NullList, Ripemd_160, SerialiseData, Sha2_256, Sha3_256, SndPair, TailList, UnBData, UnConstrData, UnIData, UnListData, UnMapData), SixArgFunc (CaseData, ChooseData), ThreeArgFunc (AndByteString, CaseList, ChooseList, ExpModInteger, IfThenElse, IntegerToByteString, OrByteString, VerifyEcdsaSecp256k1Signature, VerifyEd25519Signature, VerifySchnorrSecp256k1Signature, WriteBits, XorByteString), TwoArgFunc (AddInteger, AppendByteString, AppendString, BLS12_381_G1_add, BLS12_381_G1_equal, BLS12_381_G1_hashToGroup, BLS12_381_G1_scalarMul, BLS12_381_G2_add, BLS12_381_G2_equal, BLS12_381_G2_hashToGroup, BLS12_381_G2_scalarMul, BLS12_381_finalVerify, BLS12_381_millerLoop, BLS12_381_mulMlResult, ByteStringToInteger, ChooseUnit, ConsByteString, ConstrData, DivideInteger, EqualsByteString, EqualsData, EqualsInteger, EqualsString, IndexByteString, LessThanByteString, LessThanEqualsByteString, LessThanEqualsInteger, LessThanInteger, MkCons, MkPairData, ModInteger, MultiplyInteger, QuotientInteger, ReadBit, RemainderInteger, ReplicateByte, RotateByteString, ShiftByteString, SubtractInteger, Trace))
import Covenant.Type
  ( BuiltinFlatT (BLS12_381_G1_ElementT, BLS12_381_G2_ElementT, BLS12_381_MlResultT, BoolT, ByteStringT, IntegerT, StringT, UnitT),
    Constructor (Constructor),
    DataDeclaration (DataDeclaration),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataConstructor (PlutusB, PlutusConstr, PlutusI, PlutusList, PlutusMap),
    PlutusDataStrategy (EnumData, NewtypeData, ProductListData),
    TyName (TyName),
    ValT (Abstraction, Datatype),
  )
import Covenant.Type qualified as Ty
import Data.Aeson
  ( FromJSON (parseJSON),
    ToJSON (toEncoding, toJSON),
    Value,
    (.=),
  )
import Data.Aeson.Encoding (Encoding, int, list, pair, pairs, text)
import Data.Aeson.Encoding.Internal (econcat, (><))
import Data.Aeson.KeyMap qualified as KM
import Data.Aeson.Types (Array, Key, Object, Parser, Value (Array, Object, String), prependFailure, typeMismatch)
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.Char (isAlphaNum, isUpper)
import Data.Foldable (foldl', toList, traverse_)
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty qualified as NEV
import GHC.TypeLits (KnownSymbol, Symbol)
import Optics.Core (preview, review, set, view)
import Text.Hex qualified as Hex

-- | A concrete monadic stack, providing the minimum amount of functionality
-- needed to build an ASG using the combinators given in this module, plus
-- some functionality needed to handle parsing an ASG from JSON.
-- @since 1.3.0
newtype ASGParser (a :: Type)
  = ASGParser (ReaderT ASGEnv (ExceptT CovenantTypeError (HashConsT Id ASGNode Parser)) a)
  deriving
    ( -- | @since 1.3.0
      Functor,
      -- | @since 1.3.0
      Applicative,
      -- | @since 1.3.0
      Monad,
      -- | @since 1.3.0
      MonadReader ASGEnv,
      -- | @since 1.3.0
      MonadError CovenantTypeError,
      -- | @since 1.3.0
      MonadHashCons Id ASGNode
    )
    via ReaderT ASGEnv (ExceptT CovenantTypeError (HashConsT Id ASGNode Parser))

data Version = Version {_major :: Int, _minor :: Int}
  deriving stock (Show, Eq, Ord)

data CompilationUnit
  = CompilationUnit
  { _datatypes :: [DataDeclaration AbstractTy],
    _asg :: Map Id ASGNode,
    _version :: Version
  }
  deriving stock (Show, Eq)

-- NOTE: We run w/ an empty map because the declarations get inserted after they are kindchecked
validateCompilationUnit :: CompilationUnit -> Either CovenantError ASG
validateCompilationUnit = runASGBuilder M.empty . validateCompilationUnit'

validateCompilationUnit' :: CompilationUnit -> ASGBuilder ()
validateCompilationUnit' (CompilationUnit datatypes asg _) = do
  let tyDict = foldl' (\acc x -> M.insert (view #datatypeName x) x acc) M.empty datatypes
  case checkDataDecls tyDict of
    Left kcErr -> error $ "KindCheck error: " <> show kcErr
    Right _ -> do
      case mkDatatypeInfos tyDict of
        Left dtErr -> error $ "DatatypeInfo error: " <> show dtErr
        Right infos -> local (set #datatypeInfo infos) $ traverse_ go (M.toList asg)
  where
    mkDatatypeInfos ::
      Map TyName (DataDeclaration AbstractTy) ->
      Either BBFError (Map TyName (DatatypeInfo AbstractTy))
    mkDatatypeInfos =
      foldl' (\acc decl -> (<>) <$> mkDatatypeInfo decl <*> acc) (Right primBaseFunctorInfos)

    go :: (Id, ASGNode) -> ASGBuilder ()
    go (parsedId, parsedNode) = case parsedNode of
      ACompNode compT compInfo -> case compInfo of
        Builtin1Internal bi1 -> checkNode "builtin1" (builtin1 bi1)
        Builtin2Internal bi2 -> checkNode "builtin2" (builtin2 bi2)
        Builtin3Internal bi3 -> checkNode "builtin3" (builtin3 bi3)
        Builtin6Internal bi6 -> checkNode "builtin6" (builtin6 bi6)
        LamInternal bodyRef -> checkNode "lam" $ lam compT (pure bodyRef)
        ForceInternal ref -> checkNode "force" $ force ref
      AValNode _ valInfo -> case valInfo of
        LitInternal aConstant -> checkNode "Lit" (lit aConstant)
        AppInternal fId argRefs -> checkNode "App" (app' fId argRefs)
        ThunkInternal i -> checkNode "Thunk" (thunk i)
        CataInternal r1 r2 -> checkNode "Cata" (cata r1 r2)
        DataConstructorInternal tn cn args -> checkNode "DataConstructor" (dataConstructor tn cn args)
        MatchInternal scrut matcharms -> checkNode "Match" (match scrut matcharms)
      AnError -> checkNode "errorNode" err
      where
        checkNode :: String -> ASGBuilder Id -> ASGBuilder ()
        checkNode msg constructedId = do
          xid <- constructedId
          unless (parsedId == xid) $ error $ msg <> " id mismatch"
          lookupRef xid >>= \case
            Nothing -> error $ msg <> " node not found"
            Just asgNode ->
              unless (asgNode == parsedNode) $ error $ msg <> " unexpected node"

{- CompilationUnit

   Encodes as an object. The maps are represented by KV pairs in arrays. Example:

   {datatypes: [{k: "Maybe", v: ...}, {k: "Foo", v: ...}],
    asg: [{k: 0, v: ...}],
    version: {major: 1, minor: 2}
   }
-}

encodeCompilationUnit :: CompilationUnit -> Encoding
encodeCompilationUnit (CompilationUnit datatypes asg version) =
  pairs $
    pair "datatypes" (list encodeDataDeclarationAbstractTy datatypes)
      <> pair "asg" (encodeMap encodeId encodeASGNode asg)
      <> pair "version" (encodeVersion version)

instance FromJSON CompilationUnit where
  parseJSON = error "TODO: Implement fromEncoding for CompilationUnit"

{- Version

   Serializes as an object with the fields you'd expect.

     Version 1 2
   ->
     {major: 1, minor: 2}

-}

-- |  @since 1.3.0
encodeVersion :: Version -> Encoding
encodeVersion (Version major minor) = pairs ("major" .= major <> "minor" .= minor)

-- | @since 1.3.0
decodeVersion :: Value -> ASGParser Version
decodeVersion = withObject' "Version" $ \obj -> do
  major <- withField "major" (liftParser . parseJSON) obj
  minor <- withField "minor" (liftParser . parseJSON) obj
  pure $ Version major minor

{- DataDeclaration & its components -}

{- Special handling to account for base functors (including "strange" base functors for Natural)

   {tyName: "Foo"}
   | {baseFunctorOf: "Foo"}
   | "NaturalBF" | "NegativeBF"
-}

-- | @since 1.3.0
encodeTyName :: TyName -> Encoding
encodeTyName (TyName tn) = case T.stripPrefix "#" tn of
  Nothing -> pairs ("tyName" .= tn)
  Just rootTypeName -> case rootTypeName of
    "#Natural" -> text "NaturalBF"
    "#Negative" -> text "NegativeBF"
    other -> pairs ("baseFunctorOf" .= other)

-- | The type name must conform with the type naming rules, i.e. it must
--   1. Begin with a capital letter
--   2. Consist only of alphanumeric characters and underscores
-- @since 1.3.0
decodeTyName :: Value -> ASGParser TyName
decodeTyName = liftParser . go
  where
    {- This is annoying. The thing we're getting *might* be an object or it might be a string,
        and we have to validate the result. Our helpers can't help us much here.
    -}
    go :: Value -> Parser TyName
    go = \case
      String str -> case str of
        "NaturalBF" -> pure "#Natural"
        "NegativeBF" -> pure "#Negative"
        other -> fail $ "Expected 'NaturalBF' or 'NegativeBF' but got " <> T.unpack other
      Object km -> case KM.lookup "tyName" km of
        Nothing -> case KM.lookup "baseFunctorOf" km of
          Nothing -> fail "Received an object for TyName, but it didn't have any valid fields"
          Just rootType -> TyName . ("#" <>) <$> (parseJSON rootType >>= validateProperName)
        Just tn -> TyName <$> (parseJSON tn >>= validateProperName)
      other -> fail $ "Expected a String or Object for TyName, but got: " <> show other

validateProperName :: Text -> Parser Text
validateProperName nm
  | T.null nm = fail "Empty String cannot be a TyName or ConstructorName"
  | (isUpper (T.head nm) || T.head nm == '#') && T.all (\c -> isAlphaNum c || c == '_') nm = pure nm
  | otherwise = fail $ "Could not validate TyName or ConstructorName '" <> T.unpack nm <> "'"

{- Encodes as a simple JSON string, e.g.
   ConstructorName "Foo" -> "Foo"
-}

-- | @since 1.3.0
encodeConstructorName :: ConstructorName -> Encoding
encodeConstructorName (ConstructorName cn) = toEncoding cn

-- | The ctor name must conform with the ctor naming rules, i.e. it must
--   1. Begin with a capital letter
--   2. Consist only of alphanumeric characters and underscores
-- @since 1.3.0
decodeConstructorName :: Value -> ASGParser ConstructorName
decodeConstructorName = withText' "ConstructorName" $ fmap ConstructorName . liftParser . validateProperName

{- Encodes as an object. E.g.:

   Constructor "Just" [IntegerT]
   ->
   { constructorName: "Just"
   , constructorArgs: [...]}

-}

-- | @since 1.3.0
encodeConstructor :: Constructor AbstractTy -> Encoding
encodeConstructor (Constructor nm args) =
  let encodedArgs = list encodeValTAbstractTy $ Vector.toList args
   in pairs $
        pair "constructorName" (encodeConstructorName nm)
          <> pair "constructorArgs" encodedArgs

-- | @since 1.3.0
decodeConstructor :: Value -> ASGParser (Constructor AbstractTy)
decodeConstructor = withObject' "Constructor" $ \obj -> do
  ctorNm <- lookupAndParse' obj "constructorName" decodeConstructorName
  ctorArgs <-
    lookupAndParse' obj "constructorArgs" $
      withArray' "Constructor Args" (traverse decodeValTAbstractTy)
  pure $ Constructor ctorNm ctorArgs

{- DataEncoding encodes as a typical sum type, and will look like:

   {tag: "SOP", fields: []}
   | {tag: "PlutusData", fields: [...]}
   | {tag: "BuiltinStrategy", fields: [...]}
-}

-- | @since 1.3.0
encodeDataEncoding :: DataEncoding -> Encoding
encodeDataEncoding = \case
  SOP -> taggedFields "SOP" []
  PlutusData strat -> taggedFields "PlutusData" [encodePlutusDataStrategy strat]
  BuiltinStrategy internalStrat -> taggedFields "BuiltinStrategy" [encodeInternalStrategy internalStrat]

-- | @since 1.3.0
decodeDataEncoding :: Value -> ASGParser DataEncoding
decodeDataEncoding = withObject' "DataEncoding" go
  where
    go :: Object -> ASGParser DataEncoding
    go obj = do
      tagStr <- lookupAndParse' obj "tag" (liftParser . parseJSON @Text)
      fieldsArrVal <- lookupAndParse' obj "fields" pure
      mfield0 <- withArray' "index 0" (\arr -> pure $ arr Vector.!? 0) fieldsArrVal
      case tagStr of
        "SOP" -> pure SOP
        otherTag -> case mfield0 of
          Nothing -> liftParser . fail $ "No fields present when deserializing a PlutusData"
          Just field0 -> case otherTag of
            "PlutusData" -> PlutusData <$> decodePlutusDataStrategy field0
            "BuiltinStrategy" -> BuiltinStrategy <$> decodeInternalStrategy field0
            other -> liftParser . fail $ "Invalid DataEncoding tag: " <> show other

{- PlutusDataStrategy encodes as a typical sum type. (Omitting the 'fields' field b/c it's an enumeration)

   {tag: "EnumData"}
   | {tag: "ProductListData"}
   | {tag: "ConstrData"}
   | {tag: "NewtypeData"}

-}

-- | @since 1.3.0
encodePlutusDataStrategy :: PlutusDataStrategy -> Encoding
encodePlutusDataStrategy = encodeEnum

-- | @since 1.3.0
decodePlutusDataStrategy :: Value -> ASGParser PlutusDataStrategy
decodePlutusDataStrategy =
  caseOnTag
    [ "EnumData" :=> constM EnumData,
      "ProductListData" :=> constM ProductListData,
      "ConstrData" :=> constM Ty.ConstrData,
      "NewtypeData" :=> constM NewtypeData
    ]

{- InternalStrategy encodes as a typical enumeration type:
  {tag: "InternalListStrat"}
  | {tag: "InternalPairStrat"}
  | {tag: "InternalDataStrat"}
  | {tag: "InternalAssocMapStrat"}
  | {tag: "InternalOpaqueStrat"}

-}
encodeInternalStrategy :: InternalStrategy -> Encoding
encodeInternalStrategy = encodeEnum

decodeInternalStrategy :: Value -> ASGParser InternalStrategy
decodeInternalStrategy =
  caseOnTag
    [ "InternalListStrat" :=> constM InternalListStrat,
      "InternalPairStrat" :=> constM InternalPairStrat,
      "InternalAssocMapStrat" :=> constM InternalAssocMapStrat,
      "InternalOpaqueStrat" :=> constM InternalOpaqueStrat
    ]

{- PlutusDataConstructor encodes as a typical enumeration type:

  {tag: "PlutusI"}
  | {tag: "PlutusB"}
  | {tag: "PlutusConstr"}
  | {tag: "PlutusList"}
  | {tag: PlutusMap}

-}

-- | @since 1.3.0
encodePlutusDataConstructor :: PlutusDataConstructor -> Encoding
encodePlutusDataConstructor = encodeEnum

-- | @since 1.3.0
decodePlutusDataConstructor :: Value -> ASGParser PlutusDataConstructor
decodePlutusDataConstructor =
  caseOnTag
    [ "PlutusI" :=> constM PlutusI,
      "PlutusB" :=> constM PlutusB,
      "PlutusConstr" :=> constM PlutusConstr,
      "PlutusList" :=> constM PlutusList,
      "PlutusMap" :=> constM PlutusMap
    ]

{- DataDeclaration AbstractTy is a bit atypical. It is a sum type, but we encode
   the arguments to the `DataDeclaration` constructor as an object instead of an array
   (to reduce the possibility for frontend errors).

   For example, if we have:

     @DataDeclaration "Maybe" (Count 1) [...Nothing...,...Just...] SOP@

   It will seralize like:

     {tag: "DataDeclaration"
     , fields: {
        datatypeName: "Maybe",
        datatypeBinders: 1,
        datatypeConstructors: [...],
        datatypeEncoding: {tag: "SOP"}
     }}

   For consistency, we do the same thing with Opaques. E.g.:

     @OpaqueData "Foo" [Plutus_I]@

   Will serialize to:

     { tag: "OpaqueData"
     , fields: {
       datatypeName: "Foo",
       opaquePlutusConstructors: [{tag: "Plutus_I"}]
     }}
-}

-- | @since 1.3.0
encodeDataDeclarationAbstractTy :: DataDeclaration AbstractTy -> Encoding
encodeDataDeclarationAbstractTy = \case
  DataDeclaration nm cnt ctors enc ->
    let fieldObj =
          pairs $
            pair "datatypeName" (encodeTyName nm)
              <> pair "datatypeBinders" (encodeCount cnt)
              <> pair "datatypeConstructors" (list encodeConstructor . Vector.toList $ ctors)
              <> pair "datatypeEncoding" (encodeDataEncoding enc)
     in pairs $ pair "tag" "DataDeclaration" <> pair "fields" fieldObj
  OpaqueData nm plutusCtors ->
    let fieldObj =
          pairs $
            pair "datatypeName" (encodeTyName nm)
              <> pair "opaquePlutusConstructors" (list encodePlutusDataConstructor . toList $ plutusCtors)
     in pairs $ pair "tag" "OpaqueData" <> pair "fields" fieldObj

-- | @since 1.3.0
decodeDataDeclarationAbstractTy :: Value -> ASGParser (DataDeclaration AbstractTy)
decodeDataDeclarationAbstractTy =
  caseOnTag
    [ "DataDeclaration" :=> goDataDecl,
      "OpaqueData" :=> goOpaqueData
    ]
  where
    goDataDecl :: Object -> ASGParser (DataDeclaration AbstractTy)
    goDataDecl obj = do
      fieldsObj <- lookupAndParse' obj "fields" (withObject' "Datatype fields" pure)
      dtName <- lookupAndParse' fieldsObj "datatypeName" decodeTyName
      dtBinders <- lookupAndParse' fieldsObj "datatypeBinders" decodeCount
      dtCtors <- lookupAndParse' fieldsObj "datatypeConstructors" (withArray' "Datatype ctors" (traverse decodeConstructor))
      dtEncoding <- lookupAndParse' fieldsObj "datatypeEncoding" decodeDataEncoding
      pure $ DataDeclaration dtName dtBinders dtCtors dtEncoding

    goOpaqueData :: Object -> ASGParser (DataDeclaration AbstractTy)
    goOpaqueData obj = do
      fieldsObj <- lookupAndParse' obj "fields" (withObject' "Datatype fields (Opaque)" pure)
      dtName <- lookupAndParse' fieldsObj "datatypeName" decodeTyName
      plutusCtors <-
        lookupAndParse'
          fieldsObj
          "opaquePlutusConstructors"
          (withArray' "Opaque Plutus Ctors" (traverse decodePlutusDataConstructor))
      pure $ OpaqueData dtName (S.fromList . Vector.toList $ plutusCtors)

{- ASG Specific Types & Components

-}

{- Id encodes directly as a number. E.g.:

   @Id 101@ -> 101
-}

-- | @since 1.3.0
encodeId :: Id -> Encoding
encodeId (Id n) = toEncoding n

-- | @since 1.3.0
decodeId :: Value -> ASGParser Id
decodeId = fmap Id . liftParser . parseJSON

{- Ref encodes as a typical sum type without named fields:

   {tag: "AnArg", fields: [...]}
   | {tag: "AnId": fields: [101]}
-}

-- | @since 1.3.0
encodeRef :: Ref -> Encoding
encodeRef = \case
  AnArg arg' -> taggedFields "AnArg" [encodeArg arg']
  AnId i -> taggedFields "AnId" [encodeId i]

-- | @since 1.3.0
decodeRef :: Value -> ASGParser Ref
decodeRef =
  caseOnTag
    [ "AnArg" :=> withFields (withIndex 0 (fmap AnArg . decodeArg)),
      "AnId" :=> withFields (withIndex 0 (fmap AnId . decodeId))
    ]

{- Arg encodes as an object, e.g.:

   {argDeBruijn: 0,
    argIndex: 1,
    argType: ...
   }

-}

-- | @since 1.3.0
encodeArg :: Arg -> Encoding
encodeArg (Arg db ix ty) =
  let dbEnc = encodeDeBruijn db
      ixEnc = encodeIndex ix
      tyEnc = encodeValTAbstractTy ty
   in pairs $
        pair "argDeBruijn" dbEnc
          <> pair "argIndex" ixEnc
          <> pair "argType" tyEnc

-- | @since 1.3.0
decodeArg :: Value -> ASGParser Arg
decodeArg = withObject' "Arg" $ \obj -> do
  argDB <- withField "argDeBruijn" decodeDeBruijn obj
  argIX <- withField "argIndex" decodeIndex obj
  argTy <- withField "argType" decodeValTAbstractTy obj
  pure $ Arg argDB argIX argTy

{- AConstant

   Serializes as a sum type without named fields:

   {tag: "AUnit"}
   | {tag: "ABoolean", fields: [true]}
   | {tag: "AnInteger", fields: [22]}
   | {tag: "AByteString", fields: ["\0x32"]}
   | {tag: "AString", fields: ["Hello"]}

-}

-- | @since 1.3.0
encodeAConstant :: AConstant -> Encoding
encodeAConstant = \case
  AUnit -> pairs $ pair "tag" "AUnit"
  ABoolean b -> taggedFields "ABoolean" [toEncoding b]
  AnInteger i -> taggedFields "AnInteger" [toEncoding i]
  AByteString bs -> taggedFields "AByteString" [toEncoding . Hex.encodeHex $ bs]
  AString str -> taggedFields "AString" [toEncoding str]

-- | @since 1.3.0
decodeAConstant :: Value -> ASGParser AConstant
decodeAConstant =
  caseOnTag
    [ "AUnit" :=> constM AUnit,
      "ABoolean" :=> withField0 (fmap ABoolean . liftParser . parseJSON),
      "AnInteger" :=> withField0 (fmap AnInteger . liftParser . parseJSON),
      "AByteString" :=> withField0 (fmap AByteString . decodeByteStringHex),
      "AString" :=> withField0 (fmap AString . liftParser . parseJSON)
    ]

{- ValNodeInfo

   Serializes as a sum type without named fields:

   {tag: "Lit", fields: [a]}
   | {tag: "App", fields: [a,b]}
   | {tag: "Thunk",fields: [a]}
   | {tag: "Cata", fields: [a,b]}
   | {tag: "DataConstructor", fields: [a,b,c]}
   | {tag: "Match", fields: [a,b]}

-}

-- | @since 1.3.0
encodeValNodeInfo :: ValNodeInfo -> Encoding
encodeValNodeInfo = \case
  LitInternal aconst -> taggedFields "Lit" [encodeAConstant aconst]
  AppInternal f args -> taggedFields "App" [encodeId f, list encodeRef . toList $ args]
  ThunkInternal f -> taggedFields "Thunk" [encodeId f]
  CataInternal r1 r2 -> taggedFields "Cata" [encodeRef r1, encodeRef r2]
  DataConstructorInternal tn cn args ->
    taggedFields
      "DataConstructor"
      [ encodeTyName tn,
        encodeConstructorName cn,
        list encodeRef . toList $ args
      ]
  MatchInternal scrut branches ->
    taggedFields "Match" [encodeRef scrut, list encodeRef . toList $ branches]

-- | @since 1.3.0
decodeValNodeInfo :: Value -> ASGParser ValNodeInfo
decodeValNodeInfo =
  caseOnTag
    [ "Lit" :=> withField0 (fmap LitInternal . decodeAConstant),
      "App"
        :=> withFields
        $ \fieldsArr -> do
          f <- withIndex 0 decodeId fieldsArr
          args <- withIndex 1 (withArray' "App args" (traverse decodeRef)) fieldsArr
          pure $ AppInternal f args,
      "Thunk" :=> withField0 (fmap ThunkInternal . decodeId),
      "Cata"
        :=> withFields
        $ \fieldsArr -> do
          r1 <- withIndex 0 decodeRef fieldsArr
          r2 <- withIndex 1 decodeRef fieldsArr
          pure $ CataInternal r1 r2,
      "DataConstructor"
        :=> withFields
        $ \fieldsArr -> do
          tn <- withIndex 0 decodeTyName fieldsArr
          ctorNm <- withIndex 1 decodeConstructorName fieldsArr
          args <- withIndex 2 (withArray' "Datatype args" (traverse decodeRef)) fieldsArr
          pure $ DataConstructorInternal tn ctorNm args,
      "Match"
        :=> withFields
        $ \fieldsArr -> do
          scrut <- withIndex 0 decodeRef fieldsArr
          args <- withIndex 1 (withArray' "Match branches" (traverse decodeRef)) fieldsArr
          pure $ MatchInternal scrut args
    ]

{- CompNodeInfo

   Serializes as a sum type without named fields:

   {tag: "Builtin1Internal", fields: [f]}
   | {tag: "Builtin2Internal", fields: [f]}
   | {tag: "Builtin3Internal", fields: [f]}
   | {tag: "Builtin6Internal", fields: [f]}
   | {tag: "LamInternal", fields: [r]}
   | {tag: "ForceInternal", fields: [r]}
-}

-- | @since 1.3.0
encodeCompNodeInfo :: CompNodeInfo -> Encoding
encodeCompNodeInfo = \case
  Builtin1Internal fun1 -> taggedFields "Builtin1Internal" [encodeOneArgFunc fun1]
  Builtin2Internal fun2 -> taggedFields "Builtin2Internal" [encodeTwoArgFunc fun2]
  Builtin3Internal fun3 -> taggedFields "Builtin3Internal" [encodeThreeArgFunc fun3]
  Builtin6Internal fun6 -> taggedFields "Builtin6Internal" [encodeSixArgFunc fun6]
  LamInternal f -> taggedFields "LamInternal" [encodeRef f]
  ForceInternal f -> taggedFields "ForceInternal" [encodeRef f]

-- | @since 1.3.0
decodeCompNodeInfo :: Value -> ASGParser CompNodeInfo
decodeCompNodeInfo =
  caseOnTag
    [ "Builtin1Internal" :=> withField0 (fmap Builtin1Internal . decodeOneArgFunc),
      "Builtin2Internal" :=> withField0 (fmap Builtin2Internal . decodeTwoArgFunc),
      "Builtin3Internal" :=> withField0 (fmap Builtin3Internal . decodeThreeArgFunc),
      "Builtin6Internal" :=> withField0 (fmap Builtin6Internal . decodeSixArgFunc),
      "LamInternal" :=> withField0 (fmap LamInternal . decodeRef),
      "ForceInternal" :=> withField0 (fmap ForceInternal . decodeRef)
    ]

{- ASGNode

   Serializes as a sum type without named fields:

   {tag: "ACompNode", fields: [ty,info]}
   | {tag: "AValNode", fields: [ty,info]}
   | {tag: "AnError"}

-}

-- | @since 1.3.0
encodeASGNode :: ASGNode -> Encoding
encodeASGNode = \case
  ACompNode compT compInfo -> taggedFields "ACompNode" [encodeCompT compT, encodeCompNodeInfo compInfo]
  AValNode valT valInfo -> taggedFields "AValNode" [encodeValTAbstractTy valT, encodeValNodeInfo valInfo]
  AnError -> pairs $ pair "tag" "AnError"

-- | @since 1.3.0
decodeASGNode :: Value -> ASGParser ASGNode
decodeASGNode =
  caseOnTag
    [ "ACompNode" :=> withFields $ \fields -> do
        compT <- withIndex 0 decodeCompT fields
        compInfo <- withIndex 1 decodeCompNodeInfo fields
        pure $ ACompNode compT compInfo,
      "AValNode" :=> withFields $ \fields -> do
        valT <- withIndex 0 decodeValTAbstractTy fields
        valInfo <- withIndex 1 decodeValNodeInfo fields
        pure $ AValNode valT valInfo,
      "AnError" :=> constM AnError
    ]

--
-- ValT, CompT & Friends/Components
--

{- DeBruijn

   Encodes directly as a number. E.g.

     @S Z@
   ->
     1

-}

-- | @since 1.3.0
encodeDeBruijn :: DeBruijn -> Encoding
encodeDeBruijn = int . review asInt

-- | @since 1.3.0
decodeDeBruijn :: Value -> ASGParser DeBruijn
decodeDeBruijn v = do
  vRaw <- liftParser $ parseJSON @Int v
  if vRaw < 0
    then failParse "Negative DeBruijn"
    else pure . fromJust . preview asInt $ vRaw

{- AbstractTy

   Standard product serialization as array:

     @BoundAt (S Z) ix0@
   ->
     [1,0]
-}

-- | @since 1.3.0
encodeAbstractTy :: AbstractTy -> Encoding
encodeAbstractTy (BoundAt db i) = encodeDeBruijn db >< encodeIndex i

-- | @since 1.3.0
decodeAbstractTy :: Value -> ASGParser AbstractTy
decodeAbstractTy = withArray' "AbstractTy" $ \arr -> do
  guardArrLen 2 arr
  db <- withIndex 0 decodeDeBruijn arr
  i <- withIndex 1 decodeIndex arr
  pure $ BoundAt db i

{- Count

   Serializes as a Number.

    @count0@
   ->
    0

    count1
   ->
    1
-}

-- | @since 1.3.0
encodeCount :: forall (s :: Symbol). Count s -> Encoding
encodeCount = int . review intCount

-- | @since 1.3.0
decodeCount :: forall (s :: Symbol). (KnownSymbol s) => Value -> ASGParser (Count s)
decodeCount v = do
  vRaw <- liftParser $ parseJSON @Int v
  if vRaw < 0
    then failParse "Negative Count"
    else pure . fromJust . preview intCount $ vRaw

{- Index

   Serializes as a number. NOTE: Will require a type application for the decoder.

     ix0
   ->
     0

     ix1
   ->
     1
-}

-- | @since 1.3.0
encodeIndex :: forall (s :: Symbol). Index s -> Encoding
encodeIndex = int . review intIndex

-- | @since 1.3.0
decodeIndex :: forall (s :: Symbol). (KnownSymbol s) => Value -> ASGParser (Index s)
decodeIndex v = do
  vRaw <- liftParser $ parseJSON @Int v
  if vRaw < 0
    then failParse "Negative Index"
    else pure . fromJust . preview intIndex $ vRaw

{- CompT AbstractTy

   Standard serialization as an array:

     @CompT count0 ...body...@
    ->
     [0,...encodedBody...]

-}

-- | @since 1.3.0
encodeCompT :: CompT AbstractTy -> Encoding
encodeCompT (CompT cnt body) = encodeCount cnt >< encodeCompTBody body

-- | @since 1.3.0
decodeCompT :: Value -> ASGParser (CompT AbstractTy)
decodeCompT = withArray' "CompT" $ \arr -> do
  guardArrLen 2 arr
  cnt <- withIndex 0 decodeCount arr
  body <- withIndex 1 decodeCompTBody arr
  pure $ CompT cnt body

{- CompTBodyAbstractTy

   This is a newtype over a NonEmptyVector and so encodes directly as an array.

     @CompTBody [t1,t2,t3]@
   ->
     [encodedT1,encodedT2,encodedT3]

-}

-- | @since 1.3.0
encodeCompTBody :: CompTBody AbstractTy -> Encoding
encodeCompTBody (CompTBody tys) = econcat . map encodeValTAbstractTy . toList $ tys

-- | @since 1.3.0
decodeCompTBody :: Value -> ASGParser (CompTBody AbstractTy)
decodeCompTBody = withArray' "CompTBody" $ \arr -> do
  decodedBody <- NEV.fromVector <$> traverse decodeValTAbstractTy arr
  case decodedBody of
    Nothing -> failParse "Empty vector of types in a CompTBody"
    Just res -> pure . CompTBody $ res

{- BuiltinFlatT

   Encodes as an enumeration (i.e. tag-only sum)

   {tag: "UnitT"}
   | {tag: "BoolT"}
   | {tag: "IntegerT"}
   | {tag: "StringT"}
   | {tag: "ByteStringT"}
   | {tag: "BLS12_381_G1_ElementT"}
   | {tag: "BLS12_381_G2_ElementT"}
   | {tag: "BLS12_381_MlResultT"}

-}

-- | @since 1.3.0
encodeBuiltinFlatT :: BuiltinFlatT -> Encoding
encodeBuiltinFlatT = encodeEnum

-- | @since 1.3.0
decodeBuiltinFlatT :: Value -> ASGParser BuiltinFlatT
decodeBuiltinFlatT =
  caseOnTag
    [ "UnitT" :=> constM UnitT,
      "BoolT" :=> constM BoolT,
      "IntegerT" :=> constM IntegerT,
      "StringT" :=> constM StringT,
      "ByteStringT" :=> constM ByteStringT,
      "BLS12_381_G1_ElementT" :=> constM BLS12_381_G1_ElementT,
      "BLS12_381_G2_ElementT" :=> constM BLS12_381_G2_ElementT,
      "BLS12_381_MlResultT" :=> constM BLS12_381_MlResultT
    ]

{- OneArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}

-- | @since 1.3.0
encodeOneArgFunc :: OneArgFunc -> Encoding
encodeOneArgFunc = encodeEnum

-- | @since 1.3.0
decodeOneArgFunc :: Value -> ASGParser OneArgFunc
decodeOneArgFunc =
  caseOnTag
    [ "LengthOfByteString" :=> constM LengthOfByteString,
      "Sha2_256" :=> constM Sha2_256,
      "Sha3_256" :=> constM Sha3_256,
      "Blake2b_256" :=> constM Blake2b_256,
      "EncodeUtf8" :=> constM EncodeUtf8,
      "DecodeUtf8" :=> constM DecodeUtf8,
      "FstPair" :=> constM FstPair,
      "SndPair" :=> constM SndPair,
      "HeadList" :=> constM HeadList,
      "TailList" :=> constM TailList,
      "NullList" :=> constM NullList,
      "MapData" :=> constM MapData,
      "ListData" :=> constM ListData,
      "IData" :=> constM IData,
      "BData" :=> constM BData,
      "UnConstrData" :=> constM UnConstrData,
      "UnMapData" :=> constM UnMapData,
      "UnListData" :=> constM UnListData,
      "UnIData" :=> constM UnIData,
      "UnBData" :=> constM UnBData,
      "SerialiseData" :=> constM SerialiseData,
      "BLS12_381_G1_neg" :=> constM BLS12_381_G1_neg,
      "BLS12_381_G1_compress" :=> constM BLS12_381_G1_compress,
      "BLS12_381_G1_uncompress" :=> constM BLS12_381_G1_uncompress,
      "BLS12_381_G2_neg" :=> constM BLS12_381_G2_neg,
      "BLS12_381_G2_compress" :=> constM BLS12_381_G2_compress,
      "BLS12_381_G2_uncompress" :=> constM BLS12_381_G2_uncompress,
      "Keccak_256" :=> constM Keccak_256,
      "Blake2b_224" :=> constM Blake2b_224,
      "ComplementByteString" :=> constM ComplementByteString,
      "CountSetBits" :=> constM CountSetBits,
      "FindFirstSetBit" :=> constM FindFirstSetBit,
      "Ripemd_160" :=> constM Ripemd_160
    ]

{- TwoArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}

-- | @since 1.3.0
encodeTwoArgFunc :: TwoArgFunc -> Encoding
encodeTwoArgFunc = encodeEnum

-- | @since 1.3.0
decodeTwoArgFunc :: Value -> ASGParser TwoArgFunc
decodeTwoArgFunc =
  caseOnTag
    [ "AddInteger" :=> constM AddInteger,
      "SubtractInteger" :=> constM SubtractInteger,
      "MultiplyInteger" :=> constM MultiplyInteger,
      "DivideInteger" :=> constM DivideInteger,
      "QuotientInteger" :=> constM QuotientInteger,
      "RemainderInteger" :=> constM RemainderInteger,
      "ModInteger" :=> constM ModInteger,
      "EqualsInteger" :=> constM EqualsInteger,
      "LessThanInteger" :=> constM LessThanInteger,
      "LessThanEqualsInteger" :=> constM LessThanEqualsInteger,
      "AppendByteString" :=> constM AppendByteString,
      "ConsByteString" :=> constM ConsByteString,
      "IndexByteString" :=> constM IndexByteString,
      "EqualsByteString" :=> constM EqualsByteString,
      "LessThanByteString" :=> constM LessThanByteString,
      "LessThanEqualsByteString" :=> constM LessThanEqualsByteString,
      "AppendString" :=> constM AppendString,
      "EqualsString" :=> constM EqualsString,
      "ChooseUnit" :=> constM ChooseUnit,
      "Trace" :=> constM Trace,
      "MkCons" :=> constM MkCons,
      "ConstrData" :=> constM ConstrData,
      "EqualsData" :=> constM EqualsData,
      "MkPairData" :=> constM MkPairData,
      "BLS12_381_G1_add" :=> constM BLS12_381_G1_add,
      "BLS12_381_G1_scalarMul" :=> constM BLS12_381_G1_scalarMul,
      "BLS12_381_G1_equal" :=> constM BLS12_381_G1_equal,
      "BLS12_381_G1_hashToGroup" :=> constM BLS12_381_G1_hashToGroup,
      "BLS12_381_G2_add" :=> constM BLS12_381_G2_add,
      "BLS12_381_G2_scalarMul" :=> constM BLS12_381_G2_scalarMul,
      "BLS12_381_G2_equal" :=> constM BLS12_381_G2_equal,
      "BLS12_381_G2_hashToGroup" :=> constM BLS12_381_G2_hashToGroup,
      "BLS12_381_millerLoop" :=> constM BLS12_381_millerLoop,
      "BLS12_381_mulMlResult" :=> constM BLS12_381_mulMlResult,
      "BLS12_381_finalVerify" :=> constM BLS12_381_finalVerify,
      "ByteStringToInteger" :=> constM ByteStringToInteger,
      "ReadBit" :=> constM ReadBit,
      "ReplicateByte" :=> constM ReplicateByte,
      "ShiftByteString" :=> constM ShiftByteString,
      "RotateByteString" :=> constM RotateByteString
    ]

{- ThreeArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}

-- | @since 1.3.0
encodeThreeArgFunc :: ThreeArgFunc -> Encoding
encodeThreeArgFunc = encodeEnum

-- | @since 1.3.0
decodeThreeArgFunc :: Value -> ASGParser ThreeArgFunc
decodeThreeArgFunc =
  caseOnTag
    [ "VerifyEd25519Signature" :=> constM VerifyEd25519Signature,
      "VerifyEcdsaSecp256k1Signature" :=> constM VerifyEcdsaSecp256k1Signature,
      "VerifySchnorrSecp256k1Signature" :=> constM VerifySchnorrSecp256k1Signature,
      "IfThenElse" :=> constM IfThenElse,
      "ChooseList" :=> constM ChooseList,
      "CaseList" :=> constM CaseList,
      "IntegerToByteString" :=> constM IntegerToByteString,
      "AndByteString" :=> constM AndByteString,
      "OrByteString" :=> constM OrByteString,
      "XorByteString" :=> constM XorByteString,
      "WriteBits" :=> constM WriteBits,
      "ExpModInteger" :=> constM ExpModInteger
    ]

{- SixArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}

-- | @since 1.3.0
encodeSixArgFunc :: SixArgFunc -> Encoding
encodeSixArgFunc = encodeEnum

-- | @since 1.3.0
decodeSixArgFunc :: Value -> ASGParser SixArgFunc
decodeSixArgFunc =
  caseOnTag
    [ "ChooseData" :=> constM ChooseData,
      "CaseData" :=> constM CaseData
    ]

{- ValT

   Encodes as a tagged sum without explicit field names:

   {tag: "Abstraction", fields: [...]}
   | {tag: "ThunkT", fields: [...]}
   | {tag: "BuiltinFlat", fields: : [...]}
   | {tag: "Datatype", fields: [...]}

-}

-- | @since 1.3.0
encodeValTAbstractTy :: ValT AbstractTy -> Encoding
encodeValTAbstractTy = \case
  Abstraction x -> taggedFields "Abstraction" [encodeAbstractTy x]
  ThunkT compT -> taggedFields "ThunkT" [encodeCompT compT]
  BuiltinFlat biFlat -> taggedFields "BuiltinFlat" [encodeBuiltinFlatT biFlat]
  Datatype tn args -> taggedFields "Datatype" [encodeTyName tn, list encodeValTAbstractTy . toList $ args]

-- | @since 1.3.0
decodeValTAbstractTy :: Value -> ASGParser (ValT AbstractTy)
decodeValTAbstractTy =
  caseOnTag
    [ "Abstraction" :=> withField0 (fmap Abstraction . decodeAbstractTy),
      "ThunkT" :=> withField0 (fmap ThunkT . decodeCompT),
      "BuiltinFlat" :=> withField0 (fmap BuiltinFlat . decodeBuiltinFlatT),
      "Datatype" :=> withFields $ \arr -> do
        tn <- withIndex 0 decodeTyName arr
        ctors <- withIndex 1 (withArray' "datatype args" (traverse decodeValTAbstractTy)) arr
        pure $ Datatype tn ctors
    ]

-- Helpers

encodeMap :: forall k v. (k -> Encoding) -> (v -> Encoding) -> Map k v -> Encoding
encodeMap fk fv m =
  list id $
    M.foldlWithKey'
      ( \acc k v ->
          let entry = pairs $ pair "key" (fk k) <> pair "value" (fv v)
           in entry : acc
      )
      []
      m

decodeMapM ::
  forall k v.
  (Ord k) =>
  (Value -> ASGParser k) ->
  (Value -> ASGParser v) ->
  Value ->
  ASGParser (Map k v)
decodeMapM fk fv = withArray' "Map" $ \arr ->
  foldM
    ( \acc x -> flip (withObject' "kvPair") x $ \obj -> do
        kfield <- lookupAndParse' obj "key" fk
        vfield <- lookupAndParse' obj "value" fv
        pure $ M.insert kfield vfield acc
    )
    M.empty
    arr

liftParser :: forall (a :: Type). Parser a -> ASGParser a
liftParser = ASGParser . lift . lift . lift

-- Mainly for readability/custom fixity, effectively (,)
data (:=>) a b = a :=> b

infixr 0 :=>

-- Simulated pattern matching on the `tag` field of an object. Will throw an error if the
-- value is not an object. This is a convenience function, and it is *very* convenient.
caseOnTag :: forall (a :: Type). [Text :=> (Object -> ASGParser a)] -> Value -> ASGParser a
caseOnTag xs = withObject' "CaseOnTag" go
  where
    go :: Object -> ASGParser a
    go obj = do
      let caseDict = foldl' (\acc (t :=> fn) -> M.insert t fn acc) M.empty xs
      tagVal <- lookupAndParse' obj "tag" (liftParser . parseJSON @Text)
      case M.lookup tagVal caseDict of
        Just f -> f obj
        Nothing -> failParse $ "Expected a tagged object with one of the tags: " <> show (M.keys caseDict) <> " but got " <> show obj

-- Stupid helper to avoid have to type `\_ -> pure x` a million times in `caseOnTag` matches
constM :: forall (f :: Type -> Type) (a :: Type). (Applicative f) => a -> (forall (b :: Type). b -> f a)
constM x _ = pure x

-- This isn't exported from Aeson.Types.Internal but I need it -_-
prependContext :: forall (a :: Type). String -> Parser a -> Parser a
prependContext name = prependFailure ("parsing " ++ name ++ " failed, ")

-- Like `withObject` but runs in our parser monad
withObject' ::
  forall (a :: Type).
  String ->
  (Object -> ASGParser a) ->
  Value ->
  ASGParser a
withObject' _ f (Object obj) = f obj
withObject' nm _ v = liftParser $ prependContext nm (typeMismatch "Object" v)

-- Like `withArray` but runs in our parser monad
withArray' ::
  forall (a :: Type).
  String ->
  (Array -> ASGParser a) ->
  Value ->
  ASGParser a
withArray' _ f (Array arr) = f arr
withArray' nm _ v = liftParser $ prependContext nm (typeMismatch "Array" v)

-- Like `withText` but runs in our parser monad
withText' ::
  forall (a :: Type).
  String ->
  (Text -> ASGParser a) ->
  Value ->
  ASGParser a
withText' _ f (String str) = f str
withText' nm _ v = liftParser $ prependContext nm (typeMismatch "Text" v)

guardArrLen :: Int -> Array -> ASGParser ()
guardArrLen expectedLen arr
  | Vector.length arr == expectedLen = pure ()
  | otherwise =
      failParse $
        "Expected an array with "
          <> show expectedLen
          <> " elements, but got one with "
          <> show (Vector.length arr)
          <> " elements"

-- Do something with the array at the tag "fields" in an object. Convenience helper.
withFields :: forall (a :: Type). (Array -> ASGParser a) -> Object -> ASGParser a
withFields f obj = lookupAndParse' obj "fields" $ \arrVal -> withArray' "field array" f arrVal

-- Do something with the element at a given index in a JSON array.
withIndex :: forall (a :: Type). Int -> (Value -> ASGParser a) -> Array -> ASGParser a
withIndex i f arr = case arr Vector.!? i of
  Nothing -> failParse $ "No element at index " <> show i <> " found in array " <> show arr
  Just elemAtIx -> f elemAtIx

-- flipped variant of lookupAndParse', for point free functions
withField :: forall (a :: Type). Key -> (Value -> ASGParser a) -> Object -> ASGParser a
withField k f obj = lookupAndParse' obj k f

-- A lot of our sums have a "fields" object with only one element, this saves us a bit of repetition for that common case.
-- Because this is intended to be used with either `withObject` or `caseOnTag`, it takes an Object which is expected to have a
-- "fields" fieldName with an array
withField0 :: forall (a :: Type). (Value -> ASGParser a) -> Object -> ASGParser a
withField0 f = withFields (\arr -> guardArrLen 1 arr >> withIndex 0 f arr)

-- Lookup the key in an object and apply the given monadic function to the value you get.
lookupAndParse' :: forall (a :: Type). Object -> Key -> (Value -> ASGParser a) -> ASGParser a
lookupAndParse' obj k f = case KM.lookup k obj of
  Nothing -> failParse $ "No key '" <> show k <> "' found in object"
  Just v -> f v

-- convenience to prevent me having to type 'liftParser . fail' a million times
failParse :: forall (a :: Type). String -> ASGParser a
failParse = liftParser . fail

-- NOTE: Must *ONLY* be used on *true* Enums, i.e. sum types with only 0-argument constructors
encodeEnum :: forall (a :: Type). (Show a) => a -> Encoding
encodeEnum = pairs . ("tag" .=) . show

-- Helper for constructing sum type Encodings.
-- 'taggedFields "name" [f1,f2,f3]' generates '{tag: "name", fields: [f1,f2,f3]}
taggedFields :: Text -> [Encoding] -> Encoding
taggedFields tg fieldArgs = pairs $ "tag" .= tg <> pair "fields" (econcat fieldArgs)

-- Decodes a hex encoded bytestring
decodeByteStringHex :: Value -> ASGParser ByteString
decodeByteStringHex = withText' "ByteString (Hex Encoded)" $ \txt -> case Hex.decodeHex txt of
  Nothing -> failParse $ "Failed to decode hex bytestring: " <> show txt
  Just bs -> pure bs

-- TODO: Remove this after I'm certain I don't need to write any more of these -_-
mkStub :: String -> String
mkStub ty = commentsBlock <> encodingStub <> "\n\n" <> decodingStub
  where
    commentsBlock = "{- " <> cleanName <> "\n\n-}\n"
    cleanName = filter (/= ' ') ty
    encFn = "encode" <> cleanName
    decFn = "decode" <> cleanName
    encodingStub =
      encFn
        <> " :: "
        <> ty
        <> " -> "
        <> "Encoding"
        <> "\n"
        <> encFn
        <> " = error \"TODO: Implement "
        <> encFn
        <> "\""
    decodingStub =
      decFn
        <> " :: Value -> ASGParser ("
        <> ty
        <> ")"
        <> "\n"
        <> decFn
        <> " = error \"TODO: Implement "
        <> decFn
        <> "\""
