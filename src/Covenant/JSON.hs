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

import Control.Monad.Error.Class (MonadError)
import Control.Monad.HashCons (HashConsT, MonadHashCons)
import Control.Monad.Reader.Class (MonadReader)
import Control.Monad.Trans (MonadTrans (lift))
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.Reader (ReaderT)
import Covenant.ASG
  ( ASGEnv,
    ASGNode,
    Arg,
    CompNodeInfo,
    Id,
    Ref,
    ValNodeInfo,
  )
import Covenant.Constant (AConstant (ABoolean, AByteString, AString, AUnit, AnInteger))
import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index (Count, Index, intCount, intIndex)
import Covenant.Internal.Strategy (InternalStrategy (InternalAssocMapStrat, InternalListStrat, InternalOpaqueStrat, InternalPairStrat))
import Covenant.Internal.Term (ASGNode (ACompNode, AValNode, AnError), Arg (..), CompNodeInfo (Builtin1Internal, Builtin2Internal, Builtin3Internal, Builtin6Internal, ForceInternal, LamInternal), CovenantTypeError, Id (Id), Ref (AnArg, AnId), ValNodeInfo (AppInternal, CataInternal, DataConstructorInternal, LitInternal, MatchInternal, ThunkInternal))
import Covenant.Internal.Type (AbstractTy (BoundAt), CompT (CompT), CompTBody (CompTBody), ConstructorName (ConstructorName), DataDeclaration (OpaqueData), ValT (BuiltinFlat, ThunkT))
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT (BLS12_381_G1_ElementT, BLS12_381_G2_ElementT, BLS12_381_MlResultT, BoolT, ByteStringT, IntegerT, StringT, UnitT),
    CompT,
    CompTBody,
    Constructor (Constructor),
    ConstructorName,
    DataDeclaration (DataDeclaration),
    DataEncoding (BuiltinStrategy, PlutusData, SOP),
    PlutusDataConstructor (PlutusB, PlutusConstr, PlutusI, PlutusList, PlutusMap),
    PlutusDataStrategy (ConstrData, EnumData, NewtypeData, ProductListData),
    TyName (TyName),
    ValT (Abstraction, Datatype),
  )
import Data.Aeson
  ( Encoding,
    FromJSON (parseJSON),
    KeyValue,
    ToJSON (toEncoding, toJSON),
    Value,
    fromJSON,
    (.=),
  )
import Data.Aeson.Encoding
import Data.Aeson.Encoding.Internal (econcat)
import Data.Aeson.KeyMap qualified as KM
import Data.Aeson.Types (Array, Key, Object, Parser, Value (Array, Object, String), prependFailure, toJSON1, typeMismatch, withArray, withObject, withText)
import Data.ByteString (ByteString)
import Data.Char (isAlphaNum, isUpper)
import Data.Foldable (foldl', toList)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty qualified as NEV
import Data.Word (Word32)
import GHC.TypeLits (KnownSymbol, Symbol)
import Optics.Core (preview, review)
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
  { _datatypes :: Map TyName (DataDeclaration AbstractTy),
    _asg :: Map Id ASGNode,
    _version :: Version
  }
  deriving stock (Show, Eq)

{- CompilationUnit

   Encodes as an object. The maps are represented by KV pairs in arrays. Example:

   {datatypes: [{k: "Maybe", v: ...}, {k: "Foo", v: ...}],
    asg: [{k: 0, v: ...}],
    version: {major: 1, minor: 2}
   }
-}

instance ToJSON CompilationUnit where
  toEncoding = error "TODO: Implement toEncoding for CompilationUnit"
  toJSON = error "TODO: Implement toJSON for CompilationUnit"

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
decodeVersion =
  liftParser
    . withObject
      "Version"
      ( \obj -> do
          major <- lookupAndParse obj "major" parseJSON
          minor <- lookupAndParse obj "minor" parseJSON
          pure $ Version major minor
      )

{- DataDeclaration & its components -}

{- Special handling to account for base functors (including "strange" base functors for Natural)

   {tyName: "Foo"}
   | {baseFunctorOf: "Foo"}
   | "NaturalBF" | "NegativeBF"
-}

-- | @since 1.3.0
encodeTyName :: TyName -> Encoding
encodeTyName t@(TyName tn)
  | isBaseFunctor t = case tn of
      "#Natural" -> "NaturalBF"
      "#Negative" -> "NegativeBF"
      _ -> pairs ("baseFunctorOf" .= T.drop 1 tn)
  | otherwise = pairs ("tyName" .= tn)

-- | The type name must conform with the type naming rules, i.e. it must
--   1. Begin with a capital letter
--   2. Consist only of alphanumeric characters and underscores
-- @since 1.3.0
decodeTyName :: Value -> ASGParser TyName
decodeTyName = liftParser . go
  where
    {- This is annoying. The thing we're getting *might* be an object or it might be a string,
        and we have to validate the result.
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

-- For type and constructor names
validateProperName :: Text -> Parser Text
validateProperName nm
  | T.null nm = fail $ "Empty String cannot be a TyName"
  | isUpper (T.head nm) && T.all isAlphaNum nm = pure nm
  | otherwise = fail $ "Could not validate TyName '" <> T.unpack nm <> "'"

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
decodeConstructorName =
  liftParser
    . withText
      "ConstructorName"
      ( \nm -> do
          validated <- validateProperName nm
          pure . ConstructorName $ validated
      )

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
  SOP -> pairs ("tag" .= ("SOP" :: String) <> "fields" .= ([] :: [String]))
  PlutusData strat ->
    let fields = list encodePlutusDataStrategy [strat]
     in pairs $
          "tag" .= ("PlutusData" :: String)
            <> pair "fields" fields
  BuiltinStrategy internalStrat ->
    let fields = list encodeInternalStrategy [internalStrat]
     in pairs $
          "tag" .= ("BuiltinStrategy" :: String)
            <> pair "fields" fields

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
encodePlutusDataStrategy strat = pairs $ "tag" .= show strat

-- | @since 1.3.0
decodePlutusDataStrategy :: Value -> ASGParser PlutusDataStrategy
decodePlutusDataStrategy =
  caseOnTag
    [ "EnumData" :=> constM EnumData,
      "ProductListData" :=> constM ProductListData,
      "ConstrData" :=> constM ConstrData,
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
encodeInternalStrategy strat = pairs $ "tag" .= show strat

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
encodePlutusDataConstructor pdc = pairs $ "tag" .= show pdc

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
    goDataDecl, goOpaqueData :: Object -> ASGParser (DataDeclaration AbstractTy)

    goDataDecl obj = do
      fieldsObj <- lookupAndParse' obj "fields" (withObject' "Datatype fields" pure)
      dtName <- lookupAndParse' fieldsObj "datatypeName" decodeTyName
      dtBinders <- lookupAndParse' fieldsObj "datatypeBinders" decodeCount
      dtCtors <- lookupAndParse' fieldsObj "datatypeConstructors" (withArray' "Datatype ctors" (traverse decodeConstructor))
      dtEncoding <- lookupAndParse' fieldsObj "datatypeEncoding" decodeDataEncoding
      pure $ DataDeclaration dtName dtBinders dtCtors dtEncoding

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
  AnArg arg' ->
    let argEnc = list encodeArg [arg']
     in pairs $
          "tag" .= ("AnArg" :: String)
            <> pair "fields" argEnc
  AnId i ->
    let idEnc = list encodeId [i]
     in pairs $
          "tag" .= ("AnId" :: String)
            <> pair "fields" idEnc

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
  ABoolean b ->
    pairs $
      pair "tag" "ABoolean"
        <> "fields" .= [b]
  AnInteger i ->
    pairs $
      pair "tag" "AnInteger"
        <> "fields" .= [i]
  AByteString bs ->
    pairs $
      pair "tag" "AByteString"
        <> "fields" .= [Hex.encodeHex bs]
  AString str ->
    pairs $
      pair "tag" "AString"
        <> "fields" .= [str]

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

   {tag: "LitInternal", fields: [a]}
   | {tag: "AppInternal", fields: [a,b]}
   | {tag: "ThunkInternal",fields: [a]}
   | {tag: "CataInternal", fields: [a,b]}
   | {tag: "DataConstructorInternal", fields: [a,b,c]}
   | {tag: "MatchInternal", fields: [a,b]}

-}

-- | @since 1.3.0
encodeValNodeInfo :: ValNodeInfo -> Encoding
encodeValNodeInfo = \case
  LitInternal aconst -> taggedFields "LitInternal" [encodeAConstant aconst]
  AppInternal f args -> taggedFields "AppInternal" [encodeId f, list encodeRef . toList $ args]
  ThunkInternal f -> taggedFields "ThunkInternal" [encodeId f]
  CataInternal r1 r2 -> taggedFields "CataInternal" [encodeRef r1, encodeRef r2]
  DataConstructorInternal tn cn args ->
    taggedFields
      "DataConstructorInternal"
      [ encodeTyName tn,
        encodeConstructorName cn,
        list encodeRef . toList $ args
      ]
  MatchInternal scrut branches ->
    taggedFields "MatchInternal" [encodeRef scrut, list encodeRef . toList $ branches]

-- | @since 1.3.0
decodeValNodeInfo :: Value -> ASGParser ValNodeInfo
decodeValNodeInfo =
  caseOnTag
    [ "LitInternal" :=> withField0 (fmap LitInternal . decodeAConstant),
      "AppInternal"
        :=> withFields
          ( \fieldsArr -> do
              f <- withIndex 0 decodeId fieldsArr
              args <- withIndex 1 (withArray' "App args" (traverse decodeRef)) fieldsArr
              pure $ AppInternal f args
          ),
      "ThunkInternal" :=> withField0 (fmap ThunkInternal . decodeId),
      "CataInternal"
        :=> withFields
          ( \fieldsArr -> do
              r1 <- withIndex 0 decodeRef fieldsArr
              r2 <- withIndex 1 decodeRef fieldsArr
              pure $ CataInternal r1 r2
          ),
      "DataConstructorInternal"
        :=> withFields
          ( \fieldsArr -> do
              tn <- withIndex 0 decodeTyName fieldsArr
              ctorNm <- withIndex 1 decodeConstructorName fieldsArr
              args <- withIndex 2 (withArray' "Datatype args" (traverse decodeRef)) fieldsArr
              pure $ DataConstructorInternal tn ctorNm args
          ),
      "MatchInternal"
        :=> withFields
          ( \fieldsArr -> do
              scrut <- withIndex 0 decodeRef fieldsArr
              args <- withIndex 1 (withArray' "Match branches" (traverse decodeRef)) fieldsArr
              pure $ MatchInternal scrut args
          )
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
  vRaw <- liftParser $ parseJSON @Word32 v
  pure . fromJust . preview asInt . fromIntegral $ vRaw

{- AbstractTy

   Standard product serialization as array:

     @BoundAt (S Z) ix0@
   ->
     [1,0]
-}

-- | @since 1.3.0
encodeAbstractTy :: AbstractTy -> Encoding
encodeAbstractTy (BoundAt db i) = econcat [encodeDeBruijn db, encodeIndex i]

-- | @since 1.3.0
decodeAbstractTy :: Value -> ASGParser AbstractTy
decodeAbstractTy = withArray' "AbstractTy" $ \arr -> do
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
  vRaw <- liftParser $ parseJSON @Word32 v
  pure . fromJust . preview intCount . fromIntegral $ vRaw

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
  vRaw <- liftParser $ parseJSON @Word32 v
  pure . fromJust . preview intIndex . fromIntegral $ vRaw

{- CompT AbstractTy

   Standard serialization as an array:

     @CompT count0 ...body...@
    ->
     [0,...encodedBody...]

-}

-- | @since 1.3.0
encodeCompT :: CompT AbstractTy -> Encoding
encodeCompT (CompT cnt body) = econcat [encodeCount cnt, encodeCompTBody body]

-- | @since 1.3.0
decodeCompT :: Value -> ASGParser (CompT AbstractTy)
decodeCompT = withArray' "CompT" $ \arr -> do
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
  tysAsList <- traverse decodeValTAbstractTy . toList $ arr
  case tysAsList of
    [] -> failParse "Empty vector of types in a CompTBody"
    (x : xs) -> pure . CompTBody $ NEV.fromNonEmpty (x :| xs)

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
    [ "UnitT" :=> \_ -> pure UnitT,
      "BoolT" :=> \_ -> pure BoolT,
      "IntegerT" :=> \_ -> pure IntegerT,
      "StringT" :=> \_ -> pure StringT,
      "ByteStringT" :=> \_ -> pure ByteStringT,
      "BLS12_381_G1_ElementT" :=> \_ -> pure BLS12_381_G1_ElementT,
      "BLS12_381_G2_ElementT" :=> \_ -> pure BLS12_381_G2_ElementT,
      "BLS12_381_MlResultT" :=> \_ -> pure BLS12_381_MlResultT
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
decodeOneArgFunc = error "TODO: Implement decodeOneArgFunc"

{- TwoArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}

-- | @since 1.3.0
encodeTwoArgFunc :: TwoArgFunc -> Encoding
encodeTwoArgFunc = encodeEnum

-- | @since 1.3.0
decodeTwoArgFunc :: Value -> ASGParser TwoArgFunc
decodeTwoArgFunc = error "TODO: Implement decodeTwoArgFunc"

{- ThreeArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}

-- | @since 1.3.0
encodeThreeArgFunc :: ThreeArgFunc -> Encoding
encodeThreeArgFunc = encodeEnum

-- | @since 1.3.0
decodeThreeArgFunc :: Value -> ASGParser ThreeArgFunc
decodeThreeArgFunc = error "TODO: Implement decodeThreeArgFunc"

{- SixArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}

-- | @since 1.3.0
encodeSixArgFunc :: SixArgFunc -> Encoding
encodeSixArgFunc = encodeEnum

-- | @since 1.3.0
decodeSixArgFunc :: Value -> ASGParser SixArgFunc
decodeSixArgFunc = error "TODO: Implement decodeSixArgFunc"

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
  Abstraction x -> pairs $ pair "tag" "Abstraction" <> pair "fields" (list encodeAbstractTy [x])
  ThunkT compT -> pairs $ pair "tag" "ThunkT" <> pair "fields" (list encodeCompT [compT])
  BuiltinFlat biFlat -> pairs $ pair "tag" "BuiltinFlat" <> pair "fields" (list encodeBuiltinFlatT [biFlat])
  Datatype tn args ->
    pairs $
      pair "tag" "Datatype"
        <> pair "fields" (econcat [encodeTyName tn, list encodeValTAbstractTy . toList $ args])

-- | @since 1.3.0
decodeValTAbstractTy :: Value -> ASGParser (ValT AbstractTy)
decodeValTAbstractTy =
  caseOnTag
    [ "Abstraction" :=> withField0 (fmap Abstraction . decodeAbstractTy),
      "ThunkT" :=> withField0 (fmap ThunkT . decodeCompT),
      "BuiltinFlat" :=> withField0 (fmap BuiltinFlat . decodeBuiltinFlatT),
      "Datatype"
        :=> withFields
          ( \arr -> do
              tn <- withIndex 0 decodeTyName arr
              ctors <- withIndex 1 (withArray' "datatype args" (traverse decodeValTAbstractTy)) arr
              pure $ Datatype tn ctors
          )
    ]

-- Helpers

liftParser :: forall (a :: Type). Parser a -> ASGParser a
liftParser = ASGParser . lift . lift . lift

-- Mainly for readability/custom fixity, effectively (,)
data (:=>) a b = a :=> b

infixr 0 :=>

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

constM :: forall (f :: Type -> Type) (a :: Type). (Applicative f) => a -> (forall (b :: Type). b -> f a)
constM x _ = pure x

-- This isn't imported from Aeson.Types.Internal but I need it -_-
prependContext :: forall (a :: Type). String -> Parser a -> Parser a
prependContext name = prependFailure ("parsing " ++ name ++ " failed, ")

withObject' ::
  forall (a :: Type).
  String ->
  (Object -> ASGParser a) ->
  Value ->
  ASGParser a
withObject' _ f (Object obj) = f obj
withObject' nm _ v = liftParser $ prependContext nm (typeMismatch "Object" v)

withArray' ::
  forall (a :: Type).
  String ->
  (Array -> ASGParser a) ->
  Value ->
  ASGParser a
withArray' _ f (Array arr) = f arr
withArray' nm _ v = liftParser $ prependContext nm (typeMismatch "Array" v)

withText' ::
  forall (a :: Type).
  String ->
  (Text -> ASGParser a) ->
  Value ->
  ASGParser a
withText' _ f (String str) = f str
withText' nm _ v = liftParser $ prependContext nm (typeMismatch "Text" v)

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
withField0 f = withFields (withIndex 0 f)

lookupAndParse :: forall (a :: Type). Object -> Key -> (Value -> Parser a) -> Parser a
lookupAndParse obj k f = case KM.lookup k obj of
  Nothing -> fail $ "No key '" <> show k <> "' found in object"
  Just v -> f v

lookupAndParse' :: forall (a :: Type). Object -> Key -> (Value -> ASGParser a) -> ASGParser a
lookupAndParse' obj k f = case KM.lookup k obj of
  Nothing -> failParse $ "No key '" <> show k <> "' found in object"
  Just v -> f v

failParse :: forall (a :: Type). String -> ASGParser a
failParse = liftParser . fail

encodeEnum :: forall (a :: Type). (Show a) => a -> Encoding
encodeEnum = pairs . ("tag" .=) . show

isBaseFunctor :: TyName -> Bool
isBaseFunctor (TyName tn) = T.head tn == '#'

tag :: forall (v :: Type). (ToJSON v) => v -> Series
tag v = "tag" .= v

taggedFields :: Text -> [Encoding] -> Encoding
taggedFields tg fieldArgs = pairs $ "tag" .= tg <> pair "fields" (econcat fieldArgs)

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
