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
--    data Foo = Bar | Baz Int
-- Is encoded to JSON using {tag: <CTOR NAME>, fields: [<Arg1>, <Arg2>, <ArgN>]}
--
-- This is the form used for all Haskell sum types which do NOT have `LabelOptic` instances. For those with
-- field names given by those instances, the `fields` part of the encoded sum is not an array of
-- arguments, but an object with names that correspond to the label optics. (The comments for each
-- function make clear which types are encoded in which way.)
-- @since 1.0.0
module Covenant.JSON where

import Control.Monad.Error.Class (MonadError)
import Control.Monad.HashCons (HashConsT, MonadHashCons)
import Control.Monad.Reader.Class (MonadReader)
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
import Covenant.Constant (AConstant)
import Covenant.DeBruijn (DeBruijn)
import Covenant.Index (Count, Index)
import Covenant.Internal.Term (CovenantTypeError)
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT,
    CompT,
    CompTBody,
    Constructor,
    ConstructorName,
    DataDeclaration,
    DataEncoding,
    PlutusDataConstructor,
    PlutusDataStrategy,
    TyName,
    ValT,
  )
import Data.Aeson
  ( Encoding,
    FromJSON (parseJSON),
    ToJSON (toEncoding, toJSON),
    Value,
  )
import Data.Aeson.Types (Parser)
import Data.Kind (Type)
import Data.Map (Map)
import GHC.TypeLits (KnownSymbol, Symbol)

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

{- Version

   Serializes as an object with the fields you'd expect.

     Version 1 2
   ->
     {major: 1, minor: 2}

-}

-- |  @since 1.3.0
encodeVersion :: Version -> Encoding
encodeVersion = error "TODO: Implement encodeVersion"

-- | @since 1.3.0
decodeVersion :: Value -> ASGParser Version
decodeVersion = error "TODO: Implement decodeVersion"

{- DataDeclaration & its components -}

{- Encodes as a simple JSON string, e.g.
   TyName "Foo" -> "Foo"
-}

-- | @since 1.3.0
encodeTyName :: TyName -> Encoding
encodeTyName = error "TODO: Implement encodeTyName"

-- | The type name must conform with the type naming rules, i.e. it must
--   1. Begin with a capital letter
--   2. Consist only of alphanumeric characters and underscores
-- @since 1.3.0
decodeTyName :: Value -> ASGParser TyName
decodeTyName = error "TODO: Implement decodeTyName"

{- Encodes as a simple JSON string, e.g.
   ConstructorName "Foo" -> "Foo"
-}

-- | @since 1.3.0
encodeConstructorName :: TyName -> Encoding
encodeConstructorName = error "TODO: Implement encodeConstructorName"

-- | The ctor name must conform with the ctor naming rules, i.e. it must
--   1. Begin with a capital letter
--   2. Consist only of alphanumeric characters and underscores
-- @since 1.3.0
decodeConstructorName :: Value -> ASGParser ConstructorName
decodeConstructorName = error "TODO: Implement decodeConstructorName"

{- Encodes as an object. E.g.:

   Constructor "Just" [IntegerT]
   ->
   { constructorName: "Just"
   , constructorArgs: [...]}

-}

-- | @since 1.3.0
encodeConstructor :: Constructor AbstractTy -> Encoding
encodeConstructor = error "TODO: Implement encodeConstructor"

-- | @since 1.3.0
decodeConstructor :: Value -> ASGParser (Constructor AbstractTy)
decodeConstructor = error "TODO: Implement decodeConstructor"

{- DataEncoding encodes as a typical sum type, and will look like:

   {tag: "SOP", fields: []}
   | {tag: "PlutusData", fields: [...]}
   | {tag: "BuiltinStrategy", fields: [...]}
-}

-- | @since 1.3.0
encodeDataEncoding :: DataEncoding -> Encoding
encodeDataEncoding = error "TODO: Implement encodeDataEncoding"

-- | @since 1.3.0
decodeDataEncoding :: Value -> ASGParser a
decodeDataEncoding = error "TODO: Implement decodeDataEncoding"

{- PlutusDataStrategy encodes as a typical sum type. (Omitting the 'fields' field b/c it's an enumeration)

   {tag: "EnumData"}
   | {tag: "ProductListData"}
   | {tag: "ConstrData"}
   | {tag: "NewtypeData"}

-}

-- | @since 1.3.0
encodePlutusDataStrategy :: PlutusDataStrategy -> Encoding
encodePlutusDataStrategy = error "TODO: Implement encodePlutusDataStrategy"

-- | @since 1.3.0
decodePlutusDataStrategy :: Value -> ASGParser PlutusDataStrategy
decodePlutusDataStrategy = error "TODO: Implement decodePlutusDataStrategy"

{- PlutusDataConstructor encodes as a typical enumeration type:

  {tag: "PlutusI"}
  | {tag: "PlutusB"}
  | {tag: "PlutusConstr"}
  | {tag: "PlutusList"}
  | {tag: PlutusMap}

-}

-- | @since 1.3.0
encodePlutusDataConstructor :: PlutusDataConstructor -> Encoding
encodePlutusDataConstructor = error "TODO: Implement encodePlutusDataConstructor"

-- | @since 1.3.0
decodePlutusDataConstructor :: Value -> ASGParser PlutusDataConstructor
decodePlutusDataConstructor = error "TODO: Implement decodePlutusDataConstructor"

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
       opaquePlutusConstructors: {tag: "Plutus_I"}
     }}
-}

-- | @since 1.3.0
encodeDataDeclarationAbstractTy :: DataDeclaration AbstractTy -> Encoding
encodeDataDeclarationAbstractTy = error "TODO: Implement encodeDataDeclarationAbstractTy"

-- | @since 1.3.0
decodeDataDeclarationAbstractTy :: Value -> ASGParser (DataDeclaration AbstractTy)
decodeDataDeclarationAbstractTy = error "TODO: Implement decodeDataDeclarationAbstractTy"

{- ASG Specific Types & Components

-}

{- Id encodes directly as a number. E.g.:

   @Id 101@ -> 101
-}

-- | @since 1.3.0
encodeId :: Id -> Encoding
encodeId = error "TODO: Implement encodeId"

-- | @since 1.3.0
decodeId :: Value -> ASGParser Id
decodeId = error "TODO: Implement decodeId"

{- Ref encodes as a typical sum type without named fields:

   {tag: "AnArg", fields: [...]}
   | {tag: "AnId": fields: [101]}
-}

-- | @since 1.3.0
encodeRef :: Ref -> Encoding
encodeRef = error "TODO: Implement encodeRef"

-- | @since 1.3.0
decodeRef :: Value -> ASGParser Ref
decodeRef = error "TODO: Implement decodeRef"

{- Arg encodes as an object, e.g.:

   {argDebruijn: 0,
    argIndex: 1,
    argType: ...
   }

-}

-- | @since 1.3.0
encodeArg :: Arg -> Encoding
encodeArg = error "TODO: Implement encodeArg"

-- | @since 1.3.0
decodeArg :: Value -> ASGParser Arg
decodeArg = error "TODO: Implement decodeArg"

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
encodeAConstant = error "TODO: Implement encodeAConstant"

-- | @since 1.3.0
decodeAConstant :: Value -> ASGParser AConstant
decodeAConstant = error "TODO: Implement decodeAConstant"

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
encodeValNodeInfo = error "TODO: Implement encodeValNodeInfo"

-- | @since 1.3.0
decodeValNodeInfo :: Value -> ASGParser ValNodeInfo
decodeValNodeInfo = error "TODO: Implement decodeValNodeInfo"

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
encodeCompNodeInfo = error "TODO: Implement encodeCompNodeInfo"

-- | @since 1.3.0
decodeCompNodeInfo :: Value -> ASGParser CompNodeInfo
decodeCompNodeInfo = error "TODO: Implement decodeCompNodeInfo"

{- ASGNode

   Serializes as a sum type without named fields:

   {tag: "ACompNode", fields: [ty,info]}
   | {tag: "AValNode", fields: [ty,info]}
   | {tag: "AnError"}

-}

-- | @since 1.3.0
encodeASGNode :: ASGNode -> Encoding
encodeASGNode = error "TODO: Implement encodeASGNode"

-- | @since 1.3.0
decodeASGNode :: Value -> ASGParser ASGNode
decodeASGNode = error "TODO: Implement decodeASGNode"

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
encodeDeBruijn = error "TODO: Implement encodeDeBruijn"

-- | @since 1.3.0
decodeDeBruijn :: Value -> ASGParser DeBruijn
decodeDeBruijn = error "TODO: Implement decodeDeBruijn"

{- AbstractTy

   Standard product serialization as array:

     @BoundAt (S Z) ix0@
   ->
     [1,0]
-}

-- | @since 1.3.0
encodeAbstractTy :: AbstractTy -> Encoding
encodeAbstractTy = error "TODO: Implement encodeAbstractTy"

-- | @since 1.3.0
decodeAbstractTy :: Value -> ASGParser AbstractTy
decodeAbstractTy = error "TODO: Implement decodeAbstractTy"

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
encodeCount = error "TODO: Implement encodeCount"

-- | @since 1.3.0
decodeCount :: forall (s :: Symbol). (KnownSymbol s) => Value -> ASGParser (Count s)
decodeCount = error "TODO: Implement decodeCount"

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
encodeIndex = error "TODO: Implement encodeIndex"

-- | @since 1.3.0
decodeIndex :: forall (s :: Symbol). (KnownSymbol s) => Value -> ASGParser (Index s)
decodeIndex = error "TODO: Implement decodeIndex"

{- CompT AbstractTy

   Standard serialization as an array:

     @CompT count0 ...body...@
    ->
     [0,...encodedBody...]

-}

-- | @since 1.3.0
encodeCompT :: CompT AbstractTy -> Encoding
encodeCompT = error "TODO: Implement encodeCompTAbstractTy"

-- | @since 1.3.0
decodeCompT :: Value -> ASGParser (CompT AbstractTy)
decodeCompT = error "TODO: Implement decodeCompTAbstractTy"

{- CompTBodyAbstractTy

   This is a newtype over a NonEmptyVector and so encodes directly as an array.

     @CompTBody [t1,t2,t3]@
   ->
     [encodedT1,encodedT2,encodedT3]

-}

-- | @since 1.3.0
encodeCompTBody :: CompTBody AbstractTy -> Encoding
encodeCompTBody = error "TODO: Implement encodeCompTBodyAbstractTy"

-- | @since 1.3.0
decodeCompTBody :: Value -> ASGParser (CompTBody AbstractTy)
decodeCompTBody = error "TODO: Implement decodeCompTBodyAbstractTy"

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
encodeBuiltinFlatT = error "TODO: Implement encodeBuiltinFlatT"

-- | @since 1.3.0
decodeBuiltinFlatT :: Value -> ASGParser BuiltinFlatT
decodeBuiltinFlatT = error "TODO: Implement decodeBuiltinFlatT"

{- OneArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}

-- | @since 1.3.0
encodeOneArgFunc :: OneArgFunc -> Encoding
encodeOneArgFunc = error "TODO: Implement encodeOneArgFunc"

-- | @since 1.3.0
decodeOneArgFunc :: Value -> ASGParser OneArgFunc
decodeOneArgFunc = error "TODO: Implement decodeOneArgFunc"

{- TwoArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}

-- | @since 1.3.0
encodeTwoArgFunc :: TwoArgFunc -> Encoding
encodeTwoArgFunc = error "TODO: Implement encodeTwoArgFunc"

-- | @since 1.3.0
decodeTwoArgFunc :: Value -> ASGParser TwoArgFunc
decodeTwoArgFunc = error "TODO: Implement decodeTwoArgFunc"

{- ThreeArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}

-- | @since 1.3.0
encodeThreeArgFunc :: ThreeArgFunc -> Encoding
encodeThreeArgFunc = error "TODO: Implement encodeThreeArgFunc"

-- | @since 1.3.0
decodeThreeArgFunc :: Value -> ASGParser ThreeArgFunc
decodeThreeArgFunc = error "TODO: Implement decodeThreeArgFunc"

{- SixArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}

-- | @since 1.3.0
encodeSixArgFunc :: SixArgFunc -> Encoding
encodeSixArgFunc = error "TODO: Implement encodeSixArgFunc"

-- | @since 1.3.0
decodeSixArgFunc :: Value -> ASGParser SixArgFunc
decodeSixArgFunc = error "TODO: Implement decodeSixArgFunc"

{- ValT

   Encodes as a tagged sum without explicit field names:

   {tag: "Abstraction", fields: [...]}
   | {tag: "ThunkT", fields: [...]}
   | {tag: "BuiltinFlat", fields: [...]}
   | {tag: "Datatype", fields: [...]}

-}

-- | @since 1.3.0
encodeValTAbstractTy :: ValT AbstractTy -> Encoding
encodeValTAbstractTy = error "TODO: Implement encodeValTAbstractTy"

-- | @since 1.3.0
decodeValTAbstractTy :: Value -> ASGParser (ValT AbstractTy)
decodeValTAbstractTy = error "TODO: Implement decodeValTAbstractTy"
