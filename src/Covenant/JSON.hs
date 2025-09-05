{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module Covenant.JSON where

import Data.Map (Map)
import Covenant.Type (CompT,
    CompTBody,
    AbstractTy,
    DataEncoding,
    PlutusDataStrategy,
    BuiltinFlatT,
    Constructor,
    ConstructorName,
    DataDeclaration,
    PlutusDataConstructor,
    TyName,
    ValT)
import Covenant.ASG (ASGParser,
                     Id, Ref, ASGNode, Arg, ValNodeInfo, CompNodeInfo, ASGNode )

import Data.Aeson (ToJSON(toEncoding,toJSON),
                   FromJSON(parseJSON),Encoding,Value)
import GHC.TypeLits (Symbol, KnownSymbol)
import Covenant.Index (Count, Index)
import Covenant.Prim (OneArgFunc, TwoArgFunc, ThreeArgFunc, SixArgFunc)
import Covenant.Constant (AConstant)
import Covenant.DeBruijn (DeBruijn)

data Version = Version {_major :: Int, _minor :: Int}
  deriving stock (Show, Eq, Ord)

data CompilationUnit
  = CompilationUnit {
      _datatypes :: Map TyName (DataDeclaration AbstractTy),
      _asg       :: Map Id ASGNode,
      _version   :: Version
    } deriving stock (Show, Eq)

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
    encodingStub = encFn <> " :: " <> ty <> " -> " <> "Encoding"
                   <> "\n" <> encFn <> " = error \"TODO: Implement " <> encFn <> "\""
    decodingStub = decFn <> " :: Value -> ASGParser (" <> ty <> ")"
                   <> "\n" <> decFn <> " = error \"TODO: Implement " <> decFn <> "\""


{- Version

   Serializes as an object with the fields you'd expect.

     Version 1 2
   ->
     {major: 1, minor: 2}

-}
encodeVersion :: Version -> Encoding
encodeVersion = error "TODO: Implement encodeVersion"

decodeVersion :: Value -> ASGParser Version
decodeVersion = error "TODO: Implement decodeVersion"

{- DataDeclaration & its components -}

{- Encodes as a simple JSON string, e.g.
   TyName "Foo" -> "Foo"
-}
encodeTyName :: TyName -> Encoding
encodeTyName = error "TODO: Implement encodeTyName"

-- NOTE: Need to validate that the string conforms w/ the Type naming rules
decodeTyName :: Value -> ASGParser TyName
decodeTyName = error "TODO: Implement decodeTyName"

{- Encodes as a simple JSON string, e.g.
   ConstructorName "Foo" -> "Foo"
-}
encodeConstructorName :: TyName -> Encoding
encodeConstructorName = error "TODO: Implement encodeConstructorName"

-- NOTE: Need to validate that the string conforms w/ the Type naming rules
decodeConstructorName :: Value -> ASGParser ConstructorName
decodeConstructorName = error "TODO: Implement decodeConstructorName"


{- Encodes as an object. E.g.:

   Constructor "Just" [IntegerT]
   ->
   { constructorName: "Just"
   , constructorArgs: [...]}

-}
encodeConstructor :: Constructor AbstractTy -> Encoding
encodeConstructor = error "TODO: Implement encodeConstructor"

decodeConstructor :: Value -> ASGParser (Constructor AbstractTy)
decodeConstructor = error "TODO: Implement decodeConstructor"


{- DataEncoding encodes as a typical sum type, and will look like:

   {tag: "SOP", fields: []}
   | {tag: "PlutusData", fields: [...]}
   | {tag: "BuiltinStrategy", fields: [...]}
-}
encodeDataEncoding :: DataEncoding -> Encoding
encodeDataEncoding = error "TODO: Implement encodeDataEncoding"

decodeDataEncoding :: Value -> ASGParser a
decodeDataEncoding = error "TODO: Implement decodeDataEncoding"

{- PlutusDataStrategy encodes as a typical sum type. (Omitting the 'fields' field b/c it's an enumeration)

   {tag: "EnumData"}
   | {tag: "ProductListData"}
   | {tag: "ConstrData"}
   | {tag: "NewtypeData"}

-}
encodePlutusDataStrategy :: PlutusDataStrategy -> Encoding
encodePlutusDataStrategy = error "TODO: Implement encodePlutusDataStrategy"

decodePlutusDataStrategy :: Value -> ASGParser PlutusDataStrategy
decodePlutusDataStrategy = error "TODO: Implement decodePlutusDataStrategy"


{- PlutusDataConstructor encodes as a typical enumeration type:

  {tag: "PlutusI"}
  | {tag: "PlutusB"}
  | {tag: "PlutusConstr"}
  | {tag: "PlutusList"}
  | {tag: PlutusMap}

-}
encodePlutusDataConstructor :: PlutusDataConstructor -> Encoding
encodePlutusDataConstructor = error "TODO: Implement encodePlutusDataConstructor"

decodePlutusDataConstructor :: Value -> ASGParser PlutusDataConstructor
decodePlutusDataConstructor = error "TODO: Implement decodePlutusDataConstructor"

{- DataDeclaration AbstractTy is a bit atypical. It is a sum type, but I think it makes more sense to encode
   the arguments to the `DataDeclaration` constructor as an object instead of an array (to reduce the possibility for
   frontend errors).

   For example, if we have:

     1. DataDeclaration "Maybe" (Count 1) [...Nothing...,...Just...] SOP

   It will seralize like:

     {tag: "DataDeclaration"
     , fields: {
        datatypeName: "Maybe",
        datatypeBinders: 1,
        datatypeConstructors: [...],
        datatypeEncoding: {tag: "SOP"}
     }}

   For consistency, we do the same thing with Opaques. E.g.:

     2. OpaqueData "Foo" [Plutus_I]

   Will serialize to:

     { tag: "OpaqueData"
     , fields: {
       datatypeName: "Foo",
       opaquePlutusConstructors: {tag: "Plutus_I"}
     }}
-}
encodeDataDeclarationAbstractTy :: DataDeclaration AbstractTy -> Encoding
encodeDataDeclarationAbstractTy = error "TODO: Implement encodeDataDeclarationAbstractTy"

decodeDataDeclarationAbstractTy :: Value -> ASGParser (DataDeclaration AbstractTy)
decodeDataDeclarationAbstractTy = error "TODO: Implement decodeDataDeclarationAbstractTy"

{- ASG Specific Types & Components

-}

{- Id encodes directly as a number. E.g.:

   Id 101 -> 101
-}

encodeId :: Id -> Encoding
encodeId = error "TODO: Implement encodeId"

decodeId :: Value -> ASGParser Id
decodeId = error "TODO: Implement decodeId"

{- Ref encodes as a tagged sum type, e.g.

   {tag: "AnArg", fields: [...]}
   | {tag: "AnId": fields: [101]}
-}
encodeRef :: Ref -> Encoding
encodeRef = error "TODO: Implement encodeRef"

decodeRef :: Value -> ASGParser Ref
decodeRef = error "TODO: Implement decodeRef"

{- Arg encodes as an object, e.g.:

   {argDebruijn: 0,
    argIndex: 1,
    argType: ...
   }

-}
encodeArg :: Arg -> Encoding
encodeArg = error "TODO: Implement encodeArg"

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
encodeAConstant :: AConstant -> Encoding
encodeAConstant = error "TODO: Implement encodeAConstant"

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
encodeValNodeInfo :: ValNodeInfo -> Encoding
encodeValNodeInfo = error "TODO: Implement encodeValNodeInfo"

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
encodeCompNodeInfo :: CompNodeInfo -> Encoding
encodeCompNodeInfo = error "TODO: Implement encodeCompNodeInfo"

decodeCompNodeInfo :: Value -> ASGParser CompNodeInfo
decodeCompNodeInfo = error "TODO: Implement decodeCompNodeInfo"

{- ASGNode

   Serializes as a sum type without named fields:

   {tag: "ACompNode", fields: [ty,info]}
   | {tag: "AValNode", fields: [ty,info]}
   | {tag: "AnError"}

-}
encodeASGNode :: ASGNode -> Encoding
encodeASGNode = error "TODO: Implement encodeASGNode"

decodeASGNode :: Value -> ASGParser ASGNode
decodeASGNode = error "TODO: Implement decodeASGNode"

{- ***

ValT, CompT & Friends/Components

*** -}


{- DeBruijn

   Encodes directly as a number. E.g.

     S Z
   ->
     1

-}
encodeDeBruijn :: DeBruijn -> Encoding
encodeDeBruijn = error "TODO: Implement encodeDeBruijn"

decodeDeBruijn :: Value -> ASGParser DeBruijn
decodeDeBruijn = error "TODO: Implement decodeDeBruijn"

{- AbstractTy

   Standard product serialization as array:

     BoundAt (S Z) ix0
   ->
     [1,0]
-}
encodeAbstractTy :: AbstractTy -> Encoding
encodeAbstractTy = error "TODO: Implement encodeAbstractTy"

decodeAbstractTy :: Value -> ASGParser AbstractTy
decodeAbstractTy = error "TODO: Implement decodeAbstractTy"

{- Count

   Serializes as a Number.

    count0
   ->
    0

    count1
   ->
    1
-}
encodeCount :: forall (s :: Symbol). Count s -> Encoding
encodeCount = error "TODO: Implement encodeCount"

decodeCount :: forall (s :: Symbol). KnownSymbol s => Value -> ASGParser (Count s)
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
encodeIndex :: forall (s :: Symbol). Index s -> Encoding
encodeIndex = error "TODO: Implement encodeIndex"

decodeIndex :: forall (s :: Symbol). KnownSymbol s => Value -> ASGParser (Index s)
decodeIndex = error "TODO: Implement decodeIndex"

{- CompT AbstractTy

   Standard Product Array Serialization:

     CompT count0 ...body...
    ->
     [0,...encodedBody...]

-}
encodeCompT :: CompT AbstractTy -> Encoding
encodeCompT = error "TODO: Implement encodeCompTAbstractTy"

decodeCompT :: Value -> ASGParser (CompT AbstractTy)
decodeCompT = error "TODO: Implement decodeCompTAbstractTy"

{- CompTBodyAbstractTy

   This is a newtype over a NonEmptyVector and so encodes directly as an array.

     CompTBody [t1,t2,t3]
   ->
     [encodedT1,encodedT2,encodedT3]

-}
encodeCompTBody :: CompTBody AbstractTy -> Encoding
encodeCompTBody = error "TODO: Implement encodeCompTBodyAbstractTy"

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
encodeBuiltinFlatT :: BuiltinFlatT -> Encoding
encodeBuiltinFlatT = error "TODO: Implement encodeBuiltinFlatT"

decodeBuiltinFlatT :: Value -> ASGParser BuiltinFlatT
decodeBuiltinFlatT = error "TODO: Implement decodeBuiltinFlatT"

{- OneArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}
encodeOneArgFunc :: OneArgFunc -> Encoding
encodeOneArgFunc = error "TODO: Implement encodeOneArgFunc"

decodeOneArgFunc :: Value -> ASGParser OneArgFunc
decodeOneArgFunc = error "TODO: Implement decodeOneArgFunc"

{- TwoArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}
encodeTwoArgFunc :: TwoArgFunc -> Encoding
encodeTwoArgFunc = error "TODO: Implement encodeTwoArgFunc"

decodeTwoArgFunc :: Value -> ASGParser TwoArgFunc
decodeTwoArgFunc = error "TODO: Implement decodeTwoArgFunc"

{- ThreeArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}
encodeThreeArgFunc :: ThreeArgFunc -> Encoding
encodeThreeArgFunc = error "TODO: Implement encodeThreeArgFunc"

decodeThreeArgFunc :: Value -> ASGParser ThreeArgFunc
decodeThreeArgFunc = error "TODO: Implement decodeThreeArgFunc"

{- SixArgFunc

   Encodes as an enumeration (i.e. tag-only sum).

   The name of the tag literally matches the name of the constructor. (Too many to list)
-}
encodeSixArgFunc :: SixArgFunc -> Encoding
encodeSixArgFunc = error "TODO: Implement encodeSixArgFunc"

decodeSixArgFunc :: Value -> ASGParser SixArgFunc
decodeSixArgFunc = error "TODO: Implement decodeSixArgFunc"

{- ValT

   Encodes as a tagged sum without explicit field names:

   {tag: "Abstraction", fields: [...]}
   | {tag: "ThunkT", fields: [...]}
   | {tag: "BuiltinFlat", fields: [...]}
   | {tag: "Datatype", fields: [...]}

-}
encodeValTAbstractTy :: ValT AbstractTy -> Encoding
encodeValTAbstractTy = error "TODO: Implement encodeValTAbstractTy"

decodeValTAbstractTy :: Value -> ASGParser (ValT AbstractTy)
decodeValTAbstractTy = error "TODO: Implement decodeValTAbstractTy"
