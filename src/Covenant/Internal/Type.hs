{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}

module Covenant.Internal.Type
  ( AbstractTy (..),
    Renamed (..),
    CompT (..),
    CompTBody (..),
    DataDeclaration (..),
    Constructor (..),
    ConstructorName (..),
    ValT (..),
    BuiltinFlatT (..),
    TyName (..),
    DataEncoding (..),
    runConstructorName,
    abstraction,
    thunkT,
    builtinFlat,
    datatype,
    checkStrategy,
    naturalBaseFunctor,
    negativeBaseFunctor,
    byteStringBaseFunctor,
    arity,
  )
where

import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index
  ( Count,
    Index,
    count1,
    intCount,
    intIndex,
    ix0,
  )
import Covenant.Internal.PrettyPrint
  ( PrettyM,
    bindVars,
    lookupAbstraction,
    mkForall,
    runPrettyM,
  )
import Covenant.Internal.Strategy
  ( DataEncoding
      ( BuiltinStrategy,
        PlutusData,
        SOP
      ),
    InternalStrategy
      ( InternalAssocMapStrat,
        InternalDataStrat,
        InternalListStrat,
        InternalOpaqueStrat,
        InternalPairStrat
      ),
    PlutusDataConstructor,
    PlutusDataStrategy
      ( ConstrData,
        EnumData,
        NewtypeData,
        ProductListData
      ),
  )
import Covenant.Util (pattern ConsV, pattern NilV)
import Data.Functor.Classes (Eq1 (liftEq))
import Data.Kind (Type)
import Data.Set (Set)
import Data.String (IsString)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word64)
import Optics.Core
  ( A_Fold,
    A_Lens,
    LabelOptic (labelOptic),
    Prism',
    folding,
    lens,
    preview,
    prism,
    review,
  )
import Prettyprinter
  ( Doc,
    Pretty (pretty),
    hsep,
    indent,
    parens,
    vcat,
    viaShow,
    (<+>),
  )
import Test.QuickCheck.Instances.Text ()

-- | A type abstraction, using a combination of a DeBruijn index (to indicate
-- which scope it refers to) and a positional index (to indicate which bound
-- variable in that scope it refers to).
--
-- = Important note
--
-- This is a /relative/ representation: any given 'AbstractTy' could refer to
-- different things when placed in different positions in the ASG. This stems
-- from how DeBruijn indices behave: 'Z' refers to \'our immediate enclosing
-- scope\', @'S' 'Z'@ to \'one scope outside our immediate enclosing scope\',
-- etc. This can mean different things depending on what these scope(s) are.
--
-- @since 1.0.0
data AbstractTy = BoundAt DeBruijn (Index "tyvar")
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A type abstraction that has undergone renaming from a specific context.
--
-- @since 1.0.0
data Renamed
  = -- | Set by an enclosing scope, and thus is essentially a
    -- concrete type, we just don't know which. First field is its \'true
    -- level\', second field is the positional index in that scope.
    Rigid Int (Index "tyvar")
  | -- | Can be unified with something, but must be consistent: that is, only one
    -- unification for every instance. Field is this variable's positional index;
    -- we don't need to track the scope, as only one scope contains unifiable
    -- bindings.
    Unifiable (Index "tyvar")
  | -- | /Must/ unify with everything, except with other distinct wildcards in the
    -- same scope. First field is a unique /scope/ identifier; second is its
    -- \'true level\' simialr to @'Rigid'@; third is the positional index within
    -- its scope. We must have unique identifiers for wildcard scopes, as
    -- wildcards unify with everything /except/ other wildcards in the /same/
    -- scope, and child scopes aren't unique.
    Wildcard Word64 Int (Index "tyvar")
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | The \'body\' of a computation type, consisting of the types of its
-- arguments and the type of its result.
--
-- @since 1.0.0
newtype CompTBody (a :: Type) = CompTBody (NonEmptyVector (ValT a))
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance Eq1 CompTBody where
  {-# INLINEABLE liftEq #-}
  liftEq f (CompTBody xs) (CompTBody ys) =
    liftEq (liftEq f) xs ys

-- | A computation type, with abstractions indicated by the type argument. In
-- pretty much any case imaginable, this would be either 'AbstractTy' (in the
-- ASG), or 'Renamed' (after renaming).
--
-- @since 1.0.0
data CompT (a :: Type) = CompT (Count "tyvar") (CompTBody a)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance Eq1 CompT where
  {-# INLINEABLE liftEq #-}
  liftEq f (CompT abses1 xs) (CompT abses2 ys) =
    abses1 == abses2 && liftEq f xs ys

-- | @since 1.0.0
instance Pretty (CompT Renamed) where
  pretty = runPrettyM . prettyCompTWithContext

-- | Determine the arity of a computation type: that is, how many arguments a
-- function of this type must be given.
--
-- @since 1.0.0
arity :: forall (a :: Type). CompT a -> Int
arity (CompT _ (CompTBody xs)) = NonEmpty.length xs - 1

-- | The name of a data type. This refers specifically to non-\'flat\' types
-- either provided by the ledger, or defined by the user.
--
-- @since 1.1.0
newtype TyName = TyName Text
  deriving
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq,
      -- | @since 1.1.0
      Ord,
      -- | @since 1.1.0
      IsString
    )
    via Text

-- | A value type, with abstractions indicated by the type argument. In pretty
-- much any case imaginable, this would be either 'AbstractTy' (in the ASG) or
-- 'Renamed' (after renaming).
--
-- @since 1.0.0
data ValT (a :: Type)
  = -- | An abstract type.
    Abstraction a
  | -- | A suspended computation.
    ThunkT (CompT a)
  | -- | A builtin type without any nesting.
    BuiltinFlat BuiltinFlatT
  | -- | An applied type constructor for a non-\'flat\' data type.
    -- | @since 1.1.0
    Datatype TyName (Vector (ValT a))
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance Eq1 ValT where
  {-# INLINEABLE liftEq #-}
  liftEq f = \case
    Abstraction abs1 -> \case
      Abstraction abs2 -> f abs1 abs2
      _ -> False
    ThunkT t1 -> \case
      ThunkT t2 -> liftEq f t1 t2
      _ -> False
    BuiltinFlat t1 -> \case
      BuiltinFlat t2 -> t1 == t2
      _ -> False
    Datatype tn1 args1 -> \case
      Datatype tn2 args2 -> tn1 == tn2 && liftEq (liftEq f) args1 args2
      _ -> False

-- | /Do not/ use this instance to write other 'Pretty' instances. It exists to
-- ensure readable tests without having to expose a lot of internals.
--
-- @since 1.0.0
instance Pretty (ValT Renamed) where
  pretty = runPrettyM . prettyValTWithContext

abstraction :: forall (a :: Type). Prism' (ValT a) a
abstraction = prism Abstraction (\case (Abstraction a) -> Right a; other -> Left other)

thunkT :: forall (a :: Type). Prism' (ValT a) (CompT a)
thunkT = prism ThunkT (\case (ThunkT compT) -> Right compT; other -> Left other)

builtinFlat :: forall (a :: Type). Prism' (ValT a) BuiltinFlatT
builtinFlat = prism BuiltinFlat (\case (BuiltinFlat bi) -> Right bi; other -> Left other)

datatype :: forall (a :: Type). Prism' (ValT a) (TyName, Vector (ValT a))
datatype =
  prism
    (uncurry Datatype)
    (\case (Datatype tn args) -> Right (tn, args); other -> Left other)

-- | All builtin types that are \'flat\': that is, do not have other types
-- \'nested inside them\'.
--
-- @since 1.0.0
data BuiltinFlatT
  = UnitT
  | BoolT
  | IntegerT
  | StringT
  | ByteStringT
  | BLS12_381_G1_ElementT
  | BLS12_381_G2_ElementT
  | BLS12_381_MlResultT
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | The name of a data type constructor.
--
-- @since 1.1.0
newtype ConstructorName = ConstructorName Text
  deriving
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq,
      -- | @since 1.1.0
      Ord,
      -- | @since 1.1.0
      IsString
    )
    via Text

-- | @since 1.1.0
runConstructorName :: ConstructorName -> Text
runConstructorName (ConstructorName nm) = nm

-- | A single constructor of a data type.
--
-- @since 1.1.0
data Constructor (a :: Type)
  = Constructor ConstructorName (Vector (ValT a))
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq
    )

-- | @since 1.1.0
instance Eq1 Constructor where
  liftEq f (Constructor nm args) (Constructor nm' args') =
    nm == nm' && liftEq (liftEq f) args args'

-- | @since 1.1.0
instance
  (k ~ A_Lens, a ~ ConstructorName, b ~ ConstructorName) =>
  LabelOptic "constructorName" k (Constructor c) (Constructor c) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(Constructor n _) -> n) (\(Constructor _ args) n -> Constructor n args)

-- | @since 1.1.0
instance
  (k ~ A_Lens, a ~ Vector (ValT c), b ~ Vector (ValT c)) =>
  LabelOptic "constructorArgs" k (Constructor c) (Constructor c) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(Constructor _ args) -> args) (\(Constructor n _) args -> Constructor n args)

-- | Description of a non-\'flat\' type, together with how it is encoded.
--
-- @since 1.1.0
data DataDeclaration a
  = DataDeclaration TyName (Count "tyvar") (Vector (Constructor a)) DataEncoding
  | OpaqueData TyName (Set PlutusDataConstructor)
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq
    )

-- | @since 1.1.0
instance Pretty (DataDeclaration Renamed) where
  pretty = runPrettyM . prettyDataDeclWithContext

-- | @since 1.1.0
instance
  (k ~ A_Lens, a ~ TyName, b ~ TyName) =>
  LabelOptic "datatypeName" k (DataDeclaration c) (DataDeclaration c) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\case OpaqueData tn _ -> tn; DataDeclaration tn _ _ _ -> tn)
      (\decl tn -> case decl of OpaqueData _ x -> OpaqueData tn x; DataDeclaration _ x y z -> DataDeclaration tn x y z)

-- | @since 1.1.0
instance
  (k ~ A_Fold, a ~ Count "tyvar", b ~ Count "tyvar") =>
  LabelOptic "datatypeBinders" k (DataDeclaration c) (DataDeclaration c) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    folding $ \case
      DataDeclaration _ cnt _ _ -> Just cnt
      _ -> Nothing

-- | @since 1.1.0
instance
  (k ~ A_Fold, a ~ Vector (Constructor c), b ~ Vector (Constructor c)) =>
  LabelOptic "datatypeConstructors" k (DataDeclaration c) (DataDeclaration c) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    folding $ \case
      DataDeclaration _ _ ctors _ -> Just ctors
      _ -> Nothing

-- | @since 1.1.0
instance
  (k ~ A_Lens, a ~ DataEncoding, b ~ DataEncoding) =>
  LabelOptic "datatypeEncoding" k (DataDeclaration c) (DataDeclaration c) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\case OpaqueData {} -> BuiltinStrategy InternalOpaqueStrat; DataDeclaration _ _ _ enc -> enc)
      (\decl enc -> case decl of OpaqueData tn x -> OpaqueData tn x; DataDeclaration tn x y _ -> DataDeclaration tn x y enc)

checkStrategy :: forall (a :: Type). DataDeclaration a -> Bool
checkStrategy = \case
  OpaqueData _ _ -> True
  DataDeclaration tn _ ctors strat -> case strat of
    SOP -> True
    BuiltinStrategy internalStrat -> case internalStrat of
      InternalListStrat -> tn == "List"
      InternalPairStrat -> tn == "Pair"
      InternalDataStrat -> tn == "Data"
      InternalAssocMapStrat -> tn == "Map"
      InternalOpaqueStrat -> False
    PlutusData plutusStrat -> case plutusStrat of
      ConstrData -> True
      EnumData -> all (\(Constructor _ args) -> null args) ctors
      ProductListData -> length ctors == 1
      NewtypeData -> case ctors of
        ConsV x NilV -> case preview #constructorArgs x of
          Just (ConsV _ NilV) -> True
          _ -> False
        _ -> False

naturalBaseFunctor :: DataDeclaration AbstractTy
naturalBaseFunctor = DataDeclaration "Natural_F" count1 constrs SOP
  where
    constrs :: Vector (Constructor AbstractTy)
    constrs =
      [ Constructor "ZeroNat_F" [],
        Constructor "SuccNat_F" [Abstraction . BoundAt Z $ ix0]
      ]

negativeBaseFunctor :: DataDeclaration AbstractTy
negativeBaseFunctor = DataDeclaration "Negative_F" count1 constrs SOP
  where
    constrs :: Vector (Constructor AbstractTy)
    constrs =
      [ Constructor "ZeroNeg_F" [],
        Constructor "PredNeg_F" [Abstraction . BoundAt Z $ ix0]
      ]

byteStringBaseFunctor :: DataDeclaration AbstractTy
byteStringBaseFunctor = DataDeclaration "ByteString_F" count1 constrs SOP
  where
    constrs :: Vector (Constructor AbstractTy)
    constrs =
      [ Constructor "EmptyByteString_F" [],
        Constructor "ConsByteString_F" [BuiltinFlat IntegerT, Abstraction . BoundAt Z $ ix0]
      ]

-- Helpers

prettyCompTWithContext :: forall (ann :: Type). CompT Renamed -> PrettyM ann (Doc ann)
prettyCompTWithContext (CompT count (CompTBody funArgs))
  | review intCount count == 0 = prettyFunTy' funArgs
  | otherwise = bindVars count $ \newVars -> do
      funTy <- prettyFunTy' funArgs
      pure $ mkForall newVars funTy

prettyFunTy' ::
  forall (ann :: Type).
  NonEmptyVector (ValT Renamed) ->
  PrettyM ann (Doc ann)
prettyFunTy' args = case NonEmpty.unsnoc args of
  (rest, resTy) -> do
    resTy' <- ("!" <>) <$> prettyValTWithContext resTy
    case Vector.uncons rest of
      Nothing -> pure resTy'
      Just (firstArg, otherArgs) -> do
        prettyArg1 <- prettyValTWithContext firstArg
        argsWithoutResult <- Vector.foldM (\acc x -> (\z -> acc <+> "->" <+> z) <$> prettyValTWithContext x) prettyArg1 otherArgs
        pure . parens $ argsWithoutResult <+> "->" <+> resTy'

prettyValTWithContext :: forall (ann :: Type). ValT Renamed -> PrettyM ann (Doc ann)
prettyValTWithContext = \case
  Abstraction abstr -> prettyRenamedWithContext abstr
  ThunkT compT -> prettyCompTWithContext compT
  BuiltinFlat biFlat -> pure $ viaShow biFlat
  Datatype (TyName tn) args -> do
    args' <- traverse prettyValTWithContext args
    let tn' = pretty tn
    case Vector.toList args' of
      [] -> pure tn'
      argsList -> pure . parens $ tn' <+> hsep argsList

prettyCtorWithContext :: forall (ann :: Type). Constructor Renamed -> PrettyM ann (Doc ann)
prettyCtorWithContext (Constructor ctorNm ctorArgs)
  | Vector.null ctorArgs = pure $ pretty (runConstructorName ctorNm)
  | otherwise = do
      let ctorNm' = pretty (runConstructorName ctorNm)
      args' <- Vector.toList <$> traverse prettyValTWithContext ctorArgs
      pure $ ctorNm' <+> hsep args'

prettyRenamedWithContext :: forall (ann :: Type). Renamed -> PrettyM ann (Doc ann)
prettyRenamedWithContext = \case
  Rigid offset index -> lookupAbstraction offset index
  Unifiable i -> lookupAbstraction 0 i
  Wildcard w64 offset i -> pure $ pretty offset <> "_" <> viaShow w64 <> "#" <> pretty (review intIndex i)

prettyDataDeclWithContext :: forall (ann :: Type). DataDeclaration Renamed -> PrettyM ann (Doc ann)
prettyDataDeclWithContext (OpaqueData (TyName tn) _) = pure . pretty $ tn
prettyDataDeclWithContext (DataDeclaration (TyName tn) numVars ctors _) = bindVars numVars $ \boundVars -> do
  let tn' = pretty tn
  ctors' <- traverse prettyCtorWithContext ctors
  let prettyCtors = indent 2 . vcat . prefix "| " . Vector.toList $ ctors'
  if Vector.null ctors
    then pure $ "data" <+> tn' <+> hsep (Vector.toList boundVars)
    else pure $ "data" <+> tn' <+> hsep (Vector.toList boundVars) <+> "=" <+> prettyCtors
  where
    -- I don't think there's a library fn that does this? This is for the `|` in a sum type.
    prefix :: Doc ann -> [Doc ann] -> [Doc ann]
    prefix _ [] = []
    prefix _ [x] = [x]
    prefix sep (x : xs) = x : goPrefix xs
      where
        goPrefix [] = []
        goPrefix (y : ys) = (sep <> y) : goPrefix ys
