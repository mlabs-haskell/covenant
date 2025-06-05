{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use camelCase" #-}
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
    ScopeBoundary (..), -- used in the generators
    DataEncoding (..),
    PlutusDataConstructor (..),
    PlutusDataStrategy (..),
    InternalStrategy (..),
    runConstructorName,
    abstraction,
    thunkT,
    builtinFlat,
    datatype,
    -- generic utility for debugging/testing
    prettyStr,
    checkStrategy,
    naturalBaseFunctor,
    negativeBaseFunctor,
    byteStringBaseFunctor,
  )
where

import Control.Monad.Reader
  ( MonadReader (local),
    Reader,
    asks,
    runReader,
  )
import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index
  ( Count,
    Index,
    count1,
    intCount,
    intIndex,
    ix0,
  )
import Data.Functor.Classes (Eq1 (liftEq))
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.String (IsString)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word64)
import GHC.Exts (fromListN)
import Optics.At ()
import Optics.Core
  ( A_Fold,
    A_Lens,
    LabelOptic (labelOptic),
    Prism',
    folding,
    ix,
    lens,
    over,
    preview,
    prism,
    review,
    set,
    view,
    (%),
  )
import Prettyprinter
  ( Doc,
    Pretty (pretty),
    defaultLayoutOptions,
    hsep,
    indent,
    layoutPretty,
    parens,
    vcat,
    viaShow,
    (<+>),
  )
import Prettyprinter.Render.Text (renderStrict)
import Test.QuickCheck.Instances.Text ()

-- need the arbitary instance for TyName
-- largely for TyName

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

-- | @since 1.1.0
newtype TyName = TyName Text
  deriving (Show, Eq, Ord, IsString) via Text

-- | @since 1.0.0
instance Pretty (CompT Renamed) where
  pretty = runPrettyM . prettyCompTWithContext

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
  | -- An applied type constructor, with a vector of arguments (which may be empty if the constructor is nullary)
    Datatype TyName (Vector (ValT a))
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

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

-- | All builtin types that are \'flat\': that is, do not have other types
-- \'nested inside them\'.
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

prettyStr :: forall (b :: Type). (Pretty b) => b -> String
prettyStr = T.unpack . renderStrict . layoutPretty defaultLayoutOptions . pretty

newtype ScopeBoundary = ScopeBoundary Int
  deriving (Show, Eq, Ord, Num, Real, Enum, Integral) via Int

-- Keeping the field names for clarity even if we don't use them
data PrettyContext (ann :: Type)
  = PrettyContext
  { _boundIdents :: Map ScopeBoundary (Vector (Doc ann)),
    _currentScope :: ScopeBoundary,
    _varStream :: [Doc ann]
  }

instance
  (k ~ A_Lens, a ~ Map ScopeBoundary (Vector (Doc ann)), b ~ Map ScopeBoundary (Vector (Doc ann))) =>
  LabelOptic "boundIdents" k (PrettyContext ann) (PrettyContext ann) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(PrettyContext x _ _) -> x)
      (\(PrettyContext _ y z) x -> PrettyContext x y z)

instance
  (k ~ A_Lens, a ~ ScopeBoundary, b ~ ScopeBoundary) =>
  LabelOptic "currentScope" k (PrettyContext ann) (PrettyContext ann) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(PrettyContext _ x _) -> x)
      (\(PrettyContext x _ z) y -> PrettyContext x y z)

instance
  (k ~ A_Lens, a ~ [Doc ann], b ~ [Doc ann]) =>
  LabelOptic "varStream" k (PrettyContext ann) (PrettyContext ann) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(PrettyContext _ _ x) -> x)
      (\(PrettyContext x y _) z -> PrettyContext x y z)

-- Maybe make a newtype with error reporting since this can fail, but do later since *should't* fail
newtype PrettyM (ann :: Type) (a :: Type) = PrettyM (Reader (PrettyContext ann) a)
  deriving
    ( Functor,
      Applicative,
      Monad,
      MonadReader (PrettyContext ann)
    )
    via (Reader (PrettyContext ann))

runPrettyM :: forall (ann :: Type) (a :: Type). PrettyM ann a -> a
runPrettyM (PrettyM ma) = runReader ma (PrettyContext mempty 0 infiniteVars)
  where
    -- Lazily generated infinite list of variables. Will start with a, b, c...
    -- and cycle around to a1, b2, c3 etc.
    -- We could do something more sophisticated but this should work.
    infiniteVars :: [Doc ann]
    infiniteVars =
      let aToZ = ['a' .. 'z']
          intStrings = ("" <$ aToZ) <> map (show @Integer) [0 ..]
       in zipWith (\x xs -> pretty (x : xs)) aToZ intStrings

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

bindVars ::
  forall (ann :: Type) (a :: Type).
  Count "tyvar" ->
  (Vector (Doc ann) -> PrettyM ann a) ->
  PrettyM ann a
bindVars count' act
  | count == 0 = crossBoundary (act Vector.empty)
  | otherwise = crossBoundary $ do
      here <- asks (view #currentScope)
      withFreshVarNames count $ \newBoundVars ->
        local (over #boundIdents (Map.insert here newBoundVars)) (act newBoundVars)
  where
    -- Increment the current scope
    crossBoundary :: PrettyM ann a -> PrettyM ann a
    crossBoundary = local (over #currentScope (+ 1))
    count :: Int
    count = review intCount count'

mkForall ::
  forall (ann :: Type).
  Vector (Doc ann) ->
  Doc ann ->
  Doc ann
mkForall tvars funTyBody =
  if Vector.null tvars
    then funTyBody
    else "forall" <+> hsep (Vector.toList tvars) <> "." <+> funTyBody

-- | DO NOT USE THIS TO WRITE OTHER INSTANCES
--   It exists soley to make readable tests easier to write w/o having to export a bunch of internal printing stuff
instance Pretty (ValT Renamed) where
  pretty = runPrettyM . prettyValTWithContext

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

-- Generate N fresh var names and use the supplied monadic function to do something with them.
withFreshVarNames ::
  forall (ann :: Type) (a :: Type).
  Int ->
  (Vector (Doc ann) -> PrettyM ann a) ->
  PrettyM ann a
withFreshVarNames n act = do
  stream <- asks (view #varStream)
  let (used, rest) = splitAt n stream
  local (set #varStream rest) . act . fromListN n $ used

prettyRenamedWithContext :: forall (ann :: Type). Renamed -> PrettyM ann (Doc ann)
prettyRenamedWithContext = \case
  Rigid offset index -> lookupAbstraction offset index
  Unifiable i -> lookupAbstraction 0 i
  Wildcard w64 offset i -> pure $ pretty offset <> "_" <> viaShow w64 <> "#" <> pretty (review intIndex i)

lookupAbstraction :: forall (ann :: Type). Int -> Index "tyvar" -> PrettyM ann (Doc ann)
lookupAbstraction offset argIndex = do
  let scopeOffset = ScopeBoundary offset
  let argIndex' = review intIndex argIndex
  here <- asks (view #currentScope)
  asks (preview (#boundIdents % ix (here + scopeOffset) % ix argIndex')) >>= \case
    Nothing ->
      -- TODO: actual error reporting
      error $
        "Internal error: The encountered a variable at arg index "
          <> show argIndex'
          <> " with true level "
          <> show scopeOffset
          <> " but could not locate the corresponding pretty form at scope level "
          <> show here
    Just res' -> pure res'

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

-- Datatype stuff. Stashing this here for now because this much is needed for the ValT change PR
-- (technically only need TyName for the ValT change but the "kind checker" needs decls)

-- @since 1.1.0
newtype ConstructorName = ConstructorName Text
  deriving (Show, Eq, Ord, IsString) via Text

-- @since 1.1.0
runConstructorName :: ConstructorName -> Text
runConstructorName (ConstructorName nm) = nm

-- I.e. a product in the sum of products
data Constructor (a :: Type)
  = Constructor ConstructorName (Vector (ValT a))
  deriving stock (Show, Eq)

instance Eq1 Constructor where
  liftEq f (Constructor nm args) (Constructor nm' args') = nm == nm' && liftEq (liftEq f) args args'

instance (k ~ A_Lens, a ~ ConstructorName, b ~ ConstructorName) => LabelOptic "constructorName" k (Constructor c) (Constructor c) a b where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(Constructor n _) -> n) (\(Constructor _ args) n -> Constructor n args)

instance (k ~ A_Lens, a ~ Vector (ValT c), b ~ Vector (ValT c)) => LabelOptic "constructorArgs" k (Constructor c) (Constructor c) a b where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(Constructor _ args) -> args) (\(Constructor n _) args -> Constructor n args)

-- | @since 1.1.0
data DataEncoding
  = SOP
  | PlutusData PlutusDataStrategy
  | BuiltinStrategy InternalStrategy
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq,
      -- | @since 1.1.0
      Ord
    )

-- | @since 1.1.0
data PlutusDataConstructor
  = PD_I
  | PD_B
  | PD_Constructor
  | PD_List
  | PD_Map
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq,
      -- | @since 1.1.0
      Ord
    )

-- | @since 1.1.0
-- NOTE: Wrapped data-primitive (Integer + ByteString) require a special case for their encoders, which was originally
--       part of a "WrapperData" strategy here which we generalized to the NewtypeData strategy.
data PlutusDataStrategy
  = EnumData
  | ProductListData
  | ConstrData
  | NewtypeData
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq,
      -- | @since 1.1.0
      Ord
    )

-- TxID encoding changes from v2 to v3 (so make sure to use the v3) / MLResult has a weird broken instance
data InternalStrategy = InternalListStrat | InternalPairStrat | InternalDataStrat | InternalAssocMapStrat
  deriving stock (Show, Eq, Ord)

-- | @since 1.1.0
data DataDeclaration a
  = DataDeclaration TyName (Count "tyvar") (Vector (Constructor a)) DataEncoding -- Allows for representations of "empty" types in case we want to represent Void like that
  | OpaqueData TyName (Set PlutusDataConstructor)
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq
    )

checkStrategy :: forall (a :: Type). DataDeclaration a -> Bool
checkStrategy OpaqueData {} = True
checkStrategy (DataDeclaration _ _ _ SOP) = True
{- This isn't *ideal* -}
checkStrategy (DataDeclaration tn _ _ (BuiltinStrategy internalStrat)) = case internalStrat of
  InternalListStrat -> tn == TyName "List"
  InternalPairStrat -> tn == TyName "Pair"
  InternalDataStrat -> tn == TyName "Data"
  InternalAssocMapStrat -> tn == TyName "Map"
checkStrategy (DataDeclaration _ _ ctors (PlutusData strat)) = case strat of
  ConstrData -> True
  EnumData -> all (\(Constructor _ args) -> Vector.null args) ctors
  ProductListData -> Vector.length ctors == 1
  NewtypeData
    | Vector.length ctors == 1 -> case Vector.toList <$> preview #constructorArgs (ctors Vector.! 0) of
        Just [_] -> True -- pushing the cycle check to the "kind checker"
        _ -> False
    | otherwise -> False

instance Pretty (DataDeclaration Renamed) where
  pretty = runPrettyM . prettyDataDeclWithContext

instance (k ~ A_Lens, a ~ TyName, b ~ TyName) => LabelOptic "datatypeName" k (DataDeclaration c) (DataDeclaration c) a b where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\case OpaqueData tn _ -> tn; DataDeclaration tn _ _ _ -> tn)
      (\decl tn -> case decl of OpaqueData _ x -> OpaqueData tn x; DataDeclaration _ x y z -> DataDeclaration tn x y z)

instance (k ~ A_Fold, a ~ Count "tyvar", b ~ Count "tyvar") => LabelOptic "datatypeBinders" k (DataDeclaration c) (DataDeclaration c) a b where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    folding $ \case
      DataDeclaration _ cnt _ _ -> Just cnt
      _ -> Nothing

instance (k ~ A_Fold, a ~ Vector (Constructor c), b ~ Vector (Constructor c)) => LabelOptic "datatypeConstructors" k (DataDeclaration c) (DataDeclaration c) a b where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    folding $ \case
      DataDeclaration _ _ ctors _ -> Just ctors
      _ -> Nothing
