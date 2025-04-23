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
    runTyName,
    runConstructorName,
    datatypeName,
    datatypeConstructors,
    datatypeBinders,
    constructorName,
    abstraction,
    thunkT,
    builtinFlat,
    datatype,
    constructorArgs,
  )
where

import Control.Monad.Reader
  ( MonadReader (local),
    Reader,
    asks,
    runReader,
  )
import Covenant.DeBruijn (DeBruijn)
import Covenant.Index
  ( Count,
    Index,
    intCount,
    intIndex,
  )
import Data.Functor.Classes (Eq1 (liftEq))
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.String (IsString)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word64)
import GHC.Exts (fromListN)
import Optics.At ()
import Optics.Core
  ( A_Lens,
    LabelOptic (labelOptic),
    Lens',
    Prism',
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
    hsep,
    indent,
    parens,
    vcat,
    viaShow,
    (<+>),
  )
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
    -- same scope. First field is a unique /scope/ identifier, second is the
    -- positional index within that scope. We must have unique identifiers for
    -- wildcard scopes, as wildcards unify with everything /except/ other
    -- wildcards in the same scope.
    Wildcard Word64 (Index "tyvar")
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
-- = Important note
--
-- This type has a \'type abstraction boundary\' just before it: the first field
-- indicates how many type variables it binds.
--
-- @since 1.0.0
data CompT (a :: Type) = CompT (Count "tyvar") (CompTBody a)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance Eq1 CompT where
  {-# INLINEABLE liftEq #-}
  liftEq f (CompT abses1 xs) (CompT abses2 ys) =
    abses1 == abses2 && liftEq f xs ys

newtype TyName = TyName Text
  deriving (Show, Eq, Ord, IsString) via Text

runTyName :: TyName -> Text
runTyName (TyName nm) = nm

-- | @since 1.0.0
instance Pretty (CompT Renamed) where
  pretty = runPrettyM . prettyCompTWithContext

-- | A value type, with abstractions indicated by the type argument. In pretty
-- much any case imaginable, this would be either 'AbstractTy' (in the ASG) or
-- 'Renamed' (after renaming).
--
-- @ since 1.0.0
data ValT (a :: Type)
  = -- | An abstract type.
    Abstraction a
  | -- | A suspended computation.
    ThunkT (CompT a)
  | -- | A builtin type without any nesting.
    BuiltinFlat BuiltinFlatT
  | -- A type constructor, with a list of arguments and an explicit scope boundary (REVIEW: Do we need the explicit scope boundary?)
    Datatype TyName (Vector (ValT a))
  deriving stock
    ( -- | @since 1.0.0
      Eq,
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
      Show
    )

-- Helpers

newtype ScopeBoundary = ScopeBoundary Int
  deriving (Show, Eq, Ord, Num) via Int

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
  | review intCount count == 0 = prettyFunTy funArgs
  | otherwise = bindVars count $ \newVars -> do
      funTy <- prettyFunTy funArgs
      pure $ mkForall newVars funTy

prettyFunTy ::
  forall (ann :: Type).
  NonEmptyVector (ValT Renamed) ->
  PrettyM ann (Doc ann)
prettyFunTy args = case NonEmpty.uncons args of
  (arg, rest) -> parens <$> Vector.foldl' go (("!" <>) <$> prettyArg arg) rest
  where
    go ::
      PrettyM ann (Doc ann) ->
      ValT Renamed ->
      PrettyM ann (Doc ann)
    go acc t = (\x y -> x <+> "->" <+> y) <$> prettyArg t <*> acc
    prettyArg :: ValT Renamed -> PrettyM ann (Doc ann)
    prettyArg vt =
      let prettyVT = prettyValTWithContext vt
       in if isSimpleValT vt
            then prettyVT
            else parens <$> prettyVT

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

-- I.e. can we omit parens and get something unambiguous? This might be overly aggressive w/ parens but that's OK
isSimpleValT :: forall (a :: Type). ValT a -> Bool
isSimpleValT = \case
  ThunkT thunk -> isSimpleCompT thunk
  _ -> True
  where
    isSimpleCompT :: CompT a -> Bool
    isSimpleCompT (CompT count (CompTBody args)) =
      review intCount count == 0 && NonEmpty.length args == 1

prettyValTWithContext :: forall (ann :: Type). ValT Renamed -> PrettyM ann (Doc ann)
prettyValTWithContext = \case
  Abstraction abstr -> prettyRenamedWithContext abstr
  ThunkT compT -> prettyCompTWithContext compT
  BuiltinFlat biFlat -> pure $ viaShow biFlat
  Datatype tn args -> do
    args' <- traverse prettyValTWithContext args
    let tn' = pretty $ runTyName tn
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
  Wildcard w64 i -> pure $ "_" <> viaShow w64 <> "#" <> pretty (review intIndex i)

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
prettyDataDeclWithContext (DataDeclaration tn numVars ctors) = bindVars numVars $ \boundVars -> do
  let tn' = pretty (runTyName tn)
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

newtype ConstructorName = ConstructorName Text
  deriving (Show, Eq, Ord, IsString) via Text

runConstructorName :: ConstructorName -> Text
runConstructorName (ConstructorName nm) = nm

-- I.e. a product in the sum of products
data Constructor (a :: Type)
  = Constructor ConstructorName (Vector (ValT a))
  deriving stock (Show, Eq)

instance Eq1 Constructor where
  liftEq f (Constructor nm args) (Constructor nm' args') = nm == nm' && liftEq (liftEq f) args args'

constructorName :: forall a. Lens' (Constructor a) ConstructorName
constructorName = lens (\(Constructor n _) -> n) (\(Constructor _ args) n -> Constructor n args)

constructorArgs :: forall a. Lens' (Constructor a) (Vector (ValT a))
constructorArgs = lens (\(Constructor _ args) -> args) (\(Constructor n _) args -> Constructor n args)

data DataDeclaration a
  = DataDeclaration TyName (Count "tyvar") (Vector (Constructor a)) -- Allows for representations of "empty" types in case we want to represent Void like that
  deriving stock (Show, Eq)

instance Pretty (DataDeclaration Renamed) where
  pretty = runPrettyM . prettyDataDeclWithContext

-- we'll need them
datatypeName :: forall (a :: Type). Lens' (DataDeclaration a) TyName
datatypeName =
  lens
    (\(DataDeclaration tn _ _) -> tn)
    (\(DataDeclaration _ cnt ctors) tn -> DataDeclaration tn cnt ctors)

datatypeBinders :: forall (a :: Type). Lens' (DataDeclaration a) (Count "tyvar")
datatypeBinders =
  lens
    (\(DataDeclaration _ cnt _) -> cnt)
    (\(DataDeclaration tn _ ctors) cnt -> DataDeclaration tn cnt ctors)

datatypeConstructors :: forall (a :: Type). Lens' (DataDeclaration a) (Vector (Constructor a))
datatypeConstructors =
  lens
    (\(DataDeclaration _ _ ctors) -> ctors)
    (\(DataDeclaration tn cnt _) ctors -> DataDeclaration tn cnt ctors)
