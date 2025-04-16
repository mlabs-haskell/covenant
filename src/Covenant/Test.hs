module Covenant.Test
  ( Concrete (Concrete),
    prettyTestConcrete,
    prettyNestedConcrete
  )
where

import Control.Applicative ((<|>))
import Covenant.Index (count0)
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT
      ( BLS12_381_G1_ElementT,
        BLS12_381_G2_ElementT,
        BLS12_381_MlResultT,
        BoolT,
        ByteStringT,
        IntegerT,
        StringT,
        UnitT
      ),
    CompT (Comp0, CompN),
    CompTBody (ArgsAndResult),
    ValT (Abstraction, BuiltinFlat, ThunkT),
  )
import Data.Coerce (coerce)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Set (Set)
import Data.Set qualified as Set
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Gen,
    elements,
    liftArbitrary,
    oneof,
    sized, generate, frequency, scale,
  )
import Test.QuickCheck.Instances.Vector ()
import Covenant.Internal.Type (ValT(..), DataDeclaration (DataDeclaration), ConstructorName(..), TyName(..), runConstructorName, Constructor (Constructor), datatypeName, datatypeConstructors, constructorName, ScopeBoundary)
import Data.Text (Text)
import Data.Text qualified as T
import Test.QuickCheck.Gen (suchThat, resize, chooseInt)
import Covenant.Internal.Rename
import Data.Kind (Type)
import Control.Exception (throwIO)
import Prettyprinter (pretty, (<+>), hardline)
import Prettyprinter.Render.Text (putDoc)
import Test.QuickCheck.Instances.Containers ()
import Control.Monad.Reader (Reader, ReaderT (..), MonadTrans (..), MonadReader (..), asks)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Optics.Operators ((^.), (^..))
import Data.Foldable (traverse_)
import Optics.Core ((%), folded, Lens', lens, view, over)
import Control.Monad.State.Strict (StateT, runStateT, evalStateT, MonadState (..))
import Control.Monad.State.Class (MonadState, gets, modify)
import Control.Monad (void)
import GHC.Word (Word32)

-- | Wrapper for 'ValT' to provide an 'Arbitrary' instance to generate only
-- value types without any type variables.
--
-- @since 1.0.0
newtype Concrete = Concrete (ValT AbstractTy)
  deriving
    ( -- | @since 1.0.0
      Eq
    )
    via (ValT AbstractTy)
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance Arbitrary Concrete where
  {-# INLINEABLE arbitrary #-}
  arbitrary = Concrete <$> sized go
    where
      go :: Int -> Gen (ValT AbstractTy)
      go size
        | size <= 0 =
            BuiltinFlat
              <$> elements
                [ UnitT,
                  BoolT,
                  IntegerT,
                  StringT,
                  ByteStringT,
                  BLS12_381_G1_ElementT,
                  BLS12_381_G2_ElementT,
                  BLS12_381_MlResultT
                ]
        | otherwise =
            oneof
              [ pure . BuiltinFlat $ UnitT,
                pure . BuiltinFlat $ BoolT,
                pure . BuiltinFlat $ IntegerT,
                pure . BuiltinFlat $ StringT,
                pure . BuiltinFlat $ ByteStringT,
                pure . BuiltinFlat $ BLS12_381_G1_ElementT,
                pure . BuiltinFlat $ BLS12_381_G2_ElementT,
                pure . BuiltinFlat $ BLS12_381_MlResultT,
                ThunkT . Comp0 <$> (ArgsAndResult <$> liftArbitrary (go (size `quot` 4)) <*> go (size `quot` 4))
               -- This is probably right but things will break if we generate datatypes at this stage
               -- ,  Datatype <$> arbitrary <*> pure count0 <*> liftArbitrary (go (size `quot` 4))
              ]
  {-# INLINEABLE shrink #-}
  shrink (Concrete v) =
    Concrete <$> case v of
      -- impossible
      Abstraction _ -> []
      ThunkT (CompN _ (ArgsAndResult args result)) ->
        ThunkT . CompN count0 <$> do
          let argsList = Vector.toList args
          argsList' <- fmap coerce . shrink . fmap Concrete $ argsList
          result' <- fmap coerce . shrink . Concrete $ result
          let args' = Vector.fromList argsList'
          pure (ArgsAndResult args' result) <|> pure (ArgsAndResult args result')
      -- Can't shrink this
      BuiltinFlat _ -> []
      Datatype{} -> []


{- "Concrete" data declarations and constructors. More specifically: "Basic" concrete datatypes and constructors,
   i.e., no tyvars & the argument to every constructor is a Concrete as defined above
-}

-- Information we need to correctly generate concrete types. Contains a map of all the already-generated types & the set of
-- already generated constructor names for the current type. Need the latter to avoid duplicates in the same datatype
data DataGen = DataGen {
        _dgDecls :: Map TyName (DataDeclaration AbstractTy),
        _dgCtors :: Set ConstructorName,
        _dgCurrentScope :: ScopeBoundary,
        _dgBoundVars :: Map ScopeBoundary Word32
        }

dgDecls :: Lens' DataGen (Map TyName (DataDeclaration AbstractTy))
dgDecls = lens (\(DataGen a _ _ _) -> a) (\(DataGen _ b c d) a -> DataGen a b c d)

dgConstructors :: Lens' DataGen (Set ConstructorName)
dgConstructors = lens (\(DataGen _ b _ _) -> b) (\(DataGen a _ c d) b -> DataGen a b c d)

dgCurrentScope :: Lens' DataGen ScopeBoundary
dgCurrentScope = lens (\(DataGen _ _ c _) -> c) (\(DataGen a b _ d) c -> DataGen a b c d)

dgBoundVars :: Lens' DataGen (Map ScopeBoundary Word32)
dgBoundVars = lens (\(DataGen _ _ _ d) -> d) (\(DataGen a b c _) d -> DataGen a b c d)



-- Monadic stack for generating monomorphic datatype declarations. Need a different one for polymorphic ones to track the level & available variables
-- In theory this could be a reader but it becomes super awkward to work, StateT is easier
newtype DataGenM a = DataGenM (StateT DataGen Gen a)
 deriving newtype (Functor, Applicative, Monad)
 deriving (MonadState DataGen) via StateT DataGen Gen

runDataGenM :: DataGenM a -> Gen a
runDataGenM (DataGenM ma) = evalStateT ma (DataGen M.empty Set.empty 0 M.empty)

liftGen :: forall (a :: Type). Gen a -> DataGenM a
liftGen ma = DataGenM (lift ma)


uniqueVector :: forall (a :: Type). (Arbitrary a, Ord a) => Gen (Vector a)
uniqueVector = Vector.fromList . Set.toList <$> arbitrary @(Set a)

uniqueNonEmptyVector :: forall (a :: Type). (Arbitrary a, Ord a) => Gen (Vector a)
uniqueNonEmptyVector = uniqueVector @a `suchThat` (not . null)

newtype ConcreteDataDecl = ConcreteDataDecl (DataDeclaration AbstractTy)
  deriving Eq via (DataDeclaration AbstractTy)
  deriving stock Show

instance Arbitrary ConstructorName where
  arbitrary = ConstructorName <$> genValidCtorName
    where
      genValidCtorName :: Gen Text
      genValidCtorName = do
        let caps = ['A'..'Z']
            lower = ['a'..'z']
        x <- arbitrary `suchThat` (`elem` caps)
        xs <- scale (* 4) $ arbitrary `suchThat` all (`elem` (caps <> lower))
        pure . T.pack $ (x:xs)
  -- Default shrink should be fine? The name of constructors doesn't affect much

freshConstructorName :: DataGenM ConstructorName
freshConstructorName = do
  datatypes <- gets (M.elems . view dgDecls)
  let allCtorNames = Set.fromList $ datatypes ^.. (folded % datatypeConstructors % folded % constructorName)
  liftGen $ arbitrary @ConstructorName `suchThat` (`Set.notMember` allCtorNames)

freshTyName :: DataGenM TyName
freshTyName = do
  datatypes <- gets (M.elems . view dgDecls)
  let allDataTypeNames = Set.fromList $ datatypes ^.. (folded % datatypeName)
  liftGen $ arbitrary @TyName `suchThat` (`Set.notMember` allDataTypeNames)

instance Arbitrary TyName where
  arbitrary = TyName . runConstructorName <$> arbitrary

newtype ConcreteConstructor = ConcreteConstructor (Constructor AbstractTy)
  deriving Eq via (Constructor AbstractTy)
  deriving stock Show

genConcreteConstructor :: DataGenM ConcreteConstructor
genConcreteConstructor = ConcreteConstructor <$> go
  where
    go :: DataGenM (Constructor AbstractTy)
    go = do
      ctorNm <- freshConstructorName
      numArgs <- liftGen $ chooseInt (0,5)
      args <- liftGen $ Vector.replicateM numArgs (arbitrary @Concrete)
      modify (over dgConstructors (Set.insert ctorNm))
      pure $ Constructor ctorNm (coerce <$> args)

genConcreteDataDecl :: DataGenM ConcreteDataDecl
genConcreteDataDecl = ConcreteDataDecl <$> do
  tyNm <- freshTyName
  numArgs <- liftGen $ chooseInt (0,5)
  ctors <- coerce <$> Vector.replicateM numArgs genConcreteConstructor
  let decl = DataDeclaration tyNm count0 ctors
  modify (over dgDecls (M.insert tyNm decl))
  pure decl

{- Concrete datatypes which may contain other concrete datatypes as constructor args. (Still no TyVars)

   Going to try to add the capability for these to be recursive. Won't give us anything *that* interesting but
   should give us things like: data IntList = Empty | IntListCons Int IntList
-}

newtype NestedConcreteDataDecl = NestedConcreteDataDecl (DataDeclaration AbstractTy)
  deriving Eq via (DataDeclaration AbstractTy)
  deriving stock Show

newtype NestedConcreteCtor = NestedConcreteCtor (Constructor AbstractTy)

arbitraryNestedConcrete :: DataGenM  NestedConcreteDataDecl
arbitraryNestedConcrete = NestedConcreteDataDecl <$> do
  tyNm <-  freshTyName
  let nullary :: DataGenM (DataDeclaration AbstractTy)
      nullary = liftGen $ do
        ctorNm <- arbitrary @ConstructorName
        pure $ DataDeclaration tyNm count0 (Vector.singleton (Constructor ctorNm Vector.empty))

      nonNestedConcrete :: DataGenM (DataDeclaration AbstractTy)
      nonNestedConcrete =  do
        numCtors <- liftGen $ chooseInt (0,5)
        ctors <- fmap coerce <$> Vector.replicateM numCtors genConcreteConstructor
        pure $ DataDeclaration tyNm count0 ctors

      nested :: DataGenM (DataDeclaration AbstractTy)
      nested = do
        alreadyGenerated <- get
        numCtors <- liftGen $ chooseInt (0,5)
        ctors <- Vector.replicateM numCtors nestedCtor
        pure $ DataDeclaration tyNm count0 (coerce <$> ctors)

  options <- sequence [nullary,nonNestedConcrete,nested]
  res <- liftGen $ oneof (pure <$> options)
  modify (over dgDecls (M.insert tyNm res))
  pure res

nestedCtor :: DataGenM NestedConcreteCtor
nestedCtor = do
  alreadyGenerated <- gets (view dgDecls)
  -- I dunno how to thread the "size" through to this, so this is kind of a hack.
  numArgs <- liftGen $ chooseInt (0,5)
  args <- Vector.replicateM numArgs nestedCtorArg
  ctorNm <-  freshConstructorName
  modify (over dgConstructors (Set.insert ctorNm))
  pure . coerce $ Constructor ctorNm args
 where
   nestedCtorArg :: DataGenM (ValT AbstractTy)
   nestedCtorArg = do
     userTyNames <- gets (M.keys . view dgDecls)
     if null userTyNames
       then coerce <$> liftGen (arbitrary @Concrete)
       else do 
         let userTypes = (`Datatype` Vector.empty) <$> userTyNames
         liftGen $ frequency [(8,elements userTypes), (2, coerce <$> arbitrary @Concrete)]

nestedConcreteDatatypes :: Int -> DataGenM (Map TyName (DataDeclaration AbstractTy))
nestedConcreteDatatypes n
  | n <= 0 = gets (view dgDecls)
  | otherwise = do
      void $  arbitraryNestedConcrete
      nestedConcreteDatatypes (n-1)

-- Utilities for repl testing (so I don't have to type them every time I :r) - delete the eventually, probably
genConcreteDecl :: IO (DataDeclaration AbstractTy)
genConcreteDecl = coerce <$> generate (runDataGenM genConcreteDataDecl)

-- for convenience
unsafeRename :: forall (a :: Type). RenameM a -> IO a
unsafeRename act = case runRenameM act of
  Left err -> throwIO (userError $ show err)
  Right res -> pure res

genNestedConcrete :: Int -> IO [DataDeclaration AbstractTy]
genNestedConcrete n = generate go
  where
    go :: Gen [DataDeclaration AbstractTy]
    go = M.elems <$> runDataGenM (nestedConcreteDatatypes n)

prettyTestConcrete :: IO ()
prettyTestConcrete = genConcreteDecl >>= \decl ->
  unsafeRename (renameDataDecl decl) >>= \renamed ->
  putDoc (hardline <> pretty renamed <+> hardline <> hardline)

prettyNestedConcrete :: Int -> IO ()
prettyNestedConcrete n = genNestedConcrete n >>= \decls ->
  traverse (unsafeRename . renameDataDecl) decls >>= \renamed ->
  traverse_ (\decl -> putDoc $ hardline <> pretty decl <> hardline <> hardline) renamed

{- I don't think these instances should exist. We should always generate a set of datatypes, using these instances is probably always a mistake

instance Arbitrary ConcreteDataDecl where
  arbitrary = ConcreteDataDecl <$>  do
        tyNm <- arbitrary @TyName
        let nullary = do
              ctorNm <- arbitrary @ConstructorName
              pure $ DataDeclaration tyNm count0 (Vector.singleton (Constructor ctorNm Vector.empty))
            nonNullary = do
              ctors <- fmap coerce <$> arbitrary @[ConcreteConstructor]
              pure $ DataDeclaration tyNm count0 (Vector.fromList ctors)
        oneof [nullary,nonNullary]

  shrink (ConcreteDataDecl (DataDeclaration nm _cnt0 ctors)) = do
    -- shrink the # of constructors
    ctorsS1 <- coerce <$> shrink (ConcreteConstructor <$> ctors)
    -- shrink each constructor
    ctorsS2 <- shrink <$> Vector.toList (ConcreteConstructor <$> ctors)
    let ctorsS2' = Vector.fromList ctorsS2
        res1 = ConcreteDataDecl $ DataDeclaration nm count0 ctorsS1
        res2 = ConcreteDataDecl $ DataDeclaration nm count0 (coerce ctorsS2')
    pure res1 <|> pure res2

instance Arbitrary ConcreteConstructor where
  arbitrary = ConcreteConstructor <$> sized go
    where
      go :: Int -> Gen (Constructor AbstractTy)
      go size = do
        ctorNm <- arbitrary @ConstructorName
        args <-  resize (size `quot` 4) (arbitrary @[Concrete])
        pure $ Constructor ctorNm (Vector.fromList . fmap coerce $ args)

  -- For this one, I think we just want to shrink the args normally. This is probably equivalent to the derived method?
  shrink (ConcreteConstructor (Constructor nm args)) = do
    args' <- coerce <$> shrink (Concrete <$> args)
    pure . ConcreteConstructor . Constructor nm $ args'

-}
