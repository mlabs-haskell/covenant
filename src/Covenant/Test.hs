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
    sized, generate,
  )
import Test.QuickCheck.Instances.Vector ()
import Covenant.Internal.Type (ValT(..), DataDeclaration (DataDeclaration), ConstructorName(..), TyName(..), runConstructorName, Constructor (Constructor), datatypeName)
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
import Optics.Operators ((^.))
import Data.Foldable (traverse_)

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
        xs <- arbitrary `suchThat` all (`elem` (caps <> lower))
        pure . T.pack $ (x:xs)
  -- Default shrink should be fine? The name of constructors doesn't affect much

instance Arbitrary TyName where
  arbitrary = TyName . runConstructorName <$> arbitrary

newtype ConcreteConstructor = ConcreteConstructor (Constructor AbstractTy)
  deriving Eq via (Constructor AbstractTy)
  deriving stock Show

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

{- Concrete datatypes which may contain other concrete datatypes as constructor args. (Still no TyVars)

   Going to try to add the capability for these to be recursive. Won't give us anything *that* interesting but
   should give us things like: data IntList = Empty | IntListCons Int IntList
-}

newtype NestedConcreteDataDecl = NestedConcreteDataDecl (DataDeclaration AbstractTy)
  deriving Eq via (DataDeclaration AbstractTy)
  deriving stock Show

newtype NestedConcreteCtor = NestedConcreteCtor (Constructor AbstractTy)

arbitraryNestedConcrete :: ReaderT (Map TyName (DataDeclaration AbstractTy)) Gen NestedConcreteDataDecl
arbitraryNestedConcrete = NestedConcreteDataDecl <$> do
  tyNm <- lift $ arbitrary @TyName
  let nullary :: ReaderT (Map TyName (DataDeclaration AbstractTy)) Gen (DataDeclaration AbstractTy)
      nullary = lift $ do
        ctorNm <- arbitrary @ConstructorName
        pure $ DataDeclaration tyNm count0 (Vector.singleton (Constructor ctorNm Vector.empty))

      nonNestedConcrete :: ReaderT (Map TyName (DataDeclaration AbstractTy)) Gen (DataDeclaration AbstractTy)
      nonNestedConcrete = lift $ do
        ctors <- fmap coerce <$> (arbitrary @[ConcreteConstructor])
        pure $ DataDeclaration tyNm count0 (Vector.fromList ctors)

      nested :: ReaderT (Map TyName (DataDeclaration AbstractTy)) Gen (DataDeclaration AbstractTy)
      nested = do
        alreadyGenerated <- ask
        numCtors <- lift $ chooseInt (0,5)
        ctors <- Vector.replicateM numCtors nestedCtor
        pure $ DataDeclaration tyNm count0 (coerce <$> ctors)

  options <- sequence [nullary,nonNestedConcrete,nested]
  lift $ oneof (pure <$> options)

nestedCtor :: ReaderT (Map TyName (DataDeclaration AbstractTy)) Gen NestedConcreteCtor
nestedCtor = do
  alreadyGenerated <- ask
  -- I dunno how to thread the "size" through to this, so this is kind of a hack.
  numArgs <- lift $ chooseInt (0,5)
  args <- Vector.replicateM numArgs nestedCtorArg
  ctorNm <- lift $ arbitrary @ConstructorName
  pure . coerce $ Constructor ctorNm args
 where
   nestedCtorArg :: ReaderT (Map TyName (DataDeclaration AbstractTy)) Gen (ValT AbstractTy)
   nestedCtorArg = do
     userTyNames <- asks M.keys
     if null userTyNames
       then coerce <$> lift (arbitrary @Concrete)
       else do
         let userTypes = (`Datatype` Vector.empty) <$> userTyNames
         lift $ oneof [elements userTypes, coerce <$> arbitrary @Concrete]

nestedConcreteDatatypes :: Int -> ReaderT (Map TyName (DataDeclaration AbstractTy)) Gen (Map TyName (DataDeclaration AbstractTy))
nestedConcreteDatatypes n
  | n <= 0 = ask
  | otherwise = do
      firstDecl <- coerce <$> arbitraryNestedConcrete
      local (M.insert (firstDecl ^. datatypeName) firstDecl) $ nestedConcreteDatatypes (n-1) 

-- Utilities for repl testing (so I don't have to type them every time I :r) - delete the eventually, probably
genConcreteDecl :: IO (DataDeclaration AbstractTy)
genConcreteDecl = coerce <$> generate (arbitrary @ConcreteDataDecl)

-- for convenience
unsafeRename :: forall (a :: Type). RenameM a -> IO a
unsafeRename act = case runRenameM act of
  Left err -> throwIO (userError $ show err)
  Right res -> pure res

genNestedConcrete :: Int -> IO [DataDeclaration AbstractTy]
genNestedConcrete n = generate go
  where
    go :: Gen [DataDeclaration AbstractTy]
    go = M.elems <$> runReaderT (nestedConcreteDatatypes n) M.empty

prettyTestConcrete :: IO ()
prettyTestConcrete = genConcreteDecl >>= \decl ->
  unsafeRename (renameDataDecl decl) >>= \renamed ->
  putDoc (hardline <> pretty renamed <+> hardline <> hardline)

prettyNestedConcrete :: Int -> IO ()
prettyNestedConcrete n = genNestedConcrete n >>= \decls ->
  traverse (unsafeRename . renameDataDecl) decls >>= \renamed ->
  traverse_ (\decl -> putDoc $ hardline <> pretty decl <> hardline <> hardline) renamed
