{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
module Covenant.Test
  ( Concrete (Concrete),
    DataDeclSet (DataDeclSet),
    DataDeclFlavor (ConcreteDecl, ConcreteNestedDecl, SimpleRecursive, Poly1),
    testConcrete,
    testNested,
    testRecConcrete,
    testPoly1,
  )
where

import Control.Applicative ((<|>))
import Control.Exception (throwIO)
import Control.Monad.Reader (MonadTrans (lift))
import Control.Monad.State.Strict
  ( MonadState (get, put),
    State,
    StateT,
    evalState,
    gets,
    modify,
  )
import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index (Count, count0, count1, intCount, ix0)
import Covenant.Internal.Rename (renameDataDecl)
import Covenant.Internal.Type
  ( Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration),
    ScopeBoundary,
    TyName (TyName),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    constructorName,
    datatypeBinders,
    datatypeConstructors,
    datatypeName,
    runConstructorName,
  )
import Covenant.Type
  ( AbstractTy (BoundAt),
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
    RenameM,
    runRenameM,
  )
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity ())
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.Exts (fromListN)
import GHC.Word (Word32)
import Optics.Core (Lens', folded, lens, over, review, view, (%))
import Optics.Operators ((^.), (^..))
import Prettyprinter (hardline, pretty)
import Prettyprinter.Render.Text (putDoc)
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Arbitrary1 (liftArbitrary, liftShrink),
    Gen,
    chooseInt,
    elements,
    frequency,
    generate,
    oneof,
    sized,
    suchThat,
    vectorOf,
  )
import Test.QuickCheck.GenT (GenT, MonadGen)
import Test.QuickCheck.GenT qualified as GT
import Test.QuickCheck.Instances.Containers ()
import Test.QuickCheck.Instances.Vector ()

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
      -- NOTE @Koz: I need this here to write some other instances even though `Concrete` can't generate this
      Datatype tn args ->
        Datatype tn <$> do
          let argsList = Vector.toList args
          (fmap (Vector.fromList . coerce) . shrink . fmap Concrete) argsList

{- The state used by our datatype generators.
-}
data DataGen = DataGen
  { -- Keeps track of decls we've already generated. Used for "nested" generators and also essential for ValT generation (when we get around to implementing it)
    _dgDecls :: Map TyName (DataDeclaration AbstractTy),
    -- All used constructor names. Have to track separately, even though the information eventually ends up in the previous field, to avoid duplicate constructors in the same type.
    _dgCtors :: Set ConstructorName,
    -- Current scope. Needed for generating polymorphic `ValT`s for arguments to constructors . (That's not implemented yet but we 100% will need this )
    _dgCurrentScope :: ScopeBoundary,
    -- NOTE: Needs to maintain the invariant that the Word32 is always >0, since we will use this to select in scope variables for polymorphic args to ctors. (Again, not implemented yet)
    _dgBoundVars :: Map ScopeBoundary Word32,
    -- We need this for recursive types. We can't lookup the arity in dgDecls if we want to recurse b/c it won't be there until we've finished generating the whole decl
    _dgArities :: Map TyName (Count "tyvar")
  }

-- TODO: Rewrite as field label instances
dgDecls :: Lens' DataGen (Map TyName (DataDeclaration AbstractTy))
dgDecls = lens (\(DataGen a _ _ _ _) -> a) (\(DataGen _ b c d e) a -> DataGen a b c d e)

dgConstructors :: Lens' DataGen (Set ConstructorName)
dgConstructors = lens (\(DataGen _ b _ _ _) -> b) (\(DataGen a _ c d e) b -> DataGen a b c d e)

_dgCurrentScope :: Lens' DataGen ScopeBoundary
_dgCurrentScope = lens (\(DataGen _ _ c _ _) -> c) (\(DataGen a b _ d e) c -> DataGen a b c d e)

_dgBoundVars :: Lens' DataGen (Map ScopeBoundary Word32)
_dgBoundVars = lens (\(DataGen _ _ _ d _) -> d) (\(DataGen a b c _ e) d -> DataGen a b c d e)

dgArities :: Lens' DataGen (Map TyName (Count "tyvar"))
dgArities = lens (\(DataGen _ _ _ _ e) -> e) (\(DataGen a b c d _) e -> DataGen a b c d e)

{-  Monadic stack for generating monomorphic datatype declarations. Not every generator uses every part of the state, but
    it ought to suffice for generating *any* datatype declaration we choose.

    In theory this could be a reader but it becomes super awkward to work, StateT is easier

    While we don't have any generators for polymorphic `ValT`s yet, the scope stuff will be necessary there.
-}
newtype DataGenM a = DataGenM (GenT (State DataGen) a)
  deriving newtype (Functor, Applicative, Monad)
  deriving (MonadGen) via GenT (StateT DataGen Data.Functor.Identity.Identity)

instance MonadState DataGen DataGenM where
  get = DataGenM $ lift get
  put = DataGenM . lift . put

{- N.B. We don't need this *yet* but we will need it to generate constructors which take polymorphic functions as arguments.
-}
_bindVars :: Count "tyvar" -> DataGenM ()
_bindVars count'
  | count == 0 = crossBoundary
  | otherwise = do
      crossBoundary
      here <- gets (view _dgCurrentScope)
      modify $ over _dgBoundVars (M.insert here $ fromIntegral count)
  where
    count :: Int
    count = review intCount count'

    crossBoundary :: DataGenM ()
    crossBoundary = modify $ over _dgCurrentScope (+ 1)

runDataGenM :: forall (a :: Type). DataGenM a -> Gen a
runDataGenM (DataGenM ma) = (\x -> evalState x (DataGen M.empty Set.empty 0 M.empty M.empty)) <$> GT.runGenT ma

-- Stupid helper, saves us from forgetting to update part of the state
returnDecl :: DataDeclaration AbstractTy -> DataGenM (DataDeclaration AbstractTy)
returnDecl decl = do
  let tyNm = decl ^. datatypeName
  modify $ over dgDecls (M.insert tyNm decl)
  let arity = decl ^. datatypeBinders
  logArity tyNm arity
  pure decl

{- We need this outside of `returnDecl` to construct recursive polymorphic types, i.e. types where an argument to
   a constructor is the parent type applied to the type variables bound at the start of the declaration.
-}
logArity :: TyName -> Count "tyvar" -> DataGenM ()
logArity tn cnt = modify $ over dgArities (M.insert tn cnt)

newtype ConcreteDataDecl = ConcreteDataDecl (DataDeclaration AbstractTy)
  deriving (Eq) via (DataDeclaration AbstractTy)
  deriving stock (Show)

{- These should never be used in a DataGenM context, we should always use the fresh generators below-}
anyCtorName :: Gen ConstructorName
anyCtorName = ConstructorName <$> genValidCtorName
  where
    genValidCtorName :: Gen Text
    genValidCtorName = do
      let caps = ['A' .. 'Z']
          lower = ['a' .. 'z']
      nmLen <- chooseInt (1, 6) -- should be more than enough to ensure `suchThat` doesn't run into clashes all the time
      x <- elements caps
      xs <- vectorOf nmLen $ elements (caps <> lower)
      pure . T.pack $ (x : xs)

anyTyName :: Gen TyName
anyTyName = TyName . runConstructorName <$> anyCtorName

-- Default shrink should be fine? The name of constructors doesn't affect much

{- These ensure that we don't ever duplicate type names or constructor names. We need the DataGenM state
   to ensure that, so these should *always* be used when writing generators, and the arbitrary instances should be avoided.
-}
freshConstructorName :: DataGenM ConstructorName
freshConstructorName = do
  datatypes <- gets (M.elems . view dgDecls)
  let allCtorNames = Set.fromList $ datatypes ^.. (folded % datatypeConstructors % folded % constructorName)
  thisName <- GT.liftGen $ anyCtorName `suchThat` (`Set.notMember` allCtorNames)
  modify $ over dgConstructors (Set.insert thisName)
  pure thisName

freshTyName :: DataGenM TyName
freshTyName = do
  datatypes <- gets (M.elems . view dgDecls)
  let allDataTypeNames = Set.fromList $ datatypes ^.. (folded % datatypeName)
  GT.liftGen $ anyTyName `suchThat` (`Set.notMember` allDataTypeNames)

newtype ConcreteConstructor = ConcreteConstructor (Constructor AbstractTy)
  deriving (Eq) via (Constructor AbstractTy)
  deriving stock (Show)

genConcreteConstructor :: DataGenM ConcreteConstructor
genConcreteConstructor = ConcreteConstructor <$> go
  where
    go :: DataGenM (Constructor AbstractTy)
    go = do
      ctorNm <- freshConstructorName
      numArgs <- GT.liftGen $ chooseInt (0, 5)
      args <- GT.liftGen $ Vector.replicateM numArgs (arbitrary @Concrete)
      pure $ Constructor ctorNm (coerce <$> args)

genConcreteDataDecl :: DataGenM ConcreteDataDecl
genConcreteDataDecl =
  ConcreteDataDecl <$> do
    tyNm <- freshTyName
    numArgs <- GT.liftGen $ chooseInt (0, 5)
    ctors <- coerce <$> Vector.replicateM numArgs genConcreteConstructor
    let decl = DataDeclaration tyNm count0 ctors
    returnDecl decl

{- Concrete datatypes which may contain other concrete datatypes as constructor args. (Still no TyVars)

   For example, if you have (in the DataGen context) an already generated:

   data Foo = Foo Integer

   this can generate a datatype like:

   data Bar = Bar Foo | Baz String

   I.e. it generates datatype declarations that use previously generated datatype declarations.

   This isn't useful unless you generate a *set* (or some other collection of them) in the DataGen monad,
   since generating them one at a time will always give you the same thing as a ConcreteDataDecl.
-}
newtype NestedConcreteDataDecl = NestedConcreteDataDecl (DataDeclaration AbstractTy)
  deriving (Eq) via (DataDeclaration AbstractTy)
  deriving stock (Show)

newtype NestedConcreteCtor = NestedConcreteCtor (Constructor AbstractTy)

genNestedConcrete :: DataGenM NestedConcreteDataDecl
genNestedConcrete =
  NestedConcreteDataDecl <$> do
    tyNm <- freshTyName
    let nullary :: DataGenM (DataDeclaration AbstractTy)
        nullary = do
          ctorNm <- freshConstructorName
          pure $ DataDeclaration tyNm count0 (Vector.singleton (Constructor ctorNm Vector.empty))

        nonNestedConcrete :: DataGenM (DataDeclaration AbstractTy)
        nonNestedConcrete = do
          numCtors <- GT.liftGen $ chooseInt (0, 5)
          ctors <- fmap coerce <$> Vector.replicateM numCtors genConcreteConstructor
          pure $ DataDeclaration tyNm count0 ctors

        nested :: DataGenM (DataDeclaration AbstractTy)
        nested = do
          numCtors <- GT.liftGen $ chooseInt (0, 5)
          ctors <- Vector.replicateM numCtors nestedCtor
          pure $ DataDeclaration tyNm count0 (coerce <$> ctors)

    options <- sequence [nullary, nonNestedConcrete, nested]
    res <- GT.liftGen $ oneof (pure <$> options)
    returnDecl res

{- It's useful to have access to these outside of the above function because sometimes we want to mix and match
   "simpler" constructors like this with the more complex sorts we generate below.
-}
nestedCtor :: DataGenM NestedConcreteCtor
nestedCtor = do
  -- We want this: Not very much hinges on the # of args to each constructor and having finite bounds like this makes the output easier to read
  numArgs <- GT.liftGen $ chooseInt (0, 5)
  args <- Vector.replicateM numArgs nestedCtorArg
  ctorNm <- freshConstructorName
  pure . coerce $ Constructor ctorNm args

nestedCtorArg :: DataGenM (ValT AbstractTy)
nestedCtorArg = do
  userTyNames <- gets (M.keys . view dgDecls)
  if null userTyNames
    then coerce <$> GT.liftGen (arbitrary @Concrete)
    else do
      let userTypes = (`Datatype` Vector.empty) <$> userTyNames
      GT.liftGen $ frequency [(8, elements userTypes), (2, coerce <$> arbitrary @Concrete)]

newtype RecursiveConcreteDataDecl = RecursiveConcreteDataDecl (DataDeclaration AbstractTy)
  deriving (Eq) via (DataDeclaration AbstractTy)
  deriving stock (Show)

{- Non-polymorphic recursive types, i.e. things like:

   data IntList = Empty | ConsInt Int IntList

   The general idea is that we construct a base case constructor (Nil or Empty) and then
   construct a recursive constructor. We can expand this later (e.g. to have multiple recursive constructors, or a polymorphic variant)
   but this will be enough to handle initial testing w/ the base functor / BBF stuff (and we have to ensure we have things like this to test that)
-}
genArbitraryRecursive :: DataGenM RecursiveConcreteDataDecl
genArbitraryRecursive =
  RecursiveConcreteDataDecl <$> do
    tyNm <- freshTyName
    baseCtor <- coerce <$> genConcreteConstructor -- any concrete ctor - or any ctor that doesn't contain the parent type - will suffice as a base case
    numRecCtors <- GT.liftGen $ chooseInt (1, 5)
    recCtor <- GT.vectorOf numRecCtors $ genRecCtor tyNm
    returnDecl $ DataDeclaration tyNm count0 (Vector.fromList (baseCtor : recCtor))
  where
    genRecCtor :: TyName -> DataGenM (Constructor AbstractTy)
    genRecCtor tyNm = do
      ctorNm <- freshConstructorName
      let thisType = Datatype tyNm Vector.empty
      numNonRecArgs <- GT.liftGen $ chooseInt (1, 5) -- need at least one to avoid "bad" types
      args <- coerce $ GT.vectorOf numNonRecArgs nestedCtorArg
      pure $ Constructor ctorNm (Vector.fromList (thisType : args))

{- Single variable polymorphic datatypes. That is, things like:

   data Foo a = Nope | Yup a

   data Snowk a = Start | More (Snowk a) a
-}
newtype Polymorphic1 = Polymorphic1 (DataDeclaration AbstractTy)
  deriving (Eq) via (DataDeclaration AbstractTy)
  deriving stock (Show)

{- Generator for single variable polymorphic datatypes, no polymorphic *functions* as arguments to the datatypes yet (that requires something different).

   When run multiple times in the monadic context, will reuse single variable declarations that are "in scope" (i.e. have already been generated and are
   known in the DataGenM state).

   TODO: Rework this to generate declarations with an arbitrary number of tyvar arguments. Doing so would be fairly simple (but isn't needed ATM)
-}
genPolymorphic1Decl :: DataGenM Polymorphic1
genPolymorphic1Decl =
  Polymorphic1 <$> do
    tyNm <- freshTyName
    logArity tyNm count1
    numCtors <- GT.liftGen $ chooseInt (1, 5)
    polyCtors <- concat <$> GT.vectorOf numCtors (genPolyCtor tyNm)
    let result = DataDeclaration tyNm count1 (Vector.fromList polyCtors)
    returnDecl result
  where
    -- We return a single constructor UNLESS we're generating a recursive type, in which case we have to return 2 to ensure a base case
    genPolyCtor :: TyName -> DataGenM [Constructor AbstractTy]
    genPolyCtor thisTy = do
      ctorNm <- freshConstructorName
      numArgs <- GT.liftGen $ chooseInt (1, 5)
      argsRaw <- GT.vectorOf numArgs polyArg
      let recCase = Datatype thisTy (Vector.singleton (Abstraction (BoundAt Z ix0)))
      if recCase `elem` argsRaw
        then do
          baseCtorNm <- freshConstructorName
          let baseCtor = Constructor baseCtorNm mempty
              recCtor = Constructor ctorNm (fromListN numArgs argsRaw)
          pure [baseCtor, recCtor]
        else pure [Constructor ctorNm (fromListN numArgs argsRaw)]
      where
        arityOne :: Count "tyvar" -> Bool
        arityOne c = c == count1

        polyArg :: DataGenM (ValT AbstractTy)
        polyArg = do
          -- first we choose a type with an arity >=1. We have to have at least one of those because we've added the parent type to the arity map
          availableArity1 <- gets (M.keys . M.filter arityOne . view dgArities)
          someTyCon1 <- GT.elements availableArity1
          GT.oneof
            [ pure $ Abstraction (BoundAt Z ix0),
              pure $ Datatype someTyCon1 (Vector.singleton (Abstraction (BoundAt Z ix0))),
              GT.liftGen (coerce <$> arbitrary @Concrete)
            ]

{-
   Misc Helpers and the Arbitrary instances
-}

{- This saves us from having to write *another* newtype for each set of a "flavor" of datatypes and doesn't have any real drawbacks -}
-- @since 1.1.0
data DataDeclFlavor
  = ConcreteDecl
  | ConcreteNestedDecl
  | SimpleRecursive
  | Poly1

-- @since 1.1.0
newtype DataDeclSet (flavor :: DataDeclFlavor) = DataDeclSet [DataDeclaration AbstractTy]

{- NOTE @Koz: This is supposed to be a "generic" shrinker for datatypes. It *should* return two paths:
                - One that shrinks the number of constructors
                - One that shrinks the constructors

              This is why I had to add handling for `datatype` into `Concrete`. To use `shrink` recursively
              on the structural components, we need some kind of instance to pivot off of. Since we want to avoid
              writing a generic Arbitrary instance for Constructor or DataDeclaration, this seems like the
              simplest solution.
-}
shrinkDataDecl :: DataDeclaration AbstractTy -> [DataDeclaration AbstractTy]
shrinkDataDecl (DataDeclaration nm cnt ctors)
  | Vector.null ctors = []
  | otherwise =
      let concreteShrink :: Vector (ValT AbstractTy) -> [Vector (ValT AbstractTy)]
          concreteShrink = coerce . shrink . fmap Concrete

          concreteShrink' :: Vector (ValT AbstractTy) -> [Vector (ValT AbstractTy)]
          concreteShrink' xs = coerce $ fmap (Vector.fromList . shrink . Concrete) (Vector.toList xs)

          ctorShrink :: Constructor AbstractTy -> [Constructor AbstractTy]
          ctorShrink (Constructor ctorNm args) = Constructor ctorNm <$> concreteShrink args

          ctorArgShrink :: Constructor AbstractTy -> [Constructor AbstractTy]
          ctorArgShrink (Constructor ctorNm args) = Constructor ctorNm <$> concreteShrink' args

          withShrunkenCtors = ((DataDeclaration nm cnt . Vector.fromList) . ctorShrink <$> Vector.toList ctors)

          withShrunkenCtorArgs = DataDeclaration nm cnt . Vector.fromList . ctorArgShrink <$> Vector.toList ctors
       in withShrunkenCtors <|> withShrunkenCtorArgs

-- REVIEW: I dunno how liftShrink works under the hood so this might be redundant?
shrinkDataDecls :: [DataDeclaration AbstractTy] -> [[DataDeclaration AbstractTy]]
shrinkDataDecls decls = liftShrink shrinkDataDecl decls <|> (shrinkDataDecl <$> decls)

genDataN :: forall (a :: Type). Int -> DataGenM a -> Gen [a]
genDataN n act = runDataGenM (GT.vectorOf n act)

genDataList :: forall (a :: Type). DataGenM a -> Gen [a]
genDataList = runDataGenM . GT.listOf

-- @since 1.1.0
instance Arbitrary (DataDeclSet 'ConcreteDecl) where
  arbitrary = coerce $ genDataList genConcreteDataDecl

  shrink = coerce . shrinkDataDecls . coerce

-- @since 1.1.0
instance Arbitrary (DataDeclSet 'ConcreteNestedDecl) where
  arbitrary = coerce $ genDataList genNestedConcrete

  shrink = coerce . shrinkDataDecls . coerce

-- @since 1.1.0
instance Arbitrary (DataDeclSet 'SimpleRecursive) where
  arbitrary = coerce $ genDataList genArbitraryRecursive

  shrink = coerce . shrinkDataDecls . coerce

-- @since 1.1.0
instance Arbitrary (DataDeclSet 'Poly1) where
  arbitrary = coerce $ genDataList genPolymorphic1Decl

  shrink = coerce . shrinkDataDecls . coerce

{- Misc Repl testing utilities. I'd like to leave these here because I can't exactly have a test suite
   to validate test generators, so inspection may be necessary if something goes wrong.
-}

-- Prettifies and prints n generated datatypes using the supplied generator.
genPrettyDataN :: Int -> DataGenM (DataDeclaration AbstractTy) -> IO ()
genPrettyDataN n dg = goPrint =<< generate (genDataN n dg)
  where
    goPrint :: [DataDeclaration AbstractTy] -> IO ()
    goPrint [] = pure ()
    goPrint (x : xs) = do
      x' <- unsafeRename (renameDataDecl x)
      putDoc $ pretty x' <> hardline <> hardline
      goPrint xs

testConcrete :: Int -> IO ()
testConcrete n = genPrettyDataN n (coerce <$> genConcreteDataDecl)

testNested :: Int -> IO ()
testNested n = genPrettyDataN n (coerce <$> genNestedConcrete)

testRecConcrete :: Int -> IO ()
testRecConcrete n = genPrettyDataN n (coerce <$> genArbitraryRecursive)

testPoly1 :: Int -> IO ()
testPoly1 n = genPrettyDataN n (coerce <$> genPolymorphic1Decl)

-- For convenience. Don't remove this, necessary for efficient development on future work
unsafeRename :: forall (a :: Type). RenameM a -> IO a
unsafeRename act = case runRenameM act of
  Left err -> throwIO (userError $ show err)
  Right res -> pure res
