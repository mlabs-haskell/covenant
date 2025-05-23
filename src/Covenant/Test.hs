{-# LANGUAGE PolyKinds #-}

module Covenant.Test
  ( Concrete (Concrete),
    DataDeclSet (DataDeclSet),
    DataDeclFlavor (ConcreteDecl, ConcreteNestedDecl, SimpleRecursive, Poly1, Poly1PolyThunks),
    chooseInt,
    scale,
    testConcrete,
    testNested,
    testRecConcrete,
    testPoly1,
    testBaseF,
    testNonConcrete,
    prettyDeclSet,
    testBBF,
  )
where

import Control.Applicative ((<|>))
import Control.Monad (void)
import Control.Monad.Reader (MonadTrans (lift), runReader)
import Control.Monad.State.Strict
  ( MonadState (get, put),
    State,
    evalState,
    gets,
    modify,
  )
import Covenant.Data (mkBBF, mkBaseFunctor, noPhantomTyVars)
import Covenant.DeBruijn (DeBruijn (Z), asInt)
import Covenant.Index
  ( Count,
    count0,
    count1,
    intCount,
    intIndex,
    ix0,
  )
import Covenant.Internal.Rename (renameDataDecl, renameValT)
import Covenant.Internal.Type
  ( CompT (CompT),
    CompTBody (CompTBody),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (SOP),
    ScopeBoundary,
    TyName (TyName),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    prettyStr,
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
import Data.Foldable (forM_)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe (fromJust, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty qualified as NEV
import GHC.Exts (fromListN)
import GHC.Word (Word32)
import Optics.Core (A_Lens, LabelOptic (labelOptic), folded, lens, over, preview, review, set, toListOf, view, (%))
import Prettyprinter (hardline, pretty)
import Prettyprinter.Render.Text (putDoc)
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Arbitrary1 (liftArbitrary, liftShrink),
    Gen,
    elements,
    frequency,
    generate,
    sized,
    suchThat,
    vectorOf,
  )
import Test.QuickCheck qualified as QC (chooseInt)
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
            frequency
              [ (10, pure . BuiltinFlat $ UnitT),
                (10, pure . BuiltinFlat $ BoolT),
                (10, pure . BuiltinFlat $ IntegerT),
                (10, pure . BuiltinFlat $ StringT),
                (10, pure . BuiltinFlat $ ByteStringT),
                (10, pure . BuiltinFlat $ BLS12_381_G1_ElementT),
                (10, pure . BuiltinFlat $ BLS12_381_G2_ElementT),
                (10, pure . BuiltinFlat $ BLS12_381_MlResultT),
                (2, ThunkT . Comp0 <$> (ArgsAndResult <$> liftArbitrary (go (size `quot` 4)) <*> go (size `quot` 4)))
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

instance
  (k ~ A_Lens, a ~ Map TyName (DataDeclaration AbstractTy), b ~ Map TyName (DataDeclaration AbstractTy)) =>
  LabelOptic "decls" k DataGen DataGen a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(DataGen a _ _ _ _) -> a) (\(DataGen _ b c d e) a -> DataGen a b c d e)

instance
  (k ~ A_Lens, a ~ Set ConstructorName, b ~ Set ConstructorName) =>
  LabelOptic "constructors" k DataGen DataGen a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(DataGen _ b _ _ _) -> b) (\(DataGen a _ c d e) b -> DataGen a b c d e)

instance
  (k ~ A_Lens, a ~ ScopeBoundary, b ~ ScopeBoundary) =>
  LabelOptic "currentScope" k DataGen DataGen a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(DataGen _ _ c _ _) -> c) (\(DataGen a b _ d e) c -> DataGen a b c d e)

instance
  (k ~ A_Lens, a ~ Map ScopeBoundary Word32, b ~ Map ScopeBoundary Word32) =>
  LabelOptic "boundVars" k DataGen DataGen a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(DataGen _ _ _ d _) -> d) (\(DataGen a b c _ e) d -> DataGen a b c d e)

instance
  (k ~ A_Lens, a ~ Map TyName (Count "tyvar"), b ~ Map TyName (Count "tyvar")) =>
  LabelOptic "arities" k DataGen DataGen a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(DataGen _ _ _ _ e) -> e) (\(DataGen a b c d _) e -> DataGen a b c d e)

{-  Monadic stack for generating monomorphic datatype declarations. Not every generator uses every part of the state, but
    it ought to suffice for generating *any* datatype declaration we choose.

    In theory this could be a reader but it becomes super awkward to work, StateT is easier

    While we don't have any generators for polymorphic `ValT`s yet, the scope stuff will be necessary there.
-}
newtype DataGenM a = DataGenM (GenT (State DataGen) a)
  deriving newtype (Functor, Applicative, Monad)
  deriving (MonadGen) via GenT (State DataGen)

instance MonadState DataGen DataGenM where
  get = DataGenM $ lift get
  put = DataGenM . lift . put

{- N.B. We don't need this *yet* but we will need it to generate constructors which take polymorphic functions as arguments.
-}
bindVars :: Count "tyvar" -> DataGenM ()
bindVars count'
  | count == 0 = crossBoundary
  | otherwise = do
      crossBoundary
      here <- gets (view #currentScope)
      modify $ over #boundVars (M.insert here $ fromIntegral count)
  where
    count :: Int
    count = review intCount count'

    crossBoundary :: DataGenM ()
    crossBoundary = modify $ over #currentScope (+ 1)

-- performs action in the deeper scope then resets.
withBoundVars :: forall (a :: Type). Count "tyvar" -> DataGenM a -> DataGenM a
withBoundVars count act = do
  oldScope <- gets (view #currentScope)
  bindVars count
  res <- act
  modify $ set #currentScope oldScope
  pure res

runDataGenM :: forall (a :: Type). DataGenM a -> Gen a
runDataGenM (DataGenM ma) = (\x -> evalState x (DataGen M.empty Set.empty 0 M.empty M.empty)) <$> GT.runGenT ma

chooseInt :: forall (m :: Type -> Type). (MonadGen m) => (Int, Int) -> m Int
chooseInt bounds = GT.liftGen $ QC.chooseInt bounds

-- Stupid helper, saves us from forgetting to update part of the state
returnDecl :: DataDeclaration AbstractTy -> DataGenM (DataDeclaration AbstractTy)
returnDecl od@(OpaqueData tn _) = modify (over #decls (M.insert tn od)) >> pure od
returnDecl decl@(DataDeclaration tyNm arity _ _) = do
  modify $ over #decls (M.insert tyNm decl)
  logArity tyNm arity
  pure decl

scale :: forall (m :: Type -> Type) (a :: Type). (MonadGen m) => (Int -> Int) -> m a -> m a
scale f g = GT.sized (\n -> GT.resize (f n) g)

{- We need this outside of `returnDecl` to construct recursive polymorphic types, i.e. types where an argument to
   a constructor is the parent type applied to the type variables bound at the start of the declaration.
-}
logArity :: TyName -> Count "tyvar" -> DataGenM ()
logArity tn cnt = modify $ over #arities (M.insert tn cnt)

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

{- These ensure that we don't ever duplicate type names or constructor names. We need the DataGenM state
   to ensure that, so these should *always* be used when writing generators, and the arbitrary instances should be avoided.
-}
freshConstructorName :: DataGenM ConstructorName
freshConstructorName = do
  datatypes <- gets (M.elems . view #decls)
  let allCtorNames = Set.fromList $ toListOf (folded % #datatypeConstructors % folded % #constructorName) datatypes
  thisName <- GT.liftGen $ anyCtorName `suchThat` (`Set.notMember` allCtorNames)
  modify $ over #constructors (Set.insert thisName)
  pure thisName

freshTyName :: DataGenM TyName
freshTyName = do
  datatypes <- gets (M.elems . view #decls)
  let allDataTypeNames = Set.fromList $ toListOf (folded % #datatypeName) datatypes
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
      numArgs <- chooseInt (0, 5)
      args <- GT.liftGen $ Vector.replicateM numArgs (arbitrary @Concrete)
      pure $ Constructor ctorNm (coerce <$> args)

genConcreteDataDecl :: DataGenM ConcreteDataDecl
genConcreteDataDecl =
  ConcreteDataDecl <$> do
    tyNm <- freshTyName
    numArgs <- chooseInt (0, 5)
    ctors <- coerce <$> Vector.replicateM numArgs genConcreteConstructor
    let decl = DataDeclaration tyNm count0 ctors SOP
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
    res <- GT.oneof [nullary tyNm, nonNestedConcrete tyNm, nested tyNm]
    returnDecl res
  where
    nullary :: TyName -> DataGenM (DataDeclaration AbstractTy)
    nullary tyNm = do
      ctorNm <- freshConstructorName
      pure $ DataDeclaration tyNm count0 (Vector.singleton (Constructor ctorNm Vector.empty)) SOP

    nonNestedConcrete :: TyName -> DataGenM (DataDeclaration AbstractTy)
    nonNestedConcrete tyNm = do
      numCtors <- chooseInt (0, 5)
      ctors <- fmap coerce <$> Vector.replicateM numCtors genConcreteConstructor
      pure $ DataDeclaration tyNm count0 ctors SOP

    nested :: TyName -> DataGenM (DataDeclaration AbstractTy)
    nested tyNm = do
      numCtors <- chooseInt (0, 5)
      ctors <- Vector.replicateM numCtors nestedCtor
      pure $ DataDeclaration tyNm count0 (coerce <$> ctors) SOP

{- It's useful to have access to these outside of the above function because sometimes we want to mix and match
   "simpler" constructors like this with the more complex sorts we generate below.
-}
nestedCtor :: DataGenM NestedConcreteCtor
nestedCtor = do
  -- We want this: Not very much hinges on the # of args to each constructor and having finite bounds like this makes the output easier to read
  numArgs <- chooseInt (0, 5)
  args <- Vector.replicateM numArgs nestedCtorArg
  ctorNm <- freshConstructorName
  pure . coerce $ Constructor ctorNm args

nestedCtorArg :: DataGenM (ValT AbstractTy)
nestedCtorArg = do
  userTyNames <- gets (M.keys . view #decls)
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
    numRecCtors <- chooseInt (1, 5)
    recCtor <- GT.vectorOf numRecCtors $ genRecCtor tyNm
    returnDecl $ DataDeclaration tyNm count0 (Vector.fromList (baseCtor : recCtor)) SOP
  where
    genRecCtor :: TyName -> DataGenM (Constructor AbstractTy)
    genRecCtor tyNm = do
      ctorNm <- freshConstructorName
      let thisType = Datatype tyNm Vector.empty
      numNonRecArgs <- chooseInt (1, 5) -- need at least one to avoid "bad" types
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
  Polymorphic1
    <$> GT.suchThat
      ( do
          -- this is a hack to save avoid reworking generator logic. It should be fine cuz we're not super likely to get phantoms anyway
          tyNm <- freshTyName
          logArity tyNm count1
          numCtors <- chooseInt (1, 5)
          polyCtors <- concat <$> GT.vectorOf numCtors (genPolyCtor tyNm)
          let result = DataDeclaration tyNm count1 (Vector.fromList polyCtors) SOP
          returnDecl result
      )
      noPhantomTyVars
  where
    -- We return a single constructor UNLESS we're generating a recursive type, in which case we have to return 2 to ensure a base case
    genPolyCtor :: TyName -> DataGenM [Constructor AbstractTy]
    genPolyCtor thisTy = do
      ctorNm <- freshConstructorName
      numArgs <- chooseInt (1, 5)
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
          availableArity1 <- gets (M.keys . M.filter arityOne . view #arities)
          someTyCon1 <- GT.elements availableArity1
          GT.oneof
            [ pure $ Abstraction (BoundAt Z ix0),
              pure $ Datatype someTyCon1 (Vector.singleton (Abstraction (BoundAt Z ix0))),
              GT.liftGen (coerce <$> arbitrary @Concrete)
            ]

{- Non-concrete ValTs. This needs to be scope- and context-sensitive in order to generate ThunkTs that *use* (but never *bind*) variables.

This will give us things like:

  data Foo a b = Foo Int Bool a (a -> (Int -> b) -> b -> b)
-}

newtype NonConcrete = NonConcrete (ValT AbstractTy)
  deriving
    ( -- | @since 1.0.0
      Eq
    )
    via (ValT AbstractTy)
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

genNonConcrete :: DataGenM NonConcrete
genNonConcrete = NonConcrete <$> GT.sized go
  where
    -- smaller to make output more readable
    genConcrete :: DataGenM Concrete
    genConcrete = GT.liftGen $ scale (`quot` 8) (arbitrary @Concrete)

    go :: Int -> DataGenM (ValT AbstractTy)
    go = helper

    -- A polymorphic tycon applied to *either* an in-scope type variable *or* a concrete type.
    -- TODO: Conceivably this could recursively call `helper` to generate "fancier" tycon arguments
    --       but that shouldn't matter much for now & runs the risk of generating unusably large output w/o
    --       careful implementation.
    appliedTyCon :: Int -> DataGenM (ValT AbstractTy)
    appliedTyCon size = do
      currentScope <- gets (view #currentScope)
      tyConsWithArity <- M.toList <$> gets (view #arities)
      boundVars <- M.toList <$> gets (view #boundVars)
      -- We *have* to have some variables bound for this to work. We can't meaningfully return a `Maybe` here
      -- Also we have to have some Arity >= 1 TyCon around
      -- I.e. we cannot run this generator in a "fresh" DataGenM stack and have to both pre-generate
      -- some fresh polymorphic types *and* ensure that we only use this in a context where we have bound variables.
      (thisTyCon, thisArity) <- GT.elements tyConsWithArity
      let arityInt = review intCount thisArity
      let resolvedArgs = concatMap (resolveArgs currentScope) boundVars
      let choices
            | size <= 0 = [coerce <$> genConcrete]
            | otherwise = [coerce <$> genConcrete, GT.elements resolvedArgs]
      tyConArgs <- GT.vectorOf arityInt $ GT.oneof choices
      pure $ Datatype thisTyCon (Vector.fromList tyConArgs)

    resolveArgs :: ScopeBoundary -> (ScopeBoundary, Word32) -> [ValT AbstractTy]
    resolveArgs currentScope (varScope, numIndices) =
      let resolvedScope :: DeBruijn
          resolvedScope = fromJust . preview asInt . fromIntegral $ currentScope - varScope
       in mapMaybe (fmap (Abstraction . BoundAt resolvedScope) . preview intIndex) [0 .. (fromIntegral numIndices - 1)]

    unsafeFromList :: forall (a :: Type). [a] -> NEV.NonEmptyVector a
    unsafeFromList = fromJust . NEV.fromList

    helper :: Int -> DataGenM (ValT AbstractTy)
    helper size = withBoundVars count0 $ do
      -- we're going to return a thunk so we need to enter a new scope
      funLen <- chooseInt (1, 5)
      funList <- GT.vectorOf funLen $ GT.frequency [(5, coerce <$> genConcrete), (2, appliedTyCon size), (3, helper (size `quot` 8))]
      pure $ ThunkT . CompT count0 . CompTBody $ unsafeFromList funList

-- NOTE: We have to call this with a "driver" which pre-generates suitable (i.e. polymorphic) data declarations, see notes in `genNonConcrete`
genNonConcreteDecl :: DataGenM (DataDeclaration AbstractTy)
genNonConcreteDecl = flip GT.suchThat noPhantomTyVars . withBoundVars count1 $ do
  -- we need to bind the vars before we're done constructing the type
  tyNm <- freshTyName
  numArgs <- chooseInt (1, 5)
  ctors <- Vector.replicateM numArgs genNonConcreteCtor
  let decl = DataDeclaration tyNm count1 ctors SOP
  returnDecl decl
  where
    genNonConcreteCtor :: DataGenM (Constructor AbstractTy)
    genNonConcreteCtor = do
      ctorNm <- freshConstructorName
      numArgs <- chooseInt (0, 5)
      args <- GT.vectorOf numArgs genNonConcrete
      pure $ Constructor ctorNm (coerce . Vector.fromList $ args)

{-
   Misc Helpers and the Arbitrary instances
-}

{- This saves us from having to write *another* newtype for each set of a "flavor" of datatypes and doesn't have any real drawbacks -}
-- @since 1.1.0
data DataDeclFlavor
  = ConcreteDecl -- all ctor arguments are fully concrete and the declaration is monomorphic
  | ConcreteNestedDecl -- all ctor arguments are fully concrete & declaration is monomorphic, but can reuse already-generated concrete decls present in the monadic context
  | SimpleRecursive -- recursive but not polymorphic (e.g. data IntList = End | More Int IntList)
  | Poly1 -- polymorphic 1 variable datatypes which may (or may not be) recursive
  | Poly1PolyThunks -- Generates a polymorphic 1 variable datatypes which may contain other polymorphic arguments inside ThunkT args to the ctors
  -- (Poly1 will always yield concrete ThunkT arguments, it's a subtle difference but relevant for base functor testing)
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
shrinkDataDecl OpaqueData {} = []
shrinkDataDecl (DataDeclaration nm cnt ctors strat)
  | Vector.null ctors = []
  | otherwise = filter noPhantomTyVars $ smallerNumCtors <|> smallerCtorArgs
  where
    smallerNumCtors :: [DataDeclaration AbstractTy]
    smallerNumCtors = Vector.toList $ (\cs -> DataDeclaration nm cnt cs strat) <$> Vector.init (subVectors ctors)
    smallerCtorArgs = (\cs -> DataDeclaration nm cnt cs strat) <$> shrinkCtorsNumArgs ctors

    -- need a fn which takes a single ctor and just shrinks the args
    -- this is difficult to keep track of: THIS ONE GIVES US IDENTICALLY NAMED CTORS WITH DIFFERENT ARG LISTS
    shrinkNumArgs :: Constructor AbstractTy -> [Constructor AbstractTy]
    shrinkNumArgs (Constructor ctorNm args) =
      let smallerArgs :: [Vector (ValT AbstractTy)]
          smallerArgs = coerce $ shrink (fmap Concrete args)
       in fmap (Constructor ctorNm) smallerArgs

    shrinkCtorsNumArgs :: Vector (Constructor AbstractTy) -> [Vector (Constructor AbstractTy)]
    shrinkCtorsNumArgs cs =
      let -- the inner lists exhaust the arg-deletion possibilities for each constructor
          cs' = Vector.toList $ shrinkNumArgs <$> cs
          go [] = []
          go (x : xs) = (:) <$> x <*> xs
       in Vector.fromList <$> go cs'

-- Helper, should probably exist in Data.Vector but doesn't
subVectors :: forall (a :: Type). Vector a -> Vector (Vector a)
subVectors xs = Vector.cons Vector.empty (nonEmptySubVectors xs)

nonEmptySubVectors :: forall (a :: Type). Vector a -> Vector (Vector a)
nonEmptySubVectors v = case Vector.uncons v of
  Nothing -> Vector.empty
  Just (x, xs) ->
    let f :: Vector a -> Vector (Vector a) -> Vector (Vector a)
        f ys r = ys `Vector.cons` ((x `Vector.cons` ys) `Vector.cons` r)
     in Vector.singleton x `Vector.cons` foldr f Vector.empty (nonEmptySubVectors xs)

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

instance Arbitrary (DataDeclSet 'Poly1PolyThunks) where
  arbitrary = coerce . runDataGenM $ do
    -- If we don't have this we can't generate ctor args of the sort we want here.
    -- I *think* we're very unlikely to get 10 unsuitable decls out of this
    void $ GT.vectorOf 10 genPolymorphic1Decl
    void $ GT.listOf genNonConcreteDecl
    decls <- M.elems <$> gets (view #decls) -- simpler to just pluck them from the monadic context
    pure $ filter noPhantomTyVars decls -- TODO/FIXME: We shouldn't have to filter here, better to catch things earlier
  shrink = coerce . shrinkDataDecls . coerce

prettyDeclSet :: forall (a :: DataDeclFlavor). DataDeclSet a -> String
prettyDeclSet (DataDeclSet decls) = concatMap (\x -> (prettyStr . unsafeRename . renameDataDecl $ x) <> "\n\n") decls

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
      let x' = unsafeRename (renameDataDecl x)
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

testNonConcrete :: Int -> IO ()
testNonConcrete n = do
  res <- generate $ runDataGenM (prep >> go n)
  finalizeAndPrint res
  where
    prep :: DataGenM ()
    prep = void $ GT.vectorOf 10 genPolymorphic1Decl

    go :: Int -> DataGenM [DataDeclaration AbstractTy]
    go n'
      | n' <= 0 = M.elems <$> gets (view #decls)
      | otherwise = genNonConcreteDecl >> go (n' - 1)

    finalizeAndPrint :: [DataDeclaration AbstractTy] -> IO ()
    finalizeAndPrint [] = pure ()
    finalizeAndPrint (x : xs) = do
      let x' = unsafeRename (renameDataDecl x)
      putDoc $ pretty x' <> hardline <> hardline
      finalizeAndPrint xs

-- For convenience. Don't remove this, necessary for efficient development on future work
unsafeRename :: forall (a :: Type). RenameM a -> a
unsafeRename act = case runRenameM act of
  Left err -> error $ show err
  Right res -> res

-- crude base functor repl test, should be removed eventually in favor of a real test
testBaseF :: IO ()
testBaseF = do
  samples <- generate $ genDataN 10 (coerce <$> genPolymorphic1Decl)
  forM_ samples $ \decl -> do
    let prettyIn = pretty $ unsafeRename (renameDataDecl decl)
    putDoc $ hardline <> "INPUT:" <> hardline <> hardline <> prettyIn <> hardline <> hardline
    let output = runReader (mkBaseFunctor decl) 0
    case output of
      Nothing -> putDoc "OUTPUT: Nothing (base functor not needed)"
      Just outDecl -> do
        let prettyOut = pretty $ unsafeRename (renameDataDecl outDecl)
        putDoc $ "OUTPUT: " <> hardline <> hardline <> prettyOut <> hardline <> "-------------" <> hardline

testBBF :: IO ()
testBBF = do
  DataDeclSet inputs <- generate (arbitrary @(DataDeclSet 'Poly1))
  forM_ inputs $ \inp -> do
    let inpPretty = pretty $ unsafeRename (renameDataDecl inp)
    putDoc $ hardline <> "INPUT:" <> hardline <> hardline <> inpPretty <> hardline
    case mkBBF inp of
      Nothing -> putDoc $ hardline <> "OUTPUT: Nothing (Empty datatype)"
      Just out -> do
        let outPretty = pretty $ unsafeRename (renameValT out)
        putDoc $ hardline <> "OUTPUT:" <> hardline <> hardline <> outPretty <> hardline
