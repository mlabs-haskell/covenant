{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
module Covenant.Test
  ( Concrete (Concrete),
    DataDeclSet(DataDeclSet),
    DataDeclFlavor(ConcreteDecl,ConcreteNestedDecl,SimpleRecursive,Poly1),
    testConcrete,
    testNested,
    testRecConcrete,
    testPoly1
  )
where

import Control.Applicative ((<|>))
import Covenant.Index (count0, Count, intCount, count1, ix0)
import Covenant.Type
    ( BuiltinFlatT(BLS12_381_MlResultT, UnitT, BoolT, IntegerT,
                   StringT, ByteStringT, BLS12_381_G1_ElementT,
                   BLS12_381_G2_ElementT),
      CompT(CompN, Comp0),
      CompTBody(ArgsAndResult),
      AbstractTy(BoundAt),
      runRenameM,
      RenameM )
import Data.Coerce (coerce)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Set (Set)
import Data.Set qualified as Set
import Test.QuickCheck
    ( Arbitrary(arbitrary,shrink),
      chooseInt,
      elements,
      frequency,
      generate,
      oneof,
      sized,
      suchThat,
      vectorOf,
      Arbitrary1(liftShrink, liftArbitrary),
      Gen )
import Test.QuickCheck.Instances.Vector ()
import Covenant.Internal.Type
    ( DataDeclaration(DataDeclaration),
      Constructor(Constructor),
      ConstructorName(ConstructorName),
      ScopeBoundary,
      ValT(Datatype, Abstraction, BuiltinFlat, ThunkT),
      TyName(TyName),
      runConstructorName,
      constructorName,
      datatypeName,
      datatypeBinders,
      datatypeConstructors )
import Data.Text (Text)
import Data.Text qualified as T
import Covenant.Internal.Rename ( renameDataDecl )
import Data.Kind (Type)
import Control.Exception (throwIO)
import Prettyprinter (pretty, hardline)
import Prettyprinter.Render.Text (putDoc)
import Test.QuickCheck.Instances.Containers ()
import Control.Monad.Reader (MonadTrans (lift))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Optics.Operators ((^.), (^..))
import Optics.Core ((%), folded, Lens', lens, view, over, review)
import Control.Monad.State.Strict
    ( StateT,
      gets,
      modify,
      MonadState(get, put),
      evalState,
      State )
import GHC.Word (Word32)
import Test.QuickCheck.GenT (MonadGen, GenT)
import Test.QuickCheck.GenT qualified as GT
import Data.Functor.Identity (Identity())
import Covenant.DeBruijn (DeBruijn(Z))


-- | Wrapper for 'Covenant.Internal.Type.ValT' to provide an 'Arbitrary' instance to generate only
-- value types without any type variables.
--
-- @since 1.0.0
newtype Concrete = Concrete (Covenant.Internal.Type.ValT AbstractTy)
  deriving
    ( -- | @since 1.0.0
      Eq
    )
    via (Covenant.Internal.Type.ValT AbstractTy)
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
instance Arbitrary Concrete where
  {-# INLINEABLE arbitrary #-}
  arbitrary = Concrete <$> sized go
    where
      go :: Int -> Gen (Covenant.Internal.Type.ValT AbstractTy)
      go size
        | size <= 0 =
            Covenant.Internal.Type.BuiltinFlat
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
              [ pure . Covenant.Internal.Type.BuiltinFlat $ UnitT,
                pure . Covenant.Internal.Type.BuiltinFlat $ BoolT,
                pure . Covenant.Internal.Type.BuiltinFlat $ IntegerT,
                pure . Covenant.Internal.Type.BuiltinFlat $ StringT,
                pure . Covenant.Internal.Type.BuiltinFlat $ ByteStringT,
                pure . Covenant.Internal.Type.BuiltinFlat $ BLS12_381_G1_ElementT,
                pure . Covenant.Internal.Type.BuiltinFlat $ BLS12_381_G2_ElementT,
                pure . Covenant.Internal.Type.BuiltinFlat $ BLS12_381_MlResultT,
                Covenant.Internal.Type.ThunkT . Comp0 <$> (ArgsAndResult <$> liftArbitrary (go (size `quot` 4)) <*> go (size `quot` 4))
               -- This is probably right but things will break if we generate datatypes at this stage
               -- ,  Datatype <$> arbitrary <*> pure count0 <*> liftArbitrary (go (size `quot` 4))
              ]
  {-# INLINEABLE shrink #-}
  shrink (Concrete v) =
    Concrete <$> case v of
      -- impossible
      Covenant.Internal.Type.Abstraction _ -> []
      Covenant.Internal.Type.ThunkT (CompN _ (ArgsAndResult args result)) ->
        Covenant.Internal.Type.ThunkT . CompN count0 <$> do
          let argsList = Vector.toList args
          argsList' <- fmap coerce . shrink . fmap Concrete $ argsList
          result' <- fmap coerce . shrink . Concrete $ result
          let args' = Vector.fromList argsList'
          pure (ArgsAndResult args' result) <|> pure (ArgsAndResult args result')
      -- Can't shrink this
      Covenant.Internal.Type.BuiltinFlat _ -> []
      -- NOTE @Koz: I need this here to write some other instances even though `Concrete` can't generate this
      Covenant.Internal.Type.Datatype tn args -> Covenant.Internal.Type.Datatype tn <$> do
        let argsList = Vector.toList args
        (fmap (Vector.fromList . coerce) . shrink . fmap Concrete) argsList

{- The state used by our datatype generators.
-}
data DataGen = DataGen {
        -- Keeps track of decls we've already generated. Used for "nested" generators and also essential for ValT generation (when we get around to implementing it)
        _dgDecls :: Map Covenant.Internal.Type.TyName (Covenant.Internal.Type.DataDeclaration AbstractTy),
        -- All used constructor names. Have to track separately, even though the information eventually ends up in the previous field, to avoid duplicate constructors in the same type.
        _dgCtors :: Set Covenant.Internal.Type.ConstructorName,
        -- Current scope. Needed for generating polymorphic `ValT`s for arguments to constructors . (That's not implemented yet but we 100% will need this )
        _dgCurrentScope :: Covenant.Internal.Type.ScopeBoundary,
        -- NOTE: Needs to maintain the invariant that the Word32 is always >0, since we will use this to select in scope variables for polymorphic args to ctors. (Again, not implemented yet)
        _dgBoundVars :: Map Covenant.Internal.Type.ScopeBoundary Word32,
        -- We need this for recursive types. We can't lookup the arity in dgDecls if we want to recurse b/c it won't be there until we've finished generating the whole decl
        _dgArities :: Map Covenant.Internal.Type.TyName (Count "tyvar")
        }

-- TODO: Rewrite as field label instances
dgDecls :: Lens' DataGen (Map Covenant.Internal.Type.TyName (Covenant.Internal.Type.DataDeclaration AbstractTy))
dgDecls = lens (\(DataGen a _ _ _ _) -> a) (\(DataGen _ b c d e) a -> DataGen a b c d e)

dgConstructors :: Lens' DataGen (Set Covenant.Internal.Type.ConstructorName)
dgConstructors = lens (\(DataGen _ b _ _ _) -> b) (\(DataGen a _ c d e) b -> DataGen a b c d e)

_dgCurrentScope :: Lens' DataGen Covenant.Internal.Type.ScopeBoundary
_dgCurrentScope = lens (\(DataGen _ _ c _ _) -> c) (\(DataGen a b _ d e) c -> DataGen a b c d e)

_dgBoundVars :: Lens' DataGen (Map Covenant.Internal.Type.ScopeBoundary Word32)
_dgBoundVars = lens (\(DataGen _ _ _ d _) -> d) (\(DataGen a b c _ e) d -> DataGen a b c d e)

dgArities :: Lens' DataGen (Map Covenant.Internal.Type.TyName (Count "tyvar"))
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
returnDecl :: Covenant.Internal.Type.DataDeclaration AbstractTy -> DataGenM (Covenant.Internal.Type.DataDeclaration AbstractTy)
returnDecl decl = do
  let tyNm = decl ^. Covenant.Internal.Type.datatypeName
  modify $ over dgDecls (M.insert tyNm decl)
  let arity = decl ^. Covenant.Internal.Type.datatypeBinders
  logArity tyNm arity
  pure decl

{- We need this outside of `returnDecl` to construct recursive polymorphic types, i.e. types where an argument to
   a constructor is the parent type applied to the type variables bound at the start of the declaration.
-}
logArity :: Covenant.Internal.Type.TyName -> Count "tyvar" -> DataGenM ()
logArity tn cnt = modify $ over dgArities (M.insert tn cnt)

newtype ConcreteDataDecl = ConcreteDataDecl (Covenant.Internal.Type.DataDeclaration AbstractTy)
  deriving Eq via (Covenant.Internal.Type.DataDeclaration AbstractTy)
  deriving stock Show

{- These should never be used in a DataGenM context, we should always use the fresh generators below-}
anyCtorName :: Gen Covenant.Internal.Type.ConstructorName
anyCtorName = Covenant.Internal.Type.ConstructorName <$> genValidCtorName
    where
      genValidCtorName :: Gen Text
      genValidCtorName = do
        let caps = ['A'..'Z']
            lower = ['a'..'z']
        nmLen <- chooseInt (1,6) -- should be more than enough to ensure `suchThat` doesn't run into clashes all the time
        x <- elements caps
        xs <- vectorOf nmLen  $ elements (caps <> lower)
        pure . T.pack $ (x:xs)

anyTyName :: Gen Covenant.Internal.Type.TyName
anyTyName =  Covenant.Internal.Type.TyName . Covenant.Internal.Type.runConstructorName <$> anyCtorName
  -- Default shrink should be fine? The name of constructors doesn't affect much

{- These ensure that we don't ever duplicate type names or constructor names. We need the DataGenM state
   to ensure that, so these should *always* be used when writing generators, and the arbitrary instances should be avoided.
-}
freshConstructorName :: DataGenM Covenant.Internal.Type.ConstructorName
freshConstructorName = do
  datatypes <- gets (M.elems . view dgDecls)
  let allCtorNames = Set.fromList $ datatypes ^.. (folded % Covenant.Internal.Type.datatypeConstructors % folded % Covenant.Internal.Type.constructorName)
  thisName <- GT.liftGen $ anyCtorName `suchThat` (`Set.notMember` allCtorNames)
  modify $ over dgConstructors (Set.insert thisName)
  pure thisName


freshTyName :: DataGenM Covenant.Internal.Type.TyName
freshTyName = do
  datatypes <- gets (M.elems . view dgDecls)
  let allDataTypeNames = Set.fromList $ datatypes ^.. (folded % Covenant.Internal.Type.datatypeName)
  GT.liftGen $ anyTyName `suchThat` (`Set.notMember` allDataTypeNames)

newtype ConcreteConstructor = ConcreteConstructor (Covenant.Internal.Type.Constructor AbstractTy)
  deriving Eq via (Covenant.Internal.Type.Constructor AbstractTy)
  deriving stock Show

genConcreteConstructor :: DataGenM ConcreteConstructor
genConcreteConstructor = ConcreteConstructor <$> go
  where
    go :: DataGenM (Covenant.Internal.Type.Constructor AbstractTy)
    go = do
      ctorNm <- freshConstructorName
      numArgs <- GT.liftGen $ chooseInt (0,5)
      args <- GT.liftGen $ Vector.replicateM numArgs (arbitrary @Concrete)
      pure $ Covenant.Internal.Type.Constructor ctorNm (coerce <$> args)

genConcreteDataDecl :: DataGenM ConcreteDataDecl
genConcreteDataDecl = ConcreteDataDecl <$> do
  tyNm <- freshTyName
  numArgs <- GT.liftGen $ chooseInt (0,5)
  ctors <- coerce <$> Vector.replicateM numArgs genConcreteConstructor
  let decl = Covenant.Internal.Type.DataDeclaration tyNm count0 ctors
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
newtype NestedConcreteDataDecl = NestedConcreteDataDecl (Covenant.Internal.Type.DataDeclaration AbstractTy)
  deriving Eq via (Covenant.Internal.Type.DataDeclaration AbstractTy)
  deriving stock Show

newtype NestedConcreteCtor = NestedConcreteCtor (Covenant.Internal.Type.Constructor AbstractTy)

genNestedConcrete :: DataGenM NestedConcreteDataDecl
genNestedConcrete = NestedConcreteDataDecl <$> do
  tyNm <-  freshTyName
  let nullary :: DataGenM (Covenant.Internal.Type.DataDeclaration AbstractTy)
      nullary = do
        ctorNm <- freshConstructorName
        pure $ Covenant.Internal.Type.DataDeclaration tyNm count0 (Vector.singleton (Covenant.Internal.Type.Constructor ctorNm Vector.empty))

      nonNestedConcrete :: DataGenM (Covenant.Internal.Type.DataDeclaration AbstractTy)
      nonNestedConcrete =  do
        numCtors <- GT.liftGen $ chooseInt (0,5)
        ctors <- fmap coerce <$> Vector.replicateM numCtors genConcreteConstructor
        pure $ Covenant.Internal.Type.DataDeclaration tyNm count0 ctors

      nested :: DataGenM (Covenant.Internal.Type.DataDeclaration AbstractTy)
      nested = do
        numCtors <- GT.liftGen $ chooseInt (0,5)
        ctors <- Vector.replicateM numCtors nestedCtor
        pure $ Covenant.Internal.Type.DataDeclaration tyNm count0 (coerce <$> ctors)

  options <- sequence [nullary,nonNestedConcrete,nested]
  res <- GT.liftGen $ oneof (pure <$> options)
  returnDecl res

{- It's useful to have access to these outside of the above function because sometimes we want to mix and match
   "simpler" constructors like this with the more complex sorts we generate below.
-}
nestedCtor :: DataGenM NestedConcreteCtor
nestedCtor = do
  -- We want this: Not very much hinges on the # of args to each constructor and having finite bounds like this makes the output easier to read
  numArgs <- GT.liftGen $ chooseInt (0,5)
  args <- Vector.replicateM numArgs nestedCtorArg
  ctorNm <-  freshConstructorName
  pure . coerce $ Covenant.Internal.Type.Constructor ctorNm args

nestedCtorArg :: DataGenM (Covenant.Internal.Type.ValT AbstractTy)
nestedCtorArg = do
     userTyNames <- gets (M.keys . view dgDecls)
     if null userTyNames
       then coerce <$> GT.liftGen (arbitrary @Concrete)
       else do
         let userTypes = (`Covenant.Internal.Type.Datatype` Vector.empty) <$> userTyNames
         GT.liftGen $ frequency [(8,elements userTypes), (2, coerce <$> arbitrary @Concrete)]

newtype RecursiveConcreteDataDecl = RecursiveConcreteDataDecl (Covenant.Internal.Type.DataDeclaration AbstractTy)
  deriving Eq via (Covenant.Internal.Type.DataDeclaration AbstractTy)
  deriving stock Show

{- Non-polymorphic recursive types, i.e. things like:

   data IntList = Empty | ConsInt Int IntList

   The general idea is that we construct a base case constructor (Nil or Empty) and then
   construct a recursive constructor. We can expand this later (e.g. to have multiple recursive constructors, or a polymorphic variant)
   but this will be enough to handle initial testing w/ the base functor / BBF stuff (and we have to ensure we have things like this to test that)
-}
genArbitraryRecursive :: DataGenM RecursiveConcreteDataDecl
genArbitraryRecursive = RecursiveConcreteDataDecl <$> do
  tyNm <- freshTyName
  baseCtor <- coerce <$> genConcreteConstructor -- any concrete ctor - or any ctor that doesn't contain the parent type - will suffice as a base case
  numRecCtors <- GT.liftGen $ chooseInt (1,5)
  recCtor  <- GT.vectorOf numRecCtors $ genRecCtor tyNm
  returnDecl $  Covenant.Internal.Type.DataDeclaration tyNm count0 (Vector.fromList (baseCtor:recCtor))
 where
   genRecCtor :: Covenant.Internal.Type.TyName -> DataGenM (Covenant.Internal.Type.Constructor AbstractTy)
   genRecCtor tyNm = do
     ctorNm <- freshConstructorName
     let thisType = Covenant.Internal.Type.Datatype tyNm Vector.empty
     numNonRecArgs <- GT.liftGen $ chooseInt (1,5) -- need at least one to avoid "bad" types
     args <- coerce $ GT.vectorOf numNonRecArgs nestedCtorArg
     pure $ Covenant.Internal.Type.Constructor ctorNm (Vector.fromList (thisType:args))


{- Single variable polymorphic datatypes. That is, things like:

   data Foo a = Nope | Yup a

   data Snowk a = Start | More (Snowk a) a
-}
newtype Polymorphic1 = Polymorphic1 (Covenant.Internal.Type.DataDeclaration AbstractTy)
  deriving Eq via (Covenant.Internal.Type.DataDeclaration AbstractTy)
  deriving stock Show

{- Generator for single variable polymorphic datatypes, no polymorphic *functions* as arguments to the datatypes yet (that requires something different).

   When run multiple times in the monadic context, will reuse single variable declarations that are "in scope" (i.e. have already been generated and are
   known in the DataGenM state).

   TODO: Rework this to generate declarations with an arbitrary number of tyvar arguments. Doing so would be fairly simple (but isn't needed ATM)
-}
genPolymorphic1Decl :: DataGenM Polymorphic1
genPolymorphic1Decl = Polymorphic1 <$> do
  tyNm <- freshTyName
  logArity tyNm count1
  numCtors <- GT.liftGen $ chooseInt (1,5)
  polyCtors <- concat <$> GT.vectorOf numCtors (genPolyCtor tyNm)
  let result = Covenant.Internal.Type.DataDeclaration tyNm count1 (Vector.fromList polyCtors)
  returnDecl result
 where
   -- We return a single constructor UNLESS we're generating a recursive type, in which case we have to return 2 to ensure a base case
   genPolyCtor :: Covenant.Internal.Type.TyName -> DataGenM [Covenant.Internal.Type.Constructor AbstractTy]
   genPolyCtor thisTy = do
     ctorNm <- freshConstructorName
     numArgs <- GT.liftGen $ chooseInt (1,5)
     argsRaw <- GT.vectorOf numArgs polyArg
     let recCase = Covenant.Internal.Type.Datatype thisTy (Vector.singleton (Covenant.Internal.Type.Abstraction (BoundAt Z ix0)))
     if recCase `elem` argsRaw
       then do
         baseCtorNm <- freshConstructorName
         let baseCtor = Covenant.Internal.Type.Constructor baseCtorNm mempty
             recCtor = Covenant.Internal.Type.Constructor ctorNm (Vector.fromList argsRaw)
         pure [baseCtor,recCtor]
       else pure [Covenant.Internal.Type.Constructor ctorNm (Vector.fromList argsRaw)]
    where
     arityOne :: Count "tyvar" -> Bool
     arityOne c = c == count1

     polyArg :: DataGenM (Covenant.Internal.Type.ValT AbstractTy)
     polyArg = do
       -- first we choose a type with an arity >=1. We have to have at least one of those because we've added the parent type to the arity map
       availableArity1 <- gets (fmap fst . (filter (arityOne . snd) . M.toList) . view dgArities)
       someTyCon1 <- GT.elements availableArity1
       GT.oneof [pure $ Covenant.Internal.Type.Abstraction (BoundAt Z ix0),
                 pure $ Covenant.Internal.Type.Datatype someTyCon1 (Vector.singleton (Covenant.Internal.Type.Abstraction (BoundAt Z ix0))),
                 GT.liftGen (coerce <$> arbitrary @Concrete)]

{-
   Misc Helpers and the Arbitrary instances
-}

{- This saves us from having to write *another* newtype for each set of a "flavor" of datatypes and doesn't have any real drawbacks -}
data DataDeclFlavor
  = ConcreteDecl
  | ConcreteNestedDecl
  | SimpleRecursive
  | Poly1

-- can't be a Set b/c don't have the Ord instances, don't see what benefit a Vector gives since we'll almost always consume this
-- via folding anyway
newtype DataDeclSet (flavor :: DataDeclFlavor) = DataDeclSet [Covenant.Internal.Type.DataDeclaration AbstractTy]

{- NOTE @Koz: This is supposed to be a "generic" shrinker for datatypes. It *should* return two paths:
                - One that shrinks the number of constructors
                - One that shrinks the constructors

              This is why I had to add handling for `datatype` into `Concrete`. To use `shrink` recursively
              on the structural components, we need some kind of instance to pivot off of. Since we want to avoid
              writing a generic Arbitrary instance for Constructor or DataDeclaration, this seems like the
              simplest solution.
-}
shrinkDataDecl ::  Covenant.Internal.Type.DataDeclaration AbstractTy -> [Covenant.Internal.Type.DataDeclaration AbstractTy]
shrinkDataDecl (Covenant.Internal.Type.DataDeclaration nm cnt ctors)
  | Vector.null ctors = []
  | otherwise =
    let concreteShrink :: Vector (Covenant.Internal.Type.ValT AbstractTy) -> [Vector (Covenant.Internal.Type.ValT AbstractTy)]
        concreteShrink = coerce . shrink . fmap Concrete

        concreteShrink' :: Vector (Covenant.Internal.Type.ValT AbstractTy) -> [Vector (Covenant.Internal.Type.ValT AbstractTy)]
        concreteShrink' xs = coerce $ fmap (Vector.fromList . shrink . Concrete) (Vector.toList xs)

        ctorShrink :: Covenant.Internal.Type.Constructor AbstractTy -> [Covenant.Internal.Type.Constructor AbstractTy]
        ctorShrink (Covenant.Internal.Type.Constructor ctorNm args) = Covenant.Internal.Type.Constructor ctorNm <$> concreteShrink args

        ctorArgShrink :: Covenant.Internal.Type.Constructor AbstractTy -> [Covenant.Internal.Type.Constructor AbstractTy]
        ctorArgShrink (Covenant.Internal.Type.Constructor ctorNm args) = Covenant.Internal.Type.Constructor ctorNm <$> concreteShrink' args

        withShrunkenCtors = ((Covenant.Internal.Type.DataDeclaration nm cnt . Vector.fromList) . ctorShrink <$> Vector.toList ctors)

        withShrunkenCtorArgs = Covenant.Internal.Type.DataDeclaration nm cnt . Vector.fromList . ctorArgShrink <$> Vector.toList ctors
    in withShrunkenCtors <|> withShrunkenCtorArgs


-- REVIEW: I dunno how liftShrink works under the hood so this might be redundant?
shrinkDataDecls :: [Covenant.Internal.Type.DataDeclaration AbstractTy] -> [[Covenant.Internal.Type.DataDeclaration AbstractTy]]
shrinkDataDecls decls = liftShrink shrinkDataDecl decls  <|> (shrinkDataDecl <$> decls)

genDataN :: forall (a :: Type). Int -> DataGenM a -> Gen [a]
genDataN n act = runDataGenM (GT.vectorOf n act)

genDataList :: forall (a :: Type). DataGenM a -> Gen [a]
genDataList = runDataGenM . GT.listOf

instance Arbitrary (DataDeclSet 'ConcreteDecl) where
  arbitrary = coerce $ genDataList genConcreteDataDecl

  shrink = coerce . shrinkDataDecls . coerce

instance Arbitrary (DataDeclSet 'ConcreteNestedDecl) where
  arbitrary = coerce $ genDataList genNestedConcrete

  shrink = coerce . shrinkDataDecls . coerce

instance Arbitrary (DataDeclSet 'SimpleRecursive) where
  arbitrary = coerce $ genDataList genArbitraryRecursive

  shrink = coerce . shrinkDataDecls . coerce

instance Arbitrary (DataDeclSet 'Poly1) where
  arbitrary = coerce $ genDataList genPolymorphic1Decl

  shrink = coerce . shrinkDataDecls . coerce

{- Misc Repl testing utilities. I'd like to leave these here because I can't exactly have a test suite
   to validate test generators, so inspection may be necessary if something goes wrong.
-}

-- Prettifies and prints n generated datatypes using the supplied generator.
genPrettyDataN ::  Int -> DataGenM (Covenant.Internal.Type.DataDeclaration AbstractTy) -> IO ()
genPrettyDataN n dg = goPrint =<< generate (genDataN n dg)
  where
    goPrint :: [Covenant.Internal.Type.DataDeclaration AbstractTy] -> IO ()
    goPrint [] = pure ()
    goPrint (x:xs) = do
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
