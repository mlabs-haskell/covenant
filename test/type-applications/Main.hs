{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Control.Applicative ((<|>))
import Control.Exception.Base (throwIO)
import Control.Monad (guard, (<=<))
import Covenant.Data (DatatypeInfo, mkDatatypeInfo)
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index
  ( Index,
    ix0,
    ix1,
    ix2,
  )
import Covenant.Test (Concrete (Concrete), testDatatypes)
import Covenant.Type
  ( AbstractTy (BoundAt),
    BuiltinFlatT (BoolT, IntegerT, UnitT),
    CompT (Comp0, Comp1, Comp2, Comp3),
    DataDeclaration,
    Renamed (Rigid, Unifiable, Wildcard),
    TyName,
    TypeAppError (DoesNotUnify, ExcessArgs, InsufficientArgs),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    checkApp,
    integerT,
    prettyStr,
    renameCompT,
    renameDataDecl,
    renameValT,
    runRenameM,
    tyvar,
    pattern ReturnT,
    pattern (:--:>),
  )
import Data.Coerce (coerce)
import Data.Foldable (Foldable (foldl'))
import Data.Functor.Identity (Identity (Identity))
import Data.Kind (Type)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Vector qualified as Vector
import Optics.Core (review, view)
import Test.QuickCheck
  ( Gen,
    Property,
    arbitrary,
    counterexample,
    discard,
    elements,
    forAllShrink,
    getSize,
    liftShrink,
    oneof,
    shrink,
    suchThat,
    vectorOf,
    (===),
  )
import Test.Tasty (TestTree, adjustOption, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "Type application" $
    [ testProperty "Too many arguments to id" propTooManyArgs,
      testCase "id on no arguments" unitInsufficientArgs,
      testGroup
        "Substitution"
        [ testProperty "id applied to concrete" propIdConcrete,
          testProperty "two-arg const to same concretes" propConst2Same,
          testProperty "two-arg const to different concretes" propConst2Different
        ],
      testGroup
        "Unification"
        [ testProperty "concrete expected, concrete actual" propUnifyConcrete,
          testProperty "rigid expected, concrete actual" propUnifyRigidConcrete,
          testProperty "wildcard expected, concrete actual" propUnifyWildcardConcrete,
          testProperty "wildcard expected, unifiable actual" propUnifyWildcardUnifiable,
          testProperty "concrete expected, rigid actual" propUnifyConcreteRigid,
          testProperty "unifiable expected, rigid actual" propUnifyUnifiableRigid,
          testProperty "rigid expected, rigid actual" propUnifyRigid,
          testProperty "wildcard expected, rigid actual" propUnifyWildcardRigid
        ],
      testGroup
        "Datatypes"
        [ testMonotypeBB,
          testEitherConcrete,
          polymorphicApplicationM,
          polymorphicApplicationE,
          polymorphicApplicationP,
          unifyMaybe,
          renameRigid
        ]
    ]
  where
    -- Note (Koz, 26/02/2025): By default, QuickCheck runs only 100 tests per
    -- property, which is far too few. Using the method below, we can ensure that
    -- we run a decent number of tests, while also permitting more than this to
    -- be set via the CLI if we want.
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 10_000

-- Units and properties

-- Try to apply more than one argument to `forall a . a -> !a`.
-- Result should indicate excess arguments.
propTooManyArgs :: Property
propTooManyArgs = forAllShrink gen shr $ \excessArgs ->
  withRenamedComp idT $ \renamedIdT ->
    withRenamedVals excessArgs $ \renamedExcessArgs ->
      case renamedExcessArgs of
        [] -> discard -- should be impossible
        _ : extraArgs ->
          let expected = Left . ExcessArgs renamedIdT . Vector.fromList . fmap Just $ extraArgs
              actual = checkApp M.empty renamedIdT (fmap Just renamedExcessArgs)
           in expected === actual
  where
    -- Note (Koz, 14/04/2025): The default size of 100 makes it rather painful
    -- to generate excess arguments, as the generator used for concrete types
    -- is recursive. Furthermore, we need to ensure the list has at least two
    -- elements, which forces too many restarts. Thus, we roll our own.
    gen :: Gen [ValT AbstractTy]
    gen = do
      size <- getSize
      lenIncrease <- elements [0, 1 .. size `quot` 4]
      Concrete firstTy <- arbitrary
      Concrete secondTy <- arbitrary
      ([firstTy, secondTy] <>) <$> vectorOf lenIncrease (coerce @Concrete <$> arbitrary)
    shr :: [ValT AbstractTy] -> [[ValT AbstractTy]]
    shr = \case
      [] -> []
      [_] -> []
      [_, _] -> []
      xs -> liftShrink (coerce . shrink . Concrete) xs

-- Try to apply `forall a . a -> !a` to zero arguments. Result should indicate
-- insufficient arguments.
unitInsufficientArgs :: IO ()
unitInsufficientArgs = do
  renamedIdT <- failLeft . runRenameM . renameCompT $ idT
  let expected = Left $ InsufficientArgs 0 renamedIdT []
  let actual = checkApp M.empty renamedIdT []
  assertEqual "" expected actual

-- Try to apply `forall a . a -> !a` to a random concrete type. Result should be
-- that type.
propIdConcrete :: Property
propIdConcrete = forAllShrink arbitrary shrink $ \(Concrete t) ->
  withRenamedComp idT $ \renamedIdT ->
    withRenamedVals (Identity t) $ \(Identity t') ->
      let expected = Right t'
          actual = checkApp M.empty renamedIdT [Just t']
       in expected === actual

-- Try to apply `forall a b . a -> b -> !a` to two identical concrete types.
-- Result should be that type.
propConst2Same :: Property
propConst2Same = forAllShrink arbitrary shrink $ \(Concrete t) ->
  withRenamedComp const2T $ \renamedConst2T ->
    withRenamedVals (Identity t) $ \(Identity t') ->
      let expected = Right t'
          actual = checkApp M.empty renamedConst2T [Just t', Just t']
       in expected === actual

-- Try to apply `forall a b . a -> b -> !a` to two random _different_ concrete
-- types. Result should be the choice for `a`.
propConst2Different :: Property
propConst2Different = forAllShrink arbitrary shrink $ \(Concrete t1, Concrete t2) ->
  if t1 == t2
    then discard
    else withRenamedComp const2T $ \renamedConst2T ->
      withRenamedVals (Identity t1) $ \(Identity t1') ->
        withRenamedVals (Identity t2) $ \(Identity t2') ->
          let expected = Right t1'
              actual = checkApp M.empty renamedConst2T [Just t1', Just t2']
           in expected === actual

-- Randomly pick a concrete type `A`, then pick a type `b` which is either `A`
-- or a type different from `A` (50% of the time each way). Then try to apply `A
-- -> !Integer` to `b`. Result should unify be `Integer` if `b ~ A`, and a
-- unification error otherwise.
propUnifyConcrete :: Property
propUnifyConcrete = forAllShrink gen shr $ \(tA, mtB) ->
  withRenamedComp (Comp0 $ tA :--:> ReturnT integerT) $ \f ->
    withRenamedVals (Identity tA) $ \(Identity tA') ->
      case mtB of
        Nothing ->
          let expected = Right integerT
              actual = checkApp M.empty f [Just tA']
           in expected === actual
        Just tB ->
          if tA == tB
            then discard
            else withRenamedVals (Identity tB) $ \(Identity arg) ->
              let expected = Left . DoesNotUnify tA' $ arg
                  actual = checkApp M.empty f [Just arg]
               in expected === actual
  where
    -- This ensures that our cases occur with equal frequency.
    gen :: Gen (ValT AbstractTy, Maybe (ValT AbstractTy))
    gen = do
      Concrete x <- arbitrary
      (x,) <$> oneof [pure Nothing, Just . coerce <$> arbitrary @Concrete]
    -- We don't want to 'shrink out of case'; if we have a `Just`, we want to
    -- keep it a `Just`.
    shr :: (ValT AbstractTy, Maybe (ValT AbstractTy)) -> [(ValT AbstractTy, Maybe (ValT AbstractTy))]
    shr (x, my) = do
      Concrete x' <- shrink (Concrete x)
      case my of
        Nothing -> pure (x', Nothing)
        Just y -> do
          Concrete y' <- shrink (Concrete y)
          pure (x', my) <|> pure (x, Just y')

-- Randomly pick a rigid type A and concrete type B, then try to apply `A ->
-- !Integer` to `b`. Result should fail to unify.
propUnifyRigidConcrete :: Property
propUnifyRigidConcrete = forAllShrink arbitrary shrink $ \(Concrete t, scope, ix) ->
  withRenamedComp (Comp0 $ tyvar (S scope) ix :--:> ReturnT integerT) $ \f ->
    withRenamedVals (Identity t) $ \(Identity t') ->
      -- This is a little confusing, as we would expect that the true level will
      -- be based on `S scope`, since that's what's in the computation type.
      -- However, we actually have to reduce it by 1, as we have a 'scope
      -- stepdown' for `f` even though we bind no variables.
      let trueLevel = negate . review asInt $ scope
          expected = Left . DoesNotUnify (Abstraction . Rigid trueLevel $ ix) $ t'
          actual = checkApp M.empty f [Just t']
       in expected === actual

-- Randomly pick a concrete type A, then try to apply `(forall a . a ->
-- !Integer) -> !Integer` to `(A -> !Integer)`. Result should fail to unify.
propUnifyWildcardConcrete :: Property
propUnifyWildcardConcrete = forAllShrink arbitrary shrink $ \(Concrete t) ->
  let thunk = ThunkT . Comp1 $ tyvar Z ix0 :--:> ReturnT integerT
   in withRenamedComp (Comp0 $ thunk :--:> ReturnT integerT) $ \f ->
        let argT = ThunkT . Comp0 $ t :--:> ReturnT integerT
         in withRenamedVals (Identity argT) $ \(Identity argT') ->
              let lhs = ThunkT . Comp1 $ Abstraction (Wildcard 1 2 ix0) :--:> ReturnT integerT
                  expected = Left . DoesNotUnify lhs $ argT'
                  actual = checkApp M.empty f [Just argT']
               in expected === actual

-- Randomly generate a concrete type A, then try to apply
-- `(forall a . a -> !A) -> !A` to `forall a . (a -> !A)`. Result should unify
-- to `A`.
propUnifyWildcardUnifiable :: Property
propUnifyWildcardUnifiable = forAllShrink arbitrary shrink $ \(Concrete t) ->
  withRenamedComp (Comp0 $ ThunkT (Comp1 $ tyvar Z ix0 :--:> ReturnT t) :--:> ReturnT t) $ \f ->
    withRenamedVals (Identity t) $ \(Identity t') ->
      withRenamedVals (Identity . ThunkT . Comp1 $ tyvar Z ix0 :--:> ReturnT t) $ \(Identity arg) ->
        let expected = Right t'
            actual = checkApp M.empty f [Just arg]
         in expected === actual

-- Randomly generate a concrete type A, and a rigid type B, then try to apply `A
-- -> !Integer` to `B`. Result should fail to unify.
propUnifyConcreteRigid :: Property
propUnifyConcreteRigid = forAllShrink arbitrary shrink $ \(Concrete aT, scope, index) ->
  withRenamedComp (Comp0 $ aT :--:> ReturnT integerT) $ \f ->
    withRenamedVals (Identity $ tyvar scope index) $ \(Identity arg) ->
      withRenamedVals (Identity aT) $ \(Identity aT') ->
        let level = negate . review asInt $ scope
            expected = Left . DoesNotUnify aT' . Abstraction . Rigid level $ index
            actual = checkApp M.empty f [Just arg]
         in expected === actual

-- Randomly generate a rigid type A, then try to apply `forall a . a -> !a` to
-- `A`. Result should unify to `A`.
propUnifyUnifiableRigid :: Property
propUnifyUnifiableRigid = forAllShrink arbitrary shrink $ \(scope, index) ->
  withRenamedComp idT $ \f ->
    withRenamedVals (Identity $ tyvar scope index) $ \(Identity arg) ->
      let expected = Right arg
          actual = checkApp M.empty f [Just arg]
       in expected === actual

-- Randomly generate a scope S and an index I, then another scope S' and another
-- index I', that may or may not be different to S and/or I respectively. Let
-- `T` be the rigid type that results from `S` and `I`, and `U` be the rigid
-- type that results from `S'` and `I'`. Attempt to unify `T -> !Integer` with
-- `U`. This should unify to `Integer` if, and only if, `T == U`; otherwise, it
-- should fail to unify.
propUnifyRigid :: Property
propUnifyRigid = forAllShrink gen shr $ \testData ->
  withTestData testData $ \(f, arg, expected) ->
    let actual = checkApp M.empty f [Just arg]
     in expected === actual
  where
    gen :: Gen (DeBruijn, Index "tyvar", Maybe (Either DeBruijn (Index "tyvar")))
    gen = do
      db <- arbitrary
      index <- arbitrary
      (db,index,)
        <$> oneof
          [ pure Nothing,
            Just . Left <$> suchThat arbitrary (db /=),
            Just . Right <$> suchThat arbitrary (index /=)
          ]
    shr ::
      (DeBruijn, Index "tyvar", Maybe (Either DeBruijn (Index "tyvar"))) ->
      [(DeBruijn, Index "tyvar", Maybe (Either DeBruijn (Index "tyvar")))]
    shr (db, index, mrest) = do
      db' <- shrink db
      index' <- shrink index
      case mrest of
        Nothing -> pure (db', index, Nothing) <|> pure (db, index', Nothing)
        Just (Left db2) -> do
          db2' <- shrink db2
          (db', index, Just (Left db2)) <$ guard (db' /= db2)
            <|> pure (db, index', Just (Left db2))
            <|> (db, index, Just (Left db2')) <$ guard (db /= db2')
        Just (Right index2) -> do
          index2' <- shrink index2
          pure (db', index, Just (Right index2))
            <|> (db, index', Just (Right index2)) <$ guard (index' /= index2)
            <|> (db, index, Just (Right index2')) <$ guard (index /= index2')
    withTestData ::
      (DeBruijn, Index "tyvar", Maybe (Either DeBruijn (Index "tyvar"))) ->
      ((CompT Renamed, ValT Renamed, Either TypeAppError (ValT Renamed)) -> Property) ->
      Property
    withTestData (db, index, mrest) f =
      withRenamedComp (Comp0 $ tyvar (S db) index :--:> ReturnT integerT) $ \fun ->
        case mrest of
          Nothing -> withRenamedVals (Identity . tyvar db $ index) $ \(Identity arg) ->
            f (fun, arg, Right integerT)
          Just rest ->
            let level = negate . review asInt $ db
                lhs = Abstraction . Rigid level $ index
             in case rest of
                  Left db2 -> withRenamedVals (Identity . tyvar db2 $ index) $ \(Identity arg) ->
                    f (fun, arg, Left . DoesNotUnify lhs $ arg)
                  Right index2 -> withRenamedVals (Identity . tyvar db $ index2) $ \(Identity arg) ->
                    f (fun, arg, Left . DoesNotUnify lhs $ arg)

-- Randomly pick a rigid type A, then try to apply `(forall a . a -> !Integer)
-- -> !Integer` to `(A -> !Integer)`. Result should fail to unify.
propUnifyWildcardRigid :: Property
propUnifyWildcardRigid = forAllShrink arbitrary shrink $ \(scope, index) ->
  let thunk = ThunkT . Comp1 $ tyvar Z ix0 :--:> ReturnT integerT
   in withRenamedComp (Comp0 $ thunk :--:> ReturnT integerT) $ \f ->
        let argT = ThunkT . Comp0 $ tyvar (S scope) index :--:> ReturnT integerT
         in withRenamedVals (Identity argT) $ \(Identity argT') ->
              let lhs = ThunkT . Comp1 $ Abstraction (Wildcard 1 2 ix0) :--:> ReturnT integerT
                  expected = Left . DoesNotUnify lhs $ argT'
                  actual = checkApp M.empty f [Just argT']
               in expected === actual

-- Simple datatype unification unit test. Checks whether `data Unit = Unit` has the expected BB form
testMonotypeBB :: TestTree
testMonotypeBB = testCase "unitBbf" $ do
  let expected = Comp1 $ Abstraction (BoundAt Z ix0) :--:> ReturnT (Abstraction $ BoundAt Z ix0)
  expected' <- failLeft . runRenameM . renameCompT $ expected
  actual <- case fromJust . (view #bbForm <=< M.lookup "Unit") $ tyAppTestDatatypes of
    ThunkT inner -> either (throwIO . userError . show) pure . runRenameM $ renameCompT inner
    _ -> assertFailure "BB form not a thunk!"
  assertEqual "unit bbf" expected' actual

-- Tries to apply some concrete types to `defaultLeft`, checks that the return type is
-- correct after unification (via checkApp)
testEitherConcrete :: TestTree
testEitherConcrete = testCase "testEitherConcrete" $ do
  -- a == unit
  -- b == bool
  -- c == integer
  let arg1 = BuiltinFlat IntegerT
      arg2 = ThunkT (Comp0 $ BuiltinFlat BoolT :--:> ReturnT (BuiltinFlat IntegerT))
      arg3 = Datatype "Either" . Vector.fromList $ [BuiltinFlat UnitT, BuiltinFlat BoolT]

      expected = BuiltinFlat IntegerT
  defaultLeftRenamed <- failLeft . runRenameM . renameCompT $ defaultLeft
  actual <-
    either (assertFailure . show) pure $
      checkApp
        tyAppTestDatatypes
        defaultLeftRenamed
        (pure <$> [arg1, arg2, arg3])
  assertEqual "testEitherConcrete" expected actual

-- Tries to apply arguments containing a mixture of concrete and abstract types to the BB form for maybe,
-- then checks whether the application types as the (concrete) return type.
-- note: The order of args is wrong for a Plutus "Maybe" (but that doesn't matter). BB form is:
-- forall a r. r -> (a -> r) -> r
-- (Plutus defines 'Maybe' incorrectly, i.e., with the 'Just' ctor first)
polymorphicApplicationM :: TestTree
polymorphicApplicationM = testCase "polyAppMaybe" $ do
  let testFn =
        Comp1 $
          ( ThunkT . Comp1 $
              tyvar Z ix0
                :--:> ThunkT (Comp0 (tyvar (S (S Z)) ix0 :--:> ReturnT (tyvar (S Z) ix0)))
                :--:> ReturnT (tyvar Z ix0)
          )
            :--:> ReturnT (BuiltinFlat IntegerT)
      testArg =
        ThunkT . Comp1 $
          tyvar Z ix0
            :--:> ThunkT (Comp0 (BuiltinFlat BoolT :--:> ReturnT (tyvar (S Z) ix0)))
            :--:> ReturnT (tyvar Z ix0)
  fnRenamed <- failLeft . runRenameM . renameCompT $ testFn
  argRenamed <- failLeft . runRenameM . renameValT $ testArg
  result <-
    either (assertFailure . show) pure $
      checkApp tyAppTestDatatypes fnRenamed [Just argRenamed]
  assertEqual "polyAppMaybe" result (BuiltinFlat IntegerT)

-- Applies a mixture of polymorphic and concrete arguments to `defaultLeft` and checks that the  return
-- type is what we expected after unification
polymorphicApplicationE :: TestTree
polymorphicApplicationE = testCase "polyAppEither" $ do
  -- a = a' (arbitrary unifiable)
  -- b = Bool
  -- c = Integer
  let arg1 = Abstraction $ Unifiable ix0
      arg2 = ThunkT (Comp0 $ BuiltinFlat BoolT :--:> ReturnT (BuiltinFlat IntegerT))
      arg3 = Datatype "Either" . Vector.fromList $ [arg1, BuiltinFlat BoolT]
  fnRenamed <- failLeft . runRenameM . renameCompT $ defaultLeft
  actual <-
    either (assertFailure . show) pure $
      checkApp tyAppTestDatatypes fnRenamed (pure <$> [arg1, arg2, arg3])
  assertEqual "polyAppEither" actual (BuiltinFlat IntegerT)

-- Applies a mixture of polymorphic and concrete arguments to `defaultPair` and checks that the return type
-- is what we expected after unification
polymorphicApplicationP :: TestTree
polymorphicApplicationP = testCase "polyAppPair" $ do
  -- a = a' (arbitrary unifiable)
  -- b = Bool
  -- c = Integer
  let arg1 = Abstraction $ Unifiable ix0
      arg2 = BuiltinFlat BoolT
      arg3 = ThunkT $ Comp0 $ Abstraction (Rigid 1 ix0) :--:> BuiltinFlat BoolT :--:> ReturnT (BuiltinFlat IntegerT)
      arg4 = Datatype "Pair" (Vector.fromList [arg1, BuiltinFlat BoolT])
  fnRenamed <- failLeft . runRenameM . renameCompT $ defaultPair
  actual <-
    either (assertFailure . show) pure $
      checkApp tyAppTestDatatypes fnRenamed (pure <$> [arg1, arg2, arg3, arg4])
  assertEqual "polyAppPair" actual (BuiltinFlat IntegerT)

-- Checks whether `forall a. Maybe a -> Integer` unifies properly with `Maybe Bool -> Integer`
unifyMaybe :: TestTree
unifyMaybe = testCase "unifyMaybe" $ do
  let testFn =
        Comp1 $
          Datatype "Maybe" (Vector.fromList [tyvar Z ix0])
            :--:> ReturnT (BuiltinFlat IntegerT)
      testArg = Datatype "Maybe" (Vector.fromList [BuiltinFlat BoolT])
  fnRenamed <- failLeft . runRenameM . renameCompT $ testFn
  result <-
    either (assertFailure . catchInsufficientArgs) pure $
      checkApp tyAppTestDatatypes fnRenamed [Just testArg]
  assertEqual "debugTest2" result (BuiltinFlat IntegerT)
  where
    catchInsufficientArgs :: TypeAppError -> String
    catchInsufficientArgs = \case
      InsufficientArgs _ fn _ -> prettyStr fn
      other -> show other

-- Tests whether renaming works as "expected" with free type variables.
-- NOTE/FIXME/REVIEW: This test *probably* shouldn't pass, since it lets a free type variable through
--                    by converting it into a rigid where it should fail.
renameRigid :: TestTree
renameRigid = testCase "debugTest3" $ do
  let testFn =
        Comp1 $
          Datatype "Maybe" (Vector.fromList [tyvar (S Z) ix0])
            :--:> ReturnT (BuiltinFlat IntegerT)
  fnRenamed <- failLeft . runRenameM . renameCompT $ testFn
  let expected =
        Comp1 $
          Datatype "Maybe" (Vector.fromList [Abstraction $ Rigid 0 ix0])
            :--:> ReturnT (BuiltinFlat IntegerT)
  assertEqual "debugTest3" expected fnRenamed

-- Helpers

-- `forall a. a -> !a`
idT :: CompT AbstractTy
idT = Comp1 $ tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)

-- `forall a b . a -> b -> !a
const2T :: CompT AbstractTy
const2T = Comp2 $ tyvar Z ix0 :--:> tyvar Z ix1 :--:> ReturnT (tyvar Z ix0)

-- forall a b c. c -> (b -> !c) -> Either a b -> !c
-- ...I hope
defaultLeft :: CompT AbstractTy
defaultLeft =
  Comp3 $
    tyvar Z ix2
      :--:> ThunkT (Comp0 $ tyvar (S Z) ix1 :--:> ReturnT (tyvar (S Z) ix2))
      :--:> Datatype "Either" (Vector.fromList [tyvar Z ix0, tyvar Z ix1])
      :--:> ReturnT (tyvar Z ix2)

-- forall a b c. a -> b -> (a -> b -> !c) -> Pair a b -> c
defaultPair :: CompT AbstractTy
defaultPair =
  Comp3 $
    tyvar Z ix0
      :--:> tyvar Z ix1
      :--:> ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> tyvar (S Z) ix1 :--:> ReturnT (tyvar (S Z) ix2))
      :--:> Datatype "Pair" (Vector.fromList [tyvar Z ix0, tyvar Z ix1])
      :--:> ReturnT (tyvar Z ix2)

failLeft ::
  forall (a :: Type) (b :: Type).
  (Show a) =>
  Either a b ->
  IO b
failLeft = either (assertFailure . show) pure

withRenamedComp ::
  CompT AbstractTy ->
  (CompT Renamed -> Property) ->
  Property
withRenamedComp t f = case runRenameM . renameCompT $ t of
  Left err -> counterexample (show err) False
  Right t' -> f t'

withRenamedVals ::
  forall (t :: Type -> Type).
  (Traversable t) =>
  t (ValT AbstractTy) ->
  (t (ValT Renamed) -> Property) ->
  Property
withRenamedVals vals f = case runRenameM . traverse renameValT $ vals of
  Left err -> counterexample (show err) False
  Right vals' -> f vals'

_withRenamedDatadecl ::
  DataDeclaration AbstractTy ->
  (DataDeclaration Renamed -> Property) ->
  Property
_withRenamedDatadecl decl f = case runRenameM . renameDataDecl $ decl of
  Left err -> counterexample (show err) False
  Right decl' -> f decl'

tyAppTestDatatypes :: M.Map TyName (DatatypeInfo AbstractTy)
tyAppTestDatatypes = foldl' (\acc decl -> M.insert (view #datatypeName decl) (mkDatatypeInfo decl) acc) M.empty testDatatypes
