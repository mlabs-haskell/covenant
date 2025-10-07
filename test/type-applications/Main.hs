{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Control.Applicative ((<|>))
import Covenant.ASG
  ( TypeAppError
      ( DoesNotUnify,
        ExcessArgs,
        InsufficientArgs
      ),
  )
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index
  ( Index,
    intIndex,
    ix0,
    ix1,
    ix2,
  )
import Covenant.Test
  ( Concrete (Concrete),
    checkApp,
    failLeft,
    renameCompT,
    renameValT,
    runRenameM,
    tyAppTestDatatypes,
  )
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT (BoolT, IntegerT, UnitT),
    CompT (Comp0, Comp1, Comp2, Comp3),
    Renamed (Rigid, Unifiable, Wildcard),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    integerT,
    tyvar,
    pattern ReturnT,
    pattern (:--:>),
  )
import Covenant.Util (prettyStr)
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity (Identity))
import Data.Kind (Type)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Word (Word32)
import Optics.Core (preview, review)
import Test.QuickCheck
  ( Gen,
    Property,
    arbitrary,
    chooseInt,
    counterexample,
    discard,
    elements,
    forAll,
    forAllShrink,
    getNonZero,
    getSize,
    liftArbitrary,
    liftShrink,
    oneof,
    shrink,
    suchThat,
    suchThatMap,
    vectorOf,
    (===),
  )
import Test.Tasty (TestTree, adjustOption, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Test.Tasty.QuickCheck (QuickCheckMaxSize, QuickCheckTests, testProperty)

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
          adjustOption smallerTests . testProperty "rigid expected, concrete actual" $ propUnifyRigidConcrete,
          testProperty "wildcard expected, concrete actual" propUnifyWildcardConcrete,
          testProperty "wildcard expected, unifiable actual" propUnifyWildcardUnifiable,
          adjustOption smallerTests . testProperty "concrete expected, rigid actual" $ propUnifyConcreteRigid,
          adjustOption smallerTests . testProperty "unifiable expected, rigid actual" $ propUnifyUnifiableRigid,
          testProperty "rigid expected, rigid actual" propUnifyRigid,
          adjustOption smallerTests . testProperty "wildcard expected, rigid actual" $ propUnifyWildcardRigid,
          testProperty "thunk with unifiable result" propThunkWithUnifiableResult
        ],
      testGroup
        "Datatypes"
        [ testEitherConcrete,
          polymorphicApplicationM,
          polymorphicApplicationE,
          polymorphicApplicationP,
          unifyMaybe,
          testCase "nested datatypes" unitNestedDatatypes,
          testProperty "thunk with datatype argument" propThunkWithDatatype,
          testProperty "concrete thunk with datatype argument" propConcreteThunkWithDatatype,
          testProperty "thunk with unifiable and datatype argument" propThunkUnifiableWithDatatype,
          testProperty "thunk with unifiable datatype" propThunkUnifiableDatatype
        ]
    ]
  where
    -- Note (Koz, 26/02/2025): By default, QuickCheck runs only 100 tests per
    -- property, which is far too few. Using the method below, we can ensure that
    -- we run a decent number of tests, while also permitting more than this to
    -- be set via the CLI if we want.
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 10_000

    -- fewerTests :: QuickCheckTests -> QuickCheckTests
    -- fewerTests = const 100

    smallerTests :: QuickCheckMaxSize -> QuickCheckMaxSize
    smallerTests = (`div` 4)

-- Units and properties

-- Try to apply more than one argument to `forall a . a -> !a`.
-- Result should indicate excess arguments.
propTooManyArgs :: Property
propTooManyArgs = forAllShrink gen shr $ \excessArgs ->
  withRenamedComp mempty idT $ \renamedIdT ->
    withRenamedVals mempty excessArgs $ \renamedExcessArgs ->
      case renamedExcessArgs of
        [] -> discard -- should be impossible
        arg : extraArgs ->
          let expected = Left . ExcessArgs renamedIdT . Vector.fromList . fmap Just $ (arg:extraArgs)
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
  renamedIdT <- failLeft . runRenameM mempty . renameCompT $ idT
  let expected = Left $ InsufficientArgs 0 renamedIdT []
  let actual = checkApp M.empty renamedIdT []
  assertEqual "" expected actual

-- Try to apply `forall a . a -> !a` to a random concrete type. Result should be
-- that type.
propIdConcrete :: Property
propIdConcrete = forAllShrink arbitrary shrink $ \(Concrete t) ->
  withRenamedComp mempty idT $ \renamedIdT ->
    withRenamedVals mempty (Identity t) $ \(Identity t') ->
      let expected = Right t'
          actual = checkApp M.empty renamedIdT [Just t']
       in expected === actual

-- Try to apply `forall a b . a -> b -> !a` to two identical concrete types.
-- Result should be that type.
propConst2Same :: Property
propConst2Same = forAllShrink arbitrary shrink $ \(Concrete t) ->
  withRenamedComp mempty const2T $ \renamedConst2T ->
    withRenamedVals mempty (Identity t) $ \(Identity t') ->
      let expected = Right t'
          actual = checkApp M.empty renamedConst2T [Just t', Just t']
       in expected === actual

-- Try to apply `forall a b . a -> b -> !a` to two random _different_ concrete
-- types. Result should be the choice for `a`.
propConst2Different :: Property
propConst2Different = forAllShrink arbitrary shrink $ \(Concrete t1, Concrete t2) ->
  if t1 == t2
    then discard
    else withRenamedComp mempty const2T $ \renamedConst2T ->
      withRenamedVals mempty (Identity t1) $ \(Identity t1') ->
        withRenamedVals mempty (Identity t2) $ \(Identity t2') ->
          let expected = Right t1'
              actual = checkApp M.empty renamedConst2T [Just t1', Just t2']
           in expected === actual

-- Randomly pick a concrete type `A`, then pick a type `b` which is either `A`
-- or a type different from `A` (50% of the time each way). Then try to apply `A
-- -> !Integer` to `b`. Result should unify be `Integer` if `b ~ A`, and a
-- unification error otherwise.
propUnifyConcrete :: Property
propUnifyConcrete = forAllShrink gen shr $ \(tA, mtB) ->
  withRenamedComp mempty (Comp0 $ tA :--:> ReturnT integerT) $ \f ->
    withRenamedVals mempty (Identity tA) $ \(Identity tA') ->
      case mtB of
        Nothing ->
          let expected = Right integerT
              actual = checkApp M.empty f [Just tA']
           in expected === actual
        Just tB ->
          if tA == tB
            then discard
            else withRenamedVals mempty (Identity tB) $ \(Identity arg) ->
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
  let mockScope = Vector.replicate (review asInt scope + 1) (fromIntegral $ review intIndex ix + 1)
   in withRenamedComp mockScope (Comp0 $ tyvar (S scope) ix :--:> ReturnT integerT) $ \f ->
        withRenamedVals mockScope (Identity t) $ \(Identity t') ->
          -- This is a little confusing, as we would expect that the true level will
          -- be based on `S scope`, since that's what's in the computation type.
          -- However, we actually have to reduce it by 1, as we have a 'scope
          -- stepdown' for `f` even though we bind no variables.
          let trueLevel = ezTrueLevel mockScope scope ix
              expected = Left . DoesNotUnify (Abstraction . Rigid trueLevel $ ix) $ t'
              actual = checkApp M.empty f [Just t']
           in expected === actual

-- Randomly pick a concrete type A, then try to apply `(forall a . a ->
-- !Integer) -> !Integer` to `(A -> !Integer)`. Result should fail to unify.
propUnifyWildcardConcrete :: Property
propUnifyWildcardConcrete = forAllShrink arbitrary shrink $ \(Concrete t) ->
  let thunk = ThunkT . Comp1 $ tyvar Z ix0 :--:> ReturnT integerT
   in withRenamedComp mempty (Comp0 $ thunk :--:> ReturnT integerT) $ \f ->
        let argT = ThunkT . Comp0 $ t :--:> ReturnT integerT
         in withRenamedVals mempty (Identity argT) $ \(Identity argT') ->
              let lhs = ThunkT . Comp1 $ Abstraction (Wildcard 1 1 ix0) :--:> ReturnT integerT
                  expected = Left . DoesNotUnify lhs $ argT'
                  actual = checkApp M.empty f [Just argT']
               in expected === actual

-- Randomly generate a concrete type A, then try to apply
-- `(forall a . a -> !A) -> !A` to `forall a . (a -> !A)`. Result should unify
-- to `A`.
propUnifyWildcardUnifiable :: Property
propUnifyWildcardUnifiable = forAllShrink arbitrary shrink $ \(Concrete t) ->
  let mockScope = Vector.singleton 1
   in withRenamedComp mockScope (Comp0 $ ThunkT (Comp1 $ tyvar Z ix0 :--:> ReturnT t) :--:> ReturnT t) $ \f ->
        withRenamedVals mockScope (Identity t) $ \(Identity t') ->
          withRenamedVals mockScope (Identity . ThunkT . Comp1 $ tyvar Z ix0 :--:> ReturnT t) $ \(Identity arg) ->
            let expected = Right t'
                actual = checkApp M.empty f [Just arg]
             in expected === actual

-- Randomly generate a concrete type A, and a rigid type B, then try to apply `A
-- -> !Integer` to `B`. Result should fail to unify.
propUnifyConcreteRigid :: Property
propUnifyConcreteRigid = forAllShrink arbitrary shrink $ \(Concrete aT, scope, index) ->
  let mockScope = Vector.replicate (review asInt scope + 1) (fromIntegral $ review intIndex index + 1)
   in withRenamedComp mockScope (Comp0 $ aT :--:> ReturnT integerT) $ \f ->
        withRenamedVals mockScope (Identity $ tyvar scope index) $ \(Identity arg) ->
          withRenamedVals mockScope (Identity aT) $ \(Identity aT') ->
            let level = ezTrueLevel mockScope scope index
                expected = Left . DoesNotUnify aT' . Abstraction . Rigid level $ index
                actual = checkApp M.empty f [Just arg]
             in expected === actual

-- Randomly generate a rigid type A, then try to apply `forall a . a -> !a` to
-- `A`. Result should unify to `A`.
propUnifyUnifiableRigid :: Property
propUnifyUnifiableRigid = forAllShrink arbitrary shrink $ \(scope, index) ->
  let mockScope = Vector.replicate (review asInt scope + 1) (fromIntegral $ review intIndex index + 1)
   in withRenamedComp mockScope idT $ \f ->
        withRenamedVals mockScope (Identity $ tyvar scope index) $ \(Identity arg) ->
          let expected = Right arg
              actual = checkApp M.empty f [Just arg]
           in expected === actual

-- Randomly generate a scope stack of height at least 2, then two indexes `I`
-- and `J`, both valid in that scope stack. `I` and `J` may be different or the
-- same, with equal probability. Let `T` be the rigid type corresponding to some
-- variable index in the scope stack at the position for `I`, and `U` be the
-- rigid type corresponding to some variable index in the scope stack at the
-- position for `J`. Attempt to unify `T -> !Integer` with `U`. This should
-- unify to `Integer` if, and only if, `T == U`; otherwise, it should fail to
-- unify.
propUnifyRigid :: Property
propUnifyRigid = forAll gen $ \(scopeStack, t, u, same) ->
  withRenamedComp scopeStack (Comp0 $ t :--:> ReturnT integerT) $ \fun ->
    withRenamedVals scopeStack (Identity u) $ \(Identity arg) ->
      case checkApp mempty fun [Just arg] of
        Left err -> counterexample ("Identical rigids, but got " <> show err) $ not same
        Right res -> counterexample ("Different rigids, but unified to " <> show res) same
  where
    gen :: Gen (Vector Word32, ValT AbstractTy, ValT AbstractTy, Bool)
    gen = do
      -- Note (Koz, 08/08/2025): We have to use this rather odd method to ensure
      -- that we never have any scope stack smaller than 2 elements. If we have
      -- an empty stack, we loop forever as we can't find a valid index, and if
      -- the scope stack is a singleton, we can never hit the 'different' case.
      --
      -- Furthermore, we must ensure every scope stack has at least 1 available
      -- variable, as otherwise, our subsequent generator can 'miss'.
      firstScope <- getNonZero <$> arbitrary
      secondScope <- getNonZero <$> arbitrary
      restOfScopes <- liftArbitrary (getNonZero <$> arbitrary)
      let scopeStack = Vector.cons firstScope . Vector.cons secondScope $ restOfScopes
      (t, u, same) <- genAbstractions scopeStack
      pure (scopeStack, t, u, same)
    genAbstractions :: Vector Word32 -> Gen (ValT AbstractTy, ValT AbstractTy, Bool)
    genAbstractions scopeStack = do
      let len = Vector.length scopeStack
      iPosition <- chooseInt (0, len - 1)
      jPosition <- suchThat (chooseInt (0, len - 1)) (/= iPosition)
      let iDB = fromJust . preview asInt $ iPosition
      let jDB = fromJust . preview asInt $ jPosition
      let iVarsAvailable = fromIntegral $ scopeStack Vector.! iPosition
      let jVarsAvailable = fromIntegral $ scopeStack Vector.! jPosition
      iIx <- suchThatMap (chooseInt (0, iVarsAvailable - 1)) (preview intIndex)
      jIx <- suchThatMap (chooseInt (0, jVarsAvailable - 1)) (preview intIndex)
      -- Note (Koz, 08/08/2025): We have to offset `t` by 1, because it's being
      -- bundled directly into a `Comp0`, which means that to refer to the same
      -- position in the scope stack, it needs to be one higher.
      elements
        [ -- 'Same' option.
          (tyvar (S iDB) iIx, tyvar iDB iIx, True),
          -- 'Different' option.
          (tyvar (S iDB) iIx, tyvar jDB jIx, False)
        ]

-- Randomly pick a rigid type A, then try to apply `(forall a . a -> !Integer)
-- -> !Integer` to `(A -> !Integer)`. Result should fail to unify.
propUnifyWildcardRigid :: Property
propUnifyWildcardRigid = forAllShrink arbitrary shrink $ \(scope, index) ->
  let thunk = ThunkT . Comp1 $ tyvar Z ix0 :--:> ReturnT integerT
      mockScope = Vector.replicate (review asInt scope + 1) (fromIntegral $ review intIndex index + 1)
   in withRenamedComp mockScope (Comp0 $ thunk :--:> ReturnT integerT) $ \f ->
        let argT = ThunkT . Comp0 $ tyvar (S scope) index :--:> ReturnT integerT
         in withRenamedVals mockScope (Identity argT) $ \(Identity argT') ->
              let lhs = ThunkT . Comp1 $ Abstraction (Wildcard 1 1 ix0) :--:> ReturnT integerT
                  expected = Left . DoesNotUnify lhs $ argT'
                  actual = checkApp M.empty f [Just argT']
               in expected === actual

-- Randomly pick concrete types A and B, then try to apply to `forall a . ((A -> B ->
-- !a) -> !a)` the argument `(A -> B -> !A)`. Result should unify and produce
-- `A`.
propThunkWithUnifiableResult :: Property
propThunkWithUnifiableResult = forAllShrink arbitrary shrink $ \(Concrete aT, Concrete bT) ->
  let funThunkArgT = ThunkT $ Comp0 $ aT :--:> bT :--:> ReturnT (tyvar (S Z) ix0)
      funT = Comp1 $ funThunkArgT :--:> ReturnT (tyvar Z ix0)
      thunkT = ThunkT $ Comp0 $ aT :--:> bT :--:> ReturnT aT
   in withRenamedComp mempty funT $ \f ->
        withRenamedVals mempty (Identity thunkT) $ \(Identity argT) ->
          withRenamedVals mempty (Identity aT) $ \(Identity aT') ->
            let expected = Right aT'
                actual = checkApp M.empty f [Just argT]
             in expected === actual

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
  defaultLeftRenamed <- failLeft . runRenameM mempty . renameCompT $ defaultLeft
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
  fnRenamed <- failLeft . runRenameM mempty . renameCompT $ testFn
  argRenamed <- failLeft . runRenameM mempty . renameValT $ testArg
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
  fnRenamed <- failLeft . runRenameM mempty . renameCompT $ defaultLeft
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
  fnRenamed <- failLeft . runRenameM mempty . renameCompT $ defaultPair
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
  fnRenamed <- failLeft . runRenameM mempty . renameCompT $ testFn
  result <-
    either (assertFailure . catchInsufficientArgs) pure $
      checkApp tyAppTestDatatypes fnRenamed [Just testArg]
  assertEqual "unifyMaybe" result (BuiltinFlat IntegerT)
  where
    catchInsufficientArgs :: TypeAppError -> String
    catchInsufficientArgs = \case
      InsufficientArgs _ fn _ -> prettyStr fn
      other -> show other

-- Checks that `forall a . Maybe a -> Maybe (Maybe a)`, when applied to `Maybe
-- Integer`, produces `Maybe (Maybe Integer)`
unitNestedDatatypes :: IO ()
unitNestedDatatypes = do
  let fn =
        Comp1 $
          Datatype "Maybe" (Vector.singleton $ tyvar Z ix0)
            :--:> ReturnT (Datatype "Maybe" (Vector.singleton . Datatype "Maybe" . Vector.singleton $ tyvar Z ix0))
  fnRenamed <- failLeft . runRenameM mempty . renameCompT $ fn
  let arg = Datatype "Maybe" . Vector.singleton $ integerT
  let expected = Datatype "Maybe" . Vector.singleton . Datatype "Maybe" . Vector.singleton $ integerT
  case checkApp tyAppTestDatatypes fnRenamed [Just arg] of
    Left err -> assertFailure . show $ err
    Right res -> assertEqual "type mismatch" expected res

-- Randomly pick concrete types A and B, then try to apply to `forall a. ((A ->
-- Maybe B -> !a) -> !a)` the argument `(A -> Maybe B -> !A)`. Result should
-- unify and produce `A`.
propThunkWithDatatype :: Property
propThunkWithDatatype = forAllShrink arbitrary shrink $ \(Concrete aT, Concrete bT) ->
  let maybeT = Datatype "Maybe" (Vector.singleton bT)
      funThunkArg = ThunkT $ Comp0 $ aT :--:> maybeT :--:> ReturnT (tyvar (S Z) ix0)
      funT = Comp1 $ funThunkArg :--:> ReturnT (tyvar Z ix0)
      thunkT = ThunkT $ Comp0 $ aT :--:> maybeT :--:> ReturnT aT
   in withRenamedComp mempty funT $ \f ->
        withRenamedVals mempty (Identity thunkT) $ \(Identity argT) ->
          withRenamedVals mempty (Identity aT) $ \(Identity aT') ->
            let expected = Right aT'
                actual = checkApp tyAppTestDatatypes f [Just argT]
             in expected === actual

-- Randomly pick concrete types A and B, then try to apply to `((A -> Maybe B ->
-- !A) -> !A)` the argument `(A -> Maybe B -> !A)`. Result should unify and
-- produce `A`.
propConcreteThunkWithDatatype :: Property
propConcreteThunkWithDatatype = forAllShrink arbitrary shrink $ \(Concrete aT, Concrete bT) ->
  let maybeT = Datatype "Maybe" (Vector.singleton bT)
      funThunkArg = ThunkT $ Comp0 $ aT :--:> maybeT :--:> ReturnT aT
      funT = Comp0 $ funThunkArg :--:> ReturnT aT
      thunkT = ThunkT $ Comp0 $ aT :--:> maybeT :--:> ReturnT aT
   in withRenamedComp mempty funT $ \f ->
        withRenamedVals mempty (Identity thunkT) $ \(Identity argT) ->
          withRenamedVals mempty (Identity aT) $ \(Identity aT') ->
            let expected = Right aT'
                actual = checkApp tyAppTestDatatypes f [Just argT]
             in expected === actual

-- Randomly pick concrete types A and B, then try to apply to `forall a. ((a -> Maybe B
-- -> !A) -> !A)` the argument `(A -> Maybe B -> !A)`. Result should unify and
-- produce `A`.
propThunkUnifiableWithDatatype :: Property
propThunkUnifiableWithDatatype = forAllShrink arbitrary shrink $ \(Concrete aT, Concrete bT) ->
  let maybeT = Datatype "Maybe" (Vector.singleton bT)
      funThunkArg = ThunkT $ Comp1 $ tyvar (S Z) ix0 :--:> maybeT :--:> ReturnT aT
      funT = Comp1 $ funThunkArg :--:> ReturnT aT
      thunkT = ThunkT $ Comp0 $ aT :--:> maybeT :--:> ReturnT aT
   in withRenamedComp mempty funT $ \f ->
        withRenamedVals mempty (Identity thunkT) $ \(Identity argT) ->
          withRenamedVals mempty (Identity aT) $ \(Identity aT') ->
            let expected = Right aT'
                actual = checkApp tyAppTestDatatypes f [Just argT]
             in expected === actual

-- Randomly pick concrete type A, then try to apply to `forall a . ((Maybe A ->
-- !a) -> !a)` the argument `(Maybe A -> !A)`. Result should unify and produce
-- `A`.
propThunkUnifiableDatatype :: Property
propThunkUnifiableDatatype = forAllShrink arbitrary shrink $ \(Concrete aT) ->
  let -- maybeTUnifiable = Datatype "Maybe" . Vector.singleton $ tyvar (S Z) ix0
      maybeTConcrete = Datatype "Maybe" . Vector.singleton $ aT
      funThunkArg = ThunkT $ Comp0 $ maybeTConcrete :--:> ReturnT (tyvar (S Z) ix0)
      funT = Comp1 $ funThunkArg :--:> ReturnT (tyvar Z ix0)
      thunkT = ThunkT $ Comp0 $ maybeTConcrete :--:> ReturnT aT
   in withRenamedComp mempty funT $ \f ->
        withRenamedVals mempty (Identity thunkT) $ \(Identity argT) ->
          withRenamedVals mempty (Identity aT) $ \(Identity aT') ->
            let expected = Right aT'
                actual = checkApp tyAppTestDatatypes f [Just argT]
             in expected === actual

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

withRenamedComp ::
  Vector.Vector Word32 ->
  CompT AbstractTy ->
  (CompT Renamed -> Property) ->
  Property
withRenamedComp scope t f = case runRenameM scope . renameCompT $ t of
  Left err -> counterexample (show err) False
  Right t' -> f t'

withRenamedVals ::
  forall (t :: Type -> Type).
  (Traversable t) =>
  Vector.Vector Word32 ->
  t (ValT AbstractTy) ->
  (t (ValT Renamed) -> Property) ->
  Property
withRenamedVals scope vals f = case runRenameM scope . traverse renameValT $ vals of
  Left err -> counterexample (show err) False
  Right vals' -> f vals'

ezTrueLevel :: Vector.Vector Word32 -> DeBruijn -> Index "tyvar" -> Int
ezTrueLevel inherited db ix = case runRenameM inherited . renameValT $ tyvar db ix of
  Left err' -> error ("ezTrueLevel: " <> show err')
  Right (Abstraction (Rigid res _)) -> res
  other -> error $ "ezTrueLevel didn't get a rigid, but got: " <> show other
