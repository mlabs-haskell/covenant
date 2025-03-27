{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index
  ( Index,
    count0,
    count1,
    ix0,
    ix1,
    ix2,
  )
import Covenant.Test (Concrete (Concrete))
import Covenant.Type
  ( AbstractTy,
    BuiltinNestedT (ListT),
    CompT (CompT),
    Renamed (Rigid, Wildcard),
    TypeAppError
      ( DoesNotUnify,
        ExcessArgs,
        InsufficientArgs,
        LeakingUnifiable
      ),
    ValT
      ( Abstraction,
        BuiltinNested,
        ThunkT
      ),
    checkApp,
    comp0,
    comp1,
    comp2,
    comp3,
    integerT,
    listT,
    renameCompT,
    renameValT,
    runRenameM,
    tyvar,
    (-*-),
    pattern ReturnT,
    pattern (:--:>),
  )
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity (Identity))
import Data.Kind (Type)
import Data.Vector qualified as Vector
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
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "Type application" $
    [ testCase "HeadList on polymorphic empty list" unitLeakingUnifiable,
      -- TODO: Check leaking wildcard; can't think of a case now
      testProperty "Too many arguments to HeadList" propTooManyArgs,
      testCase "HeadList on no arguments" unitInsufficientArgs,
      testGroup
        "Substitution"
        [ testProperty "id applied to concrete" propIdConcrete,
          testProperty "two-arg const to same concretes" propConst2Same,
          testProperty "two-arg const to different concretes" propConst2Different,
          testProperty "uncurry to concretes" propUncurry
        ],
      testGroup
        "Unification"
        [ testProperty "concrete expected, concrete actual" propUnifyConcrete,
          testProperty "unifiable expected, concrete actual" propUnifyUnifiableConcrete,
          testProperty "rigid expected, concrete actual" propUnifyRigidConcrete,
          testProperty "wildcard expected, concrete actual" propUnifyWildcardConcrete,
          testProperty "concrete expected, unifiable actual" propUnifyConcreteUnifiable,
          testProperty "unifiable expected, unifiable actual" propUnifyUnifiable,
          testProperty "rigid expected, unifiable actual" propUnifyRigidUnifiable,
          testProperty "wildcard expected, unifiable actual" propUnifyWildcardUnifiable,
          testProperty "concrete expected, rigid actual" propUnifyConcreteRigid,
          testProperty "unifiable expected, rigid actual" propUnifyUnifiableRigid,
          testProperty "rigid expected, rigid actual" propUnifyRigid,
          testProperty "wildcard expected, rigid actual" propUnifyWildcardRigid
          -- TODO: Wildcard arguments; can't come up with cases
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

-- Try to apply `forall a . [a] -> !a` to `forall a . [a]`. Result should be a
-- leaking unifiable.
unitLeakingUnifiable :: IO ()
unitLeakingUnifiable = do
  renamedHeadListT <- failLeft . runRenameM . renameCompT $ headListT
  renamedEmptyListT <- failLeft . runRenameM . renameValT $ emptyListT
  let expected = Left (LeakingUnifiable ix0)
  let actual = checkApp renamedHeadListT [renamedEmptyListT]
  assertEqual "" expected actual

-- Try to apply more than one argument to `forall a . [a] -> !a`, making sure
-- that the first argument is 'suitable'. Result should indicate excess
-- arguments.
propTooManyArgs :: Property
propTooManyArgs = forAllShrink gen shr $ \excessArgs ->
  withRenamedComp headListT $ \renamedHeadListT ->
    withRenamedVals (Identity emptyListT) $ \(Identity renamedEmptyListT) ->
      withRenamedVals excessArgs $ \renamedExcessArgs ->
        let expected = Left . ExcessArgs . Vector.fromList $ renamedExcessArgs
            actual = checkApp renamedHeadListT (renamedEmptyListT : renamedExcessArgs)
         in expected === actual
  where
    -- Note (Koz, 14/04/2025): The default size of 100 makes it rather painful
    -- to generate excess arguments, as the generator used for concrete types
    -- is recursive. Furthermore, we need to ensure the list is nonempty, which
    -- forces too many restarts. Thus, we roll our own.
    gen :: Gen [ValT AbstractTy]
    gen = do
      size <- getSize
      lenIncrease <- elements [0, 1 .. size `quot` 4]
      Concrete firstTy <- arbitrary
      (firstTy :) <$> vectorOf lenIncrease (coerce @Concrete <$> arbitrary)
    shr :: [ValT AbstractTy] -> [[ValT AbstractTy]]
    shr = \case
      [] -> []
      [_] -> []
      xs -> liftShrink (coerce . shrink . Concrete) xs

-- Try to apply `forall a . [a] -> !a` to zero arguments. Result should indicate
-- insufficient arguments.
unitInsufficientArgs :: IO ()
unitInsufficientArgs = do
  renamedHeadListT <- failLeft . runRenameM . renameCompT $ headListT
  let expected = Left InsufficientArgs
  let actual = checkApp renamedHeadListT []
  assertEqual "" expected actual

-- Try to apply `forall a . a -> !a` to a random concrete type. Result should be
-- that type.
propIdConcrete :: Property
propIdConcrete = forAllShrink arbitrary shrink $ \(Concrete t) ->
  withRenamedComp idT $ \renamedIdT ->
    withRenamedVals (Identity t) $ \(Identity t') ->
      let expected = Right t'
          actual = checkApp renamedIdT [t']
       in expected === actual

-- Try to apply `forall a b . a -> b -> !a` to two identical concrete types.
-- Result should be that type.
propConst2Same :: Property
propConst2Same = forAllShrink arbitrary shrink $ \(Concrete t) ->
  withRenamedComp const2T $ \renamedConst2T ->
    withRenamedVals (Identity t) $ \(Identity t') ->
      let expected = Right t'
          actual = checkApp renamedConst2T [t', t']
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
              actual = checkApp renamedConst2T [t1', t2']
           in expected === actual

-- Randomly pick concrete types `B` and `C`. Then try to apply `forall a b
-- c . ({a, b} -> !c) -> !(a -> b -> !c)` to `forall a . ({a, B} -> !C)`. Result should
-- unify to `forall a . (a -> B -> !C)`.
propUncurry :: Property
propUncurry = forAllShrink arbitrary shrink $ \(Concrete bT, Concrete cT) ->
  withRenamedComp uncurryT $ \uncurryTRenamed ->
    let argT = ThunkT . comp1 $ (tyvar Z ix0 -*- bT) :--:> ReturnT cT
        expectedT = ThunkT . comp1 $ tyvar Z ix0 :--:> bT :--:> ReturnT cT
     in withRenamedVals (Identity argT) $ \(Identity renamedArgT) ->
          withRenamedVals (Identity expectedT) $ \(Identity renamedExpectedT) ->
            let expected = Right renamedExpectedT
                actual = checkApp uncurryTRenamed [renamedArgT]
             in expected === actual

-- Randomly pick a concrete type `A`, then pick a type `b` which is either `A`
-- or a type different from `A` (50% of the time each way). Then try to apply `A
-- -> !Integer` to `b`. Result should unify be `Integer` if `b ~ A`, and a
-- unification error otherwise.
propUnifyConcrete :: Property
propUnifyConcrete = forAllShrink gen shr $ \(tA, mtB) ->
  withRenamedComp (CompT count0 $ tA :--:> ReturnT integerT) $ \f ->
    withRenamedVals (Identity tA) $ \(Identity tA') ->
      case mtB of
        Nothing ->
          let expected = Right integerT
              actual = checkApp f [tA']
           in expected === actual
        Just tB ->
          if tA == tB
            then discard
            else withRenamedVals (Identity tB) $ \(Identity arg) ->
              let expected = Left . DoesNotUnify tA' $ arg
                  actual = checkApp f [arg]
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

-- Randomly pick a concrete type A, then try to apply `forall a . [a] -> !a` to
-- `[A]`. Result should unify to `A`.
propUnifyUnifiableConcrete :: Property
propUnifyUnifiableConcrete = forAllShrink arbitrary shrink $ \(Concrete t) ->
  withRenamedComp headListT $ \renamedHeadListT ->
    withRenamedVals (Identity t) $ \(Identity arg) ->
      let asList = BuiltinNested . ListT count0 $ arg
          expected = Right arg
          actual = checkApp renamedHeadListT [asList]
       in expected === actual

-- Randomly pick a rigid type A and concrete type B, then try to apply `A ->
-- !Integer` to `b`. Result should fail to unify.
propUnifyRigidConcrete :: Property
propUnifyRigidConcrete = forAllShrink arbitrary shrink $ \(Concrete t, scope, ix) ->
  withRenamedComp (comp0 $ tyvar (S scope) ix :--:> ReturnT integerT) $ \f ->
    withRenamedVals (Identity t) $ \(Identity t') ->
      -- This is a little confusing, as we would expect that the true level will
      -- be based on `S scope`, since that's what's in the computation type.
      -- However, we actually have to reduce it by 1, as we have a 'scope
      -- stepdown' for `f` even though we bind no variables.
      let trueLevel = negate . asInt $ scope
          expected = Left . DoesNotUnify (Abstraction . Rigid trueLevel $ ix) $ t'
          actual = checkApp f [t']
       in expected === actual

-- Randomly pick a concrete type A, then try to apply `(forall a . a ->
-- !Integer) -> !Integer` to `(A -> !Integer)`. Result should fail to unify.
propUnifyWildcardConcrete :: Property
propUnifyWildcardConcrete = forAllShrink arbitrary shrink $ \(Concrete t) ->
  let thunk = ThunkT . comp1 $ tyvar Z ix0 :--:> ReturnT integerT
   in withRenamedComp (comp0 $ thunk :--:> ReturnT integerT) $ \f ->
        let argT = ThunkT . comp0 $ t :--:> ReturnT integerT
         in withRenamedVals (Identity argT) $ \(Identity argT') ->
              let lhs = ThunkT . CompT count1 $ Abstraction (Wildcard 1 ix0) :--:> ReturnT integerT
                  expected = Left . DoesNotUnify lhs $ argT'
                  actual = checkApp f [argT']
               in expected === actual

-- Randomly pick a concrete type A, then try to apply `[A] -> !A` to `forall a .
-- [a]`. Result should unify to `A`.
propUnifyConcreteUnifiable :: Property
propUnifyConcreteUnifiable = forAllShrink arbitrary shrink $ \(Concrete t) ->
  withRenamedComp (comp0 $ listT count0 t :--:> ReturnT t) $ \f ->
    withRenamedVals (Identity emptyListT) $ \(Identity arg) ->
      withRenamedVals (Identity t) $ \(Identity t') ->
        let expected = Right t'
            actual = checkApp f [arg]
         in expected === actual

-- Randomly pick a concrete type A, then try to apply `forall a. [a] -> !A` to
-- `forall a. [a]`. Result should unify to `A`.
propUnifyUnifiable :: Property
propUnifyUnifiable = forAllShrink arbitrary shrink $ \(Concrete t) ->
  withRenamedComp (comp1 $ listT count0 (tyvar (S Z) ix0) :--:> ReturnT t) $ \f ->
    withRenamedVals (Identity emptyListT) $ \(Identity arg) ->
      withRenamedVals (Identity t) $ \(Identity t') ->
        let expected = Right t'
            actual = checkApp f [arg]
         in expected === actual

-- Randomly generate a rigid type A, and a concrete type B, then try to apply `[A]
-- -> !B` to `forall a . [a]`. Result should unify to `B`.
propUnifyRigidUnifiable :: Property
propUnifyRigidUnifiable = forAllShrink arbitrary shrink $ \(Concrete bT, scope, index) ->
  withRenamedComp (comp0 $ listT count0 (tyvar (S (S scope)) index) :--:> ReturnT bT) $ \f ->
    withRenamedVals (Identity emptyListT) $ \(Identity arg) ->
      withRenamedVals (Identity bT) $ \(Identity bT') ->
        let expected = Right bT'
            actual = checkApp f [arg]
         in expected === actual

-- Randomly generate a concrete type A, then try to apply
-- `(forall a . a -> !A) -> !A` to `forall a . (a -> !A)`. Result should unify
-- to `A`.
propUnifyWildcardUnifiable :: Property
propUnifyWildcardUnifiable = forAllShrink arbitrary shrink $ \(Concrete t) ->
  withRenamedComp (comp0 $ ThunkT (comp1 $ tyvar Z ix0 :--:> ReturnT t) :--:> ReturnT t) $ \f ->
    withRenamedVals (Identity t) $ \(Identity t') ->
      withRenamedVals (Identity . ThunkT . comp1 $ tyvar Z ix0 :--:> ReturnT t) $ \(Identity arg) ->
        let expected = Right t'
            actual = checkApp f [arg]
         in expected === actual

-- Randomly generate a concrete type A, and a rigid type B, then try to apply `A
-- -> !Integer` to `B`. Result should fail to unify.
propUnifyConcreteRigid :: Property
propUnifyConcreteRigid = forAllShrink arbitrary shrink $ \(Concrete aT, scope, index) ->
  withRenamedComp (comp0 $ aT :--:> ReturnT integerT) $ \f ->
    withRenamedVals (Identity $ tyvar scope index) $ \(Identity arg) ->
      withRenamedVals (Identity aT) $ \(Identity aT') ->
        let level = negate . asInt $ scope
            expected = Left . DoesNotUnify aT' . Abstraction . Rigid level $ index
            actual = checkApp f [arg]
         in expected === actual

-- Randomly generate a rigid type A, then try to apply `forall a . a -> !a` to
-- `A`. Result should unify to `A`.
propUnifyUnifiableRigid :: Property
propUnifyUnifiableRigid = forAllShrink arbitrary shrink $ \(scope, index) ->
  withRenamedComp idT $ \f ->
    withRenamedVals (Identity $ tyvar scope index) $ \(Identity arg) ->
      let expected = Right arg
          actual = checkApp f [arg]
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
    let actual = checkApp f [arg]
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
      withRenamedComp (comp0 $ tyvar (S db) index :--:> ReturnT integerT) $ \fun ->
        case mrest of
          Nothing -> withRenamedVals (Identity . tyvar db $ index) $ \(Identity arg) ->
            f (fun, arg, Right integerT)
          Just rest ->
            let level = negate . asInt $ db
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
  let thunk = ThunkT . comp1 $ tyvar Z ix0 :--:> ReturnT integerT
   in withRenamedComp (comp0 $ thunk :--:> ReturnT integerT) $ \f ->
        let argT = ThunkT . comp0 $ tyvar (S scope) index :--:> ReturnT integerT
         in withRenamedVals (Identity argT) $ \(Identity argT') ->
              let lhs = ThunkT . CompT count1 $ Abstraction (Wildcard 1 ix0) :--:> ReturnT integerT
                  expected = Left . DoesNotUnify lhs $ argT'
                  actual = checkApp f [argT']
               in expected === actual

-- Helpers

-- `forall a b c . ({a, b} -> !c) -> !(a -> b -> !c)`
uncurryT :: CompT AbstractTy
uncurryT =
  let argT =
        ThunkT . comp0 $
          (tyvar (S Z) ix0 -*- tyvar (S Z) ix1)
            :--:> ReturnT (tyvar (S Z) ix2)
      resultT =
        ThunkT . comp0 $
          tyvar (S Z) ix0
            :--:> tyvar (S Z) ix1
            :--:> ReturnT (tyvar (S Z) ix2)
   in comp3 $ argT :--:> ReturnT resultT

-- `forall a. a -> !a`
idT :: CompT AbstractTy
idT = comp1 $ tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)

-- `forall a b . a -> b -> !a
const2T :: CompT AbstractTy
const2T = comp2 $ tyvar Z ix0 :--:> tyvar Z ix1 :--:> ReturnT (tyvar Z ix0)

-- `forall a . [a] -> !a`
headListT :: CompT AbstractTy
headListT =
  comp1 $ listT count0 (tyvar (S Z) ix0) :--:> ReturnT (tyvar Z ix0)

-- `forall a. [a]`
emptyListT :: ValT AbstractTy
emptyListT = listT count1 (tyvar Z ix0)

failLeft ::
  forall (a :: Type) (b :: Type).
  (Show a) => Either a b -> IO b
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
