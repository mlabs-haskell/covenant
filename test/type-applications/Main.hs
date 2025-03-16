{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Control.Applicative ((<|>))
import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index
  ( count0,
    count1,
    ix0,
    ix1,
  )
import Covenant.Test (Concrete (Concrete))
import Covenant.Type
  ( AbstractTy,
    CompT (CompT),
    Renamed,
    TypeAppError
      ( DoesNotUnify,
        ExcessArgs,
        InsufficientArgs,
        LeakingUnifiable
      ),
    ValT,
    checkApp,
    comp1,
    comp2,
    integerT,
    listT,
    renameCompT,
    renameValT,
    runRenameM,
    tyvar,
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
          testProperty "two-arg const to different concretes" propConst2Different
        ],
      testGroup
        "Unification"
        [ testProperty "concrete expected, concrete actual" propUnifyConcrete
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

-- Helpers

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
