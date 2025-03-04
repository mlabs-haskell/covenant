module Main (main) where

import Covenant.Type
  ( AbstractTy (BoundAtScope, ForallAA),
    BuiltinFlatT
      ( BLS12_381_G1_ElementT,
        BLS12_381_G2_ElementT,
        BLS12_381_MlResultT,
        BoolT,
        ByteStringT,
        DataT,
        IntegerT,
        StringT,
        UnitT
      ),
    BuiltinNestedT (ListT, PairT),
    CompT (CompT),
    Renamed (Can'tSet, CanSet),
    ValT (Abstraction, BuiltinFlat, BuiltinNested, ThunkT),
    renameCompT,
    renameValT,
    runRenameM,
  )
import Data.Bimap qualified as Bimap
import Data.Coerce (coerce)
import Data.Functor.Classes (liftEq)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.List.NonEmpty qualified as NonEmpty
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Gen,
    Property,
    elements,
    forAllShrinkShow,
    listOf,
    oneof,
    sized,
    (.&&.),
    (===),
  )
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "Renaming" $
    [ testCase "bare abstraction" testBareAbs,
      testGroup
        "Builtin flat types"
        [ testCase "UnitT" $ testFlat UnitT,
          testCase "BoolT" $ testFlat BoolT,
          testCase "IntegerT" $ testFlat IntegerT,
          testCase "StringT" $ testFlat StringT,
          testCase "ByteStringT" $ testFlat ByteStringT,
          testCase "G1ElementT" $ testFlat BLS12_381_G1_ElementT,
          testCase "G2ElementT" $ testFlat BLS12_381_G2_ElementT,
          testCase "MlResultT" $ testFlat BLS12_381_MlResultT,
          testCase "DataT" $ testFlat DataT
        ],
      testProperty "Nested concrete types" propNestedConcrete,
      testCase "Rename id type" testIdT,
      testCase "Rename const type" testConstT,
      testCase "Rename HeadList type" testHeadListT,
      testCase "Rename SndPair type" testSndPairT,
      testCase "Rename map function over lists" testMapT,
      testGroup
        "Nested foralls"
        [ testCase "forall a b . (a, b)" testPairTOuterOuter,
          testCase "forall a . (a, forall b . b)" testPairTOuterInner,
          testCase "forall b . (forall a . a, b)" testPairTInnerOuter,
          testCase "(forall a . a, forall b . b)" testPairTInnerInner
        ]
    ]
  where
    -- Note (Koz, 26/02/2025): By default, QuickCheck runs only 100 tests per
    -- property, which is far to few. Using the method below, we can ensure that
    -- we run a decent number of tests, while also permitting more than this to
    -- be set via the CLI if we want.
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 10_000

-- Tests and properties

-- Checks that `forall a . a` renames correctly. Also verifies that there are no
-- fixed bindings in the tracker afterwards.
testBareAbs :: IO ()
testBareAbs = do
  let absTy = Abstraction ForallAA
  let expected = Abstraction (CanSet 0)
  let (tracker, actual) = runRenameM . renameValT $ absTy
  assertEqual "" expected actual
  let entry = Bimap.lookup (0, 0) tracker
  assertEqual "" Nothing entry

-- Checks that the given 'flat' type renames to itself. Also verifies that there
-- are no fixed bindings in the tracker afterwards.
testFlat :: BuiltinFlatT -> IO ()
testFlat t = do
  let input = BuiltinFlat t
  let (tracker, actual) = runRenameM . renameValT $ input
  assertBool "" (liftEq (\_ _ -> False) input actual)
  assertEqual "" Bimap.empty tracker

-- Checks that for any 'fully concretified' type (nested or not), renaming
-- changes nothing. Also verifies that there are no fixed bindings in the
-- tracker afterwards.
propNestedConcrete :: Property
propNestedConcrete = forAllShrinkShow arbitrary shrink show $ \(Concrete t) ->
  let (tracker, actual) = runRenameM . renameValT $ t
   in tracker === Bimap.empty .&&. liftEq (\_ _ -> False) t actual

-- Checks that `forall a . a -> !a` correctly renames. Also verifies there are no
-- fixed bindings in the tracker afterwards.
testIdT :: IO ()
testIdT = do
  let absA = BoundAtScope 1 0
  let idT = CompT 1 $ Abstraction absA :| [Abstraction absA]
  let expected = CompT 1 $ Abstraction (CanSet 0) :| [Abstraction (CanSet 0)]
  let (tracker, actual) = runRenameM . renameCompT $ idT
  assertEqual "" expected actual
  assertEqual "" Bimap.empty tracker

-- Checks that `forall a b . a -> b -> !a` correctly renames. Also verifies that
-- there are no fixed bindings in the tracker afterwards.
testConstT :: IO ()
testConstT = do
  let absA = BoundAtScope 1 0
  let absB = BoundAtScope 1 1
  let constT = CompT 2 $ Abstraction absA :| [Abstraction absB, Abstraction absA]
  let expected = CompT 2 $ Abstraction (CanSet 0) :| [Abstraction (CanSet 1), Abstraction (CanSet 0)]
  let (tracker, actual) = runRenameM . renameCompT $ constT
  assertEqual "" expected actual
  assertEqual "" Bimap.empty tracker

-- Checks that `forall a . [a] -> !a` correctly renames. Also verifies that
-- there are no fixed bindings in the tracker afterwards.
testHeadListT :: IO ()
testHeadListT = do
  let absA = BoundAtScope 1 0
  let absAInner = BoundAtScope 2 0
  let headListT = CompT 1 $ BuiltinNested (ListT 0 (Abstraction absAInner)) :| [Abstraction absA]
  let expected = CompT 1 $ BuiltinNested (ListT 0 (Abstraction (CanSet 0))) :| [Abstraction (CanSet 0)]
  let (tracker, actual) = runRenameM . renameCompT $ headListT
  assertEqual "" expected actual
  assertEqual "" Bimap.empty tracker

-- Checks that `forall a b . (a, b) -> !b` correctly renames. Also verifies that
-- there are no fixed bindings in the tracker afterwards.
testSndPairT :: IO ()
testSndPairT = do
  let sndPairT =
        CompT 2 $
          BuiltinNested (PairT 0 (Abstraction (BoundAtScope 2 0)) (Abstraction (BoundAtScope 2 1)))
            :| [Abstraction (BoundAtScope 1 1)]
  let expected =
        CompT 2 $
          BuiltinNested (PairT 0 (Abstraction (CanSet 0)) (Abstraction (CanSet 1)))
            :| [Abstraction (CanSet 1)]
  let (tracker, actual) = runRenameM . renameCompT $ sndPairT
  assertEqual "" expected actual
  assertEqual "" Bimap.empty tracker

-- Checks that `forall a b . (a -> !b) -> [a] -> !b` correctly renames with
-- nothing left in the tracker. Also renames the thunk argument type _only_, and
-- checks that two fixed bindings remain in the tracker afterwards.
testMapT :: IO ()
testMapT = do
  let mapThunkT = ThunkT . CompT 0 $ Abstraction (BoundAtScope 2 0) :| [Abstraction (BoundAtScope 2 1)]
  let mapT =
        CompT 2 $
          mapThunkT
            :| [ BuiltinNested (ListT 0 (Abstraction (BoundAtScope 2 0))),
                 BuiltinNested (ListT 0 (Abstraction (BoundAtScope 2 1)))
               ]
  let expectedMapThunkT = ThunkT . CompT 0 $ Abstraction (Can'tSet 0) :| [Abstraction (Can'tSet 1)]
  let expectedThunkT = ThunkT . CompT 0 $ Abstraction (CanSet 0) :| [Abstraction (CanSet 1)]
  let expectedMapT =
        CompT 2 $
          expectedThunkT
            :| [ BuiltinNested (ListT 0 (Abstraction (CanSet 0))),
                 BuiltinNested (ListT 0 (Abstraction (CanSet 1)))
               ]
  let (trackerThunkT, actualThunkT) = runRenameM . renameValT $ mapThunkT
  assertEqual "" expectedMapThunkT actualThunkT
  let expectedThunkTracker = Bimap.fromList [((-1, 0), 0), ((-1, 1), 1)]
  assertEqual "" expectedThunkTracker trackerThunkT
  let (trackerMapT, actualMapT) = runRenameM . renameCompT $ mapT
  assertEqual "" expectedMapT actualMapT
  assertEqual "" Bimap.empty trackerMapT

-- Checks that `forall a b . (a, b)` correctly renames with nothing left in the
-- tracker.
testPairTOuterOuter :: IO ()
testPairTOuterOuter = do
  let pairT =
        BuiltinNested . PairT 2 (Abstraction (BoundAtScope 1 0)) . Abstraction . BoundAtScope 1 $ 1
  let expected =
        BuiltinNested . PairT 2 (Abstraction (CanSet 0)) . Abstraction . CanSet $ 1
  let (tracker, actual) = runRenameM . renameValT $ pairT
  assertEqual "" expected actual
  assertEqual "" Bimap.empty tracker

-- Checks that `forall b . (forall a . a, b)` renames correctly with nothing
-- left in the tracker.
testPairTInnerOuter :: IO ()
testPairTInnerOuter = do
  let pairT =
        BuiltinNested . PairT 1 (Abstraction ForallAA) . Abstraction . BoundAtScope 1 $ 0
  let expected =
        BuiltinNested . PairT 1 (Abstraction (Can'tSet 0)) . Abstraction . CanSet $ 0
  let (tracker, actual) = runRenameM . renameValT $ pairT
  assertEqual "" expected actual
  assertEqual "" Bimap.empty tracker

-- Checks that `forall a . (a, forall b . b)` renames correctly with nothing
-- left in the tracker.
testPairTOuterInner :: IO ()
testPairTOuterInner = do
  let pairT =
        BuiltinNested . PairT 1 (Abstraction (BoundAtScope 1 0)) . Abstraction $ ForallAA
  let expected =
        BuiltinNested . PairT 1 (Abstraction (CanSet 0)) . Abstraction . Can'tSet $ 0
  let (tracker, actual) = runRenameM . renameValT $ pairT
  assertEqual "" expected actual
  assertEqual "" Bimap.empty tracker

-- Checks that `(forall a . a, forall b . b)` renames correctly with nothing
-- left in the tracker. Also verifies that the two fixed renames are distinct.
testPairTInnerInner :: IO ()
testPairTInnerInner = do
  let pairT =
        BuiltinNested . PairT 0 (Abstraction ForallAA) . Abstraction $ ForallAA
  let expected =
        BuiltinNested . PairT 0 (Abstraction (Can'tSet 0)) . Abstraction . Can'tSet $ 1
  let (tracker, actual) = runRenameM . renameValT $ pairT
  assertEqual "" expected actual
  let expectedTracker = Bimap.empty
  assertEqual "" expectedTracker tracker

-- Helpers

-- A newtype wrapper which generates only 'fully concrete' ValTs
newtype Concrete = Concrete (ValT AbstractTy)
  deriving (Eq) via (ValT AbstractTy)
  deriving stock (Show)

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
                  BLS12_381_MlResultT,
                  DataT
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
                pure . BuiltinFlat $ DataT,
                BuiltinNested . ListT 0 <$> go (size `quot` 4),
                BuiltinNested <$> (PairT 0 <$> go (size `quot` 4) <*> go (size `quot` 4)),
                ThunkT . CompT 0 <$> ((:|) <$> go (size `quot` 4) <*> listOf (go (size `quot` 4)))
              ]
  {-# INLINEABLE shrink #-}
  shrink (Concrete v) =
    Concrete <$> case v of
      -- impossible
      Abstraction _ -> []
      ThunkT (CompT _ ts) ->
        -- Note (Koz, 26/02/2025): This is needed because, for some weird
        -- reason, NonEmpty lacks an Arbitrary instance.
        ThunkT . CompT 0 <$> do
          let asList = NonEmpty.toList ts
          shrunk <- fmap coerce . shrink . fmap Concrete $ asList
          case shrunk of
            [] -> []
            x : xs -> pure (x :| xs)
      -- Can't shrink this
      BuiltinFlat _ -> []
      BuiltinNested t ->
        BuiltinNested <$> case t of
          ListT _ t' -> do
            Concrete shrunk <- shrink (Concrete t')
            pure . ListT 0 $ shrunk
          PairT _ t1 t2 -> do
            Concrete shrunkT1 <- shrink (Concrete t1)
            Concrete shrunkT2 <- shrink (Concrete t2)
            [PairT 0 shrunkT1 t2, PairT 0 t1 shrunkT2]
