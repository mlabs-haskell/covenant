{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index (count0, count1, count2, ix0, ix1)
import Covenant.Type
  ( AbstractTy (BoundAt),
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
    RenameError
      ( InvalidAbstractionReference,
        IrrelevantAbstraction,
        OverdeterminateAbstraction
      ),
    Renamed (Rigid, Unifiable, Wildcard),
    ValT (Abstraction, BuiltinFlat, BuiltinNested, ThunkT),
    renameCompT,
    renameValT,
    runRenameM,
    pattern ReturnT,
    pattern (:--:>),
  )
import Data.Coerce (coerce)
import Data.Functor.Classes (liftEq)
import Data.Kind (Type)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty qualified as NonEmpty
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Gen,
    Property,
    elements,
    forAllShrinkShow,
    liftArbitrary,
    oneof,
    sized,
  )
import Test.QuickCheck.Instances.Vector ()
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, testCase)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "Renaming" $
    [ testGroup
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
      testCase "forall a . a -> !a" testIdT,
      testCase "forall a b . a -> b -> !a" testConstT,
      testCase "forall a . a -> !(forall b . b -> !a)" testConstT2,
      testCase "forall a . [a] -> !a" testHeadListT,
      testCase "forall a b . (a, b) -> !b" testSndPairT,
      testCase "forall a b . (a -> !b) -> [a] -> ![b]" testMapT,
      testCase "forall a b . (a, b)" testPairT,
      testGroup
        "Irrelevance"
        [ testCase "forall a b . [a]" testDodgyListT
        ],
      testGroup
        "Overdeterminance"
        [ testCase "forall a b . a -> !(b -> !a)" testDodgyConstT,
          testCase "forall a b . a -> !a" testDodgyIdT
        ],
      testGroup
        "Non-existent abstractions"
        [ testCase "forall a . b -> !a" testIndexingIdT
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

-- Checks that the given 'flat' type renames to itself.
testFlat :: BuiltinFlatT -> IO ()
testFlat t = do
  let input = BuiltinFlat t
  let result = runRenameM . renameValT $ input
  assertRight (assertBool "" . liftEq (\_ _ -> False) input) result

-- Checks that for any 'fully concretified' type (nested or not), renaming
-- changes nothing.
propNestedConcrete :: Property
propNestedConcrete = forAllShrinkShow arbitrary shrink show $ \(Concrete t) ->
  let result = runRenameM . renameValT $ t
   in case result of
        Left _ -> False
        Right actual -> liftEq (\_ _ -> False) t actual

-- Checks that `forall a . a -> !a` correctly renames.
testIdT :: IO ()
testIdT = do
  let idT =
        CompT count1 $
          Abstraction (BoundAt Z ix0)
            :--:> ReturnT (Abstraction (BoundAt Z ix0))
  let expected =
        CompT count1 $
          Abstraction (Unifiable ix0)
            :--:> ReturnT (Abstraction (Unifiable ix0))
  let result = runRenameM . renameCompT $ idT
  assertRight (assertEqual "" expected) result

-- Checks that `forall a b . a -> b -> !a` correctly renames.
testConstT :: IO ()
testConstT = do
  let absA = BoundAt Z ix0
  let absB = BoundAt Z ix1
  let constT =
        CompT count2 $
          Abstraction absA
            :--:> Abstraction absB
            :--:> ReturnT (Abstraction absA)
  let expected =
        CompT count2 $
          Abstraction (Unifiable ix0)
            :--:> Abstraction (Unifiable ix1)
            :--:> ReturnT (Abstraction (Unifiable ix0))
  let result = runRenameM . renameCompT $ constT
  assertRight (assertEqual "" expected) result

-- Checks that `forall a . a -> !(forall b . b -> !a)` correctly renames.
testConstT2 :: IO ()
testConstT2 = do
  let constT =
        CompT count1 $
          Abstraction (BoundAt Z ix0)
            :--:> ReturnT
              ( ThunkT . CompT count1 $
                  Abstraction (BoundAt Z ix0)
                    :--:> ReturnT (Abstraction (BoundAt (S Z) ix0))
              )
  let expected =
        CompT count1 $
          Abstraction (Unifiable ix0)
            :--:> ReturnT
              ( ThunkT . CompT count1 $
                  Abstraction (Wildcard 1 ix0)
                    :--:> ReturnT (Abstraction (Unifiable ix0))
              )
  let result = runRenameM . renameCompT $ constT
  assertRight (assertEqual "" expected) result

-- Checks that `forall a . [a] -> !a` correctly renames.
testHeadListT :: IO ()
testHeadListT = do
  let absA = BoundAt Z ix0
  let absAInner = BoundAt (S Z) ix0
  let headListT =
        CompT count1 $
          BuiltinNested (ListT count0 (Abstraction absAInner))
            :--:> ReturnT (Abstraction absA)
  let expected =
        CompT count1 $
          BuiltinNested (ListT count0 (Abstraction (Unifiable ix0)))
            :--:> ReturnT (Abstraction (Unifiable ix0))
  let result = runRenameM . renameCompT $ headListT
  assertRight (assertEqual "" expected) result

-- Checks that `forall a b . (a, b) -> !b` correctly renames.
testSndPairT :: IO ()
testSndPairT = do
  let sndPairT =
        CompT count2 $
          BuiltinNested (PairT count0 (Abstraction (BoundAt (S Z) ix0)) (Abstraction (BoundAt (S Z) ix1)))
            :--:> ReturnT (Abstraction (BoundAt Z ix1))
  let expected =
        CompT count2 $
          BuiltinNested (PairT count0 (Abstraction (Unifiable ix0)) (Abstraction (Unifiable ix1)))
            :--:> ReturnT (Abstraction (Unifiable ix1))
  let result = runRenameM . renameCompT $ sndPairT
  assertRight (assertEqual "" expected) result

-- Checks that `forall a b . (a -> !b) -> [a] -> !b` correctly renames.
-- Also renames the thunk argument type _only_, to check that rigid arguments
-- behave as expected.
testMapT :: IO ()
testMapT = do
  let mapThunkT =
        ThunkT
          . CompT count0
          $ Abstraction (BoundAt (S Z) ix0) :--:> ReturnT (Abstraction (BoundAt (S Z) ix1))
  let mapT =
        CompT count2 $
          mapThunkT
            :--:> BuiltinNested (ListT count0 (Abstraction (BoundAt (S Z) ix0)))
            :--:> ReturnT (BuiltinNested (ListT count0 (Abstraction (BoundAt (S Z) ix1))))
  let expectedMapThunkT =
        ThunkT
          . CompT count0
          $ Abstraction (Rigid 0 ix0) :--:> ReturnT (Abstraction (Rigid 0 ix1))
  let expectedMapT =
        CompT count2 $
          (ThunkT . CompT count0 $ Abstraction (Unifiable ix0) :--:> ReturnT (Abstraction (Unifiable ix1)))
            :--:> BuiltinNested (ListT count0 (Abstraction (Unifiable ix0)))
            :--:> ReturnT (BuiltinNested (ListT count0 (Abstraction (Unifiable ix1))))
  let resultThunkT = runRenameM . renameValT $ mapThunkT
  assertRight (assertEqual "" expectedMapThunkT) resultThunkT
  let resultMapT = runRenameM . renameCompT $ mapT
  assertRight (assertEqual "" expectedMapT) resultMapT

-- Checks that `forall a b . (a, b)` correctly renames.
testPairT :: IO ()
testPairT = do
  let pairT =
        BuiltinNested
          . PairT count2 (Abstraction (BoundAt Z ix0))
          . Abstraction
          . BoundAt Z
          $ ix1
  let expected =
        BuiltinNested
          . PairT count2 (Abstraction (Unifiable ix0))
          . Abstraction
          . Unifiable
          $ ix1
  let result = runRenameM . renameValT $ pairT
  assertRight (assertEqual "" expected) result

-- Checks that `forall a b . [a]` triggers the irrelevance checker.
testDodgyListT :: IO ()
testDodgyListT = do
  let listT = BuiltinNested . ListT count2 $ Abstraction (BoundAt Z ix0)
  let result = runRenameM . renameValT $ listT
  case result of
    Left IrrelevantAbstraction -> assertBool "" True
    Left _ -> assertBool "wrong renaming error" False
    _ -> assertBool "renaming succeeded when it should have failed" False

-- Checks that `forall a b . a -> !a` triggers the overdeterminance checker.
testDodgyIdT :: IO ()
testDodgyIdT = do
  let idT =
        CompT count2 $ Abstraction (BoundAt Z ix0) :--:> ReturnT (Abstraction (BoundAt Z ix0))
  let result = runRenameM . renameCompT $ idT
  case result of
    Left OverdeterminateAbstraction -> assertBool "" True
    Left _ -> assertBool "wrong renaming error" False
    _ -> assertBool "renaming succeeded when it should have failed" False

-- Checks that `forall a b. a -> !(b -> !a)` triggers the overdeterminance checker.
testDodgyConstT :: IO ()
testDodgyConstT = do
  let constT =
        CompT count2 $
          Abstraction (BoundAt Z ix0)
            :--:> ReturnT (ThunkT (CompT count0 $ Abstraction (BoundAt (S Z) ix1) :--:> ReturnT (Abstraction (BoundAt (S Z) ix0))))
  let result = runRenameM . renameCompT $ constT
  case result of
    Left OverdeterminateAbstraction -> assertBool "" True
    Left _ -> assertBool "wrong renaming error" False
    _ -> assertBool "renaming succeeded when it should have failed" False

-- Checks that `forall a . b -> !a` triggers the variable indexing checker.
testIndexingIdT :: IO ()
testIndexingIdT = do
  let t =
        CompT count1 $
          Abstraction (BoundAt Z ix0) :--:> ReturnT (Abstraction (BoundAt Z ix1))
  let result = runRenameM . renameCompT $ t
  case result of
    Left (InvalidAbstractionReference trueLevel ix) -> do
      assertEqual "" trueLevel 1
      assertEqual "" ix ix1
    Left _ -> assertBool "wrong renaming error" False
    _ -> assertBool "renaming succeeded when it should have failed" False

-- Helpers

assertRight ::
  forall (a :: Type) (b :: Type).
  (b -> IO ()) ->
  Either a b ->
  IO ()
assertRight f = \case
  Left _ -> assertBool "renamer errored" False
  Right actual -> f actual

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
                BuiltinNested . ListT count0 <$> go (size `quot` 4),
                BuiltinNested <$> (PairT count0 <$> go (size `quot` 4) <*> go (size `quot` 4)),
                ThunkT . CompT count0 <$> (NonEmpty.consV <$> go (size `quot` 4) <*> liftArbitrary (go (size `quot` 4)))
              ]
  {-# INLINEABLE shrink #-}
  shrink (Concrete v) =
    Concrete <$> case v of
      -- impossible
      Abstraction _ -> []
      ThunkT (CompT _ ts) ->
        -- Note (Koz, 06/04/2025): This is needed because non-empty Vectors
        -- don't have Arbitrary instances.
        ThunkT . CompT count0 <$> do
          let asList = NonEmpty.toList ts
          shrunk <- fmap coerce . shrink . fmap Concrete $ asList
          case shrunk of
            [] -> []
            x : xs -> pure (NonEmpty.consV x . Vector.fromList $ xs)
      -- Can't shrink this
      BuiltinFlat _ -> []
      BuiltinNested t ->
        BuiltinNested <$> case t of
          ListT _ t' -> do
            Concrete shrunk <- shrink (Concrete t')
            pure . ListT count0 $ shrunk
          PairT _ t1 t2 -> do
            Concrete shrunkT1 <- shrink (Concrete t1)
            Concrete shrunkT2 <- shrink (Concrete t2)
            [PairT count0 shrunkT1 t2, PairT count0 t1 shrunkT2]
