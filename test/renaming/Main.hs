{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index
  ( ix0,
    ix1,
  )
import Covenant.Test (Concrete (Concrete))
import Covenant.Type
  ( BuiltinFlatT
      ( BLS12_381_G1_ElementT,
        BLS12_381_G2_ElementT,
        BLS12_381_MlResultT,
        BoolT,
        ByteStringT,
        IntegerT,
        StringT,
        UnitT
      ),
    CompT (Comp0, Comp1, Comp2),
    RenameError
      ( InvalidAbstractionReference,
        UndeterminedAbstraction
      ),
    Renamed (Unifiable, Wildcard),
    ValT (Abstraction, BuiltinFlat, ThunkT),
    renameCompT,
    renameValT,
    runRenameM,
    tyvar,
    pattern ReturnT,
    pattern (:--:>),
  )
import Data.Functor.Classes (liftEq)
import Data.Kind (Type)
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Property,
    forAllShrinkShow,
  )
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
          testCase "MlResultT" $ testFlat BLS12_381_MlResultT
        ],
      testProperty "Nested concrete types" propNestedConcrete,
      testCase "forall a . a -> !a" testIdT,
      testCase "forall a b . a -> b -> !a" testConstT,
      testCase "forall a . a -> !(forall b . b -> !a)" testConstT2,
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
  let idT = Comp1 $ tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)
  let expected =
        Comp1 $
          Abstraction (Unifiable ix0)
            :--:> ReturnT (Abstraction (Unifiable ix0))
  let result = runRenameM . renameCompT $ idT
  assertRight (assertEqual "" expected) result

-- Checks that `forall a b . a -> b -> !a` correctly renames.
testConstT :: IO ()
testConstT = do
  let constT = Comp2 $ tyvar Z ix0 :--:> tyvar Z ix1 :--:> ReturnT (tyvar Z ix0)
  let expected =
        Comp2 $
          Abstraction (Unifiable ix0)
            :--:> Abstraction (Unifiable ix1)
            :--:> ReturnT (Abstraction (Unifiable ix0))
  let result = runRenameM . renameCompT $ constT
  assertRight (assertEqual "" expected) result

-- Checks that `forall a . a -> !(forall b . b -> !a)` correctly renames.
testConstT2 :: IO ()
testConstT2 = do
  let constT =
        Comp1 $ tyvar Z ix0 :--:> ReturnT (ThunkT . Comp1 $ tyvar Z ix0 :--:> ReturnT (tyvar (S Z) ix0))
  let expected =
        Comp1 $
          Abstraction (Unifiable ix0)
            :--:> ReturnT
              ( ThunkT . Comp1 $
                  Abstraction (Wildcard 1 2 ix0)
                    :--:> ReturnT (Abstraction (Unifiable ix0))
              )
  let result = runRenameM . renameCompT $ constT
  assertRight (assertEqual "" expected) result

-- Checks that `forall a b . a -> !a` triggers the undetermined variable checker.
testDodgyIdT :: IO ()
testDodgyIdT = do
  let idT = Comp2 $ tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)
  let result = runRenameM . renameCompT $ idT
  case result of
    Left UndeterminedAbstraction{} -> assertBool "" True
    Left _ -> assertBool "wrong renaming error" False
    _ -> assertBool "renaming succeeded when it should have failed" False

-- Checks that `forall a b. a -> !(b -> !a)` triggers the undetermined variable checker.
testDodgyConstT :: IO ()
testDodgyConstT = do
  let constT =
        Comp2 $
          tyvar Z ix0
            :--:> ReturnT (ThunkT . Comp0 $ tyvar (S Z) ix1 :--:> ReturnT (tyvar (S Z) ix0))
  let result = runRenameM . renameCompT $ constT
  case result of
    Left UndeterminedAbstraction{} -> assertBool "" True
    Left _ -> assertBool "wrong renaming error" False
    _ -> assertBool "renaming succeeded when it should have failed" False

-- Checks that `forall a . b -> !a` triggers the variable indexing checker.
testIndexingIdT :: IO ()
testIndexingIdT = do
  let t = Comp1 $ tyvar Z ix0 :--:> ReturnT (tyvar Z ix1)
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
