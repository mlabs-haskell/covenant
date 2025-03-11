module Main (main) where

import Covenant.Prim
  ( typeOneArgFunc,
    typeSixArgFunc,
    typeThreeArgFunc,
    typeTwoArgFunc,
  )
import Covenant.Type
  ( AbstractTy (BoundAt),
    CompT (CompT),
    Renamed (Unifiable),
    renameCompT,
    runRenameM,
  )
import Data.Functor.Classes (liftEq)
import Data.Kind (Type)
import Data.Vector.NonEmpty qualified as NonEmpty
import Test.QuickCheck
  ( Property,
    arbitrary,
    counterexample,
    forAll,
    property,
    (===),
  )
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.QuickCheck (testProperty)

main :: IO ()
main =
  defaultMain . testGroup "Primops" $
    [ -- Since there are so few primops, we don't increase the test count
      -- beyond the default 100, as it would just be redundant.
      testGroup
        "Arity"
        [ testProperty "One-argument primops take one argument" prop1Arg,
          testProperty "Two-argument primops take two arguments" prop2Args,
          testProperty "Three-argument primops take three arguments" prop3Args,
          testProperty "Six-argument primops take six arguments" prop6Args
        ],
      testGroup
        "Renaming"
        [ testProperty "One-argument primops rename correctly" prop1Rename,
          testProperty "Two-argument primops rename correctly" prop2Rename,
          testProperty "Three-argument primops rename correctly" prop3Rename,
          testProperty "Six-argument primops rename correctly" prop6Rename
        ]
    ]

-- Test cases and properties

prop1Arg :: Property
prop1Arg = forAll arbitrary $ \oneArg ->
  let t = typeOneArgFunc oneArg
   in arity t === 1

prop1Rename :: Property
prop1Rename = forAll arbitrary $ \oneArg ->
  let t = typeOneArgFunc oneArg
      result = runRenameM . renameCompT $ t
   in case result of
        Left err -> counterexample (show err) False
        Right renamed -> property $ liftEq eqRenamedVar t renamed

prop2Args :: Property
prop2Args = forAll arbitrary $ \twoArg ->
  let t = typeTwoArgFunc twoArg
   in arity t === 2

prop2Rename :: Property
prop2Rename = forAll arbitrary $ \twoArg ->
  let t = typeTwoArgFunc twoArg
      result = runRenameM . renameCompT $ t
   in case result of
        Left err -> counterexample (show err) False
        Right renamed -> property $ liftEq eqRenamedVar t renamed

prop3Args :: Property
prop3Args = forAll arbitrary $ \threeArg ->
  let t = typeThreeArgFunc threeArg
   in arity t === 3

prop3Rename :: Property
prop3Rename = forAll arbitrary $ \threeArg ->
  let t = typeThreeArgFunc threeArg
      result = runRenameM . renameCompT $ t
   in case result of
        Left err -> counterexample (show err) False
        Right renamed -> property $ liftEq eqRenamedVar t renamed

prop6Args :: Property
prop6Args = forAll arbitrary $ \sixArg ->
  let t = typeSixArgFunc sixArg
   in arity t === 6

prop6Rename :: Property
prop6Rename = forAll arbitrary $ \sixArg ->
  let t = typeSixArgFunc sixArg
      result = runRenameM . renameCompT $ t
   in case result of
        Left err -> counterexample (show err) False
        Right renamed -> property $ liftEq eqRenamedVar t renamed

-- Helpers

arity :: forall (a :: Type). CompT a -> Int
arity (CompT _ xs) = NonEmpty.length xs - 1

-- In our context, the _only_ variables we have are unifiable. If we see
-- anything else, we know we've messed up somewhere. Furthermore, the indexes
-- should 'line up'.
eqRenamedVar :: AbstractTy -> Renamed -> Bool
eqRenamedVar (BoundAt _ ix) = \case
  Unifiable ix' -> ix == ix'
  _ -> False
