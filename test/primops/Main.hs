module Main (main) where

import Covenant.Prim
  ( typeOneArgFunc,
    typeThreeArgFunc,
    typeTwoArgFunc,
  )
import Covenant.Type
  ( AbstractTy (BoundAt),
    CompT,
    Renamed (Unifiable),
    arity,
    renameCompT,
    runRenameM,
  )
import Data.Functor.Classes (liftEq)
import Data.Kind (Type)
import Test.QuickCheck
  ( Arbitrary (arbitrary),
    Property,
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
          testProperty "Three-argument primops take three arguments" prop3Args
          --         testProperty "Six-argument primops take six arguments" prop6Args
        ],
      testGroup
        "Renaming"
        [ testProperty "One-argument primops rename correctly" prop1Rename,
          testProperty "Two-argument primops rename correctly" prop2Rename,
          testProperty "Three-argument primops rename correctly" prop3Rename
          -- testProperty "Six-argument primops rename correctly" prop6Rename
        ]
    ]

-- Test cases and properties

prop1Arg :: Property
prop1Arg = mkArgProp typeOneArgFunc 1

prop1Rename :: Property
prop1Rename = mkRenameProp typeOneArgFunc

prop2Args :: Property
prop2Args = mkArgProp typeTwoArgFunc 2

prop2Rename :: Property
prop2Rename = mkRenameProp typeTwoArgFunc

prop3Args :: Property
prop3Args = mkArgProp typeThreeArgFunc 3

prop3Rename :: Property
prop3Rename = mkRenameProp typeThreeArgFunc

{-
prop6Args :: Property
prop6Args = mkArgProp typeSixArgFunc 6

prop6Rename :: Property
prop6Rename = mkRenameProp typeSixArgFunc
-}

-- Helpers

mkArgProp ::
  forall (a :: Type).
  (Show a, Arbitrary a) =>
  (a -> CompT AbstractTy) ->
  Int ->
  Property
mkArgProp typingFun targetArity = forAll arbitrary $ \f ->
  let t = typingFun f
   in arity t === targetArity

mkRenameProp ::
  forall (a :: Type).
  (Show a, Arbitrary a) =>
  (a -> CompT AbstractTy) ->
  Property
mkRenameProp typingFun = forAll arbitrary $ \f ->
  let t = typingFun f
      result = runRenameM . renameCompT $ t
   in case result of
        Left err -> counterexample (show err) False
        Right renamed -> property $ liftEq eqRenamedVar t renamed

-- In our context, the _only_ variables we have are unifiable. If we see
-- anything else, we know we've messed up somewhere. Furthermore, the indexes
-- should 'line up'.
eqRenamedVar :: AbstractTy -> Renamed -> Bool
eqRenamedVar (BoundAt _ ix) = \case
  Unifiable ix' -> ix == ix'
  _ -> False
