module Main (main) where

import Covenant.ASG
  ( CovenantError (EmptyASG, TopLevelError, TopLevelValue),
    builtin1,
    builtin2,
    builtin3,
    err,
    lit,
    ret,
    rootNode,
    runASGBuilder,
  )
import Covenant.Constant (typeConstant)
import Test.QuickCheck
  ( Property,
    arbitrary,
    counterexample,
    forAllShrinkShow,
    property,
    shrink,
    (===),
  )
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "ASG" $
    [ testCase "empty ASG does not compile" unitEmptyASG,
      testCase "single error does not compile" unitSingleError,
      testProperty "toplevel constant does not compile" propTopLevelConstant,
      testProperty "toplevel one-arg builtin compiles and has the right type" propTopLevelBuiltin1,
      testProperty "toplevel two-arg builtin compiles and has the right type" propTopLevelBuiltin2,
      testProperty "toplevel three-arg builtin compiles and has the right type" propTopLevelBuiltin3,
      testProperty "toplevel return compiles and has the right type" propTopLevelReturn
    ]
  where
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 10_000

-- Units

unitEmptyASG :: IO ()
unitEmptyASG = do
  let builtUp = pure ()
  let expected = Left EmptyASG
  let actual = runASGBuilder builtUp
  assertEqual "" expected actual

unitSingleError :: IO ()
unitSingleError = do
  let builtUp = err
  let expected = Left TopLevelError
  let actual = runASGBuilder builtUp
  assertEqual "" expected actual

-- Properties

propTopLevelConstant :: Property
propTopLevelConstant = forAllShrinkShow arbitrary shrink show $ \c ->
  let builtUp = lit c
      actual = runASGBuilder builtUp
   in case actual of
        Left (TopLevelValue _ t _) -> typeConstant c === t
        Left err' ->
          counterexample ("Unexpected failure type: " <> show err')
            . property
            $ False
        Right asg ->
          counterexample ("Unexpected success: " <> show asg)
            . property
            $ False

propTopLevelBuiltin1 :: Property
propTopLevelBuiltin1 = forAllShrinkShow arbitrary shrink show $ \bi1 ->
  let builtUp = builtin1 bi1
      actual = runASGBuilder builtUp
   in case actual of
        Left err' ->
          counterexample ("Unexpected failure: " <> show err')
            . property
            $ False
        Right asg -> _

propTopLevelBuiltin2 :: Property
propTopLevelBuiltin2 = forAllShrinkShow arbitrary shrink show $ \bi2 ->
  let builtUp = builtin2 bi2
      actual = runASGBuilder builtUp
   in case actual of
        Left err' ->
          counterexample ("Unexpected failure: " <> show err')
            . property
            $ False
        Right asg -> _

propTopLevelBuiltin3 :: Property
propTopLevelBuiltin3 = forAllShrinkShow arbitrary shrink show $ \bi3 ->
  let builtUp = builtin3 bi3
      actual = runASGBuilder builtUp
   in case actual of
        Left err' ->
          counterexample ("Unexpected failure: " <> show err')
            . property
            $ False
        Right asg -> _

propTopLevelReturn :: Property
propTopLevelReturn = forAllShrinkShow arbitrary shrink show $ \case
  Left bi1 ->
    let builtUp = builtin1 bi1 >>= \i -> ret (_ i)
        actual = runASGBuilder builtUp
     in _
  Right (Left bi2) ->
    let builtUp = builtin2 bi2 >>= \i -> ret (_ i)
        actual = runASGBuilder builtUp
     in _
  Right (Right bi3) ->
    let builtUp = builtin3 bi3 >>= \i -> ret (_ i)
        actual = runASGBuilder builtUp
     in _
