module Main (main) where

import Covenant.ASG
  ( ASGNode (ACompNode, AValNode),
    CompNodeInfo
      ( Builtin1,
        Builtin2,
        Builtin3,
        Return
      ),
    CovenantError (EmptyASG, TopLevelError, TopLevelValue),
    Ref (AnArg, AnId),
    ValNodeInfo (Lit),
    builtin1,
    builtin2,
    builtin3,
    err,
    lit,
    nodeAt,
    ret,
    runASGBuilder,
    topLevelNode,
  )
import Covenant.Constant (typeConstant)
import Covenant.Prim (typeOneArgFunc, typeThreeArgFunc, typeTwoArgFunc)
import Covenant.Type (CompT (Comp0), CompTBody (ReturnT))
import Test.QuickCheck
  ( Property,
    arbitrary,
    counterexample,
    forAllShrinkShow,
    property,
    shrink,
    (.&&.),
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
        Right asg -> case topLevelNode asg of
          ACompNode t info -> case info of
            Builtin1 bi -> t === typeOneArgFunc bi1 .&&. bi === bi1
            _ ->
              counterexample ("Unexpected CompNodeInfo: " <> show info)
                . property
                $ False
          node ->
            counterexample ("Unexpected toplevel node: " <> show node)
              . property
              $ False

propTopLevelBuiltin2 :: Property
propTopLevelBuiltin2 = forAllShrinkShow arbitrary shrink show $ \bi2 ->
  let builtUp = builtin2 bi2
      actual = runASGBuilder builtUp
   in case actual of
        Left err' ->
          counterexample ("Unexpected failure: " <> show err')
            . property
            $ False
        Right asg -> case topLevelNode asg of
          ACompNode t info -> case info of
            Builtin2 bi -> t === typeTwoArgFunc bi2 .&&. bi === bi2
            _ ->
              counterexample ("Unexpected CompNodeInfo: " <> show info)
                . property
                $ False
          node ->
            counterexample ("Unexpected toplevel node: " <> show node)
              . property
              $ False

propTopLevelBuiltin3 :: Property
propTopLevelBuiltin3 = forAllShrinkShow arbitrary shrink show $ \bi3 ->
  let builtUp = builtin3 bi3
      actual = runASGBuilder builtUp
   in case actual of
        Left err' ->
          counterexample ("Unexpected failure: " <> show err')
            . property
            $ False
        Right asg -> case topLevelNode asg of
          ACompNode t info -> case info of
            Builtin3 bi -> t === typeThreeArgFunc bi3 .&&. bi === bi3
            _ ->
              counterexample ("Unexpected CompNodeInfo: " <> show info)
                . property
                $ False
          node ->
            counterexample ("Unexpected toplevel node: " <> show node)
              . property
              $ False

propTopLevelReturn :: Property
propTopLevelReturn = forAllShrinkShow arbitrary shrink show $ \c ->
  let builtUp = lit c >>= \i -> ret (AnId i)
      actual = runASGBuilder builtUp
   in case actual of
        Left err' ->
          counterexample ("Unexpected failure: " <> show err')
            . property
            $ False
        Right asg -> case topLevelNode asg of
          ACompNode t info -> case info of
            Return r -> case r of
              AnId i -> case nodeAt i asg of
                AValNode t' info' -> case info' of
                  Lit c' ->
                    let cT = typeConstant c
                     in c' === c .&&. cT === t' .&&. t === Comp0 (ReturnT cT)
                  _ ->
                    counterexample ("Unexpected ValNodeInfo: " <> show info')
                      . property
                      $ False
                node' ->
                  counterexample ("Unexpected node: " <> show node')
                    . property
                    $ False
              AnArg arg ->
                counterexample ("Unexpected argument: " <> show arg)
                  . property
                  $ False
            _ ->
              counterexample ("Unexpected CompNodeInfo: " <> show info)
                . property
                $ False
          node ->
            counterexample ("Unexpected toplevel node: " <> show node)
              . property
              $ False
