module Main (main) where

import Covenant.ASG
  ( ASG,
    ASGBuilder,
    ASGNode (ACompNode, AValNode),
    CompNodeInfo
      ( Builtin1,
        Builtin2,
        Builtin3,
        Return
      ),
    CovenantError (EmptyASG, TopLevelError, TopLevelValue),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (Lit),
    builtin1,
    builtin2,
    builtin3,
    err,
    force,
    lit,
    nodeAt,
    ret,
    runASGBuilder,
    thunk,
    topLevelNode,
  )
import Covenant.Constant (typeConstant)
import Covenant.Prim
  ( typeOneArgFunc,
    typeThreeArgFunc,
    typeTwoArgFunc,
  )
import Covenant.Type
  ( AbstractTy,
    CompT (Comp0),
    CompTBody (ReturnT),
    ValT,
  )
import Data.Kind (Type)
import Test.QuickCheck
  ( Property,
    arbitrary,
    conjoin,
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
      testProperty "toplevel return compiles and has the right type" propTopLevelReturn,
      testProperty "forcing a thunk has the same type as what the thunk wraps" propForceThunk
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
   in withCompilationFailure builtUp $ \case
        TopLevelValue _ t info -> case info of
          Lit c' ->
            conjoin
              [ typeConstant c === t,
                c' === c
              ]
          _ -> failUnexpectedValNodeInfo info
        err' -> failWithCounterExample ("Unexpected failure type: " <> show err')

propTopLevelBuiltin1 :: Property
propTopLevelBuiltin1 = forAllShrinkShow arbitrary shrink show $ \bi1 ->
  let builtUp = builtin1 bi1
   in withCompilationSuccess builtUp $ \asg ->
        withToplevelCompNode asg $ \t info ->
          case info of
            Builtin1 bi ->
              conjoin
                [ t === typeOneArgFunc bi1,
                  bi === bi1
                ]
            _ -> failUnexpectedCompNodeInfo info

propTopLevelBuiltin2 :: Property
propTopLevelBuiltin2 = forAllShrinkShow arbitrary shrink show $ \bi2 ->
  let builtUp = builtin2 bi2
   in withCompilationSuccess builtUp $ \asg ->
        withToplevelCompNode asg $ \t info ->
          case info of
            Builtin2 bi ->
              conjoin
                [ t === typeTwoArgFunc bi2,
                  bi === bi2
                ]
            _ -> failUnexpectedCompNodeInfo info

propTopLevelBuiltin3 :: Property
propTopLevelBuiltin3 = forAllShrinkShow arbitrary shrink show $ \bi3 ->
  let builtUp = builtin3 bi3
   in withCompilationSuccess builtUp $ \asg ->
        withToplevelCompNode asg $ \t info ->
          case info of
            Builtin3 bi ->
              conjoin
                [ t === typeThreeArgFunc bi3,
                  bi === bi3
                ]
            _ -> failUnexpectedCompNodeInfo info

propTopLevelReturn :: Property
propTopLevelReturn = forAllShrinkShow arbitrary shrink show $ \c ->
  let builtUp = lit c >>= \i -> ret (AnId i)
   in withCompilationSuccess builtUp $ \asg ->
        withToplevelCompNode asg $ \t info ->
          case info of
            Return r -> withExpectedId r $ \i ->
              withExpectedValNode i asg $ \t' info' ->
                case info' of
                  Lit c' ->
                    let cT = typeConstant c
                     in conjoin
                          [ c' === c,
                            cT === t',
                            t === Comp0 (ReturnT cT)
                          ]
                  _ -> failUnexpectedValNodeInfo info'
            _ -> failUnexpectedCompNodeInfo info

-- We use builtins only for this test, but this should demonstrate the
-- properties well enough
propForceThunk :: Property
propForceThunk = forAllShrinkShow arbitrary shrink show $ \x ->
  let (comp, forceThunkComp) = case x of
        Left bi1 -> mkComps builtin1 bi1
        Right (Left bi2) -> mkComps builtin2 bi2
        Right (Right bi3) -> mkComps builtin3 bi3
   in withCompilationSuccess comp $ \expectedASG ->
        withCompilationSuccess forceThunkComp $ \forceThunkASG ->
          withToplevelCompNode expectedASG $ \expectedT _ ->
            withToplevelCompNode forceThunkASG $ \actualT _ ->
              expectedT === actualT
  where
    mkComps ::
      forall (a :: Type).
      (a -> ASGBuilder Id) -> a -> (ASGBuilder Id, ASGBuilder Id)
    mkComps f x =
      let comp = f x
          forceThunkComp = do
            i <- comp
            thunkI <- thunk i
            force (AnId thunkI)
       in (comp, forceThunkComp)

-- Helpers

withCompilationFailure :: ASGBuilder Id -> (CovenantError -> Property) -> Property
withCompilationFailure comp cb = case runASGBuilder comp of
  Left err' -> cb err'
  Right asg -> failWithCounterExample ("Unexpected success: " <> show asg)

withCompilationSuccess :: ASGBuilder Id -> (ASG -> Property) -> Property
withCompilationSuccess comp cb = case runASGBuilder comp of
  Left err' -> failWithCounterExample ("Unexpected failure: " <> show err')
  Right asg -> cb asg

withToplevelCompNode :: ASG -> (CompT AbstractTy -> CompNodeInfo -> Property) -> Property
withToplevelCompNode asg cb = case topLevelNode asg of
  ACompNode t info -> cb t info
  node -> failWithCounterExample ("Unexpected toplevel node: " <> show node)

failWithCounterExample :: String -> Property
failWithCounterExample msg = counterexample msg . property $ False

failUnexpectedCompNodeInfo :: CompNodeInfo -> Property
failUnexpectedCompNodeInfo info =
  failWithCounterExample ("Unexpected CompNodeInfo: " <> show info)

failUnexpectedValNodeInfo :: ValNodeInfo -> Property
failUnexpectedValNodeInfo info =
  failWithCounterExample ("Unexpected ValNodeInfo: " <> show info)

withExpectedId :: Ref -> (Id -> Property) -> Property
withExpectedId r cb = case r of
  AnId i -> cb i
  AnArg arg -> failWithCounterExample ("Unexpected argument: " <> show arg)

withExpectedValNode :: Id -> ASG -> (ValT AbstractTy -> ValNodeInfo -> Property) -> Property
withExpectedValNode i asg cb = case nodeAt i asg of
  AValNode t info -> cb t info
  node -> failWithCounterExample ("Unexpected node: " <> show node)
