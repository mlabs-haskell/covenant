{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Control.Applicative ((<|>))
import Control.Monad (guard, void)
import Covenant.ASG
  ( ASG,
    ASGBuilder,
    ASGNode (ACompNode),
    CompNodeInfo
      ( Builtin1,
        Builtin2,
        Builtin3
      ),
    CovenantError (EmptyASG, TopLevelError, TopLevelValue, TypeError),
    CovenantTypeError
      ( ApplyCompType,
        ApplyToError,
        ApplyToValType,
        ForceCompType,
        ForceError,
        ForceNonThunk,
        NoSuchArgument,
        OutOfScopeTyVar,
        ThunkError,
        ThunkValType
      ),
    Id,
    Ref (AnArg, AnId),
    ValNodeInfo (Lit),
    app,
    arg,
    boundTyVar,
    builtin1,
    builtin2,
    builtin3,
    err,
    force,
    lam,
    lit,
    runASGBuilder,
    thunk,
    topLevelNode,
  )
import Covenant.Constant (typeConstant)
import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index (Index, intIndex, ix0, ix1)
import Covenant.Prim
  ( typeOneArgFunc,
    typeThreeArgFunc,
    typeTwoArgFunc,
  )
import Covenant.Test (Concrete (Concrete))
import Covenant.Type
  ( AbstractTy,
    CompT (Comp0, Comp1, Comp2, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    ValT(ThunkT),
    arity,
    tyvar,
  )
import Covenant.Util (pattern ConsV, pattern NilV)
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Vector qualified as Vector
import Optics.Core (preview, review)
import Test.QuickCheck
  ( Gen,
    Property,
    arbitrary,
    conjoin,
    counterexample,
    forAllShrinkShow,
    liftShrink,
    listOf,
    property,
    shrink,
    (===),
  )
import Test.Tasty (TestTree, adjustOption, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "ASG" $
    [ testCase "empty ASG does not compile" unitEmptyASG,
      testCase "single error does not compile" unitSingleError,
      testCase "forcing an error does not compile" unitForceError,
      testCase "thunking an error does not compile" unitThunkError,
      testProperty "toplevel constant does not compile" propTopLevelConstant,
      testProperty "toplevel one-arg builtin compiles and has the right type" propTopLevelBuiltin1,
      testProperty "toplevel two-arg builtin compiles and has the right type" propTopLevelBuiltin2,
      testProperty "toplevel three-arg builtin compiles and has the right type" propTopLevelBuiltin3,
      testProperty "forcing a thunk has the same type as what the thunk wraps" propForceThunk,
      testProperty "forcing a computation type does not compile" propForceComp,
      testProperty "forcing a non-thunk value type does not compile" propForceNonThunk,
      testProperty "thunking a value type does not compile" propThunkValType,
      testProperty "applying arguments to a value does not compile" propApplyToVal,
      testProperty "applying arguments to an error does not compile" propApplyToError,
      testProperty "passing computations as arguments does not compile" propApplyComp,
      testProperty "requesting a non-existent argument does not compile" propNonExistentArg,
      testProperty "requesting an argument that exists compiles" propExistingArg,
      newLamTest1,
      boundTyVarHappy,
      boundTyVarShouldFail
    ]
  where
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 10_000

-- Units

unitEmptyASG :: IO ()
unitEmptyASG = do
  let builtUp = pure ()
  let expected = Left EmptyASG
  let actual = runASGBuilder M.empty builtUp
  assertEqual "" expected actual

unitSingleError :: IO ()
unitSingleError = do
  let builtUp = err
  let expected = Left TopLevelError
  let actual = runASGBuilder M.empty builtUp
  assertEqual "" expected actual

unitForceError :: IO ()
unitForceError = do
  let builtUp = err >>= \i -> force (AnId i)
  let result = runASGBuilder M.empty builtUp
  case result of
    Left (TypeError _ ForceError) -> pure ()
    _ -> assertFailure $ "Unexpected result: " <> show result

unitThunkError :: IO ()
unitThunkError = do
  let builtUp = err >>= thunk
  let result = runASGBuilder M.empty builtUp
  case result of
    Left (TypeError _ ThunkError) -> pure ()
    _ -> assertFailure $ "Unexpected result: " <> show result

-- Properties

propTopLevelConstant :: Property
propTopLevelConstant = forAllShrinkShow arbitrary shrink show $ \c ->
  let builtUp = AnId <$> lit c
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
      (a -> ASGBuilder Id) ->
      a ->
      (ASGBuilder Id, ASGBuilder Id)
    mkComps f x =
      let comp = f x
          forceThunkComp = do
            i <- comp
            thunkI <- thunk i
            force (AnId thunkI)
       in (comp, forceThunkComp)


propForceComp :: Property
propForceComp = forAllShrinkShow arbitrary shrink show $ \x ->
  let comp = AnId <$> do
        i <- case x of
          Left bi1 -> builtin1 bi1
          Right (Left bi2) -> builtin2 bi2
          Right (Right bi3) -> builtin3 bi3
        force (AnId i)
      expectedT = case x of
        Left bi1 -> typeOneArgFunc bi1
        Right (Left bi2) -> typeTwoArgFunc bi2
        Right (Right bi3) -> typeThreeArgFunc bi3
   in withCompilationFailure comp $ \case
        TypeError _ (ForceCompType actualT) -> expectedT === actualT
        TypeError _ err' -> failWrongTypeError err'
        err' -> failWrongError err'

propForceNonThunk :: Property
propForceNonThunk = forAllShrinkShow arbitrary shrink show $ \c ->
  let comp = AnId <$> do
        i <- lit c
        force (AnId i)
   in withCompilationFailure comp $ \case
        TypeError _ (ForceNonThunk actualT) -> typeConstant c === actualT
        TypeError _ err' -> failWrongTypeError err'
        err' -> failWrongError err'

propThunkValType :: Property
propThunkValType = forAllShrinkShow arbitrary shrink show $ \c ->
  let comp = AnId <$> do
        i <- lit c
        thunk i
   in withCompilationFailure comp $ \case
        TypeError _ (ThunkValType actualT) -> typeConstant c === actualT
        TypeError _ err' -> failWrongTypeError err'
        err' -> failWrongError err'

propApplyToVal :: Property
propApplyToVal = forAllShrinkShow arbitrary shrink show $ \c args ->
  let comp = AnId <$> do
        args' <- traverse (fmap AnId . lit) args
        i <- lit c
        app i args'
   in withCompilationFailure comp $ \case
        TypeError _ (ApplyToValType t) -> typeConstant c === t
        TypeError _ err' -> failWrongTypeError err'
        err' -> failWrongError err'

propApplyToError :: Property
propApplyToError = forAllShrinkShow arbitrary shrink show $ \args ->
  let comp = AnId <$> do
        args' <- traverse (fmap AnId . lit) args
        i <- err
        app i args'
   in withCompilationFailure comp $ \case
        TypeError _ ApplyToError -> property True
        TypeError _ err' -> failWrongTypeError err'
        err' -> failWrongError err'

-- We use only builtins for this test, and specifically a one-argument builtin
-- for the thing being applied to, but this should still demonstrate the
-- behaviour as we expect
propApplyComp :: Property
propApplyComp = forAllShrinkShow arbitrary shrink show $ \f arg1 ->
  let t = case arg1 of
        Left bi1 -> typeOneArgFunc bi1
        Right (Left bi2) -> typeTwoArgFunc bi2
        Right (Right bi3) -> typeThreeArgFunc bi3

      comp = AnId <$> do
        i <- builtin1 f
        arg' <- case arg1 of
          Left bi1 -> builtin1 bi1
          Right (Left bi2) -> builtin2 bi2
          Right (Right bi3) -> builtin3 bi3
        app i (Vector.singleton . AnId $ arg')
   in withCompilationFailure comp $ \case
        TypeError _ (ApplyCompType actualT) -> t === actualT
        TypeError _ err' -> failWrongTypeError err'
        err' -> failWrongError err'

propNonExistentArg :: Property
propNonExistentArg = forAllShrinkShow arbitrary shrink show $ \(db, index) ->
  let comp = arg db index >>= \i -> pure $ AnArg i
   in withCompilationFailure comp $ \case
        TypeError _ (NoSuchArgument db' index') -> conjoin [db === db', index === index']
        TypeError _ err' -> failWrongTypeError err'
        err' -> failWrongError err'

-- Generate a lambda taking an arbitrary (positive) number of arguments, plus a
-- positional index, then return that argument in the body. The type of the
-- lambda we get back should match.
propExistingArg :: Property
propExistingArg = forAllShrinkShow gen shr show $ \(t, index) ->
  let comp = lam t $ do
        arg1 <- arg Z index
        pure (AnArg arg1)
   in withCompilationSuccess comp $ \asg ->
        withToplevelCompNode asg $ \t' _ ->
          t' === t
  where
    gen :: Gen (CompT AbstractTy, Index "arg")
    gen = do
      Concrete argT <- arbitrary
      prefixArgs <- listOf (arbitrary @Concrete)
      suffixArgs <- listOf (arbitrary @Concrete)
      -- We know that lengths can't be negative, but GHC doesn't
      let index = fromJust . preview intIndex $ length prefixArgs
      let args = Vector.fromList $ coerce prefixArgs <> [argT] <> coerce suffixArgs
      pure (Comp0 $ ArgsAndResult args argT, index)
    -- We shrink only in the index and the number of arguments, as shrinking the
    -- argument types themselves doesn't change anything
    shr :: (CompT AbstractTy, Index "arg") -> [(CompT AbstractTy, Index "arg")]
    shr (t@(CompN _ (ArgsAndResult args _)), index)
      | arity t <= 1 = []
      | index == ix0 = do
          args' <- liftShrink (const []) . fmap Concrete $ args
          case args' of
            NilV -> [] -- no arguments left to use
            ConsV (Concrete res') _ -> pure (Comp0 (ArgsAndResult (coerce args') res'), index)
      | otherwise =
          let shrinkOnIndex = do
                index' <- shrink index
                let indexAsInt = review intIndex index
                case args Vector.!? indexAsInt of
                  Nothing -> [] -- Should be impossible
                  Just res' -> pure (Comp0 (ArgsAndResult args res'), index')
              shrinkOnArgs = do
                args' <- liftShrink (const []) . fmap Concrete $ args
                let indexAsInt = review intIndex index
                guard (indexAsInt < Vector.length args')
                case args' Vector.!? indexAsInt of
                  Nothing -> [] -- Should be impossible
                  Just (Concrete res') -> pure (Comp0 (ArgsAndResult (coerce args') res'), index)
           in shrinkOnIndex <|> shrinkOnArgs

boundTyVarHappy :: TestTree
boundTyVarHappy = testCase "boundTyVarHappy" . run $ do
  lam lamTy $ do
    arg1 <- AnArg <$> arg Z ix0
    void $ boundTyVar Z ix0
    pure arg1
  where
    lamTy :: CompT AbstractTy
    lamTy = Comp1 $ tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)

    run :: forall (a :: Type). ASGBuilder a -> IO ()
    run act = case runASGBuilder M.empty act of
      Left err' -> assertFailure . show $ err'
      Right {} -> pure ()

boundTyVarShouldFail :: TestTree
boundTyVarShouldFail = testCase "boundTyVarShouldFail" . run $ boundTyVar Z ix0
  where
    run :: forall (a :: Type). (Show a) => ASGBuilder a -> IO ()
    run act = case runASGBuilder M.empty act of
      Left (TypeError _ (OutOfScopeTyVar db argpos)) ->
        if db == Z && argpos == ix0
          then pure ()
          else assertFailure $ "Expected OutOfScopeTyVar error for Z, ix0 but got: " <> show db <> ", " <> show argpos
      Left err' -> assertFailure $ "Expected an OutofScopeTyVar error, but got: " <> show err'
      Right x -> assertFailure $ "Expected boundTyVar to fail, but got: " <> show x


-- TODO: better name
newLamTest1 :: TestTree
newLamTest1 = testCase "new lam test 1" $ case runASGBuilder M.empty fn of
  Left err' -> assertFailure (show err')
  Right{} -> pure ()
 where
   fn :: ASGBuilder Id
   fn = lam expected $ do
     f <- arg Z ix0 >>= force . AnArg
     a <- AnArg <$> arg Z ix1
     AnId <$> app f (Vector.singleton a) 

   expected :: CompT AbstractTy
   expected = Comp2
              $ ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> ReturnT (tyvar (S Z) ix1))
                :--:> tyvar Z ix0
                :--:> ReturnT (tyvar Z ix1)


-- Helpers

failWrongTypeError :: CovenantTypeError -> Property
failWrongTypeError err' = failWithCounterExample ("Unexpected type error: " <> show err')

failWrongError :: CovenantError -> Property
failWrongError err' = failWithCounterExample ("Unexpected error: " <> show err')

withCompilationFailure :: ASGBuilder Ref -> (CovenantError -> Property) -> Property
withCompilationFailure comp cb = case runASGBuilder M.empty comp of
  Left err' -> cb err'
  Right asg -> failWithCounterExample ("Unexpected success: " <> show asg)

withCompilationSuccess :: ASGBuilder Id -> (ASG -> Property) -> Property
withCompilationSuccess comp cb = case runASGBuilder M.empty comp of
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

{- NOTE: Not 100% sure I won't need these 
withExpectedId :: Ref -> (Id -> Property) -> Property
withExpectedId r cb = case r of
  AnId i -> cb i
  AnArg arg' -> failWithCounterExample ("Unexpected argument: " <> show arg')

withExpectedValNode :: Id -> ASG -> (ValT AbstractTy -> ValNodeInfo -> Property) -> Property
withExpectedValNode i asg cb = case nodeAt i asg of
  AValNode t info -> cb t info
  node -> failWithCounterExample ("Unexpected node: " <> show node)
--}
