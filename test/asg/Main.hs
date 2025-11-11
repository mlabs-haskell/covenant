{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Control.Applicative ((<|>))
import Control.Monad (guard, void)
import Covenant.ASG
  ( ASG,
    ASGBuilder,
    ASGNode (ACompNode, AValNode, AnError),
    CompNodeInfo
      ( Builtin1,
        Builtin2,
        Builtin3
      ),
    CovenantError
      ( EmptyASG,
        TopLevelError,
        TopLevelValue,
        TypeError
      ),
    CovenantTypeError
      ( ApplyCompType,
        ApplyToError,
        ApplyToValType,
        BaseFunctorDoesNotExistFor,
        CataNonRigidAlgebra,
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
    app',
    arg,
    baseFunctorOf,
    boundTyVar,
    builtin1,
    builtin2,
    builtin3,
    cata,
    ctor,
    ctor',
    dataConstructor,
    defaultDatatypes,
    dtype,
    err,
    force,
    lam,
    lazyLam,
    lit,
    match,
    naturalBF,
    negativeBF,
    runASGBuilder,
    thunk,
    topLevelNode,
  )
import Covenant.Constant
  ( AConstant (AUnit, AnInteger),
    typeConstant,
  )
import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index (Index, intIndex, ix0, ix1, ix2)
import Covenant.Prim
  ( typeOneArgFunc,
    typeThreeArgFunc,
    typeTwoArgFunc,
  )
import Covenant.Test
  ( Concrete (Concrete),
    DebugASGBuilder,
    debugASGBuilder,
    tyAppTestDatatypes,
    typeIdTest,
  )
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT (ByteStringT, IntegerT, UnitT),
    CompT (Comp0, Comp1, Comp2, CompN),
    CompTBody (ArgsAndResult, ReturnT, (:--:>)),
    ValT (BuiltinFlat, Datatype, ThunkT),
    arity,
    boolT,
    byteStringT,
    integerT,
    tyvar,
  )
import Covenant.Util (pattern ConsV, pattern NilV)
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Vector qualified as Vector
import Data.Wedge (Wedge (Here, There), wedgeLeft)
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
import Test.Tasty.HUnit (Assertion, assertEqual, assertFailure, testCase)
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
      testCase "db indices are well behaved (non-datatype case)" newLamTest1,
      testCase "db indices are well behaved (datatype case)" newLamTest2,
      testCase "calling down an in-scope tyvar works" boundTyVarHappy,
      testCase "calling down an out-of-scope tyvar fails" boundTyVarShouldFail,
      nothingIntro,
      justConcreteIntro,
      justRigidIntro,
      justNothingIntro,
      testGroup
        "Catamorphisms"
        [ testCase "#Natural can tear down an Integer" unitCataNaturalF,
          testCase "#Negative can tear down an Integer" unitCataNegativeF,
          testCase "#ByteString can tear down a ByteString" unitCataByteStringF,
          testCase "Non-recursive type cata should fail" unitCataMaybeF,
          testCase "Cata with non-rigid algebra should fail" unitCataNonRigidF,
          testCase "<#List Integer Bool -> !Bool> with List Integer should be Bool" unitCataListInteger,
          testCase "<#List Integer r -> !r> with List Integer should be r" unitCataListIntegerRigid,
          testCase "<#List r Integer -> !Integer> with List r should be Integer" unitCataListRigid,
          testCase "<#List r (Maybe r) -> !Maybe r> with List r should be Maybe r" unitCataListMaybeRigid,
          testCase "introduction then cata elimination" unitCataIntroThenEliminate
        ],
      testGroup
        "Matching"
        [ matchMaybe,
          matchList,
          maybeToList
        ],
      testGroup
        "Opaque"
        [unifyOpaque],
      testGroup "matchOpaque" [matchOpaque]
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

-- Construct a function of type `Bool -> <Bool -> !Bool> -> Integer ->
-- !Bool`, whose body performs a cata over its third argument using the first
-- and second argument as handlers. The stated algebra type is `Natural Bool ->
-- !Bool`, where `Natural` refers to the natural-number base functor of
-- `Integer`. This should compile and type as expected.
unitCataNaturalF :: IO ()
unitCataNaturalF = do
  let algTy = Comp0 $ Datatype naturalBF [boolT] :--:> ReturnT boolT
  let resultTy =
        Comp0 $
          boolT
            :--:> ThunkT (Comp0 $ boolT :--:> ReturnT boolT)
            :--:> integerT
            :--:> ReturnT boolT
  let comp = lam resultTy $ do
        armZ <- arg Z ix0
        armS <- arg Z ix1
        x <- arg Z ix2
        AnId <$> cata algTy (Vector.fromList . fmap AnArg $ [armZ, armS]) (AnArg x)
  withCompilationSuccessUnit comp (matchesType resultTy)

-- Construct a function of type `Bool -> <Bool -> !Bool> -> Integer ->
-- !Bool`, whose body performs a cata over its third argument using the first
-- and second argument as handlers. The stated algebra type is `Negative Bool -> !Bool`,
-- where `Negative` refers to the negative-number base functor of `Integer`.
-- This should compile and type as expected.
unitCataNegativeF :: IO ()
unitCataNegativeF = do
  let algTy = Comp0 $ Datatype negativeBF [boolT] :--:> ReturnT boolT
  let resultTy =
        Comp0 $
          boolT
            :--:> ThunkT (Comp0 $ boolT :--:> ReturnT boolT)
            :--:> integerT
            :--:> ReturnT boolT
  let comp = lam resultTy $ do
        armZ <- arg Z ix0
        armS <- arg Z ix1
        x <- arg Z ix2
        AnId <$> cata algTy (Vector.fromList . fmap AnArg $ [armZ, armS]) (AnArg x)
  withCompilationSuccessUnit comp (matchesType resultTy)

-- Construct a function of type `Bool -> <Integer -> Bool -> !Bool>
-- -> ByteString -> !Bool>, whose body performs a cata over its third argument
-- using the first and second argument as handlers. The stated algebra type is
-- `ByteString# Bool -> !Bool`, where `ByteString#` refers to the base functor
-- of `ByteString`. This should compile and type as expected.
unitCataByteStringF :: IO ()
unitCataByteStringF = do
  let algTy = do
        bfName <- baseFunctorOf "ByteString"
        pure . Comp0 $ Datatype bfName [boolT] :--:> ReturnT boolT
  let resultTy =
        Comp0 $
          boolT
            :--:> ThunkT (Comp0 $ integerT :--:> boolT :--:> ReturnT boolT)
            :--:> byteStringT
            :--:> ReturnT boolT
  let comp = lam resultTy $ do
        t <- algTy
        armNil <- arg Z ix0
        armCons <- arg Z ix1
        x <- arg Z ix2
        AnId <$> cata t (Vector.fromList . fmap AnArg $ [armNil, armCons]) (AnArg x)
  withCompilationSuccessUnit comp (matchesType resultTy)

-- Construct a function of type `forall a . Integer -> <a -> !Integer> ->
-- Maybe a -> !Integer`, whose body performs a cata over its third argument
-- using the first and second argument as handlers. The stated algebra type is
-- `Maybe# a Integer -> !Integer`, with `a` rigid. This should fail to compile,
-- indicating that `Maybe` lacks a base functor.
unitCataMaybeF :: IO ()
unitCataMaybeF = do
  let algTy = do
        bfName <- baseFunctorOf "Maybe"
        pure . Comp0 $ Datatype bfName [tyvar (S Z) ix0, integerT] :--:> ReturnT integerT
  let resultTy =
        Comp1 $
          integerT
            :--:> ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> ReturnT integerT)
            :--:> Datatype "Maybe" [tyvar Z ix0]
            :--:> ReturnT integerT
  let comp = lam resultTy $ do
        t <- algTy
        armNothing <- arg Z ix0
        armJust <- arg Z ix1
        x <- arg Z ix2
        AnId <$> cata t (Vector.fromList . fmap AnArg $ [armNothing, armJust]) (AnArg x)
  withCompilationFailureUnit comp $ \case
    TypeError _ (BaseFunctorDoesNotExistFor tyName) -> assertEqual "" "Maybe" tyName
    err' -> assertFailure $ "Failed with unexpected type of error: " <> show err'

-- Construct a function of type forall a . Maybe a -> <a -> Maybe a ->
-- !(Maybe a)> ->
-- List Integer -> !(Maybe Integer)`, whose body performs a cata over its third
-- argument using the first and second argument as handlers. The stated algebra
-- type is `forall b. List# b (Maybe b) -> !(Maybe b)`. This should fail to
-- compile due to a non-rigid algebra.
unitCataNonRigidF :: IO ()
unitCataNonRigidF = do
  let algTy = do
        listBfName <- baseFunctorOf "List"
        pure . Comp1 $ Datatype listBfName [tyvar Z ix0, Datatype "Maybe" [tyvar Z ix0]] :--:> ReturnT (Datatype "Maybe" [tyvar Z ix0])
  let resultTy =
        Comp1 $
          Datatype "Maybe" [tyvar (S Z) ix0]
            :--:> ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> Datatype "Maybe" [tyvar (S Z) ix0] :--:> ReturnT (Datatype "Maybe" [tyvar (S Z) ix0]))
            :--:> Datatype "List" [tyvar Z ix0]
            :--:> ReturnT (Datatype "Maybe" [tyvar Z ix0])
  let comp = lam resultTy $ do
        t <- algTy
        armNil <- arg Z ix0
        armCons <- arg Z ix1
        x <- arg Z ix2
        AnId <$> cata t (Vector.fromList . fmap AnArg $ [armNil, armCons]) (AnArg x)
  withCompilationFailureUnit comp $ \case
    TypeError _ (CataNonRigidAlgebra _) -> pure ()
    err' -> assertFailure $ "Failed with unexpected type of error: " <> show err'

-- Construct a function of type `Bool -> <Integer -> Bool -> !Bool> -> List
-- Integer -> !Bool`, whose body performs a cata over its third argument using
-- the first and second argument as handlers. The stated algebra type is `List#
-- Integer Bool -> !Bool`. This should compile and type as expected.
unitCataListInteger :: IO ()
unitCataListInteger = do
  let algTy = do
        listBfName <- baseFunctorOf "List"
        pure . Comp0 $ Datatype listBfName [integerT, boolT] :--:> ReturnT boolT
  let resultTy =
        Comp0 $
          boolT
            :--:> ThunkT (Comp0 $ integerT :--:> boolT :--:> ReturnT boolT)
            :--:> Datatype "List" [integerT]
            :--:> ReturnT boolT
  let comp = lam resultTy $ do
        t <- algTy
        armNil <- arg Z ix0
        armCons <- arg Z ix1
        x <- arg Z ix2
        AnId <$> cata t (Vector.fromList . fmap AnArg $ [armNil, armCons]) (AnArg x)
  withCompilationSuccessUnit comp (matchesType resultTy)

-- Construct a function of type `forall a . a -> <!Integer -> a -> !a> ->
-- List Integer -> !a>, whose body performs a cata over its third argument using
-- the first and second argument as handlers. The stated algebra type is `List#
-- Integer a -> !a`, with `a` rigid. This should compile and type as expected.
unitCataListIntegerRigid :: IO ()
unitCataListIntegerRigid = do
  let algTy = do
        listBfName <- baseFunctorOf "List"
        pure . Comp0 $ Datatype listBfName [integerT, tyvar (S Z) ix0] :--:> ReturnT (tyvar (S Z) ix0)
  let resultTy =
        Comp1 $
          tyvar Z ix0
            :--:> ThunkT (Comp0 $ integerT :--:> tyvar (S Z) ix0 :--:> ReturnT (tyvar (S Z) ix0))
            :--:> Datatype "List" [integerT]
            :--:> ReturnT (tyvar Z ix0)
  let comp = lam resultTy $ do
        t <- algTy
        armNil <- arg Z ix0
        armCons <- arg Z ix1
        x <- arg Z ix2
        AnId <$> cata t (Vector.fromList . fmap AnArg $ [armNil, armCons]) (AnArg x)
  withCompilationSuccessUnit comp (matchesType resultTy)

-- Construct a function of type `forall a . Integer -> <a -> Integer ->
-- !Integer> -> List a -> !Integer`, whose body performs a cata over its third
-- argument using the first and second argument as handlers. The stated algebra
-- type is `List# a Integer -> !Integer`, holding `a` rigid. This should compile
-- and type as expected.
unitCataListRigid :: IO ()
unitCataListRigid = do
  let algTy = do
        listBfName <- baseFunctorOf "List"
        pure . Comp0 $ Datatype listBfName [tyvar (S Z) ix0, integerT] :--:> ReturnT integerT
  let resultTy =
        Comp1 $
          integerT
            :--:> ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> integerT :--:> ReturnT integerT)
            :--:> Datatype "List" [tyvar Z ix0]
            :--:> ReturnT integerT
  let comp = lam resultTy $ do
        t <- algTy
        armNil <- arg Z ix0
        armCons <- arg Z ix1
        x <- arg Z ix2
        AnId <$> cata t (Vector.fromList . fmap AnArg $ [armNil, armCons]) (AnArg x)
  withCompilationSuccessUnit comp (matchesType resultTy)

-- Construct a function of type `forall a . Maybe a -> <a -> Maybe a ->
-- !(Maybe a)> -> List a -> !(Maybe a)`, whose body performs a cata over its
-- third argument using the first and second argument as handlers. The stated
-- algebra type is `List# a (Maybe a) -> !(Maybe a)`, keeping `a` rigid. This
-- should compile and type as expected.
unitCataListMaybeRigid :: IO ()
unitCataListMaybeRigid = do
  let algTy = do
        listBfName <- baseFunctorOf "List"
        pure . Comp0 $ Datatype listBfName [tyvar (S Z) ix0, Datatype "Maybe" [tyvar (S Z) ix0]] :--:> ReturnT (Datatype "Maybe" [tyvar (S Z) ix0])
  let resultTy =
        Comp1 $
          Datatype "Maybe" [tyvar Z ix0]
            :--:> ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> Datatype "Maybe" [tyvar (S Z) ix0] :--:> ReturnT (Datatype "Maybe" [tyvar (S Z) ix0]))
            :--:> Datatype "List" [tyvar Z ix0]
            :--:> ReturnT (Datatype "Maybe" [tyvar Z ix0])
  let comp = lam resultTy $ do
        t <- algTy
        armNil <- arg Z ix0
        armCons <- arg Z ix1
        x <- arg Z ix2
        AnId <$> cata t (Vector.fromList . fmap AnArg $ [armNil, armCons]) (AnArg x)
  withCompilationSuccessUnit comp (matchesType resultTy)

-- Construct a function of type `forall a b . Maybe b -> <a -> Maybe b ->
-- !(Maybe b)> -> a -> !(Maybe b)`. In its body, we construct a singleton list
-- using the third argument, then eliminate it using a cata with the first and
-- second argument as handlers. The stated type of the algebra is `List# a
-- (Maybe b) -> !(Maybe b)`, keeping `a, b` rigid. This should compile and type
-- as expected.
unitCataIntroThenEliminate :: IO ()
unitCataIntroThenEliminate = do
  let algTy = do
        listBfName <- baseFunctorOf "List"
        pure . Comp0 $ Datatype listBfName [tyvar (S Z) ix0, Datatype "Maybe" [tyvar (S Z) ix1]] :--:> ReturnT (Datatype "Maybe" [tyvar (S Z) ix1])
  let resultTy =
        Comp2 $
          Datatype "Maybe" [tyvar Z ix1]
            :--:> ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> Datatype "Maybe" [tyvar (S Z) ix1] :--:> ReturnT (Datatype "Maybe" [tyvar (S Z) ix1]))
            :--:> tyvar Z ix0
            :--:> ReturnT (Datatype "Maybe" [tyvar Z ix1])
  let comp = lam resultTy $ do
        t <- algTy
        x <- arg Z ix2
        nilThunk <- dataConstructor "List" "Nil" []
        nilForced <- force (AnId nilThunk)
        aT <- boundTyVar Z ix0
        nilApplied <- app nilForced [] [Here aT]
        singleThunk <- dataConstructor "List" "Cons" [AnArg x, AnId nilApplied]
        singleForced <- force (AnId singleThunk)
        singleApplied <- app' singleForced []
        armNil <- arg Z ix0
        armCons <- arg Z ix1
        AnId <$> cata t (Vector.fromList . fmap AnArg $ [armNil, armCons]) (AnId singleApplied)
  withCompilationSuccessUnit comp (matchesType resultTy)

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
  let comp =
        AnId <$> do
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
  let comp =
        AnId <$> do
          i <- lit c
          force (AnId i)
   in withCompilationFailure comp $ \case
        TypeError _ (ForceNonThunk actualT) -> typeConstant c === actualT
        TypeError _ err' -> failWrongTypeError err'
        err' -> failWrongError err'

propThunkValType :: Property
propThunkValType = forAllShrinkShow arbitrary shrink show $ \c ->
  let comp =
        AnId <$> do
          i <- lit c
          thunk i
   in withCompilationFailure comp $ \case
        TypeError _ (ThunkValType actualT) -> typeConstant c === actualT
        TypeError _ err' -> failWrongTypeError err'
        err' -> failWrongError err'

propApplyToVal :: Property
propApplyToVal = forAllShrinkShow arbitrary shrink show $ \c args ->
  let comp =
        AnId <$> do
          args' <- traverse (fmap AnId . lit) args
          i <- lit c
          app i args' mempty
   in withCompilationFailure comp $ \case
        TypeError _ (ApplyToValType t) -> typeConstant c === t
        TypeError _ err' -> failWrongTypeError err'
        err' -> failWrongError err'

propApplyToError :: Property
propApplyToError = forAllShrinkShow arbitrary shrink show $ \args ->
  let comp =
        AnId <$> do
          args' <- traverse (fmap AnId . lit) args
          i <- err
          app i args' mempty
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

      comp =
        AnId <$> do
          i <- builtin1 f
          arg' <- case arg1 of
            Left bi1 -> builtin1 bi1
            Right (Left bi2) -> builtin2 bi2
            Right (Right bi3) -> builtin3 bi3
          app' i (Vector.singleton . AnId $ arg')
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

boundTyVarHappy :: Assertion
boundTyVarHappy = run $ do
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

boundTyVarShouldFail :: Assertion
boundTyVarShouldFail = run $ boundTyVar Z ix0
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
newLamTest1 :: Assertion
newLamTest1 = case runASGBuilder M.empty fn of
  Left err' -> assertFailure (show err')
  Right {} -> pure ()
  where
    fn :: ASGBuilder Id
    fn = lam expected $ do
      f <- arg Z ix0 >>= force . AnArg
      a <- AnArg <$> arg Z ix1
      AnId <$> app f (Vector.singleton a) mempty

    expected :: CompT AbstractTy
    expected =
      Comp2 $
        ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> ReturnT (tyvar (S Z) ix1))
          :--:> tyvar Z ix0
          :--:> ReturnT (tyvar Z ix1)

newLamTest2 :: Assertion
newLamTest2 = case runASGBuilder tyAppTestDatatypes fn of
  Left err' -> assertFailure (show err')
  Right {} -> pure ()
  where
    fn :: ASGBuilder Id
    fn = lam expected $ do
      f <- arg Z ix0 >>= force . AnArg
      a <- AnArg <$> arg Z ix1
      AnId <$> app f (Vector.singleton a) mempty

    expected :: CompT AbstractTy
    expected =
      Comp2 $
        ThunkT (Comp0 $ Datatype "Maybe" (Vector.singleton $ tyvar (S Z) ix0) :--:> ReturnT (tyvar (S Z) ix1))
          :--:> Datatype "Maybe" (Vector.singleton $ tyvar Z ix0)
          :--:> ReturnT (tyvar Z ix1)

-- Intro form tests

nothingIntro :: TestTree
nothingIntro =
  runIntroFormTest "nothing" expectNothingThunk $
    dataConstructor "Maybe" "Nothing" mempty >>= typeIdTest
  where
    expectNothingThunk :: ValT AbstractTy
    expectNothingThunk = ThunkT . Comp1 . ReturnT $ Datatype "Maybe" (Vector.fromList [tyvar Z ix0])

justConcreteIntro :: TestTree
justConcreteIntro = runIntroFormTest "justConcreteIntro" expected $ do
  argRef <- AnId <$> lit AUnit
  dataConstructor "Maybe" "Just" (Vector.singleton argRef) >>= typeIdTest
  where
    expected :: ValT AbstractTy
    expected = ThunkT . Comp0 . ReturnT $ Datatype "Maybe" (Vector.singleton $ BuiltinFlat UnitT)

justRigidIntro :: TestTree
justRigidIntro = runIntroFormTest "justRigidIntro" expected $ do
  lamId <- lam lamTy $ do
    arg1 <- AnArg <$> arg Z ix0
    justRigid <- dataConstructor "Maybe" "Just" (Vector.singleton arg1)
    pure (AnId justRigid)
  lamThunked <- thunk lamId
  typeIdTest lamThunked
  where
    lamTy :: CompT AbstractTy
    lamTy =
      Comp1 $
        tyvar Z ix0
          :--:> ReturnT
            ( ThunkT
                . Comp0
                . ReturnT
                $ Datatype "Maybe"
                $ Vector.singleton (tyvar (S Z) ix0)
            )

    expected :: ValT AbstractTy
    expected = ThunkT lamTy

justNothingIntro :: TestTree
justNothingIntro = runIntroFormTest "justNothingIntro" expectedThunk $ do
  thunkL <- lam expectedComp $ do
    var <- boundTyVar Z ix0
    nothing <- ctor "Maybe" "Nothing" mempty (Vector.singleton . wedgeLeft . Just $ var)
    justNothing <- ctor' "Maybe" "Just" (Vector.singleton (AnId nothing))
    pure (AnId justNothing)
  typeIdTest thunkL
  where
    expectedComp :: CompT AbstractTy
    expectedComp =
      Comp1
        . ReturnT
        . Datatype "Maybe"
        . Vector.singleton
        . Datatype "Maybe"
        $ Vector.singleton
        $ tyvar Z ix0

    expectedThunk :: ValT AbstractTy
    expectedThunk = ThunkT expectedComp

-- pattern matching

{- Construct a pattern match on 'Maybe Unit' that returns an integer.

   This is effectively the simplest possible pattern matching test: The type is non-recursive and the
   parameters to the type constructor are all concrete.
-}
matchMaybe :: TestTree
matchMaybe = runIntroFormTest "matchMaybe" (BuiltinFlat IntegerT) $ do
  unit <- AnId <$> lit AUnit
  scrutinee <- ctor' "Maybe" "Just" (Vector.singleton unit)
  nothingHandler <- lazyLam (Comp0 $ ReturnT (BuiltinFlat IntegerT)) (AnId <$> lit (AnInteger 0))
  justHandler <- lazyLam (Comp0 $ BuiltinFlat UnitT :--:> ReturnT (BuiltinFlat IntegerT)) (AnId <$> lit (AnInteger 1))
  result <- match (AnId scrutinee) (AnId <$> Vector.fromList [justHandler, nothingHandler])
  typeIdTest result

{- Construct a pattern match on 'List Unit' that returns an integer.

   A simple test for pattern matches on values of recursive types.
-}
matchList :: TestTree
matchList = runIntroFormTest "matchList" (BuiltinFlat IntegerT) $ do
  unit <- AnId <$> lit AUnit
  nilUnit <- ctor "List" "Nil" mempty (Vector.singleton $ There (BuiltinFlat UnitT))
  scrutinee <- ctor' "List" "Cons" (Vector.fromList [unit, AnId nilUnit])
  let nilHandlerTy = Comp0 $ ReturnT (BuiltinFlat IntegerT)
      consHandlerTy =
        Comp0 $
          BuiltinFlat UnitT
            :--:> Datatype "#List" (Vector.fromList [BuiltinFlat UnitT, Datatype "List" (Vector.singleton $ BuiltinFlat UnitT)])
            :--:> ReturnT (BuiltinFlat IntegerT)
  nilHandler <- lazyLam nilHandlerTy (AnId <$> lit (AnInteger 0))
  consHandler <- lazyLam consHandlerTy (AnId <$> lit (AnInteger 0))
  result <- match (AnId scrutinee) (AnId <$> Vector.fromList [nilHandler, consHandler])
  typeIdTest result

{- This differs from the two above tests in that we're using pattern matching to construct the
   'maybeToList :: forall a. Maybe a -> List a' function. This is very useful, because if successful, it provides good evidence that:
     1. Pattern matching works on datatypes with rigid parameters.
     2. Pattern matching works inside the body of a lambda.
     3. Nothing breaks renaming anywhere.
-}
maybeToList :: TestTree
maybeToList = runIntroFormTest "maybeToList" maybeToListTy $ do
  thonk <- lazyLam maybeToListCompTy $ do
    let nothingHandlerTy = Comp0 $ ReturnT (dtype "List" [tyvar (S Z) ix0])
        justHandlerTy = Comp0 $ tyvar (S Z) ix0 :--:> ReturnT (dtype "List" [tyvar (S Z) ix0])
    nothingHandler <- lazyLam nothingHandlerTy $ do
      tvA <- boundTyVar (S Z) ix0
      AnId <$> ctor "List" "Nil" mempty (Vector.singleton (Here tvA))
    justHandler <- lazyLam justHandlerTy $ do
      tvA <- boundTyVar (S Z) ix0
      vA <- AnArg <$> arg Z ix0
      nil <- AnId <$> ctor "List" "Nil" mempty (Vector.singleton (Here tvA))
      AnId <$> ctor "List" "Cons" (Vector.fromList [vA, nil]) Vector.empty
    scrutinee <- AnArg <$> arg Z ix0
    AnId <$> match scrutinee (AnId <$> Vector.fromList [justHandler, nothingHandler])
  typeIdTest thonk
  where
    maybeToListCompTy :: CompT AbstractTy
    maybeToListCompTy = Comp1 (dtype "Maybe" [tyvar Z ix0] :--:> ReturnT (dtype "List" [tyvar Z ix0]))

    maybeToListTy :: ValT AbstractTy
    maybeToListTy = ThunkT maybeToListCompTy

{- This tests that Opaques don't break the unifier. Arguably it should be in type-applications, but we need a bunch of
   ASG stuff that's not imported there to construct the test, so it is here instead.

   The lambda we construct has the type: Maybe Opaque -> Integer
-}

unifyOpaque :: TestTree
unifyOpaque = runIntroFormTest "unifyOpaque" unifyOpaqueTy $ do
  thonk <- lazyLam unifyOpaqueCompTy $ do
    let nothingHandlerTy = Comp0 $ ReturnT (BuiltinFlat IntegerT)
        justHandlerTy = Comp0 $ dtype "Foo" [] :--:> ReturnT (BuiltinFlat IntegerT)
    nothingHandler <- lazyLam nothingHandlerTy (AnId <$> lit (AnInteger 0))
    justHandler <- lazyLam justHandlerTy (AnId <$> lit (AnInteger 1))
    scrutinee <- AnArg <$> arg Z ix0
    AnId <$> match scrutinee (AnId <$> Vector.fromList [justHandler, nothingHandler])
  typeIdTest thonk
  where
    unifyOpaqueCompTy :: CompT AbstractTy
    unifyOpaqueCompTy = Comp0 $ dtype "Maybe" [dtype "Foo" []] :--:> ReturnT (BuiltinFlat IntegerT)
    unifyOpaqueTy :: ValT AbstractTy
    unifyOpaqueTy = ThunkT unifyOpaqueCompTy

matchOpaque :: TestTree
matchOpaque = runIntroFormTest "matchOpaque" matchOpaqueTy $ do
  thonk <- lazyLam matchOpaqueCompTy $ do
    let iHandlerTy = Comp0 $ BuiltinFlat IntegerT :--:> ReturnT (BuiltinFlat IntegerT)
        bHandlerTy = Comp0 $ BuiltinFlat ByteStringT :--:> ReturnT (BuiltinFlat IntegerT)
    iHandler <- lazyLam iHandlerTy $ AnId <$> lit (AnInteger 0)
    bHandler <- lazyLam bHandlerTy $ AnId <$> lit (AnInteger 1)
    scrutinee <- AnArg <$> arg Z ix0
    AnId <$> match scrutinee (AnId <$> Vector.fromList [iHandler, bHandler])
  typeIdTest thonk
  where
    matchOpaqueCompTy :: CompT AbstractTy
    matchOpaqueCompTy = Comp0 $ dtype "Foo" [] :--:> ReturnT (BuiltinFlat IntegerT)
    matchOpaqueTy :: ValT AbstractTy
    matchOpaqueTy = ThunkT matchOpaqueCompTy

-- Helpers

runIntroFormTest :: String -> ValT AbstractTy -> DebugASGBuilder (ValT AbstractTy) -> TestTree
runIntroFormTest nm expectedTy act = testCase nm $ case debugASGBuilder tyAppTestDatatypes act of
  Left err' -> assertFailure ("ASG Error: " <> show err')
  Right actualTy -> assertEqual nm expectedTy actualTy

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

withCompilationSuccessUnit :: ASGBuilder Id -> (ASG -> IO ()) -> IO ()
withCompilationSuccessUnit comp cb = case runASGBuilder defaultDatatypes comp of
  Left err' -> assertFailure $ "Did not compile: " <> show err'
  Right asg -> cb asg

withCompilationFailureUnit :: ASGBuilder Id -> (CovenantError -> IO ()) -> IO ()
withCompilationFailureUnit comp cb = case runASGBuilder defaultDatatypes comp of
  Left err' -> cb err'
  Right asg -> assertFailure $ "Unexpected compilation success: " <> show asg

matchesType :: CompT AbstractTy -> ASG -> IO ()
matchesType expectedTy asg = case topLevelNode asg of
  ACompNode actualTy _ -> assertEqual "" expectedTy actualTy
  u@(AValNode _ _) -> assertFailure $ "Got a value node: " <> show u
  AnError -> assertFailure "Got an error node"

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
