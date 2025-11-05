{-# LANGUAGE OverloadedLists #-}

module Main (main) where

import Control.Monad (void)
import Covenant.ASG
  ( ASG,
    ASGBuilder,
    CovenantError,
    Id,
    Ref (AnArg, AnId),
    app',
    arg,
    baseFunctorOf,
    builtin2,
    cata,
    ctor,
    ctor',
    dtype,
    err,
    lam,
    lazyLam,
    lit,
    match,
    runASGBuilder,
  )
import Covenant.Constant
  ( AConstant (AString, AnInteger),
  )
import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index (ix0, ix1)
import Covenant.JSON (deserializeAndValidate_)
import Covenant.Prim (TwoArgFunc (AddInteger, EqualsInteger, SubtractInteger))
import Covenant.Test
  ( conformanceDatatypes1,
    conformanceDatatypes2,
    unsafeMkDatatypeInfos,
  )
import Covenant.Type
  ( AbstractTy,
    BuiltinFlatT (BoolT, IntegerT, StringT),
    CompT (Comp0, Comp1),
    CompTBody (ReturnT, (:--:>)),
    ValT (BuiltinFlat, Datatype),
    tyvar,
  )
import Data.Either (isRight)
import Data.Vector qualified as Vector
import Data.Wedge (Wedge (There))
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)

main :: IO ()
main =
  defaultMain . testGroup "Conformance" $
    [ testCase "conformance1_asg" (assertBool "case 1 compiles to asg" $ isRight conformance_body1),
      testCase "conformance2_asg" (assertBool "case 2 compiles to asg" $ isRight conformance_body2),
      testCase "deserialize_1" (void $ deserializeAndValidate_ "./test/json-conformance/conformance_case_1.json"),
      testCase "deserialize_2" (void $ deserializeAndValidate_ "./test/json-conformance/conformance_case_2.json")
    ]

{- Case 1:

Datatypes:

data Maybe a = Nothing | Just a

data Result e a = Exception e | OK a

data Pair a b = Pair a b

data List a = Nil | Cons a (List a)

Body:

f :: Maybe (Pair Integer Integer) -> List Integer -> Result String Integer
f = \inpMPair inpList ->
  match inpMPair
    (Exception "Input is Nothing")
    (\pair ->
       match
         (\a b ->
            let listSum = cata (\listF -> match listF
                                  (0)
                                  (\x r -> x + r)
                               )
            in OK (a + b + listSum)
         )
    )

-}

(#+) :: Ref -> Ref -> ASGBuilder Ref
x #+ y = do
  plus <- builtin2 AddInteger
  AnId <$> app' plus [x, y]

(#-) :: Ref -> Ref -> ASGBuilder Ref
x #- y = do
  minus <- builtin2 SubtractInteger
  AnId <$> app' minus [x, y]

(#==) :: Ref -> Ref -> ASGBuilder Ref
x #== y = do
  equals <- builtin2 EqualsInteger
  AnId <$> app' equals [x, y]

conformance_body1 :: Either CovenantError ASG
conformance_body1 =
  runASGBuilder
    (unsafeMkDatatypeInfos conformanceDatatypes1)
    conformance_body1_builder

conformance_body1_builder :: ASGBuilder Id
conformance_body1_builder = lam topLevelTy body
  where
    {- arg1: Maybe (Pair Integer Integer)
       arg2: List Integer
    -}
    body :: ASGBuilder Ref
    body = do
      maybeIntPair <- AnArg <$> arg Z ix0
      nothingHandler' <- nothingHandler
      justHandler' <- justHandler
      AnId <$> match maybeIntPair [AnId nothingHandler', AnId justHandler']

    nothingHandler :: ASGBuilder Id
    nothingHandler = lazyLam nothingHandlerT $ do
      errMsg <- AnId <$> lit (AString "Input is nothing")
      AnId <$> ctor "Result" "Exception" (Vector.singleton errMsg) [There (BuiltinFlat IntegerT)]
      where
        nothingHandlerT :: CompT AbstractTy
        nothingHandlerT = Comp0 $ ReturnT resultT

    justHandler :: ASGBuilder Id
    justHandler = lazyLam justHandlerT $ do
      intPair <- AnArg <$> arg Z ix0
      pairHandler' <- pairHandler
      AnId <$> match intPair [AnId pairHandler']
      where
        justHandlerT :: CompT AbstractTy
        justHandlerT = Comp0 $ intPairT :--:> ReturnT resultT

    pairHandler :: ASGBuilder Id
    pairHandler = lazyLam pairHandlerT $ do
      int1 <- AnArg <$> arg Z ix0
      int2 <- AnArg <$> arg Z ix1
      summedArgs <- int1 #+ int2
      tlListInt <- AnArg <$> arg (S (S Z)) ix1
      summedList <- AnId <$> sumList tlListInt
      finalResult <- summedArgs #+ summedList
      AnId <$> ctor "Result" "OK" [finalResult] [There (BuiltinFlat StringT)]
      where
        pairHandlerT :: CompT AbstractTy
        pairHandlerT = Comp0 $ intT :--:> intT :--:> ReturnT resultT

    sumList :: Ref -> ASGBuilder Id
    sumList listToSum = do
      listF <- baseFunctorOf "List"
      let cataTy = Comp0 $ Datatype listF [intT, intT] :--:> ReturnT intT
      nilHandler <- lazyLam (Comp0 $ ReturnT intT) (AnId <$> lit (AnInteger 0))
      consHandler <- lazyLam (Comp0 $ intT :--:> intT :--:> ReturnT intT) $ do
        x <- AnArg <$> arg Z ix0
        y <- AnArg <$> arg Z ix1
        x #+ y
      cata cataTy [AnId nilHandler, AnId consHandler] listToSum
    {-
    sumList :: Ref -> ASGBuilder Id
    sumList listToSum = do
      sumListF' <- AnId <$> sumListF
      cata sumListF' listToSum

    sumListF :: ASGBuilder Id
    sumListF = lazyLam (Comp0 $ listFIntT :--:> ReturnT intT) $ do
      listFInt <- AnArg <$> arg Z ix0
      nilHandler <- lazyLam (Comp0 . ReturnT $ intT) (AnId <$> lit (AnInteger 0))
      consHandler <- lazyLam (Comp0 $ intT :--:> intT :--:> ReturnT intT) $ do
        x <- AnArg <$> arg Z ix0
        y <- AnArg <$> arg Z ix1
        x #+ y
      AnId <$> match listFInt (AnId <$> [nilHandler, consHandler])
      where
        listFIntT :: ValT AbstractTy
        listFIntT = dtype "#List" [intT, intT]
    -}

    intT :: ValT AbstractTy
    intT = BuiltinFlat IntegerT

    stringT :: ValT AbstractTy
    stringT = BuiltinFlat StringT

    intPairT :: ValT AbstractTy
    intPairT = dtype "Pair" [intT, intT]

    maybeIntPairT :: ValT AbstractTy
    maybeIntPairT =
      dtype
        "Maybe"
        [intPairT]

    listIntT :: ValT AbstractTy
    listIntT = dtype "List" [intT]

    resultT :: ValT AbstractTy
    resultT = dtype "Result" [stringT, intT]

    topLevelTy :: CompT AbstractTy
    topLevelTy = Comp0 $ maybeIntPairT :--:> listIntT :--:> ReturnT resultT

{- Case 2:

opaque data Foo = Foo

data Void

data Maybe a = Nothing | Just a

data Pair a b = Pair a b

f :: Maybe (Pair Integer Foo) -> Maybe Boolean
f mabPairIntFoo =
  let g :: forall a. Integer -> a  -> Integer
      g n _x = n + n
  in match mabPairIntFoo
       (error "Input is nothing")
       (\pairIntFoo ->
          match pairIntFoo (\n foo ->
            let doubled = g n foo
                zero    = doubled - doubled
            in Just (zero == 0)
          )
       )
-}

conformance_body2 :: Either CovenantError ASG
conformance_body2 =
  runASGBuilder
    (unsafeMkDatatypeInfos conformanceDatatypes2)
    conformance_body2_builder

conformance_body2_builder :: ASGBuilder Id
conformance_body2_builder = lam topLevelTy body
  where
    body :: ASGBuilder Ref
    body = do
      maybeIntFooPair <- AnArg <$> arg Z ix0
      g' <- g
      nothingHandler' <- nothingHandler
      justHandler' <- justHandler g'
      AnId <$> match maybeIntFooPair [AnId nothingHandler', AnId justHandler']

    nothingHandler :: ASGBuilder Id
    nothingHandler = lazyLam nothingHandlerT (AnId <$> err)
      where
        nothingHandlerT :: CompT AbstractTy
        nothingHandlerT = Comp0 $ ReturnT maybeBoolT

    justHandler :: Id -> ASGBuilder Id
    justHandler gx = lazyLam justHandlerTy $ do
      intFooPair <- AnArg <$> arg Z ix0
      pairHandler' <- pairHandler gx
      AnId <$> match intFooPair [AnId pairHandler']
      where
        justHandlerTy :: CompT AbstractTy
        justHandlerTy = Comp0 $ pairIntFooT :--:> ReturnT maybeBoolT

    pairHandler :: Id -> ASGBuilder Id
    pairHandler gx = lazyLam pairHandlerTy $ do
      intArg <- AnArg <$> arg Z ix0
      fooArg <- AnArg <$> arg Z ix1
      doubled <- AnId <$> app' gx [intArg, fooArg]
      zero <- doubled #- doubled
      zeroIs0 <- zero #== zero
      AnId <$> ctor' "Maybe" "Just" [zeroIs0]
      where
        pairHandlerTy :: CompT AbstractTy
        pairHandlerTy = Comp0 $ integerT :--:> fooT :--:> ReturnT maybeBoolT

    g :: ASGBuilder Id
    g = lam gTy $ do
      intArg <- AnArg <$> arg Z ix0
      intArg #+ intArg
      where
        gTy :: CompT AbstractTy
        gTy = Comp1 $ integerT :--:> tyvar Z ix0 :--:> ReturnT integerT

    topLevelTy :: CompT AbstractTy
    topLevelTy = Comp0 $ maybePairIntFooT :--:> ReturnT maybeBoolT

    integerT :: forall a. ValT a
    integerT = BuiltinFlat IntegerT

    boolT :: forall a. ValT a
    boolT = BuiltinFlat BoolT

    fooT :: ValT AbstractTy
    fooT = dtype "Foo" []

    pairIntFooT :: ValT AbstractTy
    pairIntFooT = dtype "Pair" [integerT, fooT]

    maybePairIntFooT :: ValT AbstractTy
    maybePairIntFooT = dtype "Maybe" [pairIntFooT]

    maybeBoolT :: ValT AbstractTy
    maybeBoolT = dtype "Maybe" [boolT]
