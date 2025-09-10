{-# LANGUAGE OverloadedLists #-}
module Main  where

import Data.Vector qualified as Vector
import Data.Wedge

import Covenant.Type
import Covenant.ASG
import Covenant.Test
import Covenant.Index
import Covenant.DeBruijn
import Covenant.Constant
import Covenant.Prim (TwoArgFunc(AddInteger))
import Covenant.Data (mkDatatypeInfo)

main :: IO ()
main = pure ()


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
  AnId <$> app plus [x,y] [Nowhere,Nowhere]

conformance_body1 :: Either CovenantError ASG
conformance_body1 =
  runASGBuilder
    (unsafeMkDatatypeInfos conformanceDatatypes)
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
      AnId <$> match maybeIntPair  [AnId nothingHandler', AnId justHandler']


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
      AnId <$> ctor "Result" "OK" [finalResult]  [There (BuiltinFlat StringT)]
     where
       pairHandlerT :: CompT AbstractTy
       pairHandlerT = Comp0 $ intT :--:> intT :--:> ReturnT resultT

    sumList :: Ref -> ASGBuilder Id
    sumList listToSum = do
      sumListF' <- AnId <$> sumListF
      cata sumListF' listToSum

    sumListF :: ASGBuilder Id
    sumListF = lazyLam (Comp0 $ listFIntT :--:> ReturnT intT) $ do
      listFInt <- AnArg <$> arg Z ix0
      nilHandler <-  lazyLam (Comp0 . ReturnT $ intT) (AnId <$> lit (AnInteger 0))
      consHandler <- lazyLam (Comp0 $ intT :--:> intT :--:> ReturnT intT) $ do
                       x <- AnArg <$> arg Z ix0
                       y <- AnArg <$> arg Z ix1
                       x #+ y
      AnId <$> match listFInt (AnId <$> [nilHandler,consHandler])
     where
      listFIntT :: ValT AbstractTy
      listFIntT = dtype "List_F" [intT,intT]


    intT :: ValT AbstractTy
    intT = BuiltinFlat IntegerT

    stringT :: ValT AbstractTy
    stringT = BuiltinFlat StringT

    intPairT :: ValT AbstractTy
    intPairT = dtype "Pair" [intT,intT]

    maybeIntPairT :: ValT AbstractTy
    maybeIntPairT = dtype "Maybe"
                    [intPairT]

    listIntT :: ValT AbstractTy
    listIntT = dtype "List" [intT]

    resultT :: ValT AbstractTy
    resultT = dtype "Result" [stringT,intT]

    topLevelTy :: CompT AbstractTy
    topLevelTy = Comp0 $ maybeIntPairT :--:> listIntT :--:> ReturnT resultT
