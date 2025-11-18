{-# LANGUAGE OverloadedLists #-}

module Main  where

import Control.Monad (void)
import Covenant.ASG
  ( ASG,
    ASGBuilder,
    CovenantError,
    Id,
    Ref (AnArg, AnId),
    app',
    arg,
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
    runASGBuilder, force, thunk, boundTyVar, builtin3, app,
  )
import Covenant.Constant
  ( AConstant (AString, AnInteger),
  )
import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index (ix0, ix1, intIndex, ix2, ix3)
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
    CompT (..),
    CompTBody (ReturnT, (:--:>)),
    ValT (BuiltinFlat),
    tyvar, boolT,
  )
import Data.Either (isRight)
import Data.Vector qualified as Vector
import Data.Wedge (Wedge (..))
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)
import Covenant.Type (ValT(..))
import Covenant.ASG (ASGNode(..))
import Covenant.ASG (Arg(Arg))
import Covenant.Index (Index)
import Optics.Core (preview)
import Data.Maybe (fromJust)
import Covenant.Constant (AConstant(..))
import Control.Monad.HashCons (MonadHashCons(..))
import Covenant.Prim (ThreeArgFunc(IfThenElse))

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




ix4 :: forall s. Index s
ix4 = fromJust $ preview intIndex 4

thunk0 = ThunkT . Comp0

thunk2 = ThunkT . Comp2

testFn :: Either CovenantError ASG
testFn = runASGBuilder (unsafeMkDatatypeInfos conformanceDatatypes1) testFnBuilder

debugHelp :: ASGBuilder Id -> Either CovenantError ASG
debugHelp act = runASGBuilder (unsafeMkDatatypeInfos conformanceDatatypes1) act

intT :: ValT AbstractTy
intT = BuiltinFlat IntegerT

-- boolT :: ValT AbstractTy
-- boolT = BuiltinFlat BoolT

maybeT :: ValT AbstractTy -> ValT AbstractTy
maybeT t = dtype "Maybe" [t]

ifte ::  ASGBuilder Id
ifte  = lam (Comp1 $ boolT :--:> tyvar Z ix0 :--:> tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)) $ do
  cond <- AnArg <$> arg Z ix0
  t    <- AnArg <$> arg Z ix1
  f    <- AnArg <$> arg Z ix2
  ifThen <- builtin3 IfThenElse
  tvHere <- boundTyVar Z ix0
  AnId <$> app' ifThen [cond,t,f] -- [Here tvHere]


-- NOTE: I wonder what happens if we tried to define id and monoConst in terms of each other?
--       Like if we do it so that we get infinite mutual recursion. I should probably *try*
--       to compile something like that just to see whether it explodes.
identitee :: ASGBuilder Id
identitee = lam (Comp1 $ tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)) $ do
  -- Not how you would typically implement `id` lol
  mConst <- monoConst
  tyX <- boundTyVar Z ix0
  x <- AnArg <$> arg Z ix0
  -- Might not need the ty app?
  AnId <$> app' mConst [x,x] -- [Here tyX]


-- forall a. a -> a -> a
monoConst :: ASGBuilder Id
monoConst = lam (Comp1 $ tyvar Z ix0 :--:> tyvar Z ix0 :--:> ReturnT (tyvar Z ix0)) $ do
  AnArg <$> arg Z ix1

fPolyOneIntro :: ASGBuilder Id
fPolyOneIntro = lam fPolyOneIntroTy $ do
  fba <- force . AnArg =<< arg Z ix0
  faa <- force . AnArg =<< arg Z ix1
  predA <- force . AnArg =<< arg Z ix2
  a <- AnArg <$> arg Z ix3
  b <- AnArg <$> arg Z ix4
  -- let ba = fba (monoConst b b)
  mConst <- monoConst
  fbaArg <- AnId <$> app' mConst [b,b]
  ba <- AnId <$> app' fba [fbaArg]
  -- let aaa = monoConst a (faa a ba)
  aaaArg <- AnId <$> app' faa [a,ba]
  aaa <- AnId <$> app' mConst [a,aaaArg]
  -- if (predA aaa) then Nothing else Just aaa
  tvA <- boundTyVar Z ix0
  nothing <- ctor "Maybe" "Nothing" [] [Here tvA]
  justAAA <- ctor' "Maybe" "Just" [aaa]
  ifThen <- ifte
  cond <- app' predA [aaa]
  -- might need to do this w/ the explicit type app?
  AnId <$> app' ifThen [AnId cond,AnId nothing,AnId justAAA]
 where
   fPolyOneIntroTy :: CompT AbstractTy
   fPolyOneIntroTy = Comp2 $ -- forall a b.
                     ThunkT (Comp0 $ tyvar (S Z) ix1 :--:> ReturnT (tyvar (S Z) ix0)) -- (b -> a)
                     :--:> ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> tyvar (S Z) ix0 :--:> ReturnT (tyvar (S Z) ix0)) -- (a -> a -> a)
                     :--:> ThunkT (Comp0 $ tyvar (S Z) ix0 :--:> ReturnT boolT) -- (a -> Bool)
                     :--:> tyvar Z ix0 -- a
                     :--:> tyvar Z ix1 -- b
                     :--:> ReturnT (maybeT (tyvar Z ix0)) -- Maybe a

fPolyOneElim :: ASGBuilder Id
fPolyOneElim = lam fPolyOneElimTy $ do
  -- false <- AnId <$> lit (ABoolean False)
  -- zero <- AnId <$> lit (AnInteger 0)
  -- mConst <- monoConst
  maybeA <- AnArg <$> arg Z ix0
  -- maybe we should move `b` into the nothingHandler so it blows up if there's a DB issue somewhere?
  nothingHandler <- lazyLam (Comp0 $ ReturnT intT) $ do
    --            x[       y[                 ]
    -- monoConst 0 (bToInt (monoConst False b))
    -- b <- AnArg <$> arg (S Z) ix2
    -- bToInt <- force . AnArg =<< arg (S Z) ix3
    -- y <- AnId <$> app' mConst [false,b]
    -- x <- AnId <$> app' bToInt [y]
    -- AnId <$> app' mConst [zero,x]
    AnId <$> lit (AnInteger 0)
  justHandler <- lazyLam (Comp0 $ tyvar (S Z) ix0 :--:> ReturnT intT) $ do
    -- aToInt <- force . AnArg =<< arg (S Z) ix1
    -- a <- AnArg <$> arg (S Z) ix0
    -- AnId <$> app' aToInt [a]
    AnId <$> lit (AnInteger 0)
  AnId <$> match maybeA [AnId nothingHandler,AnId justHandler]
 where
   fPolyOneElimTy :: CompT AbstractTy
   fPolyOneElimTy = Comp2 $ -- forall a b.
                    maybeT (tyvar Z ix0) -- Maybe a
                    :--:> thunk0 (tyvar (S Z) ix0 :--:> ReturnT intT) -- (a -> Int)
                    :--:> tyvar Z ix1 -- b
                    :--:> thunk0 (tyvar (S Z) ix1 :--:> ReturnT intT) -- (b -> Int)
                    :--:> ReturnT intT -- Int

fPolyOneElimMinimal :: ASGBuilder Id
fPolyOneElimMinimal =  lam fPolyOneElimTy $ do
  maybeA <- AnArg <$> arg Z ix0
  nothingHandler <- lazyLam (Comp0 $ ReturnT intT) $ do
    AnId <$> lit (AnInteger 0)
  justHandler <- lazyLam (Comp0 $ tyvar (S Z) ix0 :--:> ReturnT intT) $ do
    AnId <$> lit (AnInteger 0)
  AnId <$> match maybeA [AnId nothingHandler,AnId justHandler]
 where
   fPolyOneElimTy :: CompT AbstractTy
   fPolyOneElimTy = Comp2 $ -- forall a b.
                    maybeT (tyvar Z ix0) -- Maybe a
                    :--:> tyvar Z ix1 -- b
                    :--:> ReturnT intT -- Int

testFnBuilder' :: ASGBuilder Id
testFnBuilder' = lam topLevelTy body
  where
    topLevelTy :: CompT AbstractTy
    topLevelTy = Comp0 $ intT :--:> boolT :--:> ReturnT intT

    body :: ASGBuilder Ref
    body = do
      intArg <- AnArg <$> arg Z ix0
      boolArg <- AnArg <$> arg Z ix1
      fElim <- fPolyOneElimMinimal
      maybeInt <- ctor' "Maybe" "Just" [intArg]
      AnId <$> app' fElim [AnId maybeInt,boolArg]


fPolyOneElimMinimal' :: ASGBuilder Id
fPolyOneElimMinimal' =  lam fPolyOneElimTy $ do
  maybeA <- AnArg <$> arg Z ix0
  nothingHandler <- lazyLam (Comp0 $ ReturnT intT) $ do
    AnId <$> lit (AnInteger 0)
  justHandler <- lazyLam (Comp0 $ tyvar (S Z) ix0 :--:> ReturnT intT) $ do
    AnId <$> lit (AnInteger 0)
  AnId <$> match maybeA [AnId nothingHandler,AnId justHandler]
 where
   fPolyOneElimTy :: CompT AbstractTy
   fPolyOneElimTy = Comp1 $ -- forall a.
                    maybeT (tyvar Z ix0) -- Maybe a
                    :--:> ReturnT intT -- Int

testFnBuilder'' :: ASGBuilder Id
testFnBuilder'' = lam topLevelTy body
  where
    topLevelTy :: CompT AbstractTy
    topLevelTy = Comp0 $ intT :--:> boolT :--:> ReturnT intT

    body :: ASGBuilder Ref
    body = do
      intArg <- AnArg <$> arg Z ix0
      fElim <- fPolyOneElimMinimal'
      maybeInt <- ctor' "Maybe" "Just" [intArg]
      AnId <$> app' fElim [AnId maybeInt]


unsafeShowNodeType :: Id -> ASGBuilder String
unsafeShowNodeType i = lookupRef i >>= \case
  Nothing -> error "boom"
  Just aNode -> case aNode of
    AValNode t _ -> pure $ show t
    ACompNode t _ -> pure $ show t
    _ -> error "error node type"

unsafeShowRefType :: Ref -> ASGBuilder String
unsafeShowRefType = \case
  AnArg (Arg _ _ t) -> pure (show t)
  AnId i -> unsafeShowNodeType i

testFnBuilder :: ASGBuilder Id
testFnBuilder = lam topLevelTy body
  where
    topLevelTy :: CompT AbstractTy
    topLevelTy = Comp0 $ intT :--:> boolT :--:> ReturnT intT

    body :: ASGBuilder Ref
    body = do
      intArg <- AnArg <$> arg Z ix0
      boolArg <- AnArg <$> arg Z ix1
      idF <- AnId <$> (thunk =<< identitee)
      fmono <- AnId <$> (thunk =<< fMono)
      gmono <- AnId <$> (thunk =<< gMono)
      mConst <- AnId <$> (thunk =<< monoConst)
      intId <- AnId <$> (thunk =<< (lam (Comp0 $ intT :--:> ReturnT intT) (AnArg <$> arg Z ix0)))
      intConst <- AnId <$> (thunk =<< (lam (Comp0 $ intT :--:> intT :--:> ReturnT intT) (AnArg <$> arg Z ix1)))
      fIntro <- fPolyOneIntro
      fElim <- fPolyOneElim
      introApplied <- app' fIntro [fmono,mConst,gmono,intArg,boolArg]
      fElimTyStr <- unsafeShowNodeType fElim
      introAppliedTyStr <- unsafeShowNodeType introApplied
      idFTyStr <- unsafeShowRefType intId
      boolArgTyStr <- unsafeShowRefType boolArg
      fMonoTyStr   <- unsafeShowRefType fmono
      let msg :: String
          msg = concatMap (\(x :: String) -> x <> "\n\n" :: String)
                (  [ "fElimTy: " <> fElimTyStr
                , "introAppliedTy: " <> introAppliedTyStr
                , "idFTyStr: " <> idFTyStr
                , "boolArgTyStr: " <> boolArgTyStr
                , "fmonoTyStr: " <> fMonoTyStr
                ] :: [String])
      --error ("\n\n" <> msg)
      AnId <$> app' fElim [AnId introApplied,intId,boolArg,fmono]

fMono :: ASGBuilder Id
fMono = lam (Comp0 $ boolT :--:> ReturnT intT) $ do
      aBool <- AnArg <$> arg Z ix0
      one <- AnId <$> lit (AnInteger 1)
      zero <- AnId <$> lit (AnInteger 0)
      ifThen <- ifte
      AnId <$> app' ifThen [aBool,one,zero] -- [There (BuiltinFlat IntegerT)]

gMono :: ASGBuilder Id
gMono = lam (Comp0 $ intT :--:> ReturnT boolT) $ do
      anInt <- AnArg <$> arg Z ix0
      zero <- AnId <$> lit (AnInteger 0)
      cond <- anInt #== zero
      ifThen <- ifte
      false <- AnId <$> lit (ABoolean False)
      troo  <- AnId <$> lit (ABoolean True)
      AnId <$> app' ifThen [cond,false,troo]
