{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Covenant.ASG (defaultDatatypes)
import Covenant.Prim
  ( OneArgFunc
      ( BData,
        FstPair,
        HeadList,
        IData,
        ListData,
        MapData,
        NullList,
        SerialiseData,
        SndPair,
        TailList,
        UnBData,
        UnConstrData,
        UnIData,
        UnListData,
        UnMapData
      ),
    SixArgFunc (CaseData, ChooseData),
    ThreeArgFunc (CaseList, ChooseList),
    TwoArgFunc (ConstrData, EqualsData, MkCons, MkPairData),
    typeOneArgFunc,
    typeSixArgFunc,
    typeThreeArgFunc,
    typeTwoArgFunc,
  )
import Covenant.Type
  ( AbstractTy (BoundAt),
    CompT (Comp0),
    Renamed (Unifiable),
    ValT (Datatype, ThunkT),
    arity,
    boolT,
    byteStringT,
    checkApp,
    integerT,
    renameCompT,
    renameValT,
    runRenameM,
    pattern ReturnT,
    pattern (:--:>),
  )
import Data.Functor.Classes (liftEq)
import Data.Functor.Identity (Identity (Identity))
import Data.Kind (Type)
import Data.Vector qualified as Vector
import Test.QuickCheck
  ( Arbitrary (arbitrary),
    Property,
    counterexample,
    forAll,
    property,
    (===),
  )
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
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
        ],
      testGroup
        "Application with data types"
        [ testGroup
            "One argument"
            [ testCase "FstPair" unitFstPair,
              testCase "SndPair" unitSndPair,
              testCase "HeadList" unitHeadList,
              testCase "TailList" unitTailList,
              testCase "NullList" unitNullList,
              testCase "MapData" unitMapData,
              testCase "ListData" unitListData,
              testCase "IData" unitIData,
              testCase "BData" unitBData,
              testCase "UnConstrData" unitUnConstrData,
              testCase "UnMapData" unitUnMapData,
              testCase "UnListData" unitUnListData,
              testCase "UnIData" unitUnIData,
              testCase "UnBData" unitUnBData,
              testCase "SerialiseData" unitSerialiseData
            ],
          testGroup
            "Two arguments"
            [ testCase "MkCons" unitMkCons,
              testCase "ConstrData" unitConstrData,
              testCase "EqualsData" unitEqualsData,
              testCase "MkPairData" unitMkPairData
            ],
          testGroup
            "Three arguments"
            [ testCase "ChooseList" unitChooseList,
              testCase "CaseList" unitCaseList
            ],
          testGroup
            "Six arguments"
            [ testCase "ChooseData" unitChooseData,
              testCase "CaseData" unitCaseData
            ]
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

prop6Args :: Property
prop6Args = mkArgProp typeSixArgFunc 6

prop6Rename :: Property
prop6Rename = mkRenameProp typeSixArgFunc

unitFstPair :: IO ()
unitFstPair = withRenamedComp (typeOneArgFunc FstPair) $ \renamedFunT ->
  withRenamedVals [Datatype "Pair" . Vector.fromList $ [integerT, byteStringT]] $
    tryAndApply integerT renamedFunT

unitSndPair :: IO ()
unitSndPair = withRenamedComp (typeOneArgFunc SndPair) $ \renamedFunT ->
  withRenamedVals [Datatype "Pair" . Vector.fromList $ [integerT, byteStringT]] $
    tryAndApply byteStringT renamedFunT

unitHeadList :: IO ()
unitHeadList = withRenamedComp (typeOneArgFunc HeadList) $ \renamedFunT ->
  withRenamedVals [Datatype "List" . Vector.singleton $ integerT] $
    tryAndApply integerT renamedFunT

unitTailList :: IO ()
unitTailList = withRenamedComp (typeOneArgFunc TailList) $ \renamedFunT ->
  withRenamedVals (Identity . Datatype "List" . Vector.singleton $ integerT) $ \(Identity renamedArgT) ->
    tryAndApply renamedArgT renamedFunT [renamedArgT]

unitNullList :: IO ()
unitNullList = withRenamedComp (typeOneArgFunc NullList) $ \renamedFunT ->
  withRenamedVals [Datatype "List" . Vector.singleton $ integerT] $
    tryAndApply boolT renamedFunT

unitMapData :: IO ()
unitMapData = withRenamedComp (typeOneArgFunc MapData) $ \renamedFunT ->
  let pairDataT = Datatype "Pair" . Vector.fromList $ [dataT, dataT]
   in withRenamedVals [Datatype "List" . Vector.singleton $ pairDataT] $
        tryAndApply dataT renamedFunT

unitListData :: IO ()
unitListData = withRenamedComp (typeOneArgFunc ListData) $ \renamedFunT ->
  withRenamedVals [Datatype "List" . Vector.singleton $ dataT] $
    tryAndApply dataT renamedFunT

unitIData :: IO ()
unitIData = withRenamedComp (typeOneArgFunc IData) $ \renamedFunT ->
  withRenamedVals [integerT] $ tryAndApply dataT renamedFunT

unitBData :: IO ()
unitBData = withRenamedComp (typeOneArgFunc BData) $ \renamedFunT ->
  withRenamedVals [byteStringT] $ tryAndApply dataT renamedFunT

unitUnConstrData :: IO ()
unitUnConstrData = withRenamedComp (typeOneArgFunc UnConstrData) $ \renamedFunT ->
  withRenamedVals (Identity dataT) $ \(Identity renamedArgT) ->
    let listDataT = Datatype "List" . Vector.singleton $ dataT
        returnT = Datatype "Pair" . Vector.fromList $ [integerT, listDataT]
     in tryAndApply returnT renamedFunT [renamedArgT]

unitUnMapData :: IO ()
unitUnMapData = withRenamedComp (typeOneArgFunc UnMapData) $ \renamedFunT ->
  withRenamedVals (Identity dataT) $ \(Identity renamedArgT) ->
    let pairDataT = Datatype "Pair" . Vector.fromList $ [dataT, dataT]
        listPairDataT = Datatype "List" . Vector.singleton $ pairDataT
     in tryAndApply listPairDataT renamedFunT [renamedArgT]

unitUnListData :: IO ()
unitUnListData = withRenamedComp (typeOneArgFunc UnListData) $ \renamedFunT ->
  withRenamedVals [dataT] $
    tryAndApply (Datatype "List" . Vector.singleton $ dataT) renamedFunT

unitUnIData :: IO ()
unitUnIData = withRenamedComp (typeOneArgFunc UnIData) $ \renamedFunT ->
  withRenamedVals [dataT] $ tryAndApply integerT renamedFunT

unitUnBData :: IO ()
unitUnBData = withRenamedComp (typeOneArgFunc UnBData) $ \renamedFunT ->
  withRenamedVals [dataT] $ tryAndApply byteStringT renamedFunT

unitSerialiseData :: IO ()
unitSerialiseData = withRenamedComp (typeOneArgFunc SerialiseData) $ \renamedFunT ->
  withRenamedVals [dataT] $ tryAndApply byteStringT renamedFunT

unitMkCons :: IO ()
unitMkCons = withRenamedComp (typeTwoArgFunc MkCons) $ \renamedFunT ->
  let listT = Datatype "List" . Vector.singleton $ integerT
   in withRenamedVals [integerT, listT] $ tryAndApply listT renamedFunT

unitConstrData :: IO ()
unitConstrData = withRenamedComp (typeTwoArgFunc ConstrData) $ \renamedFunT ->
  let listT = Datatype "List" . Vector.singleton $ dataT
   in withRenamedVals [integerT, listT] $ tryAndApply dataT renamedFunT

unitEqualsData :: IO ()
unitEqualsData = withRenamedComp (typeTwoArgFunc EqualsData) $ \renamedFunT ->
  withRenamedVals [dataT, dataT] $ tryAndApply boolT renamedFunT

unitMkPairData :: IO ()
unitMkPairData = withRenamedComp (typeTwoArgFunc MkPairData) $ \renamedFunT ->
  let pairDataT = Datatype "Pair" . Vector.fromList $ [dataT, dataT]
   in withRenamedVals [dataT, dataT] $ tryAndApply pairDataT renamedFunT

unitChooseList :: IO ()
unitChooseList = withRenamedComp (typeThreeArgFunc ChooseList) $ \renamedFunT ->
  let listT = Datatype "List" . Vector.singleton $ integerT
   in withRenamedVals [listT, byteStringT, byteStringT] $
        tryAndApply byteStringT renamedFunT

unitCaseList :: IO ()
unitCaseList = withRenamedComp (typeThreeArgFunc CaseList) $ \renamedFunT ->
  let listT = Datatype "List" . Vector.singleton $ integerT
      thunkT = ThunkT $ Comp0 $ integerT :--:> listT :--:> ReturnT byteStringT
   in withRenamedVals [byteStringT, thunkT, listT] $
        tryAndApply byteStringT renamedFunT

unitChooseData :: IO ()
unitChooseData = withRenamedComp (typeSixArgFunc ChooseData) $ \renamedFunT ->
  withRenamedVals [dataT, integerT, integerT, integerT, integerT, integerT] $
    tryAndApply integerT renamedFunT

unitCaseData :: IO ()
unitCaseData = withRenamedComp (typeSixArgFunc CaseData) $ \renamedFunT ->
  let listDataT = Datatype "List" . Vector.singleton $ dataT
      pairDataT = Datatype "Pair" . Vector.fromList $ [dataT, dataT]
      listPairDataT = Datatype "List" . Vector.singleton $ pairDataT
      constrThunkT = ThunkT $ Comp0 $ integerT :--:> listDataT :--:> ReturnT integerT
      mapThunkT = ThunkT $ Comp0 $ listPairDataT :--:> ReturnT integerT
      listThunkT = ThunkT $ Comp0 $ listDataT :--:> ReturnT integerT
      integerThunkT = ThunkT $ Comp0 $ integerT :--:> ReturnT integerT
      byteStringThunkT = ThunkT $ Comp0 $ byteStringT :--:> ReturnT integerT
   in withRenamedVals [constrThunkT, mapThunkT, listThunkT, integerThunkT, byteStringThunkT, dataT] $
        tryAndApply integerT renamedFunT

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

withRenamedComp ::
  CompT AbstractTy ->
  (CompT Renamed -> IO ()) ->
  IO ()
withRenamedComp t f = case runRenameM . renameCompT $ t of
  Left err -> assertFailure $ "Could not rename: " <> show err
  Right t' -> f t'

withRenamedVals ::
  forall (t :: Type -> Type).
  (Traversable t) =>
  t (ValT AbstractTy) ->
  (t (ValT Renamed) -> IO ()) ->
  IO ()
withRenamedVals vals f = case runRenameM . traverse renameValT $ vals of
  Left err -> assertFailure $ "Could not rename: " <> show err
  Right vals' -> f vals'

tryAndApply ::
  ValT Renamed ->
  CompT Renamed ->
  [ValT Renamed] ->
  IO ()
tryAndApply expected f xs = case checkApp defaultDatatypes f . fmap Just $ xs of
  Left err -> assertFailure $ "Could not apply: " <> show err
  Right res -> assertEqual "" expected res

dataT :: forall (a :: Type). ValT a
dataT = Datatype "Data" Vector.empty
