module Main (main) where

import Covenant.Index (count0, count1)
import Covenant.Type
  ( BuiltinFlatT (IntegerT),
    Constructor (Constructor),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (SOP),
    ValT (Abstraction, BuiltinFlat, Datatype),
    cycleCheck, checkDataDecls,
  )
import Covenant.Test (ledgerTypes)
import Data.Map qualified as M
import Data.Vector qualified as V
import Test.Tasty (defaultMain, testGroup, TestTree)
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.HUnit (assertFailure, testCase)
import Optics.Core (view)

main :: IO ()
main =
  defaultMain . testGroup "DatatypeCycleCheck" $
    [ testCase "singleNonRec" $ runCycleCheck [maybee],
      testCase "singleSelfRec" $ runCycleCheck [intList],
      expectFail $ testCase "mutRecShouldFail" (runCycleCheck [mutRec1, mutRec2]),
      checkLedgerTypes
    ]

checkLedgerTypes :: TestTree
checkLedgerTypes = testCase "kindCheckLedgerTypes"
                   . either (assertFailure . show) pure
                   . checkDataDecls
                   . foldr (\x acc -> M.insert (view #datatypeName x) x acc) M.empty
                   $ ledgerTypes

runCycleCheck :: [DataDeclaration ()] -> IO ()
runCycleCheck decls = case cycleCheck declMap of
  Nothing -> pure ()
  Just err -> assertFailure $ show err
  where
    declMap =
      foldr
        ( \dd acc -> case dd of
            OpaqueData {} -> acc
            DataDeclaration tn _ _ _ -> M.insert tn dd acc
        )
        M.empty
        decls

maybee :: DataDeclaration ()
maybee = DataDeclaration "Maybe" count1 (V.fromList ctors) SOP
  where
    ctors =
      [ Constructor "Nothing" V.empty,
        Constructor "Just" (V.singleton (Abstraction ()))
      ]

intList :: DataDeclaration ()
intList = DataDeclaration "IntList" count0 (V.fromList ctors) SOP
  where
    ctors =
      [ Constructor "Empty" V.empty,
        Constructor "More" (V.fromList intListMore)
      ]

    intListMore :: [ValT ()]
    intListMore = [BuiltinFlat IntegerT, Datatype "IntList" V.empty]

mutRec1 :: DataDeclaration ()
mutRec1 = DataDeclaration "MutRec1" count0 (V.fromList ctors) SOP
  where
    ctors = [Constructor "MutRec1" (V.singleton (Datatype "MutRec2" V.empty))]

mutRec2 :: DataDeclaration ()
mutRec2 = DataDeclaration "MutRec2" count0 (V.fromList ctors) SOP
  where
    ctors = [Constructor "MutRec2" (V.fromList [Datatype "MutRec1" V.empty])]
