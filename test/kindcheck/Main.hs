module Main (main) where

import Covenant.Index (count0, count1,ix0)
import Covenant.Test (ledgerTypes)
import Covenant.Type
  ( BuiltinFlatT (IntegerT),
    Constructor (Constructor),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (SOP,PlutusData),
    ValT (Abstraction, BuiltinFlat, Datatype),
    checkDataDecls,
    cycleCheck, AbstractTy(BoundAt), PlutusDataStrategy(ConstrData), checkEncodingArgs,
    )
import Covenant.DeBruijn (DeBruijn(Z))
import Data.Map qualified as M
import Data.Vector qualified as V
import Optics.Core (view)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.ExpectedFailure (expectFail)
import Test.Tasty.HUnit (assertFailure, testCase)

main :: IO ()
main =
  defaultMain . testGroup "DatatypeCycleCheck" $
    [ testCase "singleNonRec" $ runCycleCheck [maybee],
      testCase "singleSelfRec" $ runCycleCheck [intList],
      expectFail $ testCase "mutRecShouldFail" (runCycleCheck [mutRec1, mutRec2]),
      checkLedgerTypes,
      shouldFailEncodingCheck
    ]

checkLedgerTypes :: TestTree
checkLedgerTypes =
  testCase "kindCheckLedgerTypes"
    . either (assertFailure . show) pure
    . checkDataDecls
    . foldr (\x acc -> M.insert (view #datatypeName x) x acc) M.empty
    $ ledgerTypes

shouldFailEncodingCheck :: TestTree
shouldFailEncodingCheck = expectFail . testCase "encodingArgsShouldFail" $
  either (assertFailure . show) pure $ checkEncodingArgs (view #datatypeEncoding) testTyDict encodingMismatch
 where
   testTyDict = foldr (\decl acc -> M.insert (view #datatypeName decl) decl acc) M.empty [maybee,intList]

runCycleCheck :: [DataDeclaration AbstractTy] -> IO ()
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

maybee :: DataDeclaration AbstractTy
maybee = DataDeclaration "Maybe" count1 (V.fromList ctors) (PlutusData ConstrData)
  where
    ctors =
      [ Constructor "Nothing" V.empty,
        Constructor "Just" (V.singleton (Abstraction $ BoundAt  Z ix0))
      ]

intList :: DataDeclaration AbstractTy
intList = DataDeclaration "IntList" count0 (V.fromList ctors) SOP
  where
    ctors =
      [ Constructor "Empty" V.empty,
        Constructor "More" (V.fromList intListMore)
      ]

    intListMore :: [ValT AbstractTy]
    intListMore = [BuiltinFlat IntegerT, Datatype "IntList" V.empty]

encodingMismatch :: ValT AbstractTy
encodingMismatch = Datatype "Maybe" (V.fromList [Datatype "IntList" V.empty])

mutRec1 :: DataDeclaration AbstractTy
mutRec1 = DataDeclaration "MutRec1" count0 (V.fromList ctors) SOP
  where
    ctors = [Constructor "MutRec1" (V.singleton (Datatype "MutRec2" V.empty))]

mutRec2 :: DataDeclaration AbstractTy
mutRec2 = DataDeclaration "MutRec2" count0 (V.fromList ctors) SOP
  where
    ctors = [Constructor "MutRec2" (V.fromList [Datatype "MutRec1" V.empty])]
