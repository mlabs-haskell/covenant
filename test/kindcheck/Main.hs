{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use camelCase" #-}
module Main (main) where

import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index (count0, count1, ix0)
import Covenant.Test (ledgerTypes)
import Covenant.Type
  ( AbstractTy (BoundAt),
    BuiltinFlatT (IntegerT),
    CompT (Comp1),
    CompTBody (ReturnT, (:--:>)),
    Constructor (Constructor),
    DataDeclaration (DataDeclaration, OpaqueData),
    DataEncoding (PlutusData, SOP),
    PlutusDataStrategy (ConstrData),
    TyName,
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    checkDataDecls,
    checkEncodingArgs,
    cycleCheck,
    tyCon,
    tyvar,
  )
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
      simpleEncodingMismatch,
      nestedThunkArg,
      noThunkArgsToSOPTyCons_for_now,
      goodSOPArg
    ]

checkLedgerTypes :: TestTree
checkLedgerTypes =
  testCase "kindCheckLedgerTypes"
    . either (assertFailure . show) pure
    . checkDataDecls
    . foldr (\x acc -> M.insert (view #datatypeName x) x acc) M.empty
    $ ledgerTypes

encodingCheck :: String -> [DataDeclaration AbstractTy] -> ValT AbstractTy -> TestTree
encodingCheck testNm tyDict valT =
  testCase testNm $
    either (assertFailure . show) pure $
      checkEncodingArgs (view #datatypeEncoding) (mkTyDict tyDict) valT

shouldFailEncodingCheck :: String -> [DataDeclaration AbstractTy] -> ValT AbstractTy -> TestTree
shouldFailEncodingCheck tnm tyDict valT = expectFail $ encodingCheck tnm tyDict valT

simpleEncodingMismatch :: TestTree
simpleEncodingMismatch = shouldFailEncodingCheck "simpleEncodingMismatch" [maybee, intList] encodingMismatch

noThunkArgsToSOPTyCons_for_now :: TestTree
noThunkArgsToSOPTyCons_for_now = shouldFailEncodingCheck "no thunk args to SOP tycons (for now)" [maybeSOP] badSOPThunk

nestedThunkArg :: TestTree
nestedThunkArg = shouldFailEncodingCheck "nestedThunkArg" [maybee] badThunkArg

goodSOPArg :: TestTree
goodSOPArg = encodingCheck "goodSOP" [maybeSOP] goodSOP

mkTyDict :: forall a. [DataDeclaration a] -> M.Map TyName (DataDeclaration a)
mkTyDict = foldr (\decl acc -> M.insert (view #datatypeName decl) decl acc) M.empty

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
        Constructor "Just" (V.singleton (Abstraction $ BoundAt Z ix0))
      ]

maybeSOP :: DataDeclaration AbstractTy
maybeSOP = DataDeclaration "MaybeSOP" count1 (V.fromList ctors) SOP
  where
    ctors =
      [ Constructor "Nothing" V.empty,
        Constructor "Just" (V.singleton (Abstraction $ BoundAt Z ix0))
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

-- DATA ENCODED MAYBE, SOP ENCODED INTLIST
-- Maybe IntList
encodingMismatch :: ValT AbstractTy
encodingMismatch = Datatype "Maybe" (V.fromList [Datatype "IntList" V.empty])

-- forall a. (a -> a)
identitee :: ValT AbstractTy
identitee = ThunkT $ Comp1 (tyvar Z ix0 :--:> ReturnT (tyvar Z ix0))

-- DATA ENCODED MAYBE
-- Maybe (Maybe (forall a. a -> a))
badThunkArg :: ValT AbstractTy
badThunkArg = tyCon "Maybe" [tyCon "Maybe" [identitee]]

-- SOP ENCODED MAYBE
-- Maybe (Maybe (Maybe Integer))
goodSOP :: ValT AbstractTy
goodSOP = tyCon "MaybeSOP" [tyCon "MaybeSOP" [tyCon "MaybeSOP" [BuiltinFlat IntegerT]]]

-- NOTE Sean 7/2/2025: We are *temporarily* forbidding thunk arguments even to SOP encoded type constructors.
--                     This is not strictly necessary, and we can go back and change that if we have time, but it
--                     does greatly simplify getting a proof-of-concept off the ground.
-- SOP ENCODED MAYBE
-- Maybe (forall a. a -> a)
badSOPThunk :: ValT AbstractTy
badSOPThunk = tyCon "MaybeSOP" [identitee]

mutRec1 :: DataDeclaration AbstractTy
mutRec1 = DataDeclaration "MutRec1" count0 (V.fromList ctors) SOP
  where
    ctors = [Constructor "MutRec1" (V.singleton (Datatype "MutRec2" V.empty))]

mutRec2 :: DataDeclaration AbstractTy
mutRec2 = DataDeclaration "MutRec2" count0 (V.fromList ctors) SOP
  where
    ctors = [Constructor "MutRec2" (V.fromList [Datatype "MutRec1" V.empty])]
