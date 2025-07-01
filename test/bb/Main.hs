{-# LANGUAGE ViewPatterns #-}
module Main (main) where

-- import Data.Either (isRight)

import Control.Exception (throwIO)
import Control.Monad ((<=<))
import Covenant.Data
  ( mkBBF,
  )
import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Test
  ( DataDeclFlavor (Poly1PolyThunks),
    DataDeclSet (DataDeclSet),
    failLeft,
    prettyDeclSet,
    tyAppTestDatatypes,
    list,
    tree
  )
import Covenant.Type
  ( AbstractTy (BoundAt),
    CompT (CompT,Comp1),
    CompTBody (CompTBody, ReturnT, (:--:>)),
    ValT (Abstraction, ThunkT),
    Renamed(Unifiable),
    renameCompT,
    renameValT,
    runRenameM,
  )
import Covenant.Index (ix0,ix1,count0,count2)
import Data.Map qualified as M
import Data.Maybe (fromJust, catMaybes)
import Optics.Core (view)
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Property,
  )
import Data.Vector.NonEmpty qualified as NEV
import Test.Tasty (TestTree, adjustOption, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Test.Tasty.QuickCheck (QuickCheckTests, forAllShrinkShow, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "BB" $
    [ testProperty "All BBF transformations rename properly" bbFormRenames,
      testMonotypeBB,
      bbfList,
      bbfTree
    ]
  where
    -- These tests are suuuuppeeerr inefficient, it'd be ideal to run more but it'll take too long
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 500

{- This is the only reasonable property I can think of, and is ultimately more of a test of the
   "ensure there aren't any phantom type variables" than it is of the bb transform.

   Fortunately the transform itself is fairly straightforward and isn't likely to contain major errors.
-}
bbFormRenames :: Property
bbFormRenames = forAllShrinkShow (arbitrary @(DataDeclSet 'Poly1PolyThunks)) shrink prettyDeclSet $ \(DataDeclSet decls) ->
  case traverse mkBBF decls of
    Left _ -> False
    Right (catMaybes -> bbfDecls) ->
      let results = mapM (\valT -> case runRenameM . renameValT $ valT of
                              Left err -> Left (err,valT)
                              Right res -> Right res) bbfDecls
      in case results of -- all (isRight . runRenameM . renameValT) bbfDecls
          Right{} -> True
          Left err -> error (show err)

bbfList :: TestTree
bbfList = testCase "bbfList" $ do
  let bbf = mkBBF list
  bbf' <- either (assertFailure . show) (maybe (assertFailure "no bbf for list") pure)  bbf
  renamed <- either (assertFailure . show) pure . runRenameM . renameValT $ bbf'
  assertEqual "bbfList" renamed expectedListBBF
  where
    expectedListBBF  =   ThunkT (CompT count2 (
                            CompTBody (fromJust . NEV.fromList $ [
                                Abstraction (Unifiable ix1),
                                ThunkT (CompT count0 (
                                           CompTBody (fromJust . NEV.fromList $ [Abstraction (Unifiable ix0),
                                                      Abstraction (Unifiable ix1),
                                                      Abstraction (Unifiable ix1)]))),Abstraction (Unifiable ix1)])))

bbfTree :: TestTree
bbfTree = testCase "bbfTree" $ do
  let bbf = mkBBF tree
  bbf' <- either (assertFailure . show) (maybe (assertFailure "no bbf for tree") pure)  bbf
  renamed <- either (assertFailure . show) pure . runRenameM . renameValT $ bbf'
  assertEqual "bbfList" renamed expectedTreeBBF
 where
   expectedTreeBBF = ThunkT (CompT count2 (
                                CompTBody (fromJust . NEV.fromList $ [
                                              ThunkT $ CompT count0 (CompTBody (fromJust . NEV.fromList $ [
                                                Abstraction (Unifiable ix1),
                                                Abstraction (Unifiable ix1),
                                                Abstraction (Unifiable ix1)
                                                                                                ]))
                                              , ThunkT $ CompT count0 (CompTBody (fromJust . NEV.fromList $ [
                                                                                     Abstraction (Unifiable ix0),
                                                                                     Abstraction (Unifiable ix1)
                                                                                                            ]))
                                              , Abstraction (Unifiable ix1)
                                                                     ])
                                          ))

-- Simple datatype unification unit test. Checks whether `data Unit = Unit` has the expected BB form
testMonotypeBB :: TestTree
testMonotypeBB = testCase "unitBbf" $ do
  let expected = Comp1 $ Abstraction (BoundAt Z ix0) :--:> ReturnT (Abstraction $ BoundAt Z ix0)
  expected' <- failLeft . runRenameM . renameCompT $ expected
  actual <- case fromJust . (view #bbForm <=< M.lookup "Unit") $ tyAppTestDatatypes of
    ThunkT inner -> either (throwIO . userError . show) pure . runRenameM $ renameCompT inner
    _ -> assertFailure "BB form not a thunk!"
  assertEqual "unit bbf" expected' actual
