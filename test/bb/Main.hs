{-# LANGUAGE ViewPatterns #-}

module Main (main) where

-- import Data.Either (isRight)

import Control.Exception (throwIO)
import Control.Monad ((<=<))
import Covenant.Data
  ( mkBBF,
  )
import Covenant.DeBruijn (DeBruijn (S, Z))
import Covenant.Index (ix0, ix1)
import Covenant.Test
  ( DataDeclFlavor (Poly1PolyThunks),
    DataDeclSet (DataDeclSet),
    failLeft,
    list,
    prettyDeclSet,
    renameCompT,
    renameValT,
    runRenameM,
    tree,
    tyAppTestDatatypes,
    unsafeTyCon,
    weirderList,
  )
import Covenant.Type
  ( AbstractTy (BoundAt),
    CompT (Comp0, Comp1, Comp2),
    CompTBody (ReturnT, (:--:>)),
    ValT (Abstraction, ThunkT),
    tyvar,
  )
import Data.Map qualified as M
import Data.Maybe (catMaybes, fromJust)
import Optics.Core (view)
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Property,
  )
import Test.Tasty (TestTree, adjustOption, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Test.Tasty.QuickCheck (QuickCheckTests, forAllShrinkShow, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "BB" $
    [ testProperty "All BBF transformations rename properly" bbFormRenames,
      testMonotypeBB,
      bbfList,
      bbfTree,
      bbfWeirderList
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
      let results =
            mapM
              ( \valT -> case runRenameM mempty . renameValT $ valT of
                  Left err -> Left (err, valT)
                  Right res -> Right res
              )
              bbfDecls
       in case results of -- all (isRight . runRenameM . renameValT) bbfDecls
            Right {} -> True
            Left err -> error (show err)

bbfList :: TestTree
bbfList = testCase "bbfList" $ do
  let bbf = mkBBF list
  bbf' <- either (assertFailure . show) (maybe (assertFailure "no bbf for list") pure) bbf
  assertEqual "bbfList" expectedListBBF bbf'
  where
    expectedListBBF =
      ThunkT
        ( Comp2
            ( tyvar Z ix1
                :--:> ThunkT
                  ( Comp0
                      ( tyvar (S Z) ix0
                          :--:> tyvar (S Z) ix1
                          :--:> ReturnT (tyvar (S Z) ix1)
                      )
                  )
                :--:> ReturnT (tyvar Z ix1)
            )
        )

bbfTree :: TestTree
bbfTree = testCase "bbfTree" $ do
  let bbf = mkBBF tree
  bbf' <- either (assertFailure . show) (maybe (assertFailure "no bbf for tree") pure) bbf
  assertEqual "bbfList" expectedTreeBBF bbf'
  where
    expectedTreeBBF =
      ThunkT
        ( Comp2
            ( ThunkT
                ( Comp0
                    ( tyvar (S Z) ix1
                        :--:> tyvar (S Z) ix1
                        :--:> ReturnT (tyvar (S Z) ix1)
                    )
                )
                :--:> ThunkT
                  ( Comp0
                      ( tyvar (S Z) ix0
                          :--:> ReturnT (tyvar (S Z) ix1)
                      )
                  )
                :--:> ReturnT (tyvar Z ix1)
            )
        )

bbfWeirderList :: TestTree
bbfWeirderList = testCase "bbfWeirderList" $ do
  let bbf = mkBBF weirderList
  bbf' <- either (assertFailure . show) (maybe (assertFailure "no bbf for tree") pure) bbf
  assertEqual "bbfWeirderTree" expectedWeirdBBF bbf'
  where
    -- forall a r. (Maybe (a,r) -> r) -> r
    expectedWeirdBBF =
      ThunkT
        ( Comp2
            ( ThunkT
                ( Comp0
                    ( unsafeTyCon "Maybe" [unsafeTyCon "Pair" [tyvar (S Z) ix0, tyvar (S Z) ix1]]
                        :--:> ReturnT (tyvar (S Z) ix1)
                    )
                )
                :--:> ReturnT (tyvar Z ix1)
            )
        )

-- Simple datatype unification unit test. Checks whether `data Unit = Unit` has the expected BB form
testMonotypeBB :: TestTree
testMonotypeBB = testCase "unitBbf" $ do
  let expected = Comp1 $ Abstraction (BoundAt Z ix0) :--:> ReturnT (Abstraction $ BoundAt Z ix0)
  expected' <- failLeft . runRenameM mempty . renameCompT $ expected
  actual <- case fromJust . (view #bbForm <=< M.lookup "Unit") $ tyAppTestDatatypes of
    ThunkT inner -> either (throwIO . userError . show) pure . runRenameM mempty $ renameCompT inner
    _ -> assertFailure "BB form not a thunk!"
  assertEqual "unit bbf" expected' actual
