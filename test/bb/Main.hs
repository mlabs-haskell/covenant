module Main (main) where

import Covenant.Data
  ( mkBBF,
  )
import Covenant.Test
  ( DataDeclFlavor (Poly1PolyThunks),
    DataDeclSet (DataDeclSet),
    prettyDeclSet,
    failLeft,
    tyAppTestDatatypes
  )
import Covenant.Type
    ( renameValT,
      runRenameM,
      ValT(ThunkT, Abstraction),
      CompTBody((:--:>), ReturnT),
      AbstractTy(BoundAt),
      renameCompT,
      CompT(Comp1) )
-- import Data.Either (isRight)
import Control.Monad((<=<))
import Data.Map qualified as M
import Data.Maybe (mapMaybe,fromJust)
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Property,
  )
import Test.Tasty (adjustOption, defaultMain, testGroup, TestTree)
import Test.Tasty.HUnit(testCase, assertFailure, assertEqual)
import Test.Tasty.QuickCheck (QuickCheckTests, forAllShrinkShow, testProperty)
import Optics.Core (view)
import Covenant.DeBruijn (DeBruijn(Z))
import Covenant.Index (ix0)
import Control.Exception (throwIO)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "BB" $
    [testProperty "All BBF transformations rename properly" bbFormRenames
    ,testMonotypeBB]
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
  let bbfDecls = mapMaybe mkBBF decls -- only gives 'Nothing' if it's a 0 constructor type (a la `Void`) so no real point testing
      results = mapM (runRenameM . renameValT) bbfDecls
   in case results of -- all (isRight . runRenameM . renameValT) bbfDecls
        Left err -> error (show err)
        Right _ -> True

-- Simple datatype unification unit test. Checks whether `data Unit = Unit` has the expected BB form
testMonotypeBB :: TestTree
testMonotypeBB = testCase "unitBbf" $ do
  let expected = Comp1 $ Abstraction (BoundAt Z ix0) :--:> ReturnT (Abstraction $ BoundAt Z ix0)
  expected' <- failLeft . runRenameM . renameCompT $ expected
  actual <- case fromJust . (view #bbForm <=< M.lookup "Unit") $ tyAppTestDatatypes of
    ThunkT inner -> either (throwIO . userError . show) pure . runRenameM $ renameCompT inner
    _ -> assertFailure "BB form not a thunk!"
  assertEqual "unit bbf" expected' actual
