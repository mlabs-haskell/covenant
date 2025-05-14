module Main (main) where

import Covenant.Data
  ( mkBBF,
  )
import Covenant.Test
  ( DataDeclFlavor (Poly1PolyThunks),
    DataDeclSet (DataDeclSet),
    prettyDeclSet,
  )
import Covenant.Type (renameValT, runRenameM)
-- import Data.Either (isRight)
import Data.Maybe (mapMaybe)
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Property,
  )
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.QuickCheck (QuickCheckTests, forAllShrinkShow, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "BB" $
    [testProperty "All BBF transformations rename properly" bbFormRenames]
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
