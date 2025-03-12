{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Covenant.DeBruijn (DeBruijn (Z))
import Covenant.Index (count1, ix0)
import Covenant.Test (Concrete (Concrete))
import Covenant.Type
  ( AbstractTy (BoundAt),
    CompT (CompT),
    ValT (Abstraction),
    checkApp,
    renameCompT,
    renameValT,
    runRenameM,
    pattern ReturnT,
    pattern (:--:>),
  )
import Test.QuickCheck
  ( Property,
    arbitrary,
    counterexample,
    forAll,
    (===),
  )
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "Type application" $
    [ testProperty "id applied to concrete type" propIdConcrete
    ]
  where
    -- Note (Koz, 26/02/2025): By default, QuickCheck runs only 100 tests per
    -- property, which is far to few. Using the method below, we can ensure that
    -- we run a decent number of tests, while also permitting more than this to
    -- be set via the CLI if we want.
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 10_000

-- Test cases and properties

propIdConcrete :: Property
propIdConcrete = forAll arbitrary $ \(Concrete t) ->
  let aVar = Abstraction (BoundAt Z ix0)
      idT = CompT count1 $ aVar :--:> ReturnT aVar
   in case runRenameM . renameCompT $ idT of
        Left err -> counterexample (show err) False
        Right renamedIdT -> case runRenameM . renameValT $ t of
          Left err -> counterexample (show err) False
          Right renamedT -> case checkApp renamedIdT [renamedT] of
            Nothing -> counterexample "application failed" False
            Just resultT -> resultT === renamedT
