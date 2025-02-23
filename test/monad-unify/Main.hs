module Main (main) where

import Control.Monad.Unify
  ( UnifyStatus (Defined, Fresh),
    UnifyT,
    runUnifyT,
    status,
    unify,
  )
import Data.Functor.Identity (Identity, runIdentity)
import Data.Kind (Type)
import Test.QuickCheck
  ( Arbitrary (arbitrary, shrink),
    Property,
    forAllShrinkShow,
    (===),
  )
import Test.QuickCheck.Poly (B)
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.QuickCheck (QuickCheckTests, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "MonadUnify" $
    [ testProperty "Unify fresh with definition" propFreshDef,
      testProperty "Fresh variables' status agrees" propFreshStatus
    ]
  where
    -- Note (Koz, 18/02/2025): By default, QuickCheck runs very few tests for
    -- any given property (100). This ensures that we run a sensible number of
    -- tests, while not blocking us from asking for more via the CLI.
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 10_000

-- Properties

propFreshDef :: Property
propFreshDef = forAllShrinkShow arbitrary shrink show $ \(v :: EnumA, def :: B) ->
  let result = runTestM (unify v (Right def) >> status v)
   in result === Just (Defined def)

propFreshStatus :: Property
propFreshStatus = forAllShrinkShow arbitrary shrink show $ \(v :: EnumA) ->
  let result = runTestM (status v)
   in result === Just Fresh

-- Helpers

newtype EnumA = EnumA Word
  deriving (Eq, Ord, Enum, Arbitrary) via Word
  deriving stock (Show)

runTestM :: forall (a :: Type). UnifyT EnumA B Identity a -> Maybe a
runTestM = fmap fst . runIdentity . runUnifyT
