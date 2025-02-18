module Main (main) where

import Control.Monad.Unify
  ( UnifyResult (DoesNotUnify, Equivalent, UnifiesTo),
    runUnifyT,
    unify,
  )
import Data.Functor.Identity (runIdentity)
import Test.QuickCheck (Property, arbitrary, forAllShrinkShow, shrink)
import Test.QuickCheck.Monadic (assert, monadic, pre, run)
import Test.QuickCheck.Poly (B, OrdA)
import Test.Tasty (adjustOption, defaultMain, testGroup)
import Test.Tasty.QuickCheck (QuickCheckMaxSize, QuickCheckTests, testProperty)

main :: IO ()
main =
  defaultMain . adjustOption moreTests . testGroup "MonadUnify" $
    [ testProperty "equal constants unify" equalConstantProp,
      adjustOption bigger $ testProperty "unequal constants do not unify" differentConstantProp,
      testProperty "fresh variables are equivalent" freshVarEquivProp,
      testProperty "binding any element of an equivalence class binds all" bindECProp,
      testProperty "variable-to-variable binding is reflexive" ecReflexiveProp,
      testProperty "variable-to-variable binding is symmetric" ecSymmetricProp,
      testProperty "variable-to-variable binding is transitive" ecTransitiveProp,
      testProperty "bound variable unifies with binding" boundBindingUnifyProp,
      adjustOption bigger $ testProperty "bound variables does not unify with anything else" boundNotBindingProp
    ]
  where
    -- Note (Koz, 18/02/2025): By default, QuickCheck runs very few tests for
    -- any given property (100). This ensures that we run a sensible number of
    -- tests, while not blocking us from asking for more via the CLI.
    moreTests :: QuickCheckTests -> QuickCheckTests
    moreTests = max 10_000
    -- Note (Koz, 18/02/2025): When using `pre`, the default max size of 100 is
    -- very likely to cause collisions, leading to an unacceptably high discard
    -- rate. This ensures we minimize collisions, while also allowing larger
    -- sizes to be set at the CLI if we want them.
    bigger :: QuickCheckMaxSize -> QuickCheckMaxSize
    bigger = max 10_000

-- Properties

equalConstantProp :: Property
equalConstantProp = forAllShrinkShow arbitrary shrink show $ \(var1 :: OrdA, var2 :: OrdA, c :: B) ->
  monadic (runIdentity . runUnifyT) $ do
    result <- run . unify var1 (Right c) $ (\_ -> unify var2 (Right c) pure)
    assert (result == UnifiesTo c)

differentConstantProp :: Property
differentConstantProp = forAllShrinkShow arbitrary shrink show $ \(var :: OrdA, c1 :: B, c2 :: B) ->
  monadic (runIdentity . runUnifyT) $ do
    pre (c1 /= c2)
    result <- run . unify var (Right c1) $ (\_ -> unify var (Right c2) pure)
    assert (result == DoesNotUnify var (Right c2))

freshVarEquivProp :: Property
freshVarEquivProp = forAllShrinkShow arbitrary shrink show $ \(var1 :: OrdA, var2 :: OrdA) ->
  monadic (runIdentity . runUnifyT) $ do
    result <- run . unify var1 (Left var2 :: Either OrdA B) $ pure
    assert (result == Equivalent)

bindECProp :: Property
bindECProp = forAllShrinkShow arbitrary shrink show $ \(var1 :: OrdA, var2 :: OrdA, c :: B) ->
  monadic (runIdentity . runUnifyT) $ do
    bindOuter <- run . unify var1 (Left var2) $ (\_ -> unify var1 (Right c) (\_ -> unify var2 (Right c) pure))
    bindInner <- run . unify var1 (Left var2) $ (\_ -> unify var2 (Right c) (\_ -> unify var1 (Right c) pure))
    assert (bindOuter == bindInner)

ecReflexiveProp :: Property
ecReflexiveProp = forAllShrinkShow arbitrary shrink show $ \(var :: OrdA) ->
  monadic (runIdentity . runUnifyT) $ do
    result <- run . unify var (Left var :: Either OrdA B) $ pure
    assert (result == Equivalent)

ecSymmetricProp :: Property
ecSymmetricProp = forAllShrinkShow arbitrary shrink show $ \(var1 :: OrdA, var2 :: OrdA) ->
  monadic (runIdentity . runUnifyT) $ do
    bind1Then2 <- run . unify var1 (Left var2 :: Either OrdA B) $ (\_ -> unify var2 (Left var1) pure)
    bind2Then1 <- run . unify var2 (Left var1) $ (\_ -> unify var1 (Left var2) pure)
    assert (bind1Then2 == bind2Then1)

ecTransitiveProp :: Property
ecTransitiveProp = forAllShrinkShow arbitrary shrink show $ \(var1 :: OrdA, var2 :: OrdA, var3 :: OrdA) ->
  monadic (runIdentity . runUnifyT) $ do
    result <- run . unify var1 (Left var2 :: Either OrdA B) $ (\_ -> unify var2 (Left var3) $ \_ -> unify var1 (Left var3) pure)
    assert (result == Equivalent)

boundBindingUnifyProp :: Property
boundBindingUnifyProp = forAllShrinkShow arbitrary shrink show $ \(var :: OrdA, c :: B) ->
  monadic (runIdentity . runUnifyT) $ do
    result <- run . unify var (Right c) $ pure
    assert (result == UnifiesTo c)

boundNotBindingProp :: Property
boundNotBindingProp = forAllShrinkShow arbitrary shrink show $ \(var :: OrdA, c1 :: B, c2 :: B) ->
  monadic (runIdentity . runUnifyT) $ do
    pre (c1 /= c2)
    result <- run . unify var (Right c1) $ (\_ -> unify var (Right c2) pure)
    assert (result == DoesNotUnify var (Right c2))
