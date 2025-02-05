module Covenant.Internal.ASGBuilder
  ( ASGBuilder (..),
    lit,
    prim,
    app,
  )
where

import Control.Monad.HashCons (HashConsT, MonadHashCons (refTo))
import Control.Monad.Reader (Reader, ask, local, runReader)
import Control.Monad.Trans (MonadTrans (lift))
import Covenant.Constant (AConstant)
import Covenant.Internal.ASGNode
  ( ASGNode (App, Lam, Lit, Prim),
    Arg (Arg),
    Id,
    PrimCall
      ( PrimCallOne,
        PrimCallSix,
        PrimCallThree,
        PrimCallTwo
      ),
    Ref (AnArg, AnId),
  )
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import Data.Word (Word64)
import Test.QuickCheck (Arbitrary (arbitrary), chooseEnum)
import Test.QuickCheck.GenT
  ( GenT (GenT),
    frequency,
    liftGen,
    oneof,
    runGenT,
    sized,
  )

-- | A helper monad for building up Covenant programs. In particular, this
-- enables hash consing. As it is a transformer, it can also be used in stacks.
--
-- @since 1.0.0
newtype ASGBuilder (m :: Type -> Type) (a :: Type)
  = ASGBuilder (HashConsT Id ASGNode m a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via HashConsT Id ASGNode m
  deriving
    ( -- | @since 1.0.0
      MonadTrans
    )
    via HashConsT Id ASGNode

-- | @since 1.0.0
deriving via
  (HashConsT Id ASGNode m)
  instance
    (Monad m) => MonadHashCons Id ASGNode (ASGBuilder m)

-- | Does not shrink.
--
-- @since 1.0.0
instance Arbitrary (ASGBuilder Identity Id) where
  {-# INLINEABLE arbitrary #-}
  arbitrary = do
    generated <- runGenT (sized go)
    pure $ runReader generated 0
    where
      go :: Int -> GenT (Reader Word64) (ASGBuilder Identity Id)
      go size
        | size <= 0 = aLiteral
        | otherwise = oneof [aLiteral, aPrim size, aLam size, anApp size]
      aLiteral :: GenT (Reader Word64) (ASGBuilder Identity Id)
      aLiteral = liftGen arbitrary >>= \n -> pure . lit $ n
      -- Note (Koz, 22/01/25): This technically can generate nonsensical
      -- expressions, but we can already do this anyway, as we can generate
      -- `App`s which would never work due to argument unsuitability. It should
      -- be fixed, though.
      aPrim :: Int -> GenT (Reader Word64) (ASGBuilder Identity Id)
      aPrim size =
        frequency
          [ (34, oneArg size),
            (40, twoArg size),
            (12, threeArg size),
            (2, sixArg size)
          ]
      oneArg :: Int -> GenT (Reader Word64) (ASGBuilder Identity Id)
      oneArg size = do
        r1 <- argOrId size
        f <- liftGen arbitrary
        pure $ r1 >>= \r1' -> prim (PrimCallOne f r1')
      twoArg :: Int -> GenT (Reader Word64) (ASGBuilder Identity Id)
      twoArg size = do
        r1 <- argOrId size
        r2 <- argOrId size
        f <- liftGen arbitrary
        pure $ r1 >>= \r1' -> r2 >>= \r2' -> prim (PrimCallTwo f r1' r2')
      threeArg :: Int -> GenT (Reader Word64) (ASGBuilder Identity Id)
      threeArg size = do
        r1 <- argOrId size
        r2 <- argOrId size
        r3 <- argOrId size
        f <- liftGen arbitrary
        pure $ r1 >>= \r1' -> r2 >>= \r2' -> r3 >>= \r3' -> prim (PrimCallThree f r1' r2' r3')
      sixArg :: Int -> GenT (Reader Word64) (ASGBuilder Identity Id)
      sixArg size = do
        r1 <- argOrId size
        r2 <- argOrId size
        r3 <- argOrId size
        r4 <- argOrId size
        r5 <- argOrId size
        r6 <- argOrId size
        f <- liftGen arbitrary
        pure $
          r1 >>= \r1' ->
            r2 >>= \r2' ->
              r3 >>= \r3' ->
                r4 >>= \r4' ->
                  r5 >>= \r5' -> r6 >>= \r6' -> prim (PrimCallSix f r1' r2' r3' r4' r5' r6')
      aLam :: Int -> GenT (Reader Word64) (ASGBuilder Identity Id)
      aLam size = do
        body <- expand (argOrId size)
        -- Note (Koz, 21/01/25): We 'bypass' our protections on construction of
        -- lambdas here for convenience, as otherwise, we would have to carry
        -- around a `Scope n`, with `n` changing. While not impossible, this
        -- would require existentialization (using something like `Some`), which
        -- doesn't really help us any (because we have full control anyway), but
        -- does make the code much harder to read and debug.
        pure $ body >>= \bodyRef -> refTo (Lam bodyRef)
      -- Note (Koz, 21/01/25): This is essentially `local`, but because GenT
      -- isn't an instance of MonadReader, we have to write it by hand. We could
      -- have defined an orphan instance instead, but I figured it'd be better
      -- not to.
      expand ::
        forall (a :: Type).
        GenT (Reader Word64) (ASGBuilder Identity a) ->
        GenT (Reader Word64) (ASGBuilder Identity a)
      expand (GenT f) = GenT $ \qcgen size -> local (+ 1) (f qcgen size)
      anApp :: Int -> GenT (Reader Word64) (ASGBuilder Identity Id)
      anApp size = do
        lhs <- aLam size
        rhs <- argOrId size
        -- Note (Koz, 21/01/25): This is technically not as general as it could
        -- be. By 'recycling' aLam, we always generate a 'fresh' lambda, rather
        -- than (possibly) re-using one available to us as an argument. This is
        -- not really practical to track at the moment, though once we have
        -- types, it could be done. For now, this works well enough.
        pure $ lhs >>= \lhsRef -> rhs >>= \rhsRef -> app (AnId lhsRef) rhsRef
      argOrId :: Int -> GenT (Reader Word64) (ASGBuilder Identity Ref)
      argOrId originalSize = do
        availableArgs <- lift ask
        if availableArgs == 0
          -- No arguments possible, so reduce the size and recurse
          then fmap AnId <$> go (originalSize `quot` 2)
          -- 20% chance we make an argument, 80% chance we don't
          else
            frequency
              [ (1, pure . AnArg . Arg <$> liftGen (chooseEnum (0, availableArgs - 1))),
                (4, fmap AnId <$> go (originalSize `quot` 2))
              ]

-- | Construct a literal (constant) value.
--
-- @since 1.0.0
lit ::
  forall (m :: Type -> Type).
  (Monad m) => AConstant -> ASGBuilder m Id
lit = refTo . Lit

-- | Construct a primitive function call.
--
-- @since 1.0.0
prim ::
  forall (m :: Type -> Type).
  (Monad m) => PrimCall -> ASGBuilder m Id
prim = refTo . Prim

-- | Construct a function application. The first argument is (an expression
-- evaluating to) a function, the second argument is (an expression evaluating
-- to) an argument.
--
-- = Important note
--
-- Currently, this does not verify that the first argument is indeed a function,
-- nor that the second argument is appropriate.
app ::
  forall (m :: Type -> Type).
  (Monad m) =>
  Ref -> Ref -> ASGBuilder m Id
app f x = refTo (App f x)
