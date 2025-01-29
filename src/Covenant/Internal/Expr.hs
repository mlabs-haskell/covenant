module Covenant.Internal.Expr
  ( Id (..),
    Arg (..),
    Ref (..),
    PrimCall (..),
    Expr (..),
    ExprBuilder (..),
    lit,
    prim,
    app,
    idOf,
  )
where

import Control.Monad.Reader (Reader, ask, local, runReader)
import Control.Monad.State.Strict (State, get, put)
import Control.Monad.Trans (lift)
import Covenant.Constant (AConstant)
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
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

-- | A unique identifier for a node in a Covenant program.
--
-- @since 1.0.0
newtype Id = Id Word64
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord
    )
    via Word64
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

-- | An argument passed to a function in a Covenant program.
--
-- @since 1.0.0
newtype Arg = Arg Word64
  deriving
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord
    )
    via Word64
  deriving stock
    ( -- | @since 1.0.0
      Show
    )

-- | A general reference in a Covenant program. This is either a computation
-- (represented by its unique 'Id') or a function argument (represented by an
-- 'Arg').
--
-- @since 1.0.0
data Ref = AnArg Arg | AnId Id
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A call to a Plutus primitive.
--
-- @since 1.0.0
data PrimCall
  = PrimCallOne OneArgFunc Ref
  | PrimCallTwo TwoArgFunc Ref Ref
  | PrimCallThree ThreeArgFunc Ref Ref Ref
  | PrimCallSix SixArgFunc Ref Ref Ref Ref Ref Ref
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A node in a Covenant program.
--
-- @since 1.0.0
data Expr
  = Lit AConstant
  | Prim PrimCall
  | Lam Ref
  | App Ref Ref
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A helper monad for building up Covenant programs. In particular, this
-- enables hash consing.
--
-- @since 1.0.0
newtype ExprBuilder (a :: Type) = ExprBuilder (State (Bimap Id Expr) a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via (State (Bimap Id Expr))

-- | Does not shrink.
--
-- @since 1.0.0
instance Arbitrary (ExprBuilder Id) where
  {-# INLINEABLE arbitrary #-}
  arbitrary = do
    generated <- runGenT (sized go)
    pure $ runReader generated 0
    where
      go :: Int -> GenT (Reader Word64) (ExprBuilder Id)
      go size
        | size <= 0 = aLiteral
        | otherwise = oneof [aLiteral, aPrim size, aLam size, anApp size]
      aLiteral :: GenT (Reader Word64) (ExprBuilder Id)
      aLiteral = liftGen arbitrary >>= \n -> pure . lit $ n
      -- Note (Koz, 22/01/25): This technically can generate nonsensical
      -- expressions, but we can already do this anyway, as we can generate
      -- `App`s which would never work due to argument unsuitability. It should
      -- be fixed, though.
      aPrim :: Int -> GenT (Reader Word64) (ExprBuilder Id)
      aPrim size =
        frequency
          [ (34, oneArg size),
            (40, twoArg size),
            (12, threeArg size),
            (2, sixArg size)
          ]
      oneArg :: Int -> GenT (Reader Word64) (ExprBuilder Id)
      oneArg size = do
        r1 <- argOrId size
        f <- liftGen arbitrary
        pure $ r1 >>= \r1' -> prim (PrimCallOne f r1')
      twoArg :: Int -> GenT (Reader Word64) (ExprBuilder Id)
      twoArg size = do
        r1 <- argOrId size
        r2 <- argOrId size
        f <- liftGen arbitrary
        pure $ r1 >>= \r1' -> r2 >>= \r2' -> prim (PrimCallTwo f r1' r2')
      threeArg :: Int -> GenT (Reader Word64) (ExprBuilder Id)
      threeArg size = do
        r1 <- argOrId size
        r2 <- argOrId size
        r3 <- argOrId size
        f <- liftGen arbitrary
        pure $ r1 >>= \r1' -> r2 >>= \r2' -> r3 >>= \r3' -> prim (PrimCallThree f r1' r2' r3')
      sixArg :: Int -> GenT (Reader Word64) (ExprBuilder Id)
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
      aLam :: Int -> GenT (Reader Word64) (ExprBuilder Id)
      aLam size = do
        body <- expand (argOrId size)
        -- Note (Koz, 21/01/25): We 'bypass' our protections on construction of
        -- lambdas here for convenience, as otherwise, we would have to carry
        -- around a `Scope n`, with `n` changing. While not impossible, this
        -- would require existentialization (using something like `Some`), which
        -- doesn't really help us any (because we have full control anyway), but
        -- does make the code much harder to read and debug.
        pure $ body >>= \bodyRef -> idOf (Lam bodyRef)
      -- Note (Koz, 21/01/25): This is essentially `local`, but because GenT
      -- isn't an instance of MonadReader, we have to write it by hand. We could
      -- have defined an orphan instance instead, but I figured it'd be better
      -- not to.
      expand ::
        forall (a :: Type).
        GenT (Reader Word64) (ExprBuilder a) -> GenT (Reader Word64) (ExprBuilder a)
      expand (GenT f) = GenT $ \qcgen size -> local (+ 1) (f qcgen size)
      anApp :: Int -> GenT (Reader Word64) (ExprBuilder Id)
      anApp size = do
        lhs <- aLam size
        rhs <- argOrId size
        -- Note (Koz, 21/01/25): This is technically not as general as it could
        -- be. By 'recycling' aLam, we always generate a 'fresh' lambda, rather
        -- than (possibly) re-using one available to us as an argument. This is
        -- not really practical to track at the moment, though once we have
        -- types, it could be done. For now, this works well enough.
        pure $ lhs >>= \lhsRef -> rhs >>= \rhsRef -> app (AnId lhsRef) rhsRef
      argOrId :: Int -> GenT (Reader Word64) (ExprBuilder Ref)
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
lit :: AConstant -> ExprBuilder Id
lit = idOf . Lit

-- | Construct a primitive function call.
--
-- @since 1.0.0
prim :: PrimCall -> ExprBuilder Id
prim = idOf . Prim

-- | Construct a function application. The first argument is (an expression
-- evaluating to) a function, the second argument is (an expression evaluating
-- to) an argument.
--
-- = Important note
--
-- Currently, this does not verify that the first argument is indeed a function,
-- nor that the second argument is appropriate.
app :: Ref -> Ref -> ExprBuilder Id
app f x = idOf (App f x)

idOf :: Expr -> ExprBuilder Id
idOf e = ExprBuilder $ do
  binds <- get
  -- We have nothing in the graph, so we can freely build the first node
  if Bimap.null binds
    then do
      let first = Id 0
      first <$ (put . Bimap.insert first e $ binds)
    else case Bimap.lookupR e binds of
      -- This cannot 'miss' because of the previous check
      Nothing -> do
        let (Id highestId, _) = Bimap.findMax binds
        let next = Id $ highestId + 1
        next <$ (put . Bimap.insert next e $ binds)
      Just nodeId -> pure nodeId
