{-# LANGUAGE AllowAmbiguousTypes #-}

-- |
-- Module: Covenant.Expr
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, farseen@mlabs.city, sean@mlabs.city
--
-- Contains the basic functionality to build up Covenant expressions
-- programmatically.
--
-- @since 1.0.0
module Covenant.Expr
  ( -- * Types
    Id,
    Arg,
    Ref (..),
    PrimCall (..),
    Expr,
    ExprBuilder,
    Scope,
    ExprGraph,

    -- * Functions
    emptyScope,

    -- ** Build up expressions
    lit,
    prim,
    arg,
    app,
    lam,

    -- ** Compile an expression
    toExprGraph,
  )
where

import Algebra.Graph.Acyclic.AdjacencyMap
  ( AdjacencyMap,
    toAcyclic,
    vertex,
  )
import Algebra.Graph.AdjacencyMap qualified as Cyclic
import Control.Monad.Reader (Reader, ask, lift, local, runReader)
import Control.Monad.State.Strict (State, get, put, runState)
import Covenant.Prim (OneArgFunc, SixArgFunc, ThreeArgFunc, TwoArgFunc)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Kind (Type)
import Data.Maybe (mapMaybe)
import Data.Proxy (Proxy (Proxy))
import Data.Word (Word64)
import GHC.TypeNats (CmpNat, KnownNat, natVal, type (+))
import Numeric.Natural (Natural)
import Test.QuickCheck (Arbitrary (arbitrary), chooseEnum)
import Test.QuickCheck.GenT
  ( GenT (GenT),
    frequency,
    liftGen,
    oneof,
    runGenT,
    sized,
  )
import Test.QuickCheck.Instances.Natural ()

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
  = Lit Natural
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
newtype ExprBuilder (a :: Type) = ExprBuilder (State (Id, Bimap Id Expr) a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via (State (Id, Bimap Id Expr))

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

-- | A Covenant program, represented as an acyclic graph.
--
-- @since 1.0.0
data ExprGraph = ExprGraph (Id, Expr) (AdjacencyMap (Id, Expr))
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Given an 'Id' result in a builder monad, compile the computation that 'Id'
-- refers to into a call graph. This is guaranteed to be acyclic.
--
-- @since 1.0.0
toExprGraph :: ExprBuilder Id -> Maybe ExprGraph
toExprGraph (ExprBuilder comp) = do
  let (start, (_, binds)) = runState comp (Id 0, Bimap.empty)
  if Bimap.size binds == 1
    then do
      -- This cannot fail, but the type system can't show it
      initial <- (start,) <$> Bimap.lookup start binds
      pure . ExprGraph initial . vertex $ initial
    else do
      let asGraph = Cyclic.edges . go binds $ start
      -- This cannot fail, but the type system can't show it
      acyclic <- toAcyclic asGraph
      -- Same as above
      initial <- (start,) <$> Bimap.lookup start binds
      pure . ExprGraph initial $ acyclic
  where
    go ::
      Bimap Id Expr ->
      Id ->
      [((Id, Expr), (Id, Expr))]
    go binds curr = case Bimap.lookup curr binds of
      Nothing -> []
      Just e ->
        let idList = toIdList e
            stepdown i = case Bimap.lookup i binds of
              Nothing -> []
              Just e' -> ((curr, e), (i, e')) : go binds i
         in concatMap stepdown idList

-- | Construct a literal (constant) value.
--
-- @since 1.0.0
lit :: Natural -> ExprBuilder Id
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

-- | A proof of how many arguments are available to a Covenant program. Put
-- another way, a value of type @'Scope' n@ means that we are under @n@ lambdas,
-- each with an argument we can refer to.
--
-- @since 1.0.0
data Scope (n :: Natural) = Scope
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Constructs the scopes that proves nothing.
--
-- @since 1.0.0
emptyScope :: Scope 0
emptyScope = Scope

-- | Given a proof of scope, construct one of the arguments in that scope. This
-- requires use of @TypeApplications@ to select which argument you are
-- interested in: argument @0@ is the one from the nearest lambda, argument @1@
-- is the one from the next enclosing lambda, and so on.
--
-- See the documentation for 'lam' for an example of how this function should be
-- used.
--
-- @since 1.0.0
arg ::
  forall (n :: Natural) (m :: Natural).
  (KnownNat n, CmpNat n m ~ LT) =>
  Scope m ->
  Arg
arg Scope = Arg . fromIntegral . natVal $ Proxy @n

-- | Given a scope, and a function to construct a lambda body using a \'larger\'
-- scope, construct a lambda with that body.
--
-- For example, this is how you define @id@:
--
-- > lam emptyScope $ \s1 -> pure . AnArg $ arg @0 s1
--
-- This is @const@:
--
-- > lam emptyScope $ \s1 -> lam s1 $ \s2 -> pure . AnArg $ arg @1 s2
--
-- @since 1.0.0
lam ::
  forall (n :: Natural).
  Scope n ->
  (Scope (n + 1) -> ExprBuilder Ref) ->
  ExprBuilder Id
lam Scope f = do
  res <- f Scope
  idOf . Lam $ res

-- Helpers

idOf :: Expr -> ExprBuilder Id
idOf e = ExprBuilder $ do
  (fresh, binds) <- get
  case Bimap.lookupR e binds of
    Nothing -> do
      let newBinds = Bimap.insert fresh e binds
      let newFresh = nextId fresh
      fresh <$ put (newFresh, newBinds)
    Just nodeId -> pure nodeId

nextId :: Id -> Id
nextId (Id w) = Id $ w + 1

toIdList :: Expr -> [Id]
toIdList = \case
  Lit _ -> []
  Prim p -> mapMaybe refToId $ case p of
    PrimCallOne _ r -> [r]
    PrimCallTwo _ r1 r2 -> [r1, r2]
    PrimCallThree _ r1 r2 r3 -> [r1, r2, r3]
    PrimCallSix _ r1 r2 r3 r4 r5 r6 -> [r1, r2, r3, r4, r5, r6]
  Lam body -> mapMaybe refToId [body]
  App f x -> mapMaybe refToId [f, x]

refToId :: Ref -> Maybe Id
refToId = \case
  AnArg _ -> Nothing
  AnId i -> Just i
