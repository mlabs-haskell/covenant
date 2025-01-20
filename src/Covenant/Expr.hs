{-# LANGUAGE AllowAmbiguousTypes #-}

-- | @since 1.0.0
module Covenant.Expr
  ( -- * Types
    Id,
    Arg,
    Ref (..),
    Expr,
    ExprBuilder,
    Scope,
    ExprGraph,

    -- * Functions
    emptyScope,

    -- ** Build up expressions
    lit,
    arg,
    add,
    mul,
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
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Kind (Type)
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

-- | A node in a Covenant program.
--
-- @since 1.0.0
data Expr
  = Lit Natural
  | Add Ref Ref
  | Mul Ref Ref
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
        | otherwise = oneof [aLiteral, anAdd size, aMul size, aLam size, anApp size]
      aLiteral :: GenT (Reader Word64) (ExprBuilder Id)
      aLiteral = liftGen arbitrary >>= \n -> pure . lit $ n
      anAdd :: Int -> GenT (Reader Word64) (ExprBuilder Id)
      anAdd size = do
        lhs <- argOrId size
        rhs <- argOrId size
        pure $ lhs >>= \lhsRef -> rhs >>= \rhsRef -> add lhsRef rhsRef
      aMul :: Int -> GenT (Reader Word64) (ExprBuilder Id)
      aMul size = do
        lhs <- argOrId size
        rhs <- argOrId size
        pure $ lhs >>= \lhsRef -> rhs >>= \rhsRef -> mul lhsRef rhsRef
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
      Nothing -> [] -- technically impossible
      Just e -> foldIds [] (handleOne binds curr e) (handleTwo binds curr e) . idsFrom $ e
    idsFrom :: Expr -> Ids
    idsFrom = \case
      Lit _ -> NoId
      Add r1 r2 -> toIds r1 r2
      Mul r1 r2 -> toIds r1 r2
      Lam body -> case body of
        AnId i -> OneId i
        AnArg _ -> NoId
      App f x -> toIds f x
    handleOne ::
      Bimap Id Expr ->
      Id ->
      Expr ->
      Id ->
      [((Id, Expr), (Id, Expr))]
    handleOne binds curr e i = case Bimap.lookup i binds of
      Nothing -> [] -- technically impossible
      Just e' -> ((curr, e), (i, e')) : go binds i
    handleTwo ::
      Bimap Id Expr ->
      Id ->
      Expr ->
      Id ->
      Id ->
      [((Id, Expr), (Id, Expr))]
    handleTwo binds curr e i1 i2 = case Bimap.lookup i1 binds of
      Nothing -> [] -- technically impossible
      Just e1 -> case Bimap.lookup i2 binds of
        Nothing -> [] -- see above
        Just e2 ->
          let rest = go binds i1 <> go binds i2
           in ((curr, e), (i1, e1)) : ((curr, e), (i2, e2)) : rest

-- | Construct a literal (constant) value.
--
-- @since 1.0.0
lit :: Natural -> ExprBuilder Id
lit = idOf . Lit

-- | Construct an addition.
--
-- @since 1.0.0
add :: Ref -> Ref -> ExprBuilder Id
add x y = idOf (Add x y)

-- | Construct a multiplication.
--
-- @since 1.0.0
mul :: Ref -> Ref -> ExprBuilder Id
mul x y = idOf (Mul x y)

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

data Ids = NoId | OneId Id | TwoIds Id Id

toIds :: Ref -> Ref -> Ids
toIds r1 r2 = case r1 of
  AnArg _ -> case r2 of
    AnArg _ -> NoId
    AnId i2 -> OneId i2
  AnId i1 -> case r2 of
    AnArg _ -> OneId i1
    AnId i2 -> TwoIds i1 i2

foldIds ::
  forall (r :: Type).
  r ->
  (Id -> r) ->
  (Id -> Id -> r) ->
  Ids ->
  r
foldIds none one two = \case
  NoId -> none
  OneId i -> one i
  TwoIds i1 i2 -> two i1 i2
