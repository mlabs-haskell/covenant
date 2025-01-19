{-# LANGUAGE AllowAmbiguousTypes #-}

-- | @since 1.0.0
module Covenant.Expr
  ( -- * Types
    Id,
    Arg,
    Expr,
    ExprBuilder,
    Scope,

    -- * Functions
    emptyScope,

    -- ** Build up expressions
    lit,
    arg,
    add,
    mul,
    app,
    lam,
  )
where

import GHC.TypeNats (KnownNat, CmpNat, natVal, type (+))
import Data.Proxy (Proxy (Proxy))
import Control.Monad.State.Strict (State, get, put)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Kind (Type)
import Data.Word (Word64)
import Numeric.Natural (Natural)

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

-- | A node in a Covenant program.
--
-- @since 1.0.0
data Expr
  = Lit Natural
  | Argument Arg
  | Add Id Id
  | Mul Id Id
  | Lam Id
  | App Id Id
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

-- | Construct a literal (constant) value.
--
-- @since 1.0.0
lit :: Natural -> ExprBuilder Id
lit = idOf . Lit

-- | Construct an addition.
--
-- @since 1.0.0
add :: Id -> Id -> ExprBuilder Id
add x y = idOf (Add x y)

-- | Construct a multiplication.
--
-- @since 1.0.0
mul :: Id -> Id -> ExprBuilder Id
mul x y = idOf (Mul x y)

-- | Construct a function application. The first argument is (an expression
-- evaluating to) a function, the second argument is (an expression evaluating
-- to) an argument.
--
-- = Important note
--
-- Currently, this does not verify that the first argument is indeed a function,
-- nor that the second argument is appropriate.
app :: Id -> Id -> ExprBuilder Id
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
arg :: forall (n :: Natural) (m :: Natural) . 
  (KnownNat n, CmpNat n m ~ LT) => 
  Scope m -> 
  ExprBuilder Id
arg Scope = idOf . Argument . Arg . fromIntegral . natVal $ Proxy @n

-- | Given a scope, and a function to construct a lambda body using a \'larger\'
-- scope, construct a lambda with that body.
-- 
-- For example, this is how you define @id@:
--
-- > lam emptyScope $ \s1 -> arg @0 s1
--
-- This is @const@:
--
-- > lam emptyScope $ \s1 -> lam s1 $ \s2 -> arg @1 s2 
--
-- @since 1.0.0
lam :: forall (n :: Natural) . 
  Scope n -> 
  (Scope (n + 1) -> ExprBuilder Id) -> 
  ExprBuilder Id
lam Scope f = do
  bodyId <- f Scope
  idOf (Lam bodyId)

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
