module Covenant.Type
  ( AbstractTy (..),
    Renamed (..),
    CompT (..),
    ValT (..),
    BuiltinFlatT (..),
    BuiltinNestedT (..),
    RenameError (..),
    renameValT,
    renameCompT,
    RenameM,
    runRenameM,
  )
where

import Control.Monad (unless)
import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Control.Monad.State.Strict (State, evalState, gets, modify)
import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index (Count, Index, intCount, intIndex)
import Data.Coerce (coerce)
import Data.Functor.Classes (Eq1 (liftEq))
import Data.Kind (Type)
import Data.Tuple.Optics (_1)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word64)
import Optics.At (ix)
import Optics.Getter (to, view)
import Optics.Label (LabelOptic (labelOptic))
import Optics.Lens (A_Lens, lens)
import Optics.Optic ((%))
import Optics.Review (review)
import Optics.Setter (over, set)

-- | A type abstraction, using a combination of a DeBruijn index (to indicate
-- which scope it refers to) and a positional index (to indicate which bound
-- variable in that scope it refers to).
--
-- = Important note
--
-- This is a /relative/ representation: any given 'AbstractTy' could refer to
-- different things when placed in different positions in the ASG. This stems
-- from how DeBruijn indices behave: 'Z' refers to \'our immediate enclosing
-- scope\', @'S' 'Z'@ to \'one scope outside our immediate enclosing scope\',
-- etc. This can mean different things depending on what these scope(s) are.
--
-- @since 1.0.0
data AbstractTy = BoundAt DeBruijn (Index "tyvar")
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
data Renamed
  = -- | Set by an enclosing scope, and thus is essentially a
    -- concrete type, we just don't know which. First field is its \'true
    -- level\', second field is the positional index in that scope.
    Rigid Int (Index "tyvar")
  | -- | Can be unified with something, but must be consistent: that is, only one
    -- unification for every instance. Field is this variable's positional index;
    -- we don't need to track the scope, as only one scope contains unifiable
    -- bindings.
    Unifiable (Index "tyvar")
  | -- | /Must/ unify with everything, except with other distinct wildcards in the
    -- same scope. First field is a unique /scope/ identifier, second is the
    -- positional index within that scope. We must have unique identifiers for
    -- wildcard scopes, as wildcards unify with everything /except/ other
    -- wildcards in the same scope.
    Wildcard Word64 (Index "tyvar")
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Ord,
      -- | @since 1.0.0
      Show
    )

-- | A computation type, with abstractions indicated by the type argument. In
-- pretty much any case imaginable, this would be either 'AbstractTy' (in the
-- ASG), or 'Renamed' (after renaming).
--
-- = Important note
--
-- This type has a \'type abstraction boundary\' just before it: the first field
-- indicates how many type variables it binds.
--
-- The /last/ entry in the 'NonEmpty' indicates the return type.
--
-- @since 1.0.0
data CompT (a :: Type) = CompT (Count "tyvar") (NonEmptyVector (ValT a))
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- Note (Koz, 04/03/2025): We use this for testing to compare for structural
-- similarity.
instance Eq1 CompT where
  {-# INLINEABLE liftEq #-}
  liftEq f (CompT abses1 xs) (CompT abses2 ys) =
    abses1 == abses2 && liftEq (liftEq f) xs ys

-- | A value type, with abstractions indicated by the type argument. In pretty
-- much any case imaginable, this would be either 'AbstractTy' (in the ASG) or
-- 'Renamed' (after renaming).
--
-- @ since 1.0.0
data ValT (a :: Type)
  = -- | An abstract type.
    Abstraction a
  | -- | A suspended computation.
    ThunkT (CompT a)
  | -- | A builtin type without any nesting.
    BuiltinFlat BuiltinFlatT
  | -- | A builtin type which is \'nested\'; something like lists, pairs etc.
    BuiltinNested (BuiltinNestedT a)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- Note (Koz, 04/03/2025): We use this for testing to compare for structural
-- similarity.
instance Eq1 ValT where
  {-# INLINEABLE liftEq #-}
  liftEq f = \case
    Abstraction abs1 -> \case
      Abstraction abs2 -> f abs1 abs2
      _ -> False
    ThunkT t1 -> \case
      ThunkT t2 -> liftEq f t1 t2
      _ -> False
    BuiltinFlat t1 -> \case
      BuiltinFlat t2 -> t1 == t2
      _ -> False
    BuiltinNested t1 -> \case
      BuiltinNested t2 -> liftEq f t1 t2
      _ -> False

-- | All builtin types that are \'flat\': that is, do not have other types
-- \'nested inside them\'.
data BuiltinFlatT
  = UnitT
  | BoolT
  | IntegerT
  | StringT
  | ByteStringT
  | BLS12_381_G1_ElementT
  | BLS12_381_G2_ElementT
  | BLS12_381_MlResultT
  | DataT
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | Builtin types which have \'nested\' types. This is currently lists and
-- pairs only.
--
-- = Important note
--
-- Both \'arms\' of this type have \'type abstraction boundaries\' just before
-- them: their first field indicates how many type variables they bind. Note
-- that 'PairT' has /one/ such boundary for both of its types, rather than one
-- boundary per type.
--
-- While in truth, these types aren't /really/ polymorphic (as they cannot hold
-- thunks, for example), we define them this way for now.
--
-- @since 1.0.0
data BuiltinNestedT (a :: Type)
  = ListT (Count "tyvar") (ValT a)
  | PairT (Count "tyvar") (ValT a) (ValT a)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- Note (Koz, 04/03/2025): We use this for testing to compare for structural
-- similarity.
instance Eq1 BuiltinNestedT where
  {-# INLINEABLE liftEq #-}
  liftEq f = \case
    ListT abses1 t1 -> \case
      ListT abses2 t2 -> abses1 == abses2 && liftEq f t1 t2
      _ -> False
    PairT abses1 t11 t12 -> \case
      PairT abses2 t21 t22 -> abses1 == abses2 && liftEq f t11 t21 && liftEq f t12 t22
      _ -> False

-- Used during renaming. Contains a source of fresh indices for wildcards, as
-- well as tracking:
--
-- 1. How many variables are bound by each scope;
-- 2. Which of these variables have been noted as used; and
-- 3. A unique identifier for each scope (for wildcards).
data RenameState = RenameState Word64 (Vector (Vector Bool, Word64))
  deriving stock (Eq, Show)

instance
  (k ~ A_Lens, a ~ Word64, b ~ Word64) =>
  LabelOptic "idSource" k RenameState RenameState a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(RenameState x _) -> x)
      (\(RenameState _ y) x' -> RenameState x' y)

instance
  (k ~ A_Lens, a ~ Vector (Vector Bool, Word64), b ~ Vector (Vector Bool, Word64)) =>
  LabelOptic "tracker" k RenameState RenameState a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(RenameState _ y) -> y)
      (\(RenameState x _) y' -> RenameState x y')

-- Given a number of abstractions bound by a scope, modify the state to track
-- that scope.
stepUpScope :: Count "tyvar" -> RenameState -> RenameState
stepUpScope abses x =
  let fresh = view #idSource x
      absesI = review intCount abses
      entry = (Vector.replicate absesI False, fresh)
   in over #tracker (Vector.cons entry) . set #idSource (fresh + 1) $ x

-- Stop tracking the last scope we added.
dropDownScope :: RenameState -> RenameState
dropDownScope = over #tracker Vector.tail

-- Given a pair of DeBruijn index and positional index for a variable, note that
-- we've seen this variable.
noteUsed :: DeBruijn -> Index "tyvar" -> RenameState -> RenameState
noteUsed scope index =
  set (#tracker % ix (asInt scope) % _1 % ix (review intIndex index)) True

-- | Ways in which the renamer can fail.
--
-- @since 1.0.0
data RenameError
  = -- | An attempt to reference an abstraction in a scope where this
    -- abstraction doesn't exist. First field is the true level, second is
    -- the index that was requested.
    --
    -- @since 1.0.0
    InvalidAbstractionReference Int (Index "tyvar")
  | -- | A value type specifies an abstraction that never gets used
    -- anywhere. For example, the type @forall a b . [a]@ has @b@
    -- irrelevant.
    --
    -- @since 1.0.0
    IrrelevantAbstraction
  | -- | A computation type specifies an abstraction which is not used
    -- by any argument. For example, the type @forall a b . a -> !(b -> !a)@
    -- has @b@ overdeterminate.
    --
    -- @since 1.0.0
    OverdeterminateAbstraction
  deriving stock (Eq, Show)

-- | A \'renaming monad\' which allows us to convert type representations from
-- ones that use /relative/ abstraction labelling to /absolute/ abstraction
-- labelling.
--
-- = Why this is necessary
--
-- Consider the following 'AbstractTy': @'BoundAtScope' 1 0@. The meaning of
-- this is relative to where in a type it is positioned: it could be bound by a
-- scope higher than our own, or something we can unify with. Because its
-- meaning (namely, what it refers to) is situational, type checking becomes
-- more difficult, although it has other advantages.
--
-- This monad allows us to convert this relative form into an absolute one. More
-- specifically, the renamer does two things:
--
-- * Ensures that any given abstraction refers to one, and /only/ one, thing;
-- and
-- * Indicates which abstractions are unifiable, and which are (effectively)
-- constant or fixed.
--
-- @since 1.0.0
newtype RenameM (a :: Type)
  = RenameM (ExceptT RenameError (State RenameState) a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via (ExceptT RenameError (State RenameState))

-- | Execute a renaming computation.
--
-- @since 1.0.0
runRenameM ::
  forall (a :: Type).
  RenameM a -> Either RenameError a
runRenameM (RenameM comp) = evalState (runExceptT comp) . RenameState 0 $ Vector.empty

-- | Rename a computation type.
--
-- @since 1.0.0
renameCompT :: CompT AbstractTy -> RenameM (CompT Renamed)
renameCompT (CompT abses xs) = RenameM $ do
  -- Step up a scope
  modify (stepUpScope abses)
  -- Rename, but only the arguments
  renamedArgs <-
    Vector.generateM
      (NonEmpty.length xs - 1)
      (\i -> coerce . renameValT $ xs NonEmpty.! i)
  -- Check that we don't overdetermine anything
  ourAbstractions <- gets (view (#tracker % to Vector.head % _1))
  unless (Vector.and ourAbstractions) (throwError OverdeterminateAbstraction)
  -- Check result type
  renamedResult <- coerce . renameValT . NonEmpty.last $ xs
  -- Roll back state
  modify dropDownScope
  -- Rebuild and return
  pure . CompT abses . NonEmpty.snocV renamedArgs $ renamedResult

-- | Rename a value type.
--
-- @since 1.0.0
renameValT :: ValT AbstractTy -> RenameM (ValT Renamed)
renameValT = \case
  Abstraction (BoundAt scope index) ->
    Abstraction
      <$> RenameM
        ( do
            trueLevel <- gets (\x -> view (#tracker % to Vector.length) x - asInt scope)
            scopeInfo <- gets (\x -> view #tracker x Vector.!? asInt scope)
            let asIntIx = review intIndex index
            case scopeInfo of
              -- This variable is bound at a scope that encloses our starting
              -- point. Thus, this variable is rigid.
              Nothing -> pure . Rigid trueLevel $ index
              Just (varTracker, uniqueScopeId) -> case varTracker Vector.!? asIntIx of
                Nothing -> throwError . InvalidAbstractionReference trueLevel $ index
                Just beenUsed -> do
                  -- Note that we've seen this particular variable
                  unless beenUsed (modify (noteUsed scope index))
                  pure $
                    if trueLevel == 1
                      -- If the true level is 1, this is a unifiable
                      then Unifiable index
                      -- This variable is a wildcard
                      else Wildcard uniqueScopeId index
        )
  ThunkT t -> ThunkT <$> renameCompT t
  BuiltinFlat t -> pure . BuiltinFlat $ t
  BuiltinNested t ->
    BuiltinNested <$> case t of
      ListT abses t' -> RenameM $ do
        -- Step up a scope
        modify (stepUpScope abses)
        -- Rename the inner type
        renamed <- coerce . renameValT $ t'
        -- Check that we don't have anything irrelevant
        ourAbstractions <- gets (view (#tracker % to Vector.head % _1))
        unless (Vector.and ourAbstractions) (throwError IrrelevantAbstraction)
        -- Roll back state
        modify dropDownScope
        -- Rebuild and return
        pure . ListT abses $ renamed
      PairT abses t1 t2 -> RenameM $ do
        -- Step up a scope
        modify (stepUpScope abses)
        -- Rename t1, then t2, without any scope shifts
        renamed1 <- coerce . renameValT $ t1
        renamed2 <- coerce . renameValT $ t2
        -- Check we don't have anything irrelevant
        ourAbstractions <- gets (view (#tracker % to Vector.head % _1))
        unless (Vector.and ourAbstractions) (throwError IrrelevantAbstraction)
        -- Roll back state
        modify dropDownScope
        -- Rebuild and return
        pure . PairT abses renamed1 $ renamed2
