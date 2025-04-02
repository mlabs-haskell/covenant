module Covenant.Internal.Rename
  ( RenameM,
    RenameError (..),
    runRenameM,
    renameValT,
    renameCompT,
  )
where

import Control.Monad (unless)
import Control.Monad.Except
  ( ExceptT,
    runExceptT,
    throwError,
  )
import Control.Monad.State.Strict
  ( State,
    evalState,
    gets,
    modify,
  )
import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index (Count, Index, intCount, intIndex)
import Covenant.Internal.Type
  ( AbstractTy (BoundAt),
    CompT (CompT),
    CompTBody (CompTBody),
    Renamed (Rigid, Unifiable, Wildcard),
    ValT (Abstraction, BuiltinFlat, ThunkT),
  )
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Tuple.Optics (_1)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word64)
import Optics.Core
  ( A_Lens,
    LabelOptic (labelOptic),
    ix,
    lens,
    over,
    review,
    set,
    to,
    view,
    (%),
  )

-- Used during renaming. Contains a source of fresh indices for wildcards, as
-- well as tracking:
--
-- 1. How many variables are bound by each scope;
-- 2. Which of these variables have been noted as used; and
-- 3. A unique identifier for each scope (for wildcards).
data RenameState = RenameState Word64 (Vector (Vector Bool, Word64))
  deriving stock (Eq, Show)

-- Note (Koz, 11/04/2025): We need this field as a source of unique identifiers
-- when renaming wildcards. Wildcards are special in that they can unify with
-- anything (possibly _several_ anythings) except different wildcards in the
-- same scope as each other. For example, consider the computation type below:
--
-- (forall a b . a -> b -> !Int) -> (forall c . c -> !Int) -> String -> !Int
--
-- In particular, `a` and `c` would be defined the same way: `BoundAt Z ix0`.
-- However, while `c` and `b` could unify just fine, `a` and `b` could not.
-- Furthermore, they are identically scoped (in the sense that they're both
-- enclosed the same way), which means that, unlike rigid variables, we cannot
-- uniquely identify them just by their scoping.
--
-- Thus, we have to have to have a way to uniquely label any wildcard in such a
-- way that wildcards in the same scope, at the same level, are tagged
-- separately from wildcards in a _different_ scope at the same level. See the
-- functions `stepUpScope` and `dropDownScope` to see how we achieve this.
instance
  (k ~ A_Lens, a ~ Word64, b ~ Word64) =>
  LabelOptic "idSource" k RenameState RenameState a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(RenameState x _) -> x)
      (\(RenameState _ y) x' -> RenameState x' y)

-- The 'outer' vector represents a stack of scopes. Each entry is a combination
-- of a vector of used variables (length is equal to the number of variables
-- bound by that scope), together with a unique identifier not only for that
-- scope, but also the `step` into that scope, as required by wildcard renaming.
instance
  (k ~ A_Lens, a ~ Vector (Vector Bool, Word64), b ~ Vector (Vector Bool, Word64)) =>
  LabelOptic "tracker" k RenameState RenameState a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(RenameState _ y) -> y)
      (\(RenameState x _) y' -> RenameState x y')

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
    -- has @b@ undetermined.
    --
    -- @since 1.0.0
    UndeterminedAbstraction
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
  RenameM a ->
  Either RenameError a
runRenameM (RenameM comp) = evalState (runExceptT comp) . RenameState 0 $ Vector.empty

-- | Rename a computation type.
--
-- @since 1.0.0
renameCompT :: CompT AbstractTy -> RenameM (CompT Renamed)
renameCompT (CompT abses (CompTBody xs)) = RenameM $ do
  -- Step up a scope
  modify (stepUpScope abses)
  -- Rename, but only the arguments
  renamedArgs <-
    Vector.generateM
      (NonEmpty.length xs - 1)
      (\i -> coerce . renameValT $ xs NonEmpty.! i)
  -- Check that we don't overdetermine anything
  ourAbstractions <- gets (view (#tracker % to Vector.head % _1))
  unless (Vector.and ourAbstractions) (throwError UndeterminedAbstraction)
  -- Check result type
  renamedResult <- coerce . renameValT . NonEmpty.last $ xs
  -- Roll back state
  modify dropDownScope
  -- Rebuild and return
  pure . CompT abses . CompTBody . NonEmpty.snocV renamedArgs $ renamedResult

-- | Rename a value type.
--
-- @since 1.0.0
renameValT :: ValT AbstractTy -> RenameM (ValT Renamed)
renameValT = \case
  Abstraction t -> Abstraction <$> renameAbstraction t
  ThunkT t -> ThunkT <$> renameCompT t
  BuiltinFlat t -> pure . BuiltinFlat $ t

-- Helpers

renameAbstraction :: AbstractTy -> RenameM Renamed
renameAbstraction (BoundAt scope index) = RenameM $ do
  trueLevel <- gets (\x -> view (#tracker % to Vector.length) x - asInt scope)
  scopeInfo <- gets (\x -> view #tracker x Vector.!? asInt scope)
  let asIntIx = review intIndex index
  case scopeInfo of
    -- This variable is bound in a scope that encloses the renaming scope. Thus,
    -- the variable is rigid.
    Nothing -> pure . Rigid trueLevel $ index
    Just (occursTracker, uniqueScopeId) -> case occursTracker Vector.!? asIntIx of
      Nothing -> throwError . InvalidAbstractionReference trueLevel $ index
      Just beenUsed -> do
        -- Note that this variable has occurred
        unless beenUsed (modify (noteUsed scope index))
        pure $
          if trueLevel == 1
            -- This is a unifiable variable
            then Unifiable index
            -- This is a wildcard variable
            else Wildcard uniqueScopeId index

-- Given a number of abstractions bound by a scope, modify the state to track
-- that scope.
stepUpScope :: Count "tyvar" -> RenameState -> RenameState
stepUpScope abses x =
  let fresh = view #idSource x
      absesI = review intCount abses
      -- Label (speculatively) the current scope 'step' with a unique value.
      entry = (Vector.replicate absesI False, fresh)
   in -- Ensure that our source of fresh identifiers is incremented
      over #tracker (Vector.cons entry) . set #idSource (fresh + 1) $ x

-- Stop tracking the last scope we added.
--
-- Note that, while we 'throw away' the information about (used) variables in
-- the scope, we do _not_ roll back the `idSource`. This is in fact why we have
-- to be in `State` rather than `Reader`: that change has to be persistent to
-- achieve our goal of renaming wildcards.
dropDownScope :: RenameState -> RenameState
dropDownScope = over #tracker Vector.tail

-- Given a pair of DeBruijn index and positional index for a variable, note that
-- we've seen this variable.
noteUsed :: DeBruijn -> Index "tyvar" -> RenameState -> RenameState
noteUsed scope index =
  set (#tracker % ix (asInt scope) % _1 % ix (review intIndex index)) True
