module Covenant.Type
  ( AbstractTy (..),
    Renamed (..),
    CompT (..),
    ValT (..),
    BuiltinFlatT (..),
    BuiltinNestedT (..),
    renameValT,
    renameCompT,
    RenameM,
    runRenameM,
  )
where

import Control.Monad.Reader (asks, local)
import Control.Monad.State.Strict (gets, modify)
import Control.Monad.Trans.RWS.CPS (RWS, runRWS)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Functor.Classes (Eq1 (liftEq))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.Word (Word64)

-- | A type abstraction, using a DeBruijn index.
--
-- = Important note
--
-- This is a /relative/ representation: @'BoundAt' 1 0@ could refer to different
-- things at different points in the ASG. Note that only the first field is a
-- DeBruijn index: the second indicates which type variable bound at that
-- \'level\' we mean.
--
-- @since 1.0.0
data AbstractTy = BoundAt Word64 Word64
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | A renamed type abstraction. We separate them into two kinds:
--
-- * Ones we can decide on (that is, variables in the context of unification);
-- and
-- * Ones we /cannot/ decide on (either fixed in higher scopes than ours, or
-- untouchable).
--
-- We use 'CanSet' plus an index for the first case; the second case is a unique
-- index assigned by the renamer.
--
-- @since 1.0.0
data Renamed = CanSet Word64 | Can'tSet Word64
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
data CompT (a :: Type) = CompT Word64 (NonEmpty (ValT a))
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
-- them: their first field indicates how many type variables they bind.
--
-- While in truth, these types aren't /really/ polymorphic (as they cannot hold
-- thunks, for example), we define them this way for now.
--
-- @since 1.0.0
data BuiltinNestedT (a :: Type)
  = ListT Word64 (ValT a)
  | PairT Word64 (ValT a) (ValT a)
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
newtype RenameM (a :: Type) = RenameM (RWS Int () (Word64, Bimap (Int, Word64) Word64) a)
  deriving
    ( -- | @since 1.0.0
      Functor,
      -- | @since 1.0.0
      Applicative,
      -- | @since 1.0.0
      Monad
    )
    via (RWS Int () (Word64, Bimap (Int, Word64) Word64))

-- Note (Koz, 05/04/2025): We could check that any type abstractions we have in
-- our view (meaning, not bound higher than us) do not reference tyvars that
-- don't exist, as every 'type abstraction boundary' specifies how many
-- variables it binds. This would mean the renamer could fail if it encounters
-- an impossible situation (such as asking for the index-3 type variable from a
-- scope that only binds 2). This might not be worth it however, as we would
-- have no way of checkin anything that comes from 'above us': namely, we would
-- have to blindly trust any scopes that enclose us and that those type indexes
-- are sensible.

-- Increase the scope by one level.
stepDown :: forall (a :: Type). RenameM a -> RenameM a
stepDown (RenameM comp) = RenameM (local (+ 1) comp)

-- Given an abstraction in relative form, transform it into an abstraction in
-- absolute form.
renameAbstraction :: AbstractTy -> RenameM Renamed
renameAbstraction (BoundAt scope ix) = RenameM $ do
  -- DeBruijn scope indices are relative to our own position. They could
  -- potentially refer to stuff bound 'above' us (meaning they're fixed by our
  -- callers), or stuff bound 'below' us (meaning that they're untouchable). As
  -- the renamer walks, every time we cross a 'type abstraction barrier', we
  -- have to take into account that, to reference something, we need an index
  -- one higher.
  --
  -- We thus change the 'relative' indexes to absolute ones, choosing the
  -- starting point as zero. Thus, we get the following scheme:
  --
  -- \* After one forall, scope 0 means 'can change': 1 - 0 = 1
  -- \* After two foralls, scope 1 means 'can change': 2 - 1 = 1
  -- \* After three foralls, scope 2 means 'can change': 3 - 2 = 1
  --
  -- Thus, we must check whether the difference between the current level and
  -- the DeBruijn index is exactly 1. We call this the 'true level', although
  -- it's not the best name.
  trueLevel <- asks (\currentLevel -> currentLevel - fromIntegral scope)
  if trueLevel == 1
    then pure . CanSet $ ix
    else do
      -- Check if we already renamed this thing, and if so, rename consistently.
      priorRename <- gets (Bimap.lookup (trueLevel, ix) . snd)
      case priorRename of
        Nothing -> do
          renaming <- gets fst
          modify $ \(source, tracker) -> (source + 1, Bimap.insert (trueLevel, ix) renaming tracker)
          pure . Can'tSet $ renaming
        Just renameIx -> pure . Can'tSet $ renameIx

-- | Run a renaming computation, while also producing the mapping of any fixed
-- abstractions to their original (non-relative) scope and position.
--
-- @since 1.0.0
runRenameM ::
  forall (a :: Type).
  RenameM a -> (Bimap (Int, Word64) Word64, a)
runRenameM (RenameM comp) = case runRWS comp 0 (0, Bimap.empty) of
  (res, (_, tracker), ()) -> (tracker, res)

-- | Given a value type with relative abstractions, produce the same value type,
-- but with absolute abstractions.
--
-- @since 1.0.0
renameValT :: ValT AbstractTy -> RenameM (ValT Renamed)
renameValT = \case
  Abstraction absTy -> Abstraction <$> renameAbstraction absTy
  -- We're crossing a type abstraction boundary, so bump the level
  ThunkT t -> ThunkT <$> renameCompT t
  BuiltinFlat t -> pure . BuiltinFlat $ t
  BuiltinNested t ->
    BuiltinNested <$> case t of
      -- We're crossing a type abstraction boundary, so bump the level
      ListT abses t' -> ListT abses <$> stepDown (renameValT t')
      PairT abses t1 t2 ->
        PairT abses
          <$> stepDown (renameValT t1)
          <*> stepDown (renameValT t2)

-- | As 'renameValT', but for computation types.
--
-- @since 1.0.0
renameCompT :: CompT AbstractTy -> RenameM (CompT Renamed)
renameCompT (CompT abses xs) = CompT abses <$> stepDown (traverse renameValT xs)
