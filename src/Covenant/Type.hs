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

import Control.Monad.Reader (ask, local)
import Control.Monad.State.Strict (gets, modify)
import Control.Monad.Trans.RWS.CPS (RWS, runRWS)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Functor.Classes (Eq1 (liftEq))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.Word (Word64)

-- | A type abstraction.
--
-- = Important note
--
-- There is an implicit \'scope boundary\' in front of this. Thus, this
-- construction can mean either:
--
-- * An untouchable (effectively @forall a . a@)
-- * A single toplevel variable
-- * A reference to another binding scope and index
--
-- The 'ForallAA' constructor plays the first two roles; which depends on the
-- context. 'BoundAtScope' indicates instead how many scopes away it was bound,
-- and also which binding we're referring to (first, second, etc).
--
-- @since 1.0.0
data AbstractTy
  = ForallAA
  | BoundAtScope Word64 Word64
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

-- Increase the scope by one level.
stepDown :: forall (a :: Type). RenameM a -> RenameM a
stepDown (RenameM comp) = RenameM (local (+ 1) comp)

-- Given an abstraction in relative form, transform it into an abstraction in
-- absolute form.
renameAbstraction :: AbstractTy -> RenameM Renamed
renameAbstraction absTy = RenameM $ do
  currLevel <- ask
  case absTy of
    ForallAA ->
      if currLevel == 0
        then pure . CanSet $ 0
        else do
          renaming <- Can'tSet <$> gets fst
          -- We bump the source of fresh names, but don't record an entry for
          -- this; all such entries are completely unique, but on restoring
          -- original names, will be the same.
          modify $ \(source, tracker) -> (source + 1, tracker)
          pure renaming
    -- We need to determine the true level to see if:
    --
    -- 1. We can set this at all (aka, whether it's unfixed and touchable); and
    -- 2. Whether we've seen this before.
    BoundAtScope scope ix -> do
      let trueLevel = currLevel - fromIntegral scope
      if trueLevel == 0
        then pure . CanSet $ ix
        else do
          -- Check if this is something we already renamed previously, and if
          -- so, rename consistently.
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
