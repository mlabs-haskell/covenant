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
import Data.Coerce (coerce)
import Data.Functor.Classes (Eq1 (liftEq))
import Data.Kind (Type)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word64)

-- | A type abstraction, using a DeBruijn index.
--
-- = Important note
--
-- This is a /relative/ representation: @'BoundAt' ('S' 'Z') 0@ could refer to different
-- things at different points in the ASG. The second field indicates which type variable
-- bound at that \'level\' we mean.
--
-- @since 1.0.0
data AbstractTy = BoundAt DeBruijn Word64
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
    -- level\', second field is the index.
    Rigid Int Word64
  | -- | Can be unified with something, but must be consistent: that is, only one
    -- unification for every instance. Field is this variable's positional index.
    Unifiable Word64
  | -- | /Must/ unify with everything, except with other distinct wildcards in the
    -- same scope. First field is a unique /scope/ identifier, second is index.
    Wildcard Word64 Word64
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
data CompT (a :: Type) = CompT Word64 (NonEmptyVector (ValT a))
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

data RenameState = RenameState Word64 (Vector (Vector Bool, Word64))
  deriving stock (Eq, Show)

data RenameError
  = InvalidAbstractionReference Int Word64
  | IrrelevantAbstraction
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

runRenameM ::
  forall (a :: Type).
  RenameM a -> Either RenameError a
runRenameM (RenameM comp) = evalState (runExceptT comp) . RenameState 0 $ Vector.empty

renameCompT :: CompT AbstractTy -> RenameM (CompT Renamed)
renameCompT (CompT abses xs) = RenameM $ do
  -- Step up a scope
  modify
    ( \(RenameState fresh tracker) ->
        RenameState
          (fresh + 1)
          (Vector.cons (Vector.replicate (fromIntegral abses) False, fresh) tracker)
    )
  -- Rename, but only the arguments
  renamedArgs <- Vector.generateM (NonEmpty.length xs - 1) (\i -> coerce . renameValT $ xs NonEmpty.! i)
  -- Check the relevance condition is met
  ourAbstractions <- gets (\(RenameState _ tracker) -> fst . Vector.head $ tracker)
  unless (Vector.and ourAbstractions) (throwError IrrelevantAbstraction)
  -- Check result type
  renamedResult <- coerce . renameValT . NonEmpty.last $ xs
  -- Roll back state
  modify (\(RenameState fresh tracker) -> RenameState fresh (Vector.tail tracker))
  -- Rebuild and return
  pure . CompT abses . NonEmpty.snocV renamedArgs $ renamedResult

renameValT :: ValT AbstractTy -> RenameM (ValT Renamed)
renameValT = \case
  Abstraction (BoundAt scope ix) ->
    Abstraction
      <$> RenameM
        ( do
            trueLevel <- gets (\(RenameState _ tracker) -> Vector.length tracker - asInt scope)
            scopeInfo <- gets (\(RenameState _ tracker) -> tracker Vector.!? asInt scope)
            case scopeInfo of
              -- This variable is bound at a scope that encloses our starting
              -- point. Thus, this variable is rigid.
              Nothing -> pure . Rigid trueLevel $ ix
              Just (varTracker, uniqueScopeId) -> case varTracker Vector.!? fromIntegral ix of
                Nothing -> throwError . InvalidAbstractionReference trueLevel $ ix
                Just beenUsed -> do
                  -- Note that we've seen this particular variable
                  unless
                    beenUsed
                    ( modify $ \(RenameState fresh tracker) ->
                        let varTracker' = varTracker Vector.// [(fromIntegral ix, True)]
                         in RenameState fresh $ tracker Vector.// [(asInt scope, (varTracker', uniqueScopeId))]
                    )
                  pure $
                    if trueLevel == 1
                      -- If the true level is 1, this is a unifiable
                      then Unifiable ix
                      -- This variable is a wildcard
                      else Wildcard uniqueScopeId ix
        )
  ThunkT t -> ThunkT <$> renameCompT t
  BuiltinFlat t -> pure . BuiltinFlat $ t
  BuiltinNested t ->
    BuiltinNested <$> case t of
      ListT abses t' -> RenameM $ do
        -- Step up a scope
        modify
          ( \(RenameState fresh tracker) ->
              RenameState
                (fresh + 1)
                (Vector.cons (Vector.replicate (fromIntegral abses) False, fresh) tracker)
          )
        -- Rename the inner type
        renamed <- coerce . renameValT $ t'
        -- Check the use condition is met
        ourAbstractions <- gets (\(RenameState _ tracker) -> fst . Vector.head $ tracker)
        unless (Vector.and ourAbstractions) (throwError IrrelevantAbstraction)
        -- Roll back state
        modify
          (\(RenameState fresh tracker) -> RenameState fresh (Vector.tail tracker))
        -- Rebuild and return
        pure . ListT abses $ renamed
      PairT abses t1 t2 -> RenameM $ do
        -- Step up a scope
        modify
          ( \(RenameState fresh tracker) ->
              RenameState
                (fresh + 1)
                (Vector.cons (Vector.replicate (fromIntegral abses) False, fresh) tracker)
          )
        -- Rename t1, then t2, without any scope shifts
        renamed1 <- coerce . renameValT $ t1
        renamed2 <- coerce . renameValT $ t2
        -- Check the use condition is met
        ourAbstractions <- gets (\(RenameState _ tracker) -> fst . Vector.head $ tracker)
        unless (Vector.and ourAbstractions) (throwError IrrelevantAbstraction)
        -- Roll back state
        modify
          (\(RenameState fresh tracker) -> RenameState fresh (Vector.tail tracker))
        -- Rebuild and return
        pure . PairT abses renamed1 $ renamed2
