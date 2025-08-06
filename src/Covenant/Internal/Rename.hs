{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.Internal.Rename
  ( RenameM,
    RenameError (..),
    runRenameM,
    renameValT,
    renameDataDecl,
    renameCompT,
    undoRename,
    renameDatatypeInfo,
    UnRenameM,
    runUnRenameM,
  )
where

import Control.Monad (unless)
import Control.Monad.Except
  ( ExceptT,
    MonadError,
    runExceptT,
    throwError,
  )
import Control.Monad.Reader
  ( MonadReader,
    Reader,
    asks,
    local,
    runReader,
  )
import Control.Monad.State.Strict
  ( State,
    evalState,
    gets,
    modify,
  )
import Covenant.Data (DatatypeInfo (DatatypeInfo))
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index (Count, Index, intCount, intIndex, wordCount)
import Covenant.Internal.Type
  ( AbstractTy (BoundAt),
    CompT (CompT),
    CompTBody (CompTBody),
    Constructor (Constructor),
    DataDeclaration (DataDeclaration, OpaqueData),
    Renamed (Rigid, Unifiable, Wildcard),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
  )
import Data.Bitraversable (Bitraversable (bitraverse))
import Data.Coerce (coerce)
import Data.Kind (Type)
import Data.Tuple.Optics (_1)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word32, Word64)
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
    (%), preview,
  )
import Data.Maybe (fromJust)

--import Debug.Trace (traceM)

traceM :: forall a (m :: Type -> Type). (Monad m) => a -> m ()
traceM _ = pure ()

{- CHANGES:

  - Get rid of Vector Bool in RenameState, replace with Word32
  - runRenameM needs to take a ScopeInfo argument (or convert before passing it in)
  - The unrenamer:
     * Has to have a scope stack
     * Works like the renamer backwards
     * If you see an abstraction
       - If it's a rigid, un-translate it
       - If it's a unifiable throw an error, something's broken
       - If it's a wildcard something has gone even more wrong!
     * If it's a datatype, recurse w/o stepping
     * If it's a flat don't do anything
     * If it's a thunk, step up scope and recurse

     - Wildcard indices don't matter (can work in Reader)
     - Keep the renameM as a state, do unRenameM in a reader w/ local
     - Only need a Vector Word32 for the UnRenameM reader
-}

-- Used during renaming. Contains a source of fresh indices for wildcards, as
-- well as tracking:
--
-- 1. How many variables are bound by each scope;
-- 2. Which of these variables have been noted as used; and
-- 3. A unique identifier for each scope (for wildcards).
-- TODO: Update comments, the Word32 is the count for each scope
data RenameState = RenameState Word64 Word32 (Vector (Word32, Word64)) -- replace Vector Bool w/ Word32 from ScopeInfo, set
-- For the inherited scope stack (the thing we construct from ScopeInfo),
-- the Word64 could be anything. We can't have wildcards in an inherited scope
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
      (\(RenameState x _ _ ) -> x)
      (\(RenameState _ b c) a' -> RenameState a' b c)

instance (k ~ A_Lens, a ~ Word32, b ~ Word32) =>
  LabelOptic "inheritedScope" k RenameState RenameState a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(RenameState _ x _) -> x)
      (\(RenameState a _  c) b' -> RenameState a b' c)


-- The 'outer' vector represents a stack of scopes. Each entry is a combination
-- of a vector of used variables (length is equal to the number of variables
-- bound by that scope), together with a unique identifier not only for that
-- scope, but also the `step` into that scope, as required by wildcard renaming.
instance
  (k ~ A_Lens, a ~ Vector (Word32, Word64), b ~ Vector (Word32, Word64)) =>
  LabelOptic "tracker" k RenameState RenameState a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(RenameState _  _ y) -> y)
      (\(RenameState x y _) z' -> RenameState x y z')

-- | Ways in which the renamer can fail.
--
-- @since 1.1.0
data RenameError
  = -- | An attempt to reference an abstraction in a scope where this
    -- abstraction doesn't exist. First field is the true level, second is
    -- the index that was requested.
    --
    -- @since 1.0.0
    InvalidAbstractionReference Int (Index "tyvar")
   -- | We encountered a unifiable while un-renaming, which should not be possible.
  | InvalidScopeReference Int (Index "tyvar")
  -- TODO: Move to UnRenameError
  | UnRenameUnifiable Renamed
  | UnRenameWildCard Renamed
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

data UnRenameCxt = UnRenameCxt Word32 (Vector Word32)
  deriving stock
    ( -- @since 1.2.0
      Show,
      -- @since 1.2.0
      Eq,
      -- @since 1.2.0
      Ord
    )

instance
  (k ~ A_Lens, a ~ Word32, b ~ Word32) =>
  LabelOptic "inheritedScopeSize" k UnRenameCxt UnRenameCxt a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(UnRenameCxt x _) -> x)
      (\(UnRenameCxt _ y) x' -> UnRenameCxt x' y)


instance
  (k ~ A_Lens, a ~ Vector Word32, b ~ Vector Word32) =>
  LabelOptic "scopeInfo" k UnRenameCxt UnRenameCxt a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(UnRenameCxt _ y) -> y)
      (\(UnRenameCxt x _) y' -> UnRenameCxt x y')

-- | @since 1.2.0
newtype UnRenameM (a :: Type) = UnRenameM (ExceptT RenameError (Reader UnRenameCxt) a)
  deriving
    ( -- | @since 1.2.0
      Functor,
      -- | @since 1.2.0
      Applicative,
      -- | @since 1.2.0
      Monad,
      -- | @since 1.2.0
      MonadReader UnRenameCxt,
      -- | @since 1.2.0
      MonadError RenameError
    )
    via (ExceptT RenameError (Reader UnRenameCxt))

-- | Execute a renaming computation.
--
-- @since 1.2.0
runRenameM ::
  forall (a :: Type).
  Vector Word32 ->
  RenameM a ->
  Either RenameError a
runRenameM scopeInfo (RenameM comp) =
  evalState (runExceptT comp)
  . RenameState 0 (fromIntegral $ Vector.length scopeInfo)
  $ Vector.map (\x -> (x,0)) scopeInfo 

runUnRenameM ::
  forall (a :: Type).
  UnRenameM a ->
  Vector Word32 ->
  Either RenameError a
runUnRenameM (UnRenameM comp) inherited  = runReader (runExceptT comp) $ UnRenameCxt (fromIntegral $ Vector.length inherited) inherited

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
renameValT v = do
  r <- result
  let msg = "RenameValT: " <> show v <> "\n  result: " <> show r <> "\n"
  traceM  msg
  pure r
  where
    result = case v of
      Abstraction t -> Abstraction <$> renameAbstraction t
      ThunkT t -> ThunkT <$> renameCompT t
      BuiltinFlat t -> pure . BuiltinFlat $ t
      -- Assumes kind-checking has occurred
      Datatype tn xs -> RenameM $ do
        -- We don't step or un-step the scope here b/c a TyCon which appears as a ValT _cannot_ bind variables.
        -- This Vector here doesn't represent a function, but a product, so we there is no "return" type to treat specially (I think!)
        renamedXS <- Vector.mapM (coerce . renameValT) xs
        pure $ Datatype tn renamedXS

-- @since 1.1.0
renameDataDecl :: DataDeclaration AbstractTy -> RenameM (DataDeclaration Renamed)
renameDataDecl (OpaqueData tn manual) = pure $ OpaqueData tn manual
renameDataDecl (DataDeclaration tn cnt ctors strat) = RenameM $ do
  modify (stepUpScope cnt)
  renamedCtors <- Vector.mapM (coerce . renameCtor) ctors
  modify dropDownScope
  pure $ DataDeclaration tn cnt renamedCtors strat
  where
    renameCtor :: Constructor AbstractTy -> RenameM (Constructor Renamed)
    renameCtor (Constructor cn args) = Constructor cn <$> traverse renameValT args

-- REVIEW: I am not sure if we really want the scope arg to runRenameM to be `mempty`.
--         If something breaks w/ BB forms or datatypes, look here.
renameDatatypeInfo :: DatatypeInfo AbstractTy -> Either RenameError (DatatypeInfo Renamed)
renameDatatypeInfo (DatatypeInfo ogDecl baseFStuff bb) = runRenameM mempty $ do
  ogDecl' <- renameDataDecl ogDecl
  baseFStuff' <- traverse (bitraverse renameDataDecl renameValT) baseFStuff
  bb' <- traverse renameValT bb
  pure $ DatatypeInfo ogDecl' baseFStuff' bb'

-- A way of 'undoing' the renaming process. This is meant to be used only after
-- applications, and assumes that what is being un-renamed is the result of a
-- computation.
undoRename :: Vector Word32 -> ValT Renamed -> Either RenameError (ValT AbstractTy)
undoRename scope t = runUnRenameM (go t) scope
  where
    go :: ValT Renamed -> UnRenameM (ValT AbstractTy)
    go = \case
      Abstraction t' ->
        Abstraction <$> case t' of
          Rigid trueLevel index -> do
            db <- unTrueLevel trueLevel
            pure $ BoundAt db index
          w@(Wildcard _ trueLevel index) -> throwError $ UnRenameWildCard w -- error "Wildcard" --  BoundAt <$> trueLevelToDB trueLevel <*> pure index
          u@(Unifiable index) -> pure $ BoundAt Z index
      ThunkT (CompT abses (CompTBody xs)) ->
        ThunkT . CompT abses . CompTBody <$> local (over #scopeInfo (Vector.cons $ view wordCount abses)) (traverse go xs)
      BuiltinFlat t' -> pure . BuiltinFlat $ t'
      Datatype tn args -> Datatype tn <$> traverse go args

    unTrueLevel :: Int -> UnRenameM DeBruijn
    unTrueLevel tl = do
      trackerLen <- Vector.length <$> asks (view #scopeInfo)
      inheritedSize <- fromIntegral <$> asks (view #inheritedScopeSize)
      let db = trackerLen - 1 - inheritedSize - tl
      case preview asInt db of
        Nothing -> error "TODO: Real error. Invalid (negative) db in unTrueLevel"
        Just res -> pure res 


renameAbstraction :: AbstractTy -> RenameM Renamed
renameAbstraction (BoundAt scope index) = RenameM $ do
  let dbInt = review asInt scope
  traceM $ "\n\nRename Abstraction: Scope=" <> show scope <> ", Index: " <> show index
  tracker <- gets (view #tracker)
  traceM $ "Tracker: " <> show tracker
  inheritedScopeSize <- gets (fromIntegral . view #inheritedScope)
  traceM $ "Inherited scope size: " <> show inheritedScopeSize
  trueLevel <- gets (\x -> view (#tracker % to Vector.length) x - 1 - inheritedScopeSize - review asInt scope)
  traceM $ "True Level: " <> show trueLevel
  scopeInfo <- gets (\x -> view #tracker x Vector.!? review asInt scope)
  traceM $ "ScopeInfo: " <> show scopeInfo
  let asIntIx = review intIndex index
  case scopeInfo of
    Nothing -> throwError . InvalidAbstractionReference trueLevel $ index
    Just (occursTracker, uniqueScopeId) -> do
      result <-
            if | not (checkVarIxExists asIntIx occursTracker) -> throwError . InvalidScopeReference trueLevel $ index
               | trueLevel == 0 -> pure $ Unifiable index
               | trueLevel < 0 -> pure $ Rigid trueLevel index
               | otherwise -> pure $ Wildcard uniqueScopeId trueLevel index
      traceM $ "Result: " <> show result <> "\n\n"
      pure result
  where
    -- NOTE: The second argument here is actually a *count*, so we have to be sure to decrement it by one to check that
    --       that the first arg refers to a valid index
    checkVarIxExists :: Int -> Word32 -> Bool
    checkVarIxExists i wCount = fromIntegral i < wCount 

-- Helpers

-- Given a number of abstractions bound by a scope, modify the state to track
-- that scope.
stepUpScope :: Count "tyvar" -> RenameState -> RenameState
stepUpScope abses x =
  let fresh = view #idSource x
      absesW = view wordCount abses
      -- Label (speculatively) the current scope 'step' with a unique value.
      entry = (absesW, fresh)
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
