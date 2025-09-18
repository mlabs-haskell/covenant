{-# LANGUAGE CPP #-}

module Covenant.Internal.Unification
  ( TypeAppError (..),
    checkApp,
    runUnifyM,
    UnifyM,
    -- These are exported for use with ASG helpers, largely (but not exclusively) the intro forms helper
    unify,
    substitute,
    fixUp,
    reconcile,
  )
where

import Control.Monad (foldM, unless, when)
import Data.Ord (comparing)
#if __GLASGOW_HASKELL__==908
import Data.Foldable (foldl')
#endif
import Control.Monad.Except (MonadError, catchError, throwError)
import Control.Monad.Reader (MonadReader, ReaderT (runReaderT), ask)
import Covenant.Data (DatatypeInfo)
import Covenant.Index (Index, intCount, intIndex)
import Covenant.Internal.Rename (RenameError, renameDatatypeInfo)
import Covenant.Internal.Type
  ( AbstractTy,
    BuiltinFlatT,
    CompT (CompT),
    CompTBody (CompTBody),
    Renamed (Rigid, Unifiable, Wildcard),
    TyName,
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT), DataDeclaration (OpaqueData),
  )
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map.Merge.Strict qualified as Merge
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word64)
import Optics.Core (ix, preview, view)

-- | Possible errors resulting from applications of arguments to functions.
--
-- @since 1.0.0
data TypeAppError
  = -- | The final type after all arguments are applied is @forall a . a@.
    LeakingUnifiable (Index "tyvar")
  | -- | A wildcard (thus, a skolem) escaped its scope.
    LeakingWildcard Word64 Int (Index "tyvar")
  | -- | We were given too many arguments.
    ExcessArgs (CompT Renamed) (Vector (Maybe (ValT Renamed)))
  | -- | We weren't given enough arguments.
    --
    -- @since 1.1.0
    InsufficientArgs Int (CompT Renamed) [Maybe (ValT Renamed)]
  | -- | The expected type (first field) and actual type (second field) do not
    -- unify.
    DoesNotUnify (ValT Renamed) (ValT Renamed)
  | -- | No datatype info associated with requested TyName
    --
    -- @since 1.1.0
    NoDatatypeInfo TyName
  | -- | No BB form. The only datatypes which should lack one are those isomorphic to `Void`.
    --
    -- @since 1.1.0
    NoBBForm TyName
  | -- | Datatype renaming failed.
    --
    -- @since 1.1.0
    DatatypeInfoRenameFailed TyName RenameError
  | -- | Something happened that definitely should not have. For right now, this means: The BB form of a datatype isn't a thunk
    --   (but it might be useful to keep this around as a catchall for things that really shouldn't happen).
    --
    -- @since 1.1.0
    ImpossibleHappened Text
  | -- Could not reconcile two assignments with the same index
    -- @since 1.2.0
    CouldNotReconcile (Index "tyvar") (ValT Renamed) (ValT Renamed)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

{- This will probably only get used directly in testing and we'll use capabilities w/ the class everywhere else? -}
newtype UnifyM a = UnifyM (ReaderT (Map TyName (DatatypeInfo AbstractTy)) (Either TypeAppError) a)
  deriving
    ( -- | @since 1.1.0
      Functor,
      Applicative,
      Monad,
      MonadReader (Map TyName (DatatypeInfo AbstractTy)),
      MonadError TypeAppError
    )
    via (ReaderT (Map TyName (DatatypeInfo AbstractTy)) (Either TypeAppError))

runUnifyM :: Map TyName (DatatypeInfo AbstractTy) -> UnifyM a -> Either TypeAppError a
runUnifyM tyDict (UnifyM act) = runReaderT act tyDict

lookupDatatypeInfo ::
  TyName ->
  UnifyM (DatatypeInfo Renamed)
lookupDatatypeInfo tn =
  ask >>= \tyDict -> case preview (ix tn) tyDict of
    Nothing -> throwError . NoDatatypeInfo $ tn
    Just dti -> renamedToUnify . renameDatatypeInfo $ dti
  where
    renamedToUnify :: Either RenameError (DatatypeInfo Renamed) -> UnifyM (DatatypeInfo Renamed)
    renamedToUnify = either (throwError . DatatypeInfoRenameFailed tn) pure

lookupBBForm :: TyName -> UnifyM (ValT Renamed)
lookupBBForm tn =
  lookupDatatypeInfo tn >>= \dti -> case view #bbForm dti of
    Nothing -> throwError $ NoBBForm tn
    Just bbForm -> pure bbForm

-- Opaque types do not (and cannot) have a BB form, which breaks unification machinery that assumes all inhabiated types
-- have such a form. We need to branch on the "Opacity" of a type in `expectDatatype` and this lets us do that
isOpaqueType :: TyName -> UnifyM Bool
isOpaqueType tn = lookupDatatypeInfo tn >>= \dti -> case view #originalDecl dti of
  OpaqueData{} -> pure True
  _ -> pure False

-- | Given information about in-scope datatypes, a computation type, and a list
-- of arguments (some of which may be errors), try to construct the type of the
-- result of the application of those arguments to the computation.
--
-- @since 1.0.0
checkApp ::
  Map TyName (DatatypeInfo AbstractTy) ->
  CompT Renamed ->
  [Maybe (ValT Renamed)] ->
  Either TypeAppError (ValT Renamed)
checkApp tyDict f args = runUnifyM tyDict $ checkApp' f args

checkApp' ::
  CompT Renamed ->
  [Maybe (ValT Renamed)] ->
  UnifyM (ValT Renamed)
checkApp' f@(CompT _ (CompTBody xs)) ys = do
  let (curr, rest) = NonEmpty.uncons xs
      numArgsExpected = NonEmpty.length xs - 1
      numArgsActual = length ys
  when (numArgsActual < numArgsExpected) $
    throwError $
      InsufficientArgs numArgsActual f ys
  when (numArgsExpected > numArgsActual) $
    throwError $
      ExcessArgs f (Vector.fromList ys)
  go curr (Vector.toList rest) ys
  where
    go ::
      ValT Renamed ->
      [ValT Renamed] ->
      [Maybe (ValT Renamed)] ->
      UnifyM (ValT Renamed)
    go currParam restParams args = case restParams of
      [] -> case args of
        -- If we got here, currParam is the resulting type after all
        -- substitutions have been applied.
        [] -> fixUp currParam
        _ -> throwError . ExcessArgs f . Vector.fromList $ args
      _ -> case args of
        [] -> throwError $ InsufficientArgs (length args) f args
        (currArg : restArgs) -> do
          newRestParams <- case currArg of
            -- An error argument unifies with anything, as it's effectively
            -- `forall a . a`. Furthermore, it requires no substitutional
            -- changes. Thus, we can just skip it.
            Nothing -> pure restParams
            Just currArg' -> do
              subs <- catchError (unify currParam currArg') (promoteUnificationError currParam currArg')
              pure . Map.foldlWithKey' applySub restParams $ subs
          case newRestParams of
            [] -> throwError $ InsufficientArgs (length args) f args
            (currParam' : restParams') -> go currParam' restParams' restArgs

-- Helpers

applySub ::
  [ValT Renamed] ->
  Index "tyvar" ->
  ValT Renamed ->
  [ValT Renamed]
applySub acc index sub = fmap (substitute index sub) acc

substitute ::
  Index "tyvar" ->
  ValT Renamed ->
  ValT Renamed ->
  ValT Renamed
substitute index toSub = \case
  Abstraction t -> case t of
    Unifiable ourIndex ->
      if ourIndex == index
        then toSub
        else Abstraction t
    _ -> Abstraction t
  ThunkT (CompT abstractions (CompTBody xs)) ->
    ThunkT . CompT abstractions . CompTBody . fmap (substitute index toSub) $ xs
  BuiltinFlat t -> BuiltinFlat t
  Datatype tn args -> Datatype tn $ substitute index toSub <$> args

-- Because unification is inherently recursive, if we find an error deep within
-- a type, the message will signify only the _part_ that fails to unify, not the
-- entire type. While potentially useful, this can be quite confusing,
-- especially with generated types. Thus, we use `catchError` with this
-- function, which effectively allows us to rename the types reported in
-- unification errors to whatever types 'wrap' them.
promoteUnificationError ::
  ValT Renamed ->
  ValT Renamed ->
  TypeAppError ->
  UnifyM a
promoteUnificationError topLevelExpected topLevelActual =
  throwError . \case
    DoesNotUnify _ _ -> DoesNotUnify topLevelExpected topLevelActual
    err -> err

fixUp :: ValT Renamed -> UnifyM (ValT Renamed)
fixUp = \case
  -- We're doing the equivalent of failing the `ST` trick
  Abstraction (Wildcard scopeId trueLevel index) -> throwError . LeakingWildcard scopeId trueLevel $ index
  -- We may have a result with fewer unifiables than we started with
  -- This can be a problem, as we might be referring to unifiables that don't
  -- exist anymore
  ThunkT (CompT _ (CompTBody xs)) -> do
    -- Figure out how many variables the thunk has to introduce now
    let remainingUnifiables = NonEmpty.foldl' (\acc t -> acc <> collectUnifiables t) Set.empty xs
    let requiredIntroductions = Set.size remainingUnifiables
    -- We know that the size of a set can't be negative, but GHC doesn't.
    let asCount = fromJust . preview intCount $ requiredIntroductions
    -- Make enough indexes for us to use in one go
    let indexesToUse = mapMaybe (preview intIndex) [0, 1 .. requiredIntroductions - 1]
    -- Construct a mapping between old, possibly non-contiguous, unifiables and
    -- our new ones
    let renames =
          zipWith
            (\i replacement -> (i, Abstraction . Unifiable $ replacement))
            (Set.toList remainingUnifiables)
            indexesToUse
    let fixed = fmap (\t -> foldl' (\acc (i, r) -> substitute i r acc) t renames) xs
    pure . ThunkT . CompT asCount . CompTBody $ fixed
  t -> pure t

collectUnifiables :: ValT Renamed -> Set (Index "tyvar")
collectUnifiables = \case
  Abstraction t -> case t of
    Unifiable index -> Set.singleton index
    _ -> Set.empty
  BuiltinFlat _ -> Set.empty
  ThunkT (CompT _ (CompTBody xs)) -> NonEmpty.foldl' (\acc t -> acc <> collectUnifiables t) Set.empty xs
  Datatype _ args -> Vector.foldl' (\acc t -> acc <> collectUnifiables t) Set.empty args

unify ::
  ValT Renamed ->
  ValT Renamed ->
  UnifyM (Map (Index "tyvar") (ValT Renamed))
unify expected actual =
  catchError
    ( case expected of
        Abstraction t1 -> case t1 of
          -- Unifiables unify with everything, and require a substitutional rewrite.
          Unifiable index1 -> pure . Map.singleton index1 $ actual
          Rigid level1 index1 -> expectRigid level1 index1
          Wildcard scopeId1 _ index1 -> expectWildcard scopeId1 index1
        ThunkT t1 -> expectThunk t1
        BuiltinFlat t1 -> expectFlatBuiltin t1
        Datatype tn xs -> expectDatatype tn xs
    )
    (promoteUnificationError expected actual)
  where
    unificationError :: forall (a :: Type). UnifyM a
    unificationError = throwError . DoesNotUnify expected $ actual
    noSubUnify :: forall (k :: Type) (a :: Type). UnifyM (Map k a)
    noSubUnify = pure Map.empty
    expectRigid ::
      Int -> Index "tyvar" -> UnifyM (Map (Index "tyvar") (ValT Renamed))
    -- Rigids behave identically to concrete types: they can unify with
    -- themselves, or any other abstraction, but nothing else. No substitutional
    -- rewrites are needed.
    expectRigid level1 index1 = case actual of
      Abstraction (Rigid level2 index2) ->
        if level1 == level2 && index1 == index2
          then noSubUnify
          else unificationError
      Abstraction _ -> noSubUnify
      _ -> unificationError
    expectWildcard ::
      Word64 -> Index "tyvar" -> UnifyM (Map (Index "tyvar") (ValT Renamed))
    -- Wildcards can unify with unifiables, as well as themselves, but nothing
    -- else. No substitutional rewrites are needed.
    expectWildcard scopeId1 index1 = case actual of
      Abstraction (Unifiable _) -> noSubUnify
      Abstraction (Wildcard scopeId2 _ index2) ->
        if scopeId1 /= scopeId2 || index1 == index2
          then noSubUnify
          else unificationError
      _ -> unificationError
    expectThunk :: CompT Renamed -> UnifyM (Map (Index "tyvar") (ValT Renamed))
    -- Thunks unify unconditionally with wildcards or unifiables. They unify
    -- conditionally with other thunks, provided that we can unify each argument
    -- with its counterpart in the same position, as well as their result types,
    -- without conflicts.
    expectThunk (CompT _ (CompTBody t1)) = case actual of
      Abstraction (Rigid _ _) -> unificationError
      Abstraction _ -> noSubUnify
      ThunkT (CompT _ (CompTBody t2)) -> do
        unless (comparing NonEmpty.length t1 t2 == EQ) unificationError
        catchError
          (foldM (\acc (l, r) -> unify l r >>= reconcile acc) Map.empty . NonEmpty.zip t1 $ t2)
          (promoteUnificationError expected actual)
      _ -> unificationError
    expectFlatBuiltin :: BuiltinFlatT -> UnifyM (Map (Index "tyvar") (ValT Renamed))
    -- 'Flat' builtins are always concrete. They can unify with themselves,
    -- unifiables or wildcards, but nothing else. No substitutional rewrites are
    -- needed.
    expectFlatBuiltin t1 = case actual of
      Abstraction (Rigid _ _) -> unificationError
      Abstraction _ -> noSubUnify
      BuiltinFlat t2 ->
        if t1 == t2
          then noSubUnify
          else unificationError
      _ -> unificationError
    expectDatatype :: TyName -> Vector (ValT Renamed) -> UnifyM (Map (Index "tyvar") (ValT Renamed))
    -- Datatypes unify with wildcards or unifiables, or other "suitable" instances of the same datatype.
    -- Suitability with other datatypes is determined by converting to BB form, then concretifying
    -- the BB form using the arguments to the actual datatype.
    -- For example, the BB form of `Maybe` is: forall a r. r -> (a -> r) -> r
    -- which, if we concretify while attempting to unify with `Maybe Int`, becomes: `forall r. r -> (Int -> r) -> r`
    --
    -- Opaque datatypes are a special exception and are treated analogously to Builtins: They unify only with themselves,
    -- unifiables, or wildcards.
    expectDatatype tn args = do
      isOpaqueType tn >>= \case
        False -> do
          bbForm <- lookupBBForm tn
          bbFormConcreteE <- concretify bbForm args
          case actual of
            Abstraction (Rigid _ _) -> unificationError
            Abstraction _ -> noSubUnify
            Datatype tn' args'
              | tn' /= tn -> unificationError
              | otherwise -> do
                  bbFormConcreteA <- concretify bbForm args'
                  unify bbFormConcreteE bbFormConcreteA
            _ -> unificationError
        True -> case actual of
          Abstraction Rigid{} -> unificationError
          Abstraction _ -> noSubUnify
          -- Opaque datatypes cannot be parameterized, so we only need to check the TyName
          Datatype tn' _args ->
            if tn == tn'
             then noSubUnify
             else unificationError
          _ -> unificationError
    concretify :: ValT Renamed -> Vector (ValT Renamed) -> UnifyM (ValT Renamed)
    concretify (ThunkT (CompT count (CompTBody fn))) args = fixUp $ ThunkT (CompT count (CompTBody newFn))
      where
        indexedArgs :: [(Index "tyvar", ValT Renamed)]
        indexedArgs = Vector.toList $ Vector.imap (\i x -> (fromJust . preview intIndex $ i, x)) args
        newFn :: NonEmptyVector (ValT Renamed)
        newFn = go indexedArgs <$> fn
        go :: [(Index "tyvar", ValT Renamed)] -> ValT Renamed -> ValT Renamed
        go subs arg = foldl' (\val (i, concrete) -> substitute i concrete val) arg subs
    concretify _ _ = throwError $ ImpossibleHappened "bbForm is not a thunk"

reconcile ::
  Map (Index "tyvar") (ValT Renamed) ->
  Map (Index "tyvar") (ValT Renamed) ->
  UnifyM (Map (Index "tyvar") (ValT Renamed))
-- Note (Koz, 14/04/2025): This utter soup means the following:
--
-- - If the old map and the new map don't have any overlapping assignments,
--   just union them.
-- - Otherwise, for any assignment to a unifiable that is present in both
--   maps, ensure they assign to the same thing; if they do, it's fine,
--   otherwise we have a problem.
reconcile =
  Merge.mergeA
    Merge.preserveMissing
    Merge.preserveMissing
    (Merge.zipWithAMatched combineBindings)
  where
    combineBindings :: Index "tyvar" -> ValT Renamed -> ValT Renamed -> UnifyM (ValT Renamed)
    combineBindings i old new =
      if old == new
        then pure old
        else case old of
          Abstraction (Unifiable _) -> pure new
          _ -> case new of
            Abstraction (Unifiable _) -> pure old
            _ -> throwError $ CouldNotReconcile i old new
