{-# LANGUAGE CPP #-}

module Covenant.Internal.Unification
  ( TypeAppError (..),
    checkApp,
    runUnifyM,
    MonadUnify (..)
  )
where

import Control.Monad (foldM, unless)
import Data.Ord (comparing)
#if __GLASGOW_HASKELL__==908
import Data.Foldable (foldl')
#endif
import Control.Monad.Except (catchError, throwError, MonadError)
import Covenant.Index (Index, intCount, intIndex)
import Covenant.Internal.Type
  ( BuiltinFlatT,
    CompT (CompT),
    CompTBody (CompTBody),
    Renamed (Rigid, Unifiable, Wildcard),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT), TyName, AbstractTy,
  )
import Data.Kind (Type)
import Data.Map (Map)
import Data.Map.Merge.Strict qualified as Merge
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word64)
import Optics.Core (preview, ix, view)
import Control.Monad.Reader (ReaderT (runReaderT), MonadReader, ask)
import Covenant.Data (DatatypeInfo, renameDatatypeInfo)
import Data.Text (Text)
import Covenant.Internal.Rename (RenameError)

-- | @since 1.0.0
data TypeAppError
  = -- | The final type after all arguments are applied is @forall a . a@.
    LeakingUnifiable (Index "tyvar")
  | -- | A wildcard (thus, a skolem) escaped its scope.
    LeakingWildcard Word64 Int (Index "tyvar")
  | -- | We were given too many arguments.
    ExcessArgs (CompT Renamed) (Vector (Maybe (ValT Renamed)))
  | -- | We weren't given enough arguments.
    InsufficientArgs (CompT Renamed)
  | -- | The expected type (first field) and actual type (second field) do not
    -- unify.
    DoesNotUnify (ValT Renamed) (ValT Renamed)
  | -- | No datatype info associated with requested TyName
    NoDatatypeInfo TyName
  | -- | No BB form. The only datatypes which should lack one are those isomorphic to `Void`
    NoBBForm TyName
  | -- | Datatype renaming failed. NOTE/REVIEW: Using `DatatypeInfo AbstractTy` here lets use use the same
    --   reader context as ASGBuilder, which seems like the simplest change possible
    --   I guess actually this means that renaming the BB form of a datatype failed
    DatatypeInfoRenameFailed TyName RenameError
  | -- | Something happened that definitely should not have. For right now, this means: The BB form of a datatype isn't a thunk
    --   (but it might be useful to keep this around as a catchall for things that really shouldn't happen)
    ImpossibleHappened Text
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
    ) via (ReaderT (Map TyName (DatatypeInfo AbstractTy)) (Either TypeAppError))

runUnifyM :: Map TyName (DatatypeInfo AbstractTy) -> UnifyM a -> Either TypeAppError a
runUnifyM tyDict (UnifyM act) = runReaderT act tyDict

-- REVIEW: @Koz you hate it every time I make a type class (and you're often not wrong to), but here
--         this really seems like the best way to make this play nice with ASGBuilder
class (Monad m) => MonadUnify (m :: Type -> Type) where
  askDatatypes :: m (Map TyName (DatatypeInfo AbstractTy))
  throwTypeAppErr :: forall (a :: Type).TypeAppError -> m a
  catchTypeAppErr :: forall (a :: Type). m a -> (TypeAppError -> m a) -> m a

lookupDatatypeInfo :: forall (m :: Type -> Type)
                    . MonadUnify m
                   => TyName
                   -> m (DatatypeInfo Renamed)
lookupDatatypeInfo tn = askDatatypes >>= \tyDict -> case preview (ix tn) tyDict of
  Nothing -> throwTypeAppErr $ NoDatatypeInfo tn
  Just dti -> either (throwTypeAppErr . DatatypeInfoRenameFailed tn) pure $ renameDatatypeInfo dti

lookupBBForm :: forall (m :: Type -> Type). MonadUnify m => TyName -> m (ValT Renamed)
lookupBBForm tn = lookupDatatypeInfo tn >>= \dti -> case view #bbForm dti of
  Nothing -> throwTypeAppErr $ NoBBForm tn
  Just bbForm -> pure bbForm

instance MonadUnify UnifyM where
  askDatatypes = ask
  throwTypeAppErr = throwError
  catchTypeAppErr = catchError

-- | @since 1.1.0
checkApp :: forall (m :: Type -> Type)
          . MonadUnify m
         => CompT Renamed
         -> [Maybe (ValT Renamed)]
         -> m (ValT Renamed)
checkApp f@(CompT _ (CompTBody xs)) =
  let (curr, rest) = NonEmpty.uncons xs
   in go curr (Vector.toList rest)
  where
    go ::
      ValT Renamed ->
      [ValT Renamed] ->
      [Maybe (ValT Renamed)] ->
      m (ValT Renamed)
    go currParam restParams args = case restParams of
      [] -> case args of
        -- If we got here, currParam is the resulting type after all
        -- substitutions have been applied.
        [] -> fixUp currParam
        _ -> throwTypeAppErr . ExcessArgs f . Vector.fromList $ args
      _ -> case args of
        [] -> throwTypeAppErr  . InsufficientArgs $ f
        (currArg : restArgs) -> do
          newRestParams <- case currArg of
            -- An error argument unifies with anything, as it's effectively
            -- `forall a . a`. Furthermore, it requires no substitutional
            -- changes. Thus, we can just skip it.
            Nothing -> pure restParams
            Just currArg' -> do
              subs <- catchTypeAppErr (unify currParam currArg') (promoteUnificationError currParam currArg')
              pure . Map.foldlWithKey' applySub restParams $ subs
          case newRestParams of
            [] -> throwTypeAppErr . InsufficientArgs $ f
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
  forall (a :: Type) (m :: Type -> Type).
  MonadUnify m =>
  ValT Renamed ->
  ValT Renamed ->
  TypeAppError ->
  m a
promoteUnificationError topLevelExpected topLevelActual =
  throwTypeAppErr . \case
    DoesNotUnify _ _ -> DoesNotUnify topLevelExpected topLevelActual
    err -> err

fixUp :: forall (m :: Type -> Type). MonadUnify m => ValT Renamed -> m (ValT Renamed)
fixUp = \case
  -- We have a result that's effectively `forall a . a` but not an error
  Abstraction (Unifiable index) -> throwTypeAppErr . LeakingUnifiable $ index
  -- We're doing the equivalent of failing the `ST` trick
  Abstraction (Wildcard scopeId trueLevel index) -> throwTypeAppErr . LeakingWildcard scopeId trueLevel $ index
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
  forall (m :: Type -> Type).
  MonadUnify m =>
  ValT Renamed ->
  ValT Renamed ->
  m (Map (Index "tyvar") (ValT Renamed))
unify expected actual =
  catchTypeAppErr
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
    unificationError :: forall (a :: Type). m a
    unificationError = throwTypeAppErr . DoesNotUnify expected $ actual
    noSubUnify :: forall (k :: Type) (a :: Type). m (Map k a)
    noSubUnify = pure Map.empty
    expectRigid ::
      Int -> Index "tyvar" -> m (Map (Index "tyvar") (ValT Renamed))
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
      Word64 -> Index "tyvar" -> m (Map (Index "tyvar") (ValT Renamed))
    -- Wildcards can unify with unifiables, as well as themselves, but nothing
    -- else. No substitutional rewrites are needed.
    expectWildcard scopeId1 index1 = case actual of
      Abstraction (Unifiable _) -> noSubUnify
      Abstraction (Wildcard scopeId2 _ index2) ->
        if scopeId1 /= scopeId2 || index1 == index2
          then noSubUnify
          else unificationError
      _ -> unificationError
    expectThunk :: CompT Renamed -> m (Map (Index "tyvar") (ValT Renamed))
    -- Thunks unify unconditionally with wildcards or unifiables. They unify
    -- conditionally with other thunks, provided that we can unify each argument
    -- with its counterpart in the same position, as well as their result types,
    -- without conflicts.
    expectThunk (CompT _ (CompTBody t1)) = case actual of
      Abstraction (Rigid _ _) -> unificationError
      Abstraction _ -> noSubUnify
      ThunkT (CompT _ (CompTBody t2)) -> do
        unless (comparing NonEmpty.length t1 t2 == EQ) unificationError
        catchTypeAppErr
          (foldM (\acc (l, r) -> unify l r >>= reconcile acc) Map.empty . NonEmpty.zip t1 $ t2)
          (promoteUnificationError expected actual)
      _ -> unificationError
    expectFlatBuiltin :: BuiltinFlatT -> m (Map (Index "tyvar") (ValT Renamed))
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

    expectDatatype :: TyName -> Vector (ValT Renamed) -> m (Map (Index "tyvar") (ValT Renamed))
    expectDatatype tn args = do
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

    concretify :: ValT Renamed -> Vector (ValT Renamed) -> m (ValT Renamed)
    concretify (ThunkT compT) args = checkApp compT (pure <$> Vector.toList args)
    concretify _ _ = throwTypeAppErr $ ImpossibleHappened "BBForm not a Thunk"

    
    reconcile ::
      Map (Index "tyvar") (ValT Renamed) ->
      Map (Index "tyvar") (ValT Renamed) ->
      m (Map (Index "tyvar") (ValT Renamed))
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
        (Merge.zipWithAMatched $ \_ l r -> l <$ unless (l == r) unificationError)
