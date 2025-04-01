{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Covenant.Type
  ( AbstractTy (..),
    Renamed (..),
    CompT (..),
    ValT (..),
    BuiltinFlatT (..),
    RenameError (..),
    renameValT,
    renameCompT,
    RenameM,
    runRenameM,
    pattern ReturnT,
    pattern (:--:>),
    TypeAppError (..),
    checkApp,
    arity,
    byteStringT,
    integerT,
    stringT,
    tyvar,
    boolT,
    g1T,
    g2T,
    mlResultT,
    comp0,
    comp1,
    comp2,
    comp3,
    unitT,
  )
where

import Control.Monad (foldM, unless)
import Control.Monad.Except (MonadError (throwError), catchError)
import Covenant.DeBruijn (DeBruijn)
import Covenant.Index
  ( Index,
    count0,
    count1,
    count2,
    count3,
    intCount,
    intIndex,
  )
import Covenant.Internal.Rename
  ( RenameError
      ( InvalidAbstractionReference,
        IrrelevantAbstraction,
        UndeterminedAbstraction
      ),
    RenameM,
    renameCompT,
    renameValT,
    runRenameM,
  )
import Covenant.Internal.Type
  ( AbstractTy (BoundAt),
    BuiltinFlatT
      ( BLS12_381_G1_ElementT,
        BLS12_381_G2_ElementT,
        BLS12_381_MlResultT,
        BoolT,
        ByteStringT,
        IntegerT,
        StringT,
        UnitT
      ),
    CompT (CompT),
    Renamed (Rigid, Unifiable, Wildcard),
    ValT (Abstraction, BuiltinFlat, ThunkT),
  )
#if __GLASGOW_HASKELL__==908
import Data.Foldable (foldl')
#endif
import Data.Kind (Type)
import Data.Map.Merge.Strict qualified as Merge
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Ord (comparing)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word64)
import Optics.Core (preview)

-- | Helper for defining the \'bodies\' of computation types, without having to
-- use 'NonEmptyVector' functions.
--
-- @since 1.0.0
pattern ReturnT :: forall (a :: Type). ValT a -> NonEmptyVector (ValT a)
pattern ReturnT x <- (returnHelper -> Just x)
  where
    ReturnT x = NonEmpty.singleton x

-- | Helper for defining the \'bodies\' of computation types, without having to
-- use 'NonEmptyVector' for functions. Together with 'ReturnT', we can write:
--
-- @'CompT' count0 ('BuiltinFlat' 'IntT' ':--:>' 'ReturnT' ('BuiltinFlat' 'IntT'))@
--
-- instead of:
--
-- @'CompT' count0 ('NonEmpty.consV' ('BuiltinFlat' 'IntT') ('Vector.singleton' ('BuiltinFlat' 'IntT')))@
--
-- @since 1.0.0
pattern (:--:>) ::
  forall (a :: Type).
  ValT a ->
  NonEmptyVector (ValT a) ->
  NonEmptyVector (ValT a)
pattern x :--:> xs <- (NonEmpty.uncons -> traverse NonEmpty.fromVector -> Just (x, xs))
  where
    x :--:> xs = NonEmpty.cons x xs

infixr 1 :--:>

-- | Determine the arity of a computation type: that is, how many arguments a
-- function of this type must be given.
--
-- @since 1.0.0
arity :: forall (a :: Type). CompT a -> Int
arity (CompT _ xs) = NonEmpty.length xs - 1

-- | Helper for defining computation types that do not bind any type variables.
--
-- @since 1.0.0
comp0 :: forall (a :: Type). NonEmptyVector (ValT a) -> CompT a
comp0 = CompT count0

-- | Helper for defining a computation type that binds one type variable (that
-- is, something whose type is @forall a . ... -> ...)@.
--
-- @since 1.0.0
comp1 :: NonEmptyVector (ValT AbstractTy) -> CompT AbstractTy
comp1 = CompT count1

-- | Helper for defining a computation type that binds two type variables (that
-- is, something whose type is @forall a b . ... -> ...)@.
--
-- @since 1.0.0
comp2 :: NonEmptyVector (ValT AbstractTy) -> CompT AbstractTy
comp2 = CompT count2

-- | Helper for defining a computation type that binds three type variables
-- (that is, something whose type is @forall a b c . ... -> ...)@.
--
-- @since 1.0.0
comp3 :: NonEmptyVector (ValT AbstractTy) -> CompT AbstractTy
comp3 = CompT count3

-- | Helper for defining type variables.
--
-- @since 1.0.0
tyvar :: DeBruijn -> Index "tyvar" -> ValT AbstractTy
tyvar db = Abstraction . BoundAt db

-- | Helper for defining the value type of builtin bytestrings.
--
-- @since 1.0.0
byteStringT :: forall (a :: Type). ValT a
byteStringT = BuiltinFlat ByteStringT

-- | Helper for defining the value type of builtin integers.
--
-- @since 1.0.0
integerT :: forall (a :: Type). ValT a
integerT = BuiltinFlat IntegerT

-- | Helper for defining the value type of builtin strings.
--
-- @since 1.0.0
stringT :: forall (a :: Type). ValT a
stringT = BuiltinFlat StringT

-- | Helper for defining the value type of builtin booleans.
--
-- @since 1.0.0
boolT :: forall (a :: Type). ValT a
boolT = BuiltinFlat BoolT

-- | Helper for defining the value type of BLS12-381 G1 curve points.
--
-- @since 1.0.0
g1T :: forall (a :: Type). ValT a
g1T = BuiltinFlat BLS12_381_G1_ElementT

-- | Helper for defining the value type of BLS12-381 G2 curve points.
--
-- @since 1.0.0
g2T :: forall (a :: Type). ValT a
g2T = BuiltinFlat BLS12_381_G2_ElementT

-- | Helper for defining the value type of BLS12-381 multiplication results.
--
-- @since 1.0.0
mlResultT :: forall (a :: Type). ValT a
mlResultT = BuiltinFlat BLS12_381_MlResultT

-- | Helper for defining the value type of the builtin unit type.
--
-- @since 1.0.0
unitT :: forall (a :: Type). ValT a
unitT = BuiltinFlat UnitT

-- | @since 1.0.0
data TypeAppError
  = -- | The final type after all arguments are applied is @forall a . a@.
    LeakingUnifiable (Index "tyvar")
  | -- | A wildcard (thus, a skolem) escaped its scope.
    LeakingWildcard Word64 (Index "tyvar")
  | -- | We were given too many arguments.
    ExcessArgs (Vector (ValT Renamed))
  | -- | We weren't given enough arguments.
    InsufficientArgs
  | -- | The expected type (first field) and actual type (second field) do not
    -- unify.
    DoesNotUnify (ValT Renamed) (ValT Renamed)
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
    )

-- | @since 1.0.0
checkApp :: CompT Renamed -> [ValT Renamed] -> Either TypeAppError (ValT Renamed)
checkApp (CompT _ xs) =
  let (curr, rest) = NonEmpty.uncons xs
   in go curr (Vector.toList rest)
  where
    go ::
      ValT Renamed ->
      [ValT Renamed] ->
      [ValT Renamed] ->
      Either TypeAppError (ValT Renamed)
    go currParam restParams args = case restParams of
      [] -> case args of
        [] -> case currParam of
          Abstraction (Unifiable index) -> throwError . LeakingUnifiable $ index
          Abstraction (Wildcard scopeId index) -> throwError . LeakingWildcard scopeId $ index
          ThunkT (CompT _ xs') -> do
            let remainingUnifiables = NonEmpty.foldl' (\acc t -> acc <> collectUnifiables t) Set.empty xs'
            let requiredIntroductions = Set.size remainingUnifiables
            -- We know that the size of a set cannot be negative, but GHC
            -- doesn't.
            let asCount = fromJust . preview intCount $ requiredIntroductions
            let indexesToUse = mapMaybe (preview intIndex) [0, 1 .. requiredIntroductions - 1]
            let renames = zipWith (\i replacement -> (i, Abstraction . Unifiable $ replacement)) (Set.toList remainingUnifiables) indexesToUse
            let fixed = fmap (\t -> foldl' (\acc (i, r) -> substitute i r acc) t renames) xs'
            pure . ThunkT . CompT asCount $ fixed
          _ -> pure currParam
        _ -> throwError . ExcessArgs . Vector.fromList $ args
      _ -> case args of
        [] -> throwError InsufficientArgs
        (currArg : restArgs) -> do
          subs <- catchError (unify currParam currArg) (promoteUnificationError currParam currArg)
          case Map.foldlWithKey' (\acc index sub -> fmap (substitute index sub) acc) restParams subs of
            [] -> throwError InsufficientArgs
            (currParam' : restParams') -> go currParam' restParams' restArgs

-- Helpers

collectUnifiables :: ValT Renamed -> Set (Index "tyvar")
collectUnifiables = \case
  Abstraction t -> case t of
    Unifiable index -> Set.singleton index
    _ -> Set.empty
  BuiltinFlat _ -> Set.empty
  ThunkT (CompT _ xs) -> NonEmpty.foldl' (\acc t -> acc <> collectUnifiables t) Set.empty xs

-- Because unification is inherently recursive, if we find an error deep within
-- a type, the message will signify only the _part_ that fails to unify, not the
-- entire type. While potentially useful, this can be quite confusing,
-- especially with generated types. Thus, we use `catchError` with this
-- function, which effectively allows us to rename the types reported in
-- unification errors to whatever types 'wrap' them.
promoteUnificationError ::
  forall (a :: Type).
  ValT Renamed ->
  ValT Renamed ->
  TypeAppError ->
  Either TypeAppError a
promoteUnificationError topLevelExpected topLevelActual =
  Left . \case
    DoesNotUnify _ _ -> DoesNotUnify topLevelExpected topLevelActual
    err -> err

returnHelper ::
  forall (a :: Type).
  NonEmptyVector (ValT a) ->
  Maybe (ValT a)
returnHelper xs = case NonEmpty.uncons xs of
  (y, ys) ->
    if Vector.length ys == 0
      then pure y
      else Nothing

unify ::
  ValT Renamed ->
  ValT Renamed ->
  Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
unify expected actual =
  catchError
    ( case expected of
        Abstraction t1 -> case t1 of
          -- Unifiables unify with everything, and require a substitutional rewrite.
          Unifiable index1 -> pure . Map.singleton index1 $ actual
          Rigid level1 index1 -> expectRigid level1 index1
          Wildcard scopeId1 index1 -> expectWildcard scopeId1 index1
        ThunkT t1 -> expectThunk t1
        BuiltinFlat t1 -> expectFlatBuiltin t1
    )
    (promoteUnificationError expected actual)
  where
    unificationError :: forall (a :: Type). Either TypeAppError a
    unificationError = Left . DoesNotUnify expected $ actual
    noSubUnify :: forall (k :: Type) (a :: Type). Either TypeAppError (Map k a)
    noSubUnify = pure Map.empty
    expectRigid ::
      Int -> Index "tyvar" -> Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
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
      Word64 -> Index "tyvar" -> Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
    -- Wildcards can unify with unifiables, as well as themselves, but nothing
    -- else. No substitutional rewrites are needed.
    expectWildcard scopeId1 index1 = case actual of
      Abstraction (Unifiable _) -> noSubUnify
      Abstraction (Wildcard scopeId2 index2) ->
        if scopeId1 /= scopeId2 || index1 == index2
          then noSubUnify
          else unificationError
      _ -> unificationError
    expectThunk :: CompT Renamed -> Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
    -- Thunks unify unconditionally with wildcards or unifiables. They unify
    -- conditionally with other thunks, provided that we can unify each argument
    -- with its counterpart in the same position, as well as their result types,
    -- without conflicts.
    expectThunk (CompT _ t1) = case actual of
      Abstraction (Rigid _ _) -> unificationError
      Abstraction _ -> noSubUnify
      ThunkT (CompT _ t2) -> do
        unless (comparing NonEmpty.length t1 t2 == EQ) unificationError
        catchError
          (foldM (\acc (l, r) -> unify l r >>= reconcile acc) Map.empty . NonEmpty.zip t1 $ t2)
          (promoteUnificationError expected actual)
      _ -> unificationError
    expectFlatBuiltin :: BuiltinFlatT -> Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
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
    reconcile ::
      Map (Index "tyvar") (ValT Renamed) ->
      Map (Index "tyvar") (ValT Renamed) ->
      Either TypeAppError (Map (Index "tyvar") (ValT Renamed))
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

substitute :: Index "tyvar" -> ValT Renamed -> ValT Renamed -> ValT Renamed
substitute index toSub = \case
  Abstraction t -> case t of
    Unifiable ourIndex ->
      if ourIndex == index
        then toSub
        else Abstraction t
    _ -> Abstraction t
  ThunkT (CompT abstractions xs) ->
    ThunkT . CompT abstractions . fmap (substitute index toSub) $ xs
  BuiltinFlat t -> BuiltinFlat t
