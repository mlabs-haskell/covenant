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
import Control.Monad.Except (ExceptT, MonadError (throwError), catchError, runExceptT)
import Control.Monad.Reader (MonadReader, Reader, asks, local, runReader)
import Control.Monad.State.Strict (State, evalState, gets, modify)
import Covenant.DeBruijn (DeBruijn, asInt)
import Covenant.Index
  ( Count,
    Index,
    count0,
    count1,
    count2,
    count3,
    intCount,
    intIndex,
  )
import Data.Coerce (coerce)
#if __GLASGOW_HASKELL__==908
import Data.Foldable (foldl')
#endif
import Data.Functor.Classes (Eq1 (liftEq))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Map.Merge.Strict qualified as Merge
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust, mapMaybe)
import Data.Ord (comparing)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Tuple.Optics (_1)
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NonEmpty
import Data.Word (Word64)
import Optics.AffineFold (preview)
import Optics.At (ix)
import Optics.Getter (to, view)
import Optics.Label (LabelOptic (labelOptic))
import Optics.Lens (A_Lens, Lens', lens)
import Optics.Optic ((%))
import Optics.Review (review)
import Optics.Setter (over, set)
import Prettyprinter
  ( Doc,
    Pretty (pretty),
    hsep,
    parens,
    viaShow,
    (<+>),
  )

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

instance Pretty (CompT Renamed) where
  pretty = runPrettyM . prettyCompTWithContext

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
  deriving stock
    ( -- | @since 1.0.0
      Eq,
      -- | @since 1.0.0
      Show
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
  unless (Vector.and ourAbstractions) (throwError UndeterminedAbstraction)
  -- Check result type
  renamedResult <- coerce . renameValT . NonEmpty.last $ xs
  -- Roll back state
  modify dropDownScope
  -- Rebuild and return
  pure . CompT abses . NonEmpty.snocV renamedArgs $ renamedResult

-- | Rename an abstraction.
--
-- @since 1.0.0
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

-- | Rename a value type.
--
-- @since 1.0.0
renameValT :: ValT AbstractTy -> RenameM (ValT Renamed)
renameValT = \case
  Abstraction t -> Abstraction <$> renameAbstraction t
  ThunkT t -> ThunkT <$> renameCompT t
  BuiltinFlat t -> pure . BuiltinFlat $ t

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

-- Pretty printing stuff, somewhat awkward to put it here but doing so avoids orphan instances

-- Keeping the field names for clarify even if we don't use them
newtype ScopeBoundary = ScopeBoundary {_getBoundary :: Int}
  deriving newtype (Show, Eq, Ord, Num, Enum)

data PrettyContext (ann :: Type)
  = PrettyContext
  { _pcBoundIdents :: Map ScopeBoundary [Doc ann],
    _pcCurrentScope :: ScopeBoundary,
    _pcVarStream :: [Doc ann]
  }

-- Lazily generated infinite list of variables. Will start with a, b, c... and cycle around to a1, b2, c3 etc.
-- We could do something more sophisticated but this should work.
infiniteVars :: forall (ann :: Type). [Doc ann]
infiniteVars =
  let aToZ = ['a' .. 'z']
      intStrings = ("" <$ aToZ) <> map (show @Integer) [0 ..]
   in zipWith (\x xs -> pretty (x : xs)) aToZ intStrings

-- optics, for convenience. Manually defined b/c TH splices tend to blow up HLS
boundIdents :: forall (ann :: Type). Lens' (PrettyContext ann) (Map ScopeBoundary [Doc ann])
boundIdents = lens goGet goSet
  where
    goGet :: PrettyContext ann -> Map ScopeBoundary [Doc ann]
    goGet (PrettyContext bi _ _) = bi

    goSet :: PrettyContext ann -> Map ScopeBoundary [Doc ann] -> PrettyContext ann
    goSet (PrettyContext _ scop vars) bi' = PrettyContext bi' scop vars

currentScope :: forall (ann :: Type). Lens' (PrettyContext ann) ScopeBoundary
currentScope = lens goGet goSet
  where
    goGet :: PrettyContext ann -> ScopeBoundary
    goGet (PrettyContext _ scop _) = scop

    goSet :: PrettyContext ann -> ScopeBoundary -> PrettyContext ann
    goSet (PrettyContext bi _ vars) scop = PrettyContext bi scop vars

varStream :: forall (ann :: Type). Lens' (PrettyContext ann) [Doc ann]
varStream = lens goGet goSet
  where
    goGet :: PrettyContext ann -> [Doc ann]
    goGet (PrettyContext _ _ vars) = vars

    goSet :: PrettyContext ann -> [Doc ann] -> PrettyContext ann
    goSet (PrettyContext bi scop _) = PrettyContext bi scop

-- Generate N fresh var names and use the supplied monadic function to do something with them.
withFreshVarNames :: forall (ann :: Type) (a :: Type). Int -> ([Doc ann] -> PrettyM ann a) -> PrettyM ann a
withFreshVarNames n act = do
  stream <- asks (view varStream)
  let (used, rest) = splitAt n stream
  local (set varStream rest) $ act used

-- Maybe make a newtype with error reporting since this can fail, but do later since *should't* fail
newtype PrettyM (ann :: Type) (a :: Type) = PrettyM (Reader (PrettyContext ann) a)
  deriving newtype (Functor, Applicative, Monad, MonadReader (PrettyContext ann))

runPrettyM :: forall (ann :: Type) (a :: Type). PrettyM ann a -> a
runPrettyM (PrettyM ma) = runReader ma (PrettyContext mempty 0 infiniteVars)

bindVars :: forall (ann :: Type) (a :: Type). Count "tyvar" -> ([Doc ann] -> PrettyM ann a) -> PrettyM ann a
bindVars count' act
  | count == 0 = crossBoundary (act [])
  | otherwise = crossBoundary $ do
      here <- asks (view currentScope)
      withFreshVarNames count $ \newBoundVars ->
        local (over boundIdents (Map.insert here newBoundVars)) (act newBoundVars)
  where
    -- Increment the current scope
    crossBoundary :: PrettyM ann a -> PrettyM ann a
    crossBoundary = local (over currentScope (+ 1))

    count :: Int
    count = review intCount count'

-- Bad name, but anyway, looks up the Doc for a pretty
lookupRigid :: forall (ann :: Type). Int -> Index "tyvar" -> PrettyM ann (Doc ann)
lookupRigid (ScopeBoundary -> scopeOffset) argIndex = do
  let argIndex' = review intIndex argIndex
  here <- asks (view currentScope)
  asks (preview (boundIdents % ix (here + scopeOffset) % ix argIndex')) >>= \case
    Nothing ->
      -- TODO: actual error reporting
      error $
        "Internal error: The encountered a variable at arg index "
          <> show argIndex'
          <> " with true level "
          <> show scopeOffset
          <> " but could not locate the corresponding pretty form at scope level "
          <> show here
    Just res' -> pure res'

prettyRenamedWithContext :: forall (ann :: Type). Renamed -> PrettyM ann (Doc ann)
prettyRenamedWithContext = \case
  Rigid offset index -> lookupRigid offset index
  Unifiable i -> lookupRigid 0 i -- ok maybe 'lookupRigid' isn't the best name
  Wildcard w64 i -> pure $ "_" <> viaShow w64 <> "#" <> pretty (review intIndex i)

prettyCompTWithContext :: forall (ann :: Type). CompT Renamed -> PrettyM ann (Doc ann)
prettyCompTWithContext (CompT count funArgs)
  | review intCount count == 0 = prettyFunTy (NonEmpty.toNonEmpty funArgs)
  | otherwise = bindVars count $ \newVars -> do
      funTy <- prettyFunTy (NonEmpty.toNonEmpty funArgs) -- easier to pattern match
      pure $ mkForall newVars funTy

mkForall :: forall (ann :: Type). [Doc ann] -> Doc ann -> Doc ann
mkForall tvars funTyBody = case tvars of
  [] -> funTyBody
  vars -> "forall" <+> hsep vars <> "." <+> funTyBody

prettyFunTy :: forall (ann :: Type). NonEmpty (ValT Renamed) -> PrettyM ann (Doc ann)
prettyFunTy (arg :| rest) = case rest of
  [] -> ("!" <>) <$> prettyArg arg
  (a : as) -> (\x y -> x <+> "->" <+> y) <$> prettyArg arg <*> prettyFunTy (a :| as)
  where
    prettyArg :: ValT Renamed -> PrettyM ann (Doc ann)
    prettyArg vt
      | isSimpleValT vt = prettyValTWithContext vt
      | otherwise = parens <$> prettyValTWithContext vt

-- I.e. can we omit parens and get something unambiguous? This might be overly aggressive w/ parens but that's OK
isSimpleValT :: forall (a :: Type). ValT a -> Bool
isSimpleValT = \case
  Abstraction _ -> True
  BuiltinFlat _ -> True
  ThunkT thunk -> isSimpleCompT thunk
  where
    isSimpleCompT :: CompT a -> Bool
    isSimpleCompT (CompT count args) = review intCount count == 0 && NonEmpty.length args == 1

prettyValTWithContext :: forall (ann :: Type). ValT Renamed -> PrettyM ann (Doc ann)
prettyValTWithContext = \case
  Abstraction abstr -> prettyRenamedWithContext abstr
  ThunkT compT -> prettyCompTWithContext compT
  BuiltinFlat biFlat -> pure $ viaShow biFlat
