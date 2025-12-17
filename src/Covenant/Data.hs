{-# LANGUAGE ViewPatterns #-}

-- |
-- Module: Covenant.Data
-- Copyright: (C) MLabs 2025
-- License: Apache 2.0
-- Maintainer: koz@mlabs.city, sean@mlabs.city
--
-- Information about datatype definitions, and various ways to interact with
-- them. Most of the useful functionality is in 'DatatypeInfo' and its optics.
--
-- = Note
--
-- Some of the low-level functions in the module make use of @ScopeBoundary@.
-- This is mostly an artifact of needing this for tests; if you ever need their
-- functionality, assume that the only sensible value is @0@, which will work
-- via its overloaded number syntax.
--
-- @since 1.1.0
module Covenant.Data
  ( -- * Types
    BBFError (..),
    DatatypeInfo (..),

    -- * Functions

    -- ** Datatype-related
    mkDatatypeInfo,
    allComponentTypes,
    mkBBF,
    noPhantomTyVars,

    -- ** Lower-level
    mkBaseFunctor,
    isRecursiveChildOf,
    hasRecursive,
    everythingOf,
    mapValT,

    -- ** Constants
    primBaseFunctorInfos,
  )
where

import Control.Monad.Except (MonadError (throwError))
import Control.Monad.Reader (MonadReader (ask, local), MonadTrans (lift), Reader, runReader)
import Control.Monad.Trans.Except (ExceptT, runExceptT)
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index (Count, Index, count0, intCount, intIndex, ix0)
import Covenant.Internal.PrettyPrint (ScopeBoundary (ScopeBoundary))
import Covenant.Internal.Strategy
  ( DataEncoding (SOP),
    PlutusDataConstructor (PlutusB, PlutusConstr, PlutusI, PlutusList, PlutusMap),
  )
import Covenant.Internal.Type
  ( AbstractTy (BoundAt),
    BuiltinFlatT (ByteStringT, IntegerT),
    CompT (CompT),
    CompTBody (CompTBody),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    TyName (TyName),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
    byteStringBaseFunctor,
    naturalBaseFunctor,
    negativeBaseFunctor,
  )
import Covenant.Type
  ( CompT (Comp0, Comp1),
    CompTBody (ReturnT, (:--:>)),
    tyvar,
  )
import Data.Bitraversable (bisequence)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe (fromJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector qualified as V
import Data.Vector.NonEmpty qualified as NEV
import Optics.Core
  ( A_Lens,
    LabelOptic (labelOptic),
    folded,
    lens,
    preview,
    review,
    toListOf,
    view,
    (%),
    _2,
  )
import Optics.Indexed.Core (A_Fold)

-- | All possible errors that could arise when constructing a Boehm-Berrarducci
-- form.
--
-- @since 1.1.0
data BBFError
  = -- | The type is recursive in a prohibited way. Typically, this means
    -- contravariant recursion. This gives the type name and the invalid
    -- recursive constructor argument.
    --
    -- @since 1.1.0
    InvalidRecursion TyName (ValT AbstractTy)
  deriving stock
    ( -- | @since 1.1.0
      Show,
      -- | @since 1.1.0
      Eq
    )

-- | Contains essential information about datatype definitions. Most of the
-- time, you want to use this type via its optics, rather than directly.
--
-- In pretty much any case imaginable, the @var@ type variable will be one of
-- 'AbstractTy' or 'Renamed'.
--
-- @since 1.1.0
data DatatypeInfo (var :: Type)
  = DatatypeInfo
  { _originalDecl :: DataDeclaration var,
    -- The second element of the tuple here is the BB form of the Base functor
    -- (this is what we actually care about most of the time)
    _baseFunctorStuff :: Maybe (DataDeclaration var, ValT var),
    -- NOTE: The ONLY type that won't have a BB form is `Void` (or something isomorphic to it)
    _bbForm :: Maybe (ValT var),
    _isBaseFunctor :: Bool
  }
  deriving stock
    ( -- | @since 1.1.0
      Eq,
      -- | @since 1.1.0
      Show
    )

-- | The original declaration of the data type.
--
-- @since 1.1.0
instance
  (k ~ A_Lens, a ~ DataDeclaration var, b ~ DataDeclaration var) =>
  LabelOptic "originalDecl" k (DatatypeInfo var) (DatatypeInfo var) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(DatatypeInfo ogDecl _ _ _) -> ogDecl)
      (\(DatatypeInfo _ b c d) ogDecl -> DatatypeInfo ogDecl b c d)

-- | The base functor for this data type, if it exists. Types which are not
-- self-recursive lack base functors.
--
-- @since 1.1.0
instance
  (k ~ A_Lens, a ~ Maybe (DataDeclaration var, ValT var), b ~ Maybe (DataDeclaration var, ValT var)) =>
  LabelOptic "baseFunctor" k (DatatypeInfo var) (DatatypeInfo var) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(DatatypeInfo _ baseF _ _) -> baseF)
      (\(DatatypeInfo a _ c d) baseF -> DatatypeInfo a baseF c d)

-- | The Boehm-Berrarducci form of this type, if it exists. Types with no
-- constructors (that is, types without inhabitants) lack Boehm-Berrarducci
-- forms.
--
-- @since 1.1.0
instance
  (k ~ A_Lens, a ~ Maybe (ValT var), b ~ Maybe (ValT var)) =>
  LabelOptic "bbForm" k (DatatypeInfo var) (DatatypeInfo var) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(DatatypeInfo _ _ bb _) -> bb)
      (\(DatatypeInfo a b _ d) bb -> DatatypeInfo a b bb d)

-- | The base functor Boehm-Berrarducci form of this type, if it exists. A type
-- must have both a base functor and a Boehm-Berrarducci form to have a base
-- functor Boehm-Berrarducci form. In other words, they must have at least one
-- constructor and be self-recursive.
--
-- @since 1.1.0
instance
  (k ~ A_Fold, a ~ ValT var, b ~ ValT var) =>
  LabelOptic "bbBaseF" k (DatatypeInfo var) (DatatypeInfo var) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = #baseFunctor % folded % _2

-- | Is this the DatatypeInfo for a base functor?
-- @since 1.3.0
instance
  (k ~ A_Lens, a ~ Bool, b ~ Bool) =>
  LabelOptic "isBaseFunctor" k (DatatypeInfo var) (DatatypeInfo var) a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic =
    lens
      (\(DatatypeInfo _ _ _ isbf) -> isbf)
      (\(DatatypeInfo a b c _) isbf -> DatatypeInfo a b c isbf)

-- | Given a declaration of a datatype, either produce its datatype info, or
--   fail.
--
--   Returns a map because it will bundle the base functor declaration for a given type
--   if a base functor can be generated.
-- @since 1.3.0
mkDatatypeInfo :: DataDeclaration AbstractTy -> Either BBFError (Map TyName (DatatypeInfo AbstractTy))
mkDatatypeInfo decl = do
  bbf <- mkBBF decl
  baseF <- baseFStuff
  case baseF of
    Nothing ->
      pure . M.singleton declTyName $ DatatypeInfo decl Nothing bbf False
    bf@(Just (baseFDecl, baseFBB)) -> do
      let baseFTyName = view #datatypeName baseFDecl
          baseFDatatypeInfo =
            M.singleton baseFTyName $
              DatatypeInfo baseFDecl Nothing (Just baseFBB) True
          parentDatatypeInfo =
            M.singleton declTyName $
              DatatypeInfo decl bf bbf False
      pure $ baseFDatatypeInfo <> parentDatatypeInfo
  where
    declTyName = view #datatypeName decl
    baseFStuff :: Either BBFError (Maybe (DataDeclaration AbstractTy, ValT AbstractTy))
    baseFStuff =
      let baseFDecl = runReader (mkBaseFunctor decl) 0
          baseBBF = case baseFDecl of
            Nothing -> Right Nothing
            Just d -> mkBBF d
       in (bisequence . (baseFDecl,) <$> baseBBF)

-- | Returns all datatype constructors used as any argument to the datatype
-- defined by the first argument.
--
-- @since 1.1.0
allComponentTypes :: DataDeclaration AbstractTy -> [ValT AbstractTy]
allComponentTypes = toListOf (#datatypeConstructors % folded % #constructorArgs % folded)

-- | Constructs a base functor from a suitable data declaration, returning
-- 'Nothing' if the input is not a recursive type.
--
-- Note that naming convention for base functors and their constructors gives "illegal" type names,
-- i.e. names that users could not choose themselves. For example, in:
-- @data List a = Nil | Cons a (List a)@
-- The type name for the generated base functor is '#List' and the constructors of the base functor are
-- '#Cons' and '#Nil'.
-- @since 1.3.0
mkBaseFunctor :: DataDeclaration AbstractTy -> Reader ScopeBoundary (Maybe (DataDeclaration AbstractTy))
mkBaseFunctor OpaqueData {} = pure Nothing
mkBaseFunctor (DataDeclaration tn numVars ctors _) = do
  anyRecComponents <- or <$> traverse (hasRecursive tn) allCtorArgs
  if null ctors || not anyRecComponents
    then pure Nothing
    else do
      baseCtors <- traverse mkBaseCtor ctors
      pure . Just $ DataDeclaration baseFName baseFNumVars baseCtors SOP
  where
    baseFName :: TyName
    baseFName = case tn of
      TyName tyNameInner -> TyName ("#" <> tyNameInner)
    baseFNumVars :: Count "tyvar"
    baseFNumVars = fromJust . preview intCount $ review intCount numVars + 1
    -- The argument position of the new type variable parameter (typically `r`).
    -- A count represents the number of variables, but indices for those variables start at 0,
    -- so an additional tyvar will always have an index == the old count
    rIndex :: Index "tyvar"
    rIndex = fromJust . preview intIndex $ review intCount numVars
    -- Replace recursive children with a DeBruijn index & position index that points at the top-level binding context
    -- (technically the top level binding context is the ONLY admissable binding context if we forbid higher-rank types,
    -- but we still have to regard a computation type that binds 0 variables as having a scope boundary)
    replaceWithR :: ValT AbstractTy -> Reader ScopeBoundary (ValT AbstractTy)
    replaceWithR vt =
      isRecursive vt >>= \case
        True -> do
          ScopeBoundary here <- ask -- this should be the distance from the initial binding context (which is what we want)
          let db = fromJust $ preview asInt here
          pure $ Abstraction (BoundAt db rIndex)
        False -> pure vt
    -- TODO: This should be refactored with `mapMValT`, which I will do after I write it :P
    replaceAllRecursive :: ValT AbstractTy -> Reader ScopeBoundary (ValT AbstractTy)
    replaceAllRecursive = \case
      abst@Abstraction {} -> pure abst
      bif@BuiltinFlat {} -> pure bif
      ThunkT (CompT cnt (CompTBody compTargs)) ->
        local (+ 1) $ ThunkT . CompT cnt . CompTBody <$> traverse replaceAllRecursive compTargs
      Datatype tx args -> (replaceWithR . Datatype tx =<< traverse replaceAllRecursive args)
    mkBaseCtor :: Constructor AbstractTy -> Reader ScopeBoundary (Constructor AbstractTy)
    mkBaseCtor (Constructor ctorNm ctorArgs) = Constructor (baseFCtorName ctorNm) <$> traverse replaceAllRecursive ctorArgs
      where
        baseFCtorName :: ConstructorName -> ConstructorName
        baseFCtorName (ConstructorName nm) = ConstructorName ("#" <> nm)
    allCtorArgs :: [ValT AbstractTy]
    allCtorArgs = concatMap (V.toList . view #constructorArgs) ctors
    -- This tells us whether the ValT *is* a recursive child of the parent type
    isRecursive :: ValT AbstractTy -> Reader ScopeBoundary Bool
    isRecursive = isRecursiveChildOf tn

-- | Returns 'True' if the second argument is a recursive child of the datatype
-- named by the first argument.
--
-- @since 1.1.0
isRecursiveChildOf :: TyName -> ValT AbstractTy -> Reader ScopeBoundary Bool
isRecursiveChildOf tn = \case
  Datatype tn' args
    | tn' == tn -> V.ifoldM checkArgsIsRec' True args
    | otherwise -> pure False
  _ -> pure False
  where
    checkArgsIsRec' :: Bool -> Int -> ValT AbstractTy -> Reader ScopeBoundary Bool
    checkArgsIsRec' acc n = \case
      Abstraction (BoundAt db varIx) -> do
        ScopeBoundary here <- ask
        let dbInt = review asInt db
        -- Explanation: A component ValT is only a recursive instance of the parent type if
        --              the DeBruijn index of its type variables points to Z (and the other conditions obtain)
        if dbInt - here == 0 && review intIndex varIx == n
          then pure acc
          else pure False
      _ -> pure False

-- | Determines whether the type represented by the second argument and named by
-- the first requires a base functor.
--
-- @since 1.1.0
hasRecursive :: TyName -> ValT AbstractTy -> Reader ScopeBoundary Bool
hasRecursive tn = \case
  Abstraction {} -> pure False
  BuiltinFlat {} -> pure False
  -- NOTE: This assumes that we've forbidden higher rank arguments to constructors (i.e. we can ignore the scope here)
  ThunkT (CompT _ (CompTBody (NEV.toList -> compTArgs))) -> local (+ 1) $ do
    or <$> traverse (hasRecursive tn) compTArgs
  dt@(Datatype _ args) -> do
    thisTypeIsRecursive <- isRecursiveChildOf tn dt
    aComponentIsRecursive <- or <$> traverse (hasRecursive tn) args
    pure $ thisTypeIsRecursive || aComponentIsRecursive

-- | Constructs a base functor Boehm-Berrarducci form for the given datatype.
-- Returns 'Nothing' if the type is not self-recursive.
--
-- @since 1.1.0
mkBBF :: DataDeclaration AbstractTy -> Either BBFError (Maybe (ValT AbstractTy))
mkBBF decl = sequence . runExceptT $ mkBBF' decl

-- | Verifies that all type variables declared by the given datatype have a
-- corresponding value in some \'arm\'.
--
-- @since 1.1.0
noPhantomTyVars :: DataDeclaration AbstractTy -> Bool
noPhantomTyVars OpaqueData {} = True
noPhantomTyVars decl@(DataDeclaration _ numVars _ _) =
  let allChildren = allComponentTypes decl
      allResolved = Set.unions $ runReader (traverse allResolvedTyVars' allChildren) 0
      indices :: [Index "tyvar"]
      indices = fromJust . preview intIndex <$> [0 .. (review intCount numVars - 1)]
      declaredTyVars = BoundAt Z <$> indices
   in all (`Set.member` allResolved) declaredTyVars

-- | Collect all (other) value types a given value type refers to.
--
-- @since 1.1.0
everythingOf :: forall (a :: Type). (Ord a) => ValT a -> Set (ValT a)
everythingOf = foldValT (flip Set.insert) Set.empty

-- Helpers

{- NOTE: For the purposes of base functor transformation, we follow the pattern established by Edward Kmett's
         'recursion-schemes' library. That is, we regard a datatype as "recursive" if and only if at least one
         argument to a constructor contains "the exact same thing as we find to the left of the =". Dunno how to
         describe it more precisely, but the general idea is that things like these ARE recursive for us:

           data Foo = End Int | More Foo Int -- contains 'Foo' as a ctor arg

           data Bar a = Beep | Boom a (Bar a) -- contains 'Bar a'

         but things like this are NOT recursive by our reckoning (even though in some sense they might be considered as such):

           data FunL a b = Done b | Go (FunL b a) a -- `FunL b a` isn't `FunL a b` so it's not literally recursive

         Obviously we're working with DeBruijn indices so the letters are more-or-less fictitious, but hopefully
         these examples nonetheless get the point across.
-}

-- TODO: Rewrite this as `mapMValT`. The change to a `Reader` below makes this unusable, but we can
--       write the non-monadic version as a special case of the monadic version and it is *highly* likely
--       we will need both going forward.
mapValT :: forall (a :: Type). (ValT a -> ValT a) -> ValT a -> ValT a
mapValT f = \case
  -- for terminal nodes we just apply the function
  absr@(Abstraction {}) -> f absr
  bif@BuiltinFlat {} -> f bif
  -- For CompT and Datatype we apply the function to the components and then to the top level
  ThunkT (CompT cnt (CompTBody compTargs)) -> f (ThunkT $ CompT cnt (CompTBody (mapValT f <$> compTargs)))
  Datatype tn args -> f $ Datatype tn (mapValT f <$> args)

-- Did in fact need it
foldValT :: forall (a :: Type) (b :: Type). (b -> ValT a -> b) -> b -> ValT a -> b
foldValT f e = \case
  absr@(Abstraction {}) -> f e absr
  bif@(BuiltinFlat {}) -> f e bif
  thk@(ThunkT (CompT _ (CompTBody compTArgs))) ->
    let e' = NEV.foldl' f e compTArgs
     in f e' thk
  dt@(Datatype _ args) ->
    let e' = V.foldl' f e args
     in f e' dt

allResolvedTyVars' :: ValT AbstractTy -> Reader Int (Set AbstractTy)
allResolvedTyVars' = \case
  Abstraction (BoundAt db argpos) -> do
    here <- ask
    let db' = fromJust . preview asInt $ review asInt db - here
    pure . Set.singleton $ BoundAt db' argpos
  ThunkT (CompT _ (CompTBody nev)) -> local (+ 1) $ do
    Set.unions <$> traverse allResolvedTyVars' nev
  BuiltinFlat {} -> pure Set.empty
  Datatype _ args -> Set.unions <$> traverse allResolvedTyVars' args

incAbstractionDB :: ValT AbstractTy -> ValT AbstractTy
incAbstractionDB = mapValT $ \case
  Abstraction (BoundAt db indx) ->
    let db' = fromJust . preview asInt $ review asInt db + 1
     in Abstraction (BoundAt db' indx)
  other -> other

-- Only returns `Nothing` if there are no Constructors or the type is Opaque
mkBBF' :: DataDeclaration AbstractTy -> ExceptT BBFError Maybe (ValT AbstractTy)
mkBBF' (OpaqueData _ ctorsSet) = do
  let bbfFunArgs = map mkOpaqueFn (Set.toList ctorsSet)
  case NEV.fromList bbfFunArgs of
    Nothing -> error "No ctors for opaque. If this happens it means we didn't run the kind checker."
    Just fn -> lift . Just . ThunkT . Comp1 . CompTBody $ NEV.snoc fn (tyvar Z ix0)
  where
    -- `r` as it appears in the thunks
    r :: ValT AbstractTy
    r = Abstraction (BoundAt (S Z) ix0)
    helper :: ValT AbstractTy -> ValT AbstractTy
    helper arg = ThunkT . Comp0 $ arg :--:> ReturnT r
    pList :: V.Vector (ValT AbstractTy) -> ValT AbstractTy
    pList = Datatype "List"
    pData :: ValT AbstractTy
    pData = Datatype "Data" mempty
    pPair :: ValT AbstractTy -> ValT AbstractTy -> ValT AbstractTy
    pPair a b = Datatype "Pair" $ V.fromList [a, b]
    mkOpaqueFn :: PlutusDataConstructor -> ValT AbstractTy
    mkOpaqueFn = \case
      PlutusI -> helper $ BuiltinFlat IntegerT
      PlutusB -> helper $ BuiltinFlat ByteStringT
      PlutusConstr ->
        ThunkT . Comp0 $
          BuiltinFlat IntegerT
            :--:> pList (V.fromList [pData])
            :--:> ReturnT r
      PlutusList -> helper (pList (V.singleton pData))
      PlutusMap -> helper (pList (V.singleton (pPair pData pData)))
mkBBF' (DataDeclaration tn numVars ctors _)
  | V.null ctors = lift Nothing
  | otherwise = do
      ctors' <- traverse mkBBCtor ctors
      lift $ ThunkT . CompT bbfCount . CompTBody . flip NEV.snoc topLevelOut <$> NEV.fromVector ctors'
  where
    topLevelOut = Abstraction $ BoundAt Z outIx

    outIx :: Index "tyvar"
    outIx = fromJust . preview intIndex $ review intCount numVars

    bbfCount = fromJust . preview intCount $ review intCount numVars + 1

    mkBBCtor :: Constructor AbstractTy -> ExceptT BBFError Maybe (ValT AbstractTy)
    mkBBCtor (Constructor _ args)
      | V.null args = pure topLevelOut
      | otherwise = do
          elimArgs <- fmap incAbstractionDB <$> traverse fixArg args
          elimArgs' <- lift . NEV.fromVector $ elimArgs
          let out = Abstraction $ BoundAt (S Z) outIx
          pure . ThunkT . CompT count0 . CompTBody . flip NEV.snoc out $ elimArgs'

    fixArg :: ValT AbstractTy -> ExceptT BBFError Maybe (ValT AbstractTy)
    fixArg arg = do
      let isDirectRecursiveTy = runReader (isRecursiveChildOf tn arg) 0
      if isDirectRecursiveTy
        then pure $ Abstraction (BoundAt Z outIx)
        else case arg of
          Datatype tn' dtArgs
            | tn == tn' -> throwError $ InvalidRecursion tn arg
            | otherwise -> do
                dtArgs' <- traverse fixArg dtArgs
                pure . Datatype tn' $ dtArgs'
          _ -> pure arg

{- Note (Sean, 14/05/25): Re  DeBruijn indices:

     - None of the existing variable DeBruijn or position indices change at all b/c the binding context of the
       `forall` we're introducing replaces the binding context of the datatype declaration and only extends it.

     - The only special thing we have to keep track of is the (DeBruijn) index of the `out` variable, but this doesn't require
       any fancy scope tracking: It will always be Z for the top-level result and `S Z` wherever it occurs in a
       transformed constructor. It won't ever occur any "deeper" than that (because we don't nest these, and a constructor gets exactly one
       `out`)

     - Actually this is slightly false, we need to "bump" all of the indices inside constructor arms by one (because
       they now occur within a Thunk), but after that bump everything is stable as indicated above.
-}

{- Primitive Base Functor Datatype Info

   This has to be here to avoid cyclic dependencies and we have to write them by hand.

   NOTE: THESE MUST BE INSERTED INTO THE DEFAULT ASGBUILDER CONTEXT WHEN IT IS CONSTRUCTED/INITIALIZED
         (it's not yet clear where the best place to do that will be)
-}

primBaseFunctorInfos :: Map TyName (DatatypeInfo AbstractTy)
primBaseFunctorInfos =
  foldr
    ( ( \x acc ->
          let tnm = view (#originalDecl % #datatypeName) x
           in M.insert tnm x acc
      )
        . unsafeMkPrimInfo
    )
    M.empty
    [naturalBaseFunctor, negativeBaseFunctor, byteStringBaseFunctor]
  where
    unsafeMkPrimInfo :: DataDeclaration AbstractTy -> DatatypeInfo AbstractTy
    unsafeMkPrimInfo decl = case mkBBF decl of
      Left err -> error $ "Error constructing BBF for primitive base functor: " <> show err
      Right bbf -> DatatypeInfo decl Nothing bbf True
