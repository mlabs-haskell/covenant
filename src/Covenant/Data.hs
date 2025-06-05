{-# LANGUAGE ViewPatterns #-}

module Covenant.Data (mkBaseFunctor,
                      isRecursiveChildOf,
                      allComponentTypes,
                      hasRecursive,
                      mkBBF,
                      noPhantomTyVars,
                      everythingOf,
                      DatatypeInfo(DatatypeInfo),
                      ) where

import Control.Monad.Reader (MonadReader (ask, local), Reader, runReader)
import Covenant.DeBruijn (DeBruijn (S, Z), asInt)
import Covenant.Index (Count, Index, count0, intCount, intIndex)
import Covenant.Internal.Type
  ( AbstractTy (BoundAt),
    CompT (CompT),
    CompTBody (CompTBody),
    Constructor (Constructor),
    ConstructorName (ConstructorName),
    DataDeclaration (DataDeclaration, OpaqueData),
    ScopeBoundary (ScopeBoundary),
    TyName (TyName),
    ValT (Abstraction, BuiltinFlat, Datatype, ThunkT),
  )
import Data.Kind (Type)
import Data.Maybe (fromJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Vector qualified as V
import Data.Vector.NonEmpty qualified as NEV
import Optics.Core (folded, preview, review, toListOf, view, (%), A_Lens, LabelOptic (labelOptic), lens)

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

everythingOf :: forall (a :: Type). (Ord a) => ValT a -> Set (ValT a)
everythingOf = foldValT (flip Set.insert) Set.empty

noPhantomTyVars :: DataDeclaration AbstractTy -> Bool
noPhantomTyVars OpaqueData {} = True
noPhantomTyVars decl@(DataDeclaration _ numVars _ _) =
  let allChildren = allComponentTypes decl
      allResolved = Set.unions $ runReader (traverse allResolvedTyVars' allChildren) 0
      indices :: [Index "tyvar"]
      indices = fromJust . preview intIndex <$> [0 .. (review intCount numVars - 1)]
      declaredTyVars = BoundAt Z <$> indices
   in all (`Set.member` allResolved) declaredTyVars

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

-- This tells us whether the ValT *is* a recursive child of the parent type
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

allComponentTypes :: DataDeclaration AbstractTy -> [ValT AbstractTy]
allComponentTypes = toListOf (#datatypeConstructors % folded % #constructorArgs % folded)

-- This tells us whether a ValT *contains* a direct recursive type. I.e it tells us whether we need to construct a base functor
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

-- | Constructs a base functor from a suitable data declaration, returning 'Nothing' if the input is not a recursive type
mkBaseFunctor :: DataDeclaration AbstractTy -> Reader ScopeBoundary (Maybe (DataDeclaration AbstractTy))
mkBaseFunctor OpaqueData {} = pure Nothing
mkBaseFunctor (DataDeclaration tn numVars ctors strat) = do
  anyRecComponents <- or <$> traverse (hasRecursive tn) allCtorArgs
  if null ctors || not anyRecComponents
    then pure Nothing
    else do
      baseCtors <- traverse mkBaseCtor ctors
      pure . Just $ DataDeclaration baseFName baseFNumVars baseCtors strat
  where
    -- TODO: I think we were going to make this "illegal" so users can't use it directly but I forget the legality rules
    baseFName = case tn of
      TyName tyNameInner -> TyName (tyNameInner <> "_F")

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
        baseFCtorName (ConstructorName nm) = ConstructorName (nm <> "_F")

    allCtorArgs :: [ValT AbstractTy]
    allCtorArgs = concatMap (V.toList . view #constructorArgs) ctors

    -- This tells us whether the ValT *is* a recursive child of the parent type
    isRecursive :: ValT AbstractTy -> Reader ScopeBoundary Bool
    isRecursive = isRecursiveChildOf tn

-- data Maybe a = Just a | Nothing ~> forall out. (a -> out) -> out -> out

-- Only returns `Nothing` if there are no Constructors
mkBBF :: DataDeclaration AbstractTy -> Maybe (ValT AbstractTy)
mkBBF OpaqueData {} = Nothing
mkBBF (DataDeclaration _ numVars ctors _)
  | V.null ctors = Nothing
  | otherwise = ThunkT . CompT bbfCount . CompTBody . flip NEV.snoc topLevelOut <$> (NEV.fromVector =<< traverse mkEliminator ctors)
  where
    mkEliminator :: Constructor AbstractTy -> Maybe (ValT AbstractTy)
    mkEliminator (Constructor _ (fmap incAbstractionDB -> args))
      | V.null args = Just topLevelOut
      | otherwise =
          let out = Abstraction $ BoundAt (S Z) outIx
           in ThunkT . CompT count0 . CompTBody . flip NEV.snoc out <$> NEV.fromVector args

    incAbstractionDB :: ValT AbstractTy -> ValT AbstractTy
    incAbstractionDB = mapValT $ \case
      Abstraction (BoundAt db indx) ->
        let db' = fromJust . preview asInt $ review asInt db + 1
         in Abstraction (BoundAt db' indx)
      other -> other

    topLevelOut = Abstraction $ BoundAt Z outIx

    -- We have to add a type parameter for the result.
    bbfCount = fromJust . preview intCount $ review intCount numVars + 1

    -- The index of the 'out' parameter, indicates the return type
    outIx :: Index "tyvar"
    outIx = fromJust . preview intIndex $ review intCount numVars

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


{- Here for lack of a better place to put it (has to be available to Unification and ASG)
-}

-- | Packages up all of the relevation datatype information needed
-- for the ASGBuilder. Note that only certain datatypes have a BB or BB/BF form
-- (we do not generate forms that are "useless")
data DatatypeInfo =
  DatatypeInfo
    { _originalDecl :: DataDeclaration AbstractTy
    , _baseFunctor :: Maybe (DataDeclaration AbstractTy)
    , _bbForm :: Maybe (ValT AbstractTy)
    , _bbBaseF :: Maybe (ValT AbstractTy)}
    deriving stock
    ( -- | @since 1.1.0
     Eq,
      -- | @since 1.1.0
     Show
    )

instance (k ~ A_Lens, a ~ DataDeclaration AbstractTy, b ~ DataDeclaration AbstractTy) =>
  LabelOptic "originalDecl" k DatatypeInfo DatatypeInfo a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(DatatypeInfo ogDecl _ _ _) -> ogDecl)
                    (\(DatatypeInfo _ b c d) ogDecl -> DatatypeInfo ogDecl b c d)

instance (k ~ A_Lens, a ~ Maybe (DataDeclaration AbstractTy), b ~ Maybe (DataDeclaration AbstractTy)) =>
  LabelOptic "baseFunctor" k DatatypeInfo DatatypeInfo a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(DatatypeInfo _ baseF _ _) -> baseF)
                    (\(DatatypeInfo a _ c d) baseF -> DatatypeInfo a baseF c d)

instance (k ~ A_Lens, a ~ Maybe (ValT AbstractTy), b ~ Maybe (ValT AbstractTy)) =>
  LabelOptic "bbForm" k DatatypeInfo DatatypeInfo a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(DatatypeInfo _ _ bb _) -> bb)
                    (\(DatatypeInfo a b _ d) bb -> DatatypeInfo a b bb d)

instance (k ~ A_Lens, a ~ Maybe (ValT AbstractTy), b ~ Maybe (ValT AbstractTy)) =>
  LabelOptic "bbBaseF" k DatatypeInfo DatatypeInfo a b
  where
  {-# INLINEABLE labelOptic #-}
  labelOptic = lens (\(DatatypeInfo _ _ _ bbf) -> bbf)
                    (\(DatatypeInfo a b c _) bbf -> DatatypeInfo a b c bbf)
