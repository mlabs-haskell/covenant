{-# LANGUAGE ViewPatterns #-}
module Covenant.Internal.Data (mkBaseFunctor, isRecursiveChildOf, allComponentTypes, hasRecursive ) where

import Covenant.DeBruijn ( asInt, unsafeDeBruijn )
import Data.Vector qualified as V
import Data.Vector.NonEmpty qualified as NEV
import Covenant.Index ( Count, intCount, intIndex, Index )
import Data.Maybe (fromJust)
import Optics.Core ( (%), preview, folded, toListOf, view, review )
import Covenant.Internal.Type
    ( ValT(Abstraction,BuiltinFlat,ThunkT,Datatype),
      AbstractTy(BoundAt),
      CompT(CompT),
      CompTBody(CompTBody),
      TyName(TyName),
      DataDeclaration(DataDeclaration),
      ScopeBoundary(ScopeBoundary),
      Constructor(Constructor),
      ConstructorName(ConstructorName),
      constructorArgs,
      datatypeConstructors )
import Data.Kind ( Type )
import Control.Monad.Reader ( Reader, MonadReader(local, ask) )

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
_mapValT :: forall (a :: Type). (ValT a -> ValT a) -> ValT a -> ValT a
_mapValT f = \case
  -- for terminal nodes we just apply the function
  absr@(Abstraction{}) -> f absr
  bif@BuiltinFlat{} -> f bif
  -- For CompT and Datatype we apply the function to the components and then to the top level
  ThunkT (CompT cnt (CompTBody compTargs)) -> f (ThunkT $ CompT cnt (CompTBody (f <$> compTargs)))
  Datatype tn args -> f $ Datatype tn (_mapValT f <$> args)


-- This tells us whether the ValT *is* a recursive child of the parent type
isRecursiveChildOf :: TyName -> ValT AbstractTy -> Reader ScopeBoundary Bool
isRecursiveChildOf tn = \case
     Datatype tn' args
       | tn' == tn -> checkArgsIsRec 0 (V.toList args)
       | otherwise -> pure False
     _ -> pure False
  where
   -- Checks that the arguments to a datatype (which we expect will be checked to have the same tycon as the parent type)
   -- have the correct DeBruijn index & the same order as in the initial binding context of the declaration.
   -- Has to be monadic because need access to the current scope level.
  checkArgsIsRec :: Int -> [ValT AbstractTy] -> Reader ScopeBoundary Bool
  checkArgsIsRec _ [] = pure True
  checkArgsIsRec n (x:xs) = case x of
     Abstraction (BoundAt db varIx) -> do
       ScopeBoundary here <- ask
       let dbInt = asInt db
       -- Explanation: A component ValT is only a recursive instance of the parent type if
       --              the DeBruijn index of its type variables points to Z (and the other conditions obtain)
       if dbInt - here == 0 && review intIndex varIx == n
         then checkArgsIsRec (n + 1) xs
         else pure False
     _ -> pure False

allComponentTypes :: DataDeclaration AbstractTy -> [ValT AbstractTy]
allComponentTypes  = toListOf (datatypeConstructors % folded % constructorArgs % folded)

-- This tells us whether a ValT *contains* a direct recursive type. I.e it tells us whether we need to construct a base functor
hasRecursive :: TyName -> ValT AbstractTy -> Reader ScopeBoundary Bool
hasRecursive tn = \case
     Abstraction{} -> pure False
     BuiltinFlat{} -> pure False
     -- NOTE: This assumes that we've forbidden higher rank arguments to constructors (i.e. we can ignore the scope here)
     ThunkT (CompT _ (CompTBody (NEV.toList -> compTArgs))) -> local (+ 1) $ do
       or <$> traverse (hasRecursive tn) compTArgs
     dt@(Datatype _ args) -> do
       thisTypeIsRecursive <- isRecursiveChildOf tn  dt
       aComponentIsRecursive <- or <$> traverse (hasRecursive tn) args
       pure $ thisTypeIsRecursive || aComponentIsRecursive

-- Yeah yeah I could use ReaderT but this is less awkward imo, we only care about the "maybe" at the top level when detecting recursion
mkBaseFunctor :: DataDeclaration AbstractTy -> Reader ScopeBoundary (Maybe (DataDeclaration AbstractTy))
mkBaseFunctor (DataDeclaration tn numVars ctors) = do
  anyRecComponents <- or <$> traverse (hasRecursive tn) allCtorArgs
  if null ctors || not anyRecComponents
    then pure Nothing
    else do
      baseCtors <- traverse mkBaseCtor ctors
      pure .  Just $ DataDeclaration baseFName baseFNumVars baseCtors
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
   replaceWithR vt = isRecursive vt >>= \case
     True -> do
       ScopeBoundary here <- ask -- this should be the distance from the initial binding context (which is what we want)
       let db = unsafeDeBruijn here
       pure $ Abstraction (BoundAt db rIndex)
     False -> pure vt

   -- TODO: This should be refactored with `mapMValT`, which I will do after I write it :P
   replaceAllRecursive :: ValT AbstractTy -> Reader ScopeBoundary (ValT AbstractTy)
   replaceAllRecursive = \case
         abst@Abstraction{} -> pure abst
         bif@BuiltinFlat{} -> pure bif
         ThunkT (CompT cnt (CompTBody compTargs)) ->
           local (+ 1) $ ThunkT . CompT cnt . CompTBody <$> traverse replaceAllRecursive compTargs
         Datatype tx args -> (replaceWithR . Datatype tx =<< traverse replaceAllRecursive args)

   mkBaseCtor :: Constructor AbstractTy -> Reader ScopeBoundary (Constructor AbstractTy)
   mkBaseCtor (Constructor ctorNm ctorArgs) = Constructor (baseFCtorName ctorNm) <$> traverse replaceAllRecursive ctorArgs
     where
       baseFCtorName :: ConstructorName -> ConstructorName
       baseFCtorName (ConstructorName nm) = ConstructorName (nm <> "_F")

   allCtorArgs :: [ValT AbstractTy]
   allCtorArgs = concatMap (V.toList . view constructorArgs) ctors 

   -- This tells us whether the ValT *is* a recursive child of the parent type
   isRecursive :: ValT AbstractTy -> Reader ScopeBoundary Bool
   isRecursive = isRecursiveChildOf tn
