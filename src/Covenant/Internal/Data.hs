{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE ViewPatterns #-}
module Covenant.Internal.Data (mkBaseFunctor) where


import Data.Text (Text)
import Covenant.Type
import Covenant.DeBruijn
import Data.Vector (Vector)
import Data.Vector qualified as V
import Data.Vector.NonEmpty qualified as NEV
import Data.String (IsString)
import Covenant.Index (Count, intCount, intIndex)
import Data.Coerce (coerce)
import Optics.Core ( preview, review )
import Control.Monad.Reader
import Data.Word (Word32)
import Covenant.Index (Index)
import Data.Maybe (fromJust)
import Optics.Core hiding (Index)
import Covenant.Internal.Type
import Data.Kind
import Control.Monad.Reader


-- To replicate some functionality that we'd normally have in a Plated instances
mapValT :: forall (a :: Type). (ValT a -> ValT a) -> ValT a -> ValT a
mapValT f = \case
  -- for terminal nodes we just apply the function
  abs@(Abstraction{}) -> f abs
  bif@BuiltinFlat{} -> f bif
  -- For CompT and Datatype we apply the function to the components and then to the top level
  ThunkT (CompT cnt (CompTBody compTargs)) -> f (ThunkT $ CompT cnt (CompTBody (f <$> compTargs)))
  Datatype tn args -> f $ Datatype tn (mapValT f <$> args)


mkBaseFunctor :: DataDeclaration AbstractTy -> Maybe (DataDeclaration AbstractTy)
mkBaseFunctor (DataDeclaration tn numVars ctors)
  -- If it doesn't have any constructors or if none of of the arguments to any constructor is recursive then we don't need to generate anything
  | null ctors ||  not (any hasRecursive allCtorArgs) = Nothing
  | otherwise = Just $ DataDeclaration baseFName baseFNumVars (mkBaseCtor <$> ctors)
 where
   baseFName = case tn of
     TyName tyNameInner -> TyName (tyNameInner <> "_F")

   baseFNumVars = fromJust . preview intCount $ review  intCount numVars + 1

   rIndex :: Index "tyvar"
   rIndex = fromJust . preview intIndex $ review intCount numVars 

   r = Abstraction (BoundAt Z rIndex)

   replaceWithR :: ValT AbstractTy -> ValT AbstractTy
   replaceWithR vt
     | isRecursive vt = r
     | otherwise = vt

   mkBaseCtor :: Constructor AbstractTy -> Constructor AbstractTy
   mkBaseCtor (Constructor ctorNm ctorArgs) = Constructor (baseFCtorName ctorNm) (mapValT replaceWithR <$> ctorArgs)
     where
       baseFCtorName :: ConstructorName -> ConstructorName
       baseFCtorName (ConstructorName nm) = ConstructorName (nm <> "_F")

   allCtorArgs :: [ValT AbstractTy]
   allCtorArgs = concatMap (V.toList . view constructorArgs) ctors

   -- This tells us whether the ValT is a *direct* recursive type
   isRecursive :: ValT AbstractTy -> Bool
   isRecursive = \case
     Datatype tn' args
       | tn' == tn -> checkArgsIsRec 0 (V.toList args)
       | otherwise -> False
     _ -> False

   checkArgsIsRec :: Int -> [ValT AbstractTy] -> Bool
   checkArgsIsRec n [] = True
   checkArgsIsRec n (x:xs) = case x of
     Abstraction (BoundAt Z varIx) -> review intIndex varIx == n && checkArgsIsRec (n + 1) xs
     _ -> False

   -- This tells us whether a ValT *contains* a direct recursive type
   hasRecursive :: ValT AbstractTy -> Bool
   hasRecursive = \case
     Abstraction{} -> False
     BuiltinFlat{} -> False
     -- NOTE: This assumes that we've forbidden higher rank arguments to constructors (i.e. we can ignore the scope here)
     ThunkT (CompT _ (CompTBody (NEV.toList -> compTArgs))) -> any hasRecursive compTArgs
     dt@(Datatype _ args) -> isRecursive dt || any hasRecursive args


