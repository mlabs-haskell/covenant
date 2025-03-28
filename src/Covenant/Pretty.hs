{-# LANGUAGE ViewPatterns #-}
module Covenant.Pretty where

import Prettyprinter

import Covenant.Type
import Covenant.Index
import Covenant.DeBruijn

import Optics.Prism
import Optics.Review
import Optics.Lens

import Data.Vector.NonEmpty (NonEmptyVector)
import Data.Vector.NonEmpty qualified as NEV

import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NEL

import Control.Monad.Reader

import Data.Map (Map)
import Data.Map qualified as M
import Optics.Setter (over)
import Optics.Getter (view)
import Optics.Core (preview, (%))
import Optics.At (Ixed(ix))
import Optics.Setter (set)

newtype ScopeBoundary = ScopeBoundary {getBoundary :: Int}
  deriving newtype (Show, Eq, Ord, Num, Enum)

data PrettyContext
  = PrettyContext {
      pcBoundIdents :: Map ScopeBoundary [Doc ()]
    , pcCurrentScope :: ScopeBoundary
    , pcVarStream :: [Doc ()]
    }

infiniteVars :: [Doc ()]
infiniteVars = let aToZ = ['a'..'z']
                   intStrings = ("" <$ aToZ) <> map show [0..]
               in zipWith (\x xs -> pretty (x:xs)) aToZ intStrings

boundIdents :: Lens' PrettyContext (Map ScopeBoundary [Doc ()])
boundIdents = lens goGet goSet
  where
    goGet (PrettyContext bi _ _) = bi
    goSet (PrettyContext _ scop vars) bi' = PrettyContext bi' scop vars

currentScope :: Lens' PrettyContext ScopeBoundary
currentScope = lens goGet goSet
  where
    goGet (PrettyContext _ scop _) = scop
    goSet (PrettyContext bi _ vars) scop  = PrettyContext bi scop vars

varStream :: Lens' PrettyContext [Doc ()]
varStream = lens goGet goSet
  where
    goGet (PrettyContext _ _ vars) = vars
    goSet (PrettyContext bi scop _) = PrettyContext bi scop

withFreshVarNames :: Int -> ([Doc ()] -> PrettyM a) -> PrettyM a
withFreshVarNames n act = do
  stream <- asks (view varStream)
  let (used,rest) = splitAt n stream
  local (set varStream rest) $ act used

-- Maybe make a newtype with error reporting since this can fail, but do later since *should't* fail
type PrettyM a = Reader PrettyContext a

runPrettyM :: PrettyM a -> a
runPrettyM ma = runReader ma (PrettyContext mempty 0 infiniteVars)

crossBoundary :: PrettyM a -> PrettyM a
crossBoundary = local (over currentScope (+ 1))

-- REVIEW @Koz: You said we always consider a boundary crossed even if the count is zero,
--              but when I do that it blows up lists? I think I have to be misunderstanding something
bindVars :: Count "tyvar" -> ([Doc ()] -> PrettyM a) -> PrettyM a
bindVars count' act
  | count == 0 = crossBoundary (act [])
  | otherwise = crossBoundary $ do
      here <- asks (view currentScope)
      withFreshVarNames count $ \newBoundVars ->
        local (over boundIdents (M.insert here newBoundVars)) (act newBoundVars)
 where
   count = review intCount count'

lookupRigid :: Int -> Index "tyvar" -> PrettyM (Doc ())
lookupRigid (ScopeBoundary -> scopeOffset) argIndex = do
  let argIndex' = review intIndex argIndex
  here <- asks (view currentScope)
  asks (preview (boundIdents % ix (here + scopeOffset) % ix argIndex')) >>= \case
    Nothing -> -- TODO: actual error reporting
               error $ "Internal error: The encountered a variable at arg index "
                       <> show argIndex'
                       <> " with true level "
                       <> show scopeOffset
                       <> " but could not locate the corresponding pretty form at scope level " <> show here
    Just res' -> pure res'

class PrettyWithContext a where
  prettyWithContext :: a -> PrettyM (Doc ())

instance PrettyWithContext Renamed where
  prettyWithContext = \case
    Rigid offset index -> lookupRigid offset index
    Unifiable i -> lookupRigid 0 i -- ok maybe 'lookupRigid' isn't the best name
    Wildcard w64 i -> pure $ "_" <> viaShow w64 <> "#" <> pretty (review intIndex i)

instance PrettyWithContext (CompT Renamed) where
  prettyWithContext (CompT count funArgs)
    | review intCount count == 0 = prettyFunTy (NEV.toNonEmpty funArgs )
    | otherwise =  bindVars count $ \newVars -> do
        funTy <- prettyFunTy (NEV.toNonEmpty funArgs) -- easier to pattern match
        pure $ mkForall newVars funTy

mkForall :: [Doc ()] -> Doc () ->  Doc ()
mkForall tvars funTyBody = case tvars of
  [] -> funTyBody
  vars -> "forall" <+> hsep vars <> "." <+> funTyBody 

prettyFunTy :: NonEmpty (ValT Renamed) -> PrettyM (Doc ())
prettyFunTy (arg :| rest) = case rest of
  [] -> ("!" <>) <$>  prettyArg arg
  (a:as) -> (\a b -> a <+> "->" <+> b) <$> prettyArg arg <*> prettyFunTy (a :| as)
 where
   prettyArg :: ValT Renamed -> PrettyM (Doc ())
   prettyArg vt | isSimpleValT vt = prettyWithContext vt
                | otherwise = parens <$> prettyWithContext vt

-- I.e. can we omit parens and get something unambiguous? This might be overly aggressive w/ parens but that's OK
isSimpleValT :: forall a. ValT a -> Bool
isSimpleValT = \case
   Abstraction _ -> True
   BuiltinFlat _ -> True
   -- We want to avoid duplicating parens when we *know* they're superfluous, and we know they're superfluous
   -- if we're dealing w/ an abstraction, a "one argument thunk" (@Koz are those legitimate?), a BuiltinFlat, or a
   -- BuiltinNested that either NOT a list or is a list with a count == 0 (bleh)
   BuiltinNested nested -> isSimpleNested nested
   ThunkT thunk -> isSimpleCompT thunk
  where
    isSimpleCompT :: forall a. CompT a -> Bool
    isSimpleCompT (CompT count args) = review intCount count == 0 && NEV.length args == 1

    isSimpleNested :: forall a. BuiltinNestedT a -> Bool
    isSimpleNested = \case
      ListT count _ -> review intCount count == 0
      _ -> True

instance PrettyWithContext (ValT Renamed) where
  prettyWithContext = \case
    Abstraction abstr -> prettyWithContext abstr
    ThunkT compT -> prettyWithContext compT
    BuiltinFlat biFlat -> pure $ viaShow biFlat
    BuiltinNested biNested -> case biNested of
      PairT vt1 vt2 -> tupled <$> traverse prettyWithContext [vt1,vt2]
      ListT count listArg
        | review intCount count == 0 -> brackets <$> prettyWithContext listArg
        | otherwise -> bindVars count $ \vars -> do
          pListArg <- prettyWithContext listArg
          pure . brackets $ mkForall vars pListArg

-- "Tests" (i.e. things for me to look at in the repl)
tests :: [CompT Renamed]
tests = [idFun,constFun,headListFun,sndPairFun,mapFun]

idFun :: CompT Renamed
idFun = CompT count1 $
          Abstraction (Unifiable ix0)
            :--:> ReturnT (Abstraction (Unifiable ix0))

constFun :: CompT Renamed
constFun = CompT count2 $
          Abstraction (Unifiable ix0)
            :--:> Abstraction (Unifiable ix1)
            :--:> ReturnT (Abstraction (Unifiable ix0))


headListFun :: CompT Renamed
headListFun = CompT count1 $
          BuiltinNested (ListT count0 (Abstraction (Unifiable ix0)))
            :--:> ReturnT (Abstraction (Unifiable ix0))

sndPairFun :: CompT Renamed
sndPairFun = CompT count2 $
          BuiltinNested (PairT (Abstraction (Unifiable ix0)) (Abstraction (Unifiable ix1)))
            :--:> ReturnT (Abstraction (Unifiable ix1))

mapFun :: CompT Renamed
mapFun = CompT count2 $
          (ThunkT . CompT count0 $ Abstraction (Unifiable ix0) :--:> ReturnT (Abstraction (Unifiable ix1)))
            :--:> BuiltinNested (ListT count0 (Abstraction (Unifiable ix0)))
            :--:> ReturnT (BuiltinNested (ListT count0 (Abstraction (Unifiable ix1))))

