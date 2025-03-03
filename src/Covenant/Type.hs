module Covenant.Type
  ( AbstractTy (..),
    Renamed (..),
    CompT (..),
    ValT (..),
    BuiltinFlatT (..),
    BuiltinNestedT (..),
    renameValT,
    renameCompT,
    RenameM,
    runRenameM,
  )
where

import Control.Monad.Reader (ask, local)
import Control.Monad.State.Strict (gets, modify)
import Control.Monad.Trans.RWS.CPS (RWS, runRWS)
import Data.Bimap (Bimap)
import Data.Bimap qualified as Bimap
import Data.Functor.Classes (Eq1 (liftEq))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.Word (Word64, Word8)

data AbstractTy = ForallAA | BoundAtScope Word8 Word8
  deriving stock (Eq, Show)

data Renamed = CanSet Word8 | Can'tSet Word64
  deriving stock (Eq, Ord, Show)

data CompT (a :: Type) = CompT Word8 (NonEmpty (ValT a))
  deriving stock (Eq, Show)

instance Eq1 CompT where
  {-# INLINEABLE liftEq #-}
  liftEq f (CompT abses1 xs) (CompT abses2 ys) =
    abses1 == abses2 && liftEq (liftEq f) xs ys

data ValT (a :: Type)
  = Abstraction a
  | ThunkT (CompT a)
  | BuiltinFlat BuiltinFlatT
  | BuiltinNested (BuiltinNestedT a)
  deriving stock (Eq, Show)

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
    BuiltinNested t1 -> \case
      BuiltinNested t2 -> liftEq f t1 t2
      _ -> False

data BuiltinFlatT
  = UnitT
  | BoolT
  | IntegerT
  | StringT
  | ByteStringT
  | BLS12_381_G1_ElementT
  | BLS12_381_G2_ElementT
  | BLS12_381_MlResultT
  | DataT
  deriving stock (Eq, Show)

data BuiltinNestedT (a :: Type)
  = ListT Word8 (ValT a)
  | PairT Word8 (ValT a) (ValT a)
  deriving stock (Eq, Show)

instance Eq1 BuiltinNestedT where
  {-# INLINEABLE liftEq #-}
  liftEq f = \case
    ListT abses1 t1 -> \case
      ListT abses2 t2 -> abses1 == abses2 && liftEq f t1 t2
      _ -> False
    PairT abses1 t11 t12 -> \case
      PairT abses2 t21 t22 -> abses1 == abses2 && liftEq f t11 t21 && liftEq f t12 t22
      _ -> False

newtype RenameM (a :: Type) = RenameM (RWS Int () (Word64, Bimap (Int, Word8) Word64) a)
  deriving (Functor, Applicative, Monad) via (RWS Int () (Word64, Bimap (Int, Word8) Word64))

stepDown :: forall (a :: Type). RenameM a -> RenameM a
stepDown (RenameM comp) = RenameM (local (+ 1) comp)

renameAbstraction :: AbstractTy -> RenameM Renamed
renameAbstraction absTy = RenameM $ do
  currLevel <- ask
  case absTy of
    ForallAA ->
      if currLevel == 0
        then pure . CanSet $ 0
        else do
          renaming <- Can'tSet <$> gets fst
          -- We bump the source of fresh names, but don't record an entry for
          -- this; all such entries are completely unique, but on restoring
          -- original names, will be the same.
          modify $ \(source, tracker) -> (source + 1, tracker)
          pure renaming
    -- We need to determine the true level to see if:
    --
    -- 1. We can set this at all (aka, whether it's unfixed and touchable); and
    -- 2. Whether we've seen this before.
    BoundAtScope scope ix -> do
      let trueLevel = currLevel - fromIntegral scope
      if trueLevel == 0
        then pure . CanSet $ ix
        else do
          -- Check if this is something we already renamed previously, and if
          -- so, rename consistently.
          priorRename <- gets (Bimap.lookup (trueLevel, ix) . snd)
          case priorRename of
            Nothing -> do
              renaming <- gets fst
              modify $ \(source, tracker) -> (source + 1, Bimap.insert (trueLevel, ix) renaming tracker)
              pure . Can'tSet $ renaming
            Just renameIx -> pure . Can'tSet $ renameIx

runRenameM ::
  forall (a :: Type).
  RenameM a -> (Bimap (Int, Word8) Word64, a)
runRenameM (RenameM comp) = case runRWS comp 0 (0, Bimap.empty) of
  (res, (_, tracker), ()) -> (tracker, res)

renameValT :: ValT AbstractTy -> RenameM (ValT Renamed)
renameValT = \case
  Abstraction absTy -> Abstraction <$> renameAbstraction absTy
  -- We're crossing a type abstraction boundary, so bump the level
  ThunkT t -> ThunkT <$> renameCompT t
  BuiltinFlat t -> pure . BuiltinFlat $ t
  BuiltinNested t ->
    BuiltinNested <$> case t of
      -- We're crossing a type abstraction boundary, so bump the level
      ListT abses t' -> ListT abses <$> stepDown (renameValT t')
      PairT abses t1 t2 ->
        PairT abses
          <$> stepDown (renameValT t1)
          <*> stepDown (renameValT t2)

renameCompT :: CompT AbstractTy -> RenameM (CompT Renamed)
renameCompT (CompT abses xs) = CompT abses <$> stepDown (traverse renameValT xs)

{-
data TypeApplyError
  = ExcessArgs [ValT]
  | InsufficientArgs (NonEmpty ValT)
  | IrrelevantTyVar Word8
  | CouldNotUnify ValT ValT

applyArgs :: CompT -> [ValT] -> Either TypeApplyError ValT
applyArgs (CompT comp) args = fmap fst . evalRWST (go comp args) 0 $ Map.empty
  where
    go :: NonEmpty ValT -> [ValT] -> RWST Word8 () (Map Word8 ValT) (Either TypeApplyError) ValT
    go = \case
      res :| [] -> \case
        [] -> resolveResult res
        args' -> throwError . ExcessArgs $ args'
      required@(curr :| (rest : rests)) -> \case
        [] -> throwError . InsufficientArgs $ required
        arg : args' -> unify curr arg >> go (rest :| rests) args'

resolveResult :: ValT -> RWST Word8 () (Map Word8 ValT) (Either TypeApplyError) ValT
resolveResult = \case
  absT@(AbsT scope ix) -> do
    level <- ask
    if scope == level
      then
        gets (Map.lookup ix) >>= \case
          Nothing -> throwError . IrrelevantTyVar $ ix
          Just t -> pure t
      else pure absT -- Not ours, so nothing we can really do here
  ThunkT (CompT comp) -> ThunkT . CompT <$> local (+ 1) (traverse resolveResult comp)
  BuiltinFlat t -> pure $ BuiltinFlat t -- nothing to resolve, we're concrete
  BuiltinNested t ->
    local
      (+ 1)
      ( BuiltinNested <$> case t of
          ListT t' -> ListT <$> local (+ 1) (resolveResult t')
          PairT t1 t2 -> PairT <$> local (+ 1) (resolveResult t1) <*> local (+ 1) (resolveResult t2)
      )

unify :: ValT -> ValT -> RWST Word8 () (Map Word8 ValT) (Either TypeApplyError) ()
unify lhs rhs = case lhs of
  BuiltinFlat t1 -> case rhs of
    BuiltinFlat t2 -> unless (t1 == t2) failToUnify
    AbsT scope ix -> do
      level <- ask
      if scope == level
        then
          gets (Map.lookup ix) >>= \case
            -- We've never seen this tyvar before, and it's our choice
            -- Set it to match lhs and move on
            -- We can do this safely without cycle-checking because we couldn't
            -- possibly break anything with such an assignment
            Nothing -> modify (Map.insert ix lhs)
            Just t -> unify lhs t
        else failToUnify
    _ -> throwError . CouldNotUnify lhs $ rhs
  ThunkT compT1 -> case rhs of
    ThunkT compT2 -> _
    AbsT scope ix -> _
    _ -> failToUnify
  BuiltinNested t1 -> case rhs of
    BuiltinNested t2 -> case t1 of
      ListT t1' -> local (+ 1) $ case t2 of
        ListT t2' -> local (+ 1) $ unify t1' t2'
        _ -> failToUnify
      PairT t11 t12 -> local (+ 1) $ case t2 of
        PairT t21 t22 -> local (+ 1) (unify t11 t21) >> local (+ 1) (unify t21 t22)
        _ -> failToUnify
    AbsT scope ix -> _
    _ -> failToUnify
  AbsT scope1 ix1 ->
    asks (compare scope1) >>= \case
      -- This tyvar is abstract in a way we don't control. Thus, it matches only
      -- itself.
      LT -> case rhs of
        AbsT scope2 ix2 -> unless (scope1 == scope2 && ix1 == ix2) failToUnify
        _ -> failToUnify
      -- This tyvar is a reference to one of our abstractions.
      EQ ->
        gets (Map.lookup ix1) >>= \case
          -- We've never seen this tyvar before and it's our choice.
          -- Becasue rhs could be anything, we have to tread carefully to avoid
          -- accidentally forming a cycle (meaning, failing an occurs check).
          Nothing -> _
          -- We've seen (and defined) this before, so just try unifying with it
          -- instead.
          Just t -> unify t rhs
      -- This tyvar is 'pinned' by someone above our scope. Thus, it
      -- matches only itself.
      GT -> case rhs of
        AbsT scope2 ix2 -> unless (scope1 == scope2 && ix1 == ix2) failToUnify
        _ -> failToUnify
  where
    failToUnify :: RWST Word8 () (Map Word8 ValT) (Either TypeApplyError) ()
    failToUnify = throwError . CouldNotUnify lhs $ rhs

-- Helpers

-- forall a b . (a -> !b) -> [a] -> ![b]
mapT :: CompT
mapT = CompT $ fType :| [xsType, resultType]
  where
    fType :: ValT
    fType = ThunkT (CompT $ AbsT 1 0 :| [AbsT 1 1]) -- One scope above for both, first var, then second var
    xsType :: ValT
    xsType = BuiltinNested . ListT $ AbsT 2 0 -- Two scopes above, first var
    resultType :: ValT
    resultType = BuiltinNested . ListT $ AbsT 2 1 -- Two scopes above, second var

-- forall a b . a -> b -> !a
const2T :: CompT
const2T = CompT $ AbsT 0 0 :| [AbsT 0 1, AbsT 0 0]

-- forall a . a -> !(forall b . b -> !a)
const1T :: CompT
const1T = CompT $ AbsT 0 0 :| [ThunkT . CompT $ AbsT 0 0 :| [AbsT 1 0]]

-- forall a . [a]
faListOuter :: ValT
faListOuter = BuiltinNested . ListT $ AbsT 1 0 -- 1 scope out, first variable

-- [forall a . a]
faListInner :: ValT
faListInner = BuiltinNested . ListT $ AbsT 0 0 -- our scope, first variable

-- forall a b . (a, b)
pairOuter :: ValT
pairOuter = BuiltinNested . PairT (AbsT 1 0) $ AbsT 1 1

-- forall a . (a, forall b . b)
pairRInner :: ValT
pairRInner = BuiltinNested . PairT (AbsT 1 0) $ AbsT 0 0

-- forall b . (forall a . a, b)
pairLInner :: ValT
pairLInner = BuiltinNested . PairT (AbsT 0 0) $ AbsT 1 0

-- (forall a . a, forall b . b)
pairInner :: ValT
pairInner = BuiltinNested . PairT (AbsT 0 0) $ AbsT 0 0
-}
