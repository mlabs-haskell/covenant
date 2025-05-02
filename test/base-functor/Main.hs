module Main (main) where

import Test.QuickCheck
  ( Arbitrary (arbitrary),
    Property,
  )

import Covenant.Internal.Data
    ( allComponentTypes, hasRecursive, mkBaseFunctor )
import Covenant.Type (datatypeName)
import Covenant.Test
    ( DataDeclFlavor(Poly1PolyThunks), DataDeclSet(DataDeclSet) )
import Control.Monad.Reader (runReader)
import Data.Map.Strict qualified as M
import Optics.Core (view)
import Test.Tasty.QuickCheck (forAllBlind, testProperty)
import Test.Tasty (defaultMain, testGroup) 

main :: IO ()
main = defaultMain . testGroup "BaseFunctors" $
  [testProperty "All recursion is replaced in base functor transform" baseFunctorsContainNoRecursion]

baseFunctorsContainNoRecursion :: Property
baseFunctorsContainNoRecursion = forAllBlind (arbitrary @(DataDeclSet 'Poly1PolyThunks)) $ \(DataDeclSet decls) ->
  let declMap = M.fromList $ (\x -> (view datatypeName x,x)) <$> decls
      baseFunctorResults =  flip runReader 0 . mkBaseFunctor <$> declMap
  in M.foldlWithKey' (\acc tyNm origDecl ->
       let isTyRecursive =  any (\x -> runReader (hasRecursive tyNm x) 0) (allComponentTypes origDecl)
           mBaseFDecl = baseFunctorResults M.! tyNm
       in case mBaseFDecl of
           -- if we didn't make a base functor then the original type must NOT be recursive
           Nothing -> not isTyRecursive && acc
           Just baseFDecl ->
             -- If we did make a base functor, it should contain no recursion
             let recursionInBaseF = any (\x -> runReader (hasRecursive (view datatypeName baseFDecl) x) 0) (allComponentTypes baseFDecl)
             in not recursionInBaseF && acc
      ) True declMap
