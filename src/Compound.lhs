\begin{comment}

>{-# LANGUAGE TypeSynonymInstances, DeriveFunctor #-} 

-*- mode: haskell; c-basic-offset: 2; tab-width: 2; indent-tabs-mode: nil -*-

>module Compound (Compound, AlphaCompound, D (..), applyToLeafIf) where
>import qualified Data.Set as Set
>import Data.Set (Set)
>import qualified Data.Bits as Bits
>import Data.Bits (Bits)
>import qualified Data.List as List
>import System.Random
>import Data.Word (Word)
>import Data.List (nub, subsequences)

>import Data.Maybe
>import Control.Monad (liftM, liftM2, mapM)
>import Debug.Trace

>import Test.QuickCheck
>import Test.Framework (defaultMain, testGroup)
>import Test.Framework.Providers.QuickCheck2 (testProperty)

>import Unitary

\end{comment}

A compound diagram is a generic type, which is either has unitary leaves or unitary $\alpha$-diagram leaves.

>data D u = And (D u) (D u)
>  | Or (D u) (D u)
>  | Product (D u) (D u)
>  | Not (D u)
>  | Leaf {diagram:: u} deriving (Show, Eq, Functor)

>type Compound = D Unitary
>type AlphaCompound = D Alpha

The following method is used to recursively apply reasoning rules to diagrams.  If the condition is fulfilled then the provided function is applied to the leaf node.

>applyToLeafIf :: ((D a) -> Bool) -> ((D a) -> (D a)) -> D a -> D a
>applyToLeafIf c f (Leaf d) = 
>  let d' = Leaf d in if (c d') then applyToLeafIf c f (f d') else d'
>applyToLeafIf c f (And     d1 d2) = 
>  And     (applyToLeafIf c f d1) (applyToLeafIf c f d2)
>applyToLeafIf c f (Or      d1 d2) = 
>  Or      (applyToLeafIf c f d1) (applyToLeafIf c f d2)
>applyToLeafIf c f (Product d1 d2) = 
>  Product (applyToLeafIf c f d1) (applyToLeafIf c f d2)
>applyToLeafIf c f (Not d)         = 
>  Not     (applyToLeafIf c f d)

\begin{comment}

>mkBinary :: (Compound -> Compound -> Compound) -> Int -> Gen Compound
>mkBinary f depth = 
>  liftM2 f (mkCompound depth') (mkCompound depth')
>  where
>    depth' = depth -1
    
>mkNot :: Int -> Gen Compound
>mkNot depth = 
>  liftM Not (mkCompound (depth-1))

>mkAlphaBinary :: (AlphaCompound -> AlphaCompound -> AlphaCompound) -> Int -> Gen AlphaCompound
>mkAlphaBinary f depth = 
>  liftM2 f (mkAlphaCompound depth') (mkAlphaCompound depth')
>  where
>    depth' = depth -1
    
>mkAlphaNot :: Int -> Gen AlphaCompound
>mkAlphaNot depth = 
>  liftM Not (mkAlphaCompound (depth-1))

>mkLeaf :: Gen Compound
>mkLeaf = liftM Leaf (arbitrary :: Gen Unitary)

>mkAlphaLeaf :: Gen AlphaCompound
>mkAlphaLeaf = liftM Leaf (arbitrary :: Gen Alpha)

>mkCompound :: Int -> Gen Compound
>mkCompound 0 = mkLeaf
>mkCompound depth = oneof [mkLeaf,
>                          mkBinary And depth, 
>                          mkBinary Or depth, 
>                          mkBinary Product depth,
>                          mkNot depth]

>mkAlphaCompound :: Int -> Gen AlphaCompound
>mkAlphaCompound 0 = mkAlphaLeaf
>mkAlphaCompound depth = oneof [mkAlphaLeaf, 
>                               mkAlphaBinary And depth, 
>                               mkAlphaBinary Or depth,
>                               mkAlphaBinary Product depth,
>                               mkAlphaNot depth]

>instance Arbitrary Compound where
>  arbitrary = mkCompound =<< (choose (0,4))

>instance Arbitrary AlphaCompound where
>  arbitrary = mkAlphaCompound =<< (choose (0,4))

\end{comment}