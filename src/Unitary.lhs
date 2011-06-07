\begin{comment}

>{-# LANGUAGE TypeSynonymInstances #-}

-*- mode: haskell; c-basic-offset: 2; tab-width: 2; indent-tabs-mode: nil -*-

> module Unitary (Contour, ContourSet, Zone (..), ZoneSet, Foot (..), FootSet, Spider (..), SI (..), SISet, AlphaSI (..), toSSet, toSISet, Unitary, Alpha, mkUnitary, mkAlpha, U (..), unitaryToAlpha, UnitaryAndZone2 (..), powersetS, listAllZones, UnitaryAndElem (..), UnitaryAndElem2 (..), allContours, allContoursS) where

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

\end{comment}

First, define an appropriate data structure for a spider diagram of order.  This follows the same structure as the previously presented Backus-Naur grammar.  This collection of data constructors and type synonyms form a domain specific language in which we may discuss \texttt{Contour}s and \texttt{ContourSet}s, rather than the underlying types provided by the programming language.

>type Contour = Char
>type ContourSet = Set Contour

>data Zone = Zone { zin :: ContourSet
>                 , zout:: ContourSet} deriving (Show, Eq, Ord)

>type ZoneSet = Set Zone

From definition~\ref{defn:sdoo-foot}, a spider foot is an element of the set $(\Zed^+\cup\{\bullet\})\times\mathcal{Z}$.  We use Nothing as $\bullet$ and Just i as rank i.

>data Foot = Foot { rank   :: Maybe Int
>                 , habitat:: Zone} deriving (Show, Eq, Ord)

>type FootSet = Set Foot

From definition~\ref{defn:sdoo-foot}, a spider is and element of the set $\Zed^+\times (\Pow \mathcal{F}-\{\emptyset\})$

>data Spider = Spider { scount :: Int
>                     , sfeet  :: FootSet} deriving (Show, Eq, Ord)

We distinguish between a spider and an $\alpha$-spider as some of our rules require $\alpha$-diagrams as a precondition.

>type SSet = Set Spider
>data SI = SI { count :: Int
>            , feet  :: FootSet} deriving (Show, Eq, Ord)
>data AlphaSI = AlphaSI { alphaCount :: Int
>                         , alphaFoot :: Foot } deriving (Show, Eq, Ord)
>type SISet = Set SI

\begin{comment}

>flattenSet :: (Ord a) => Set (Set a) -> Set a
>flattenSet = Set.fold Set.union Set.empty

>toSSet :: SISet -> SSet
>toSSet sis = flattenSet (Set.map mkSs sis)
>       where
>       mkSs (SI n p) = Set.fromList (map (\x->Spider x p) [1..n])

>toSISet :: SSet -> SISet
>toSISet ss = Set.map mkSIs ss
>        where
>        mkSIs (Spider n p) = SI (Set.size (Set.filter (\x -> p == (sfeet x)) ss)) p

>instance (Ord a, Arbitrary a) => Arbitrary (Set a) where
>         arbitrary = do
>           es <- listOf arbitrary
>           return (Set.fromList es)

\end{comment}

We define both unitary diagrams and unitary $\alpha$-diagrams.

>data U a = U { contours :: Set Contour
>  , zones    :: Set Zone
>  , shaded   :: Set Zone
>  , sids     :: Set a} deriving (Show, Eq, Ord)

>type Unitary = U SI
>mkUnitary :: Set Contour -> Set Zone -> Set Zone -> Set SI -> Unitary
>mkUnitary c z shz si = U c z shz si

>type Alpha = U AlphaSI
>mkAlpha :: Set Contour -> Set Zone -> Set Zone -> Set AlphaSI -> Alpha
>mkAlpha c z shz si = U c z shz si

Furthermore, we define a method for constructing a unitary $\alpha$ diagram from an appropriate unitary diagram.

>unitaryToAlpha :: Unitary -> Alpha
>unitaryToAlpha d = mkAlpha (contours d) (zones d) (shaded d) as
>  where
>  as = Set.map (\s -> AlphaSI (count s) (Set.findMin (feet s))) (sids d)

\begin{comment}

>mkFootSet :: ZoneSet -> Gen FootSet
>mkFootSet zones = 
>  do
>    max <- choose (1, 10)
>    feet <- genListFeet max Set.empty zones
>    return feet

>arbitrarySISet :: ZoneSet -> Gen SISet
>arbitrarySISet zones =
>  do
>     n <- choose (1, 10)
>     fss <- sequence (replicate n (mkFootSet zones))
>     ns <- listOf1 (choose (1, 10))
>     return (Set.fromList (zipWith SI ns (nub fss)))

>randSubset :: Ord a => Set a -> Gen (Set a)
>randSubset xs = do
>        mask <- vectorOf (Set.size xs) arbitrary
>        return  (Set.fromList [ e | (e,True) <- zip (Set.toList xs) mask ])

>-- | Given $C(d)$ and a set of contours, construct the corresponding Zone
>listAllZones :: ContourSet -> ContourSet -> Zone
>listAllZones cs inZones = Zone inZones (cs `Set.difference` inZones)

>powerset :: [a] -> [[a]]
>powerset [] = [[]]
>powerset (x:xs) = powerset xs ++ map (x:) (powerset xs)

>powersetS :: Ord a => Set a -> Set (Set a)
>powersetS xs = Set.fromList (map (Set.fromList) (powerset (Set.toList xs)))

>instance Arbitrary Unitary where
>  arbitrary = 
>    do
>      -- ensure that c is never empty
>      c <- randSubset allContoursS
>      z <- randSubset (Set.map (listAllZones c) (powersetS c))
>      shz  <- randSubset z
>      sids <- arbitrarySISet z
>      return $ mkUnitary c z shz sids

>genListFeet :: Int -> (Set Foot) -> ZoneSet -> Gen (Set Foot)
>genListFeet _ _ zones | Set.null zones = 
>  return Set.empty
>genListFeet 0 feet _ = 
>  return feet
>genListFeet max feet zones =
>  do
>     z <- elements (Set.toList zones)
>     n <- elements (Nothing : map Just [0 .. Set.size zones - 1])
>     let foot = Foot n z
>     genListFeet (max-1) (Set.insert foot feet) zones

>instance Arbitrary Alpha where
>  arbitrary = do
>    c <- randSubset allContoursS
>    z <- randSubset (Set.map (listAllZones c) (powersetS c))
>    shz  <- randSubset z
>    sids <- genSids z
>    return $ mkAlpha c z shz sids
>    where
>      genSids z = do
>        msi  <- choose (0, 9) -- up to 10 si's 
>        cnt  <- listOf1 (choose (1, 5))
>        feet <- genListFeet msi Set.empty z
>        let sis = Set.fromList (zipWith AlphaSI cnt (Set.toList feet)) 
>        return sis

Temporary data type for testing \textit{introduction of a missing zone}.

>arbitraryZone :: ZoneSet -> Gen Zone
>arbitraryZone = elements . Set.toList

>data UnitaryAndZone2 = UnitaryAndZone2 Unitary Zone Zone  deriving Show
>instance Arbitrary UnitaryAndZone2 where
>  arbitrary = do
>    d  <- arbitrary
>    let cs  = contours d
>        zs  = Set.map (listAllZones cs) (powersetS cs)
>        mzs = (zs `Set.difference` (zones d))
>    -- z1 and z2 are missing zones
>    z1 <- if (Set.null mzs) then
>            return (Zone Set.empty cs) -- Return something sane
>          else 
>            arbitraryZone mzs
>    z2 <- if (Set.null mzs) then
>            return (Zone Set.empty cs)
>          else 
>            arbitraryZone mzs
>    return (UnitaryAndZone2 d z1 z2)

>arbitrarySI :: Unitary -> Gen (Maybe SI)
>arbitrarySI d = 
>  if Set.null (sids d) then
>    return Nothing
>  else
>    elements (map Just (Set.toList (sids d)))

>data UnitaryAndElem  = UnitaryAndElem Unitary (Maybe SI) deriving Show
>data UnitaryAndElem2 = UnitaryAndElem2 Unitary (Maybe SI) (Maybe SI) deriving Show

>instance Arbitrary UnitaryAndElem where
>  arbitrary = do
>    d <- arbitrary
>    p <- arbitrarySI d
>    return (UnitaryAndElem d p)

>instance Arbitrary UnitaryAndElem2 where
>  arbitrary = do
>    d <- arbitrary
>    p  <- arbitrarySI d
>    p2 <- arbitrarySI d
>    return (UnitaryAndElem2 d p p2)

tests = []

>allContours :: [Contour]
>allContours = "PQRWX"
>allContoursS :: Set Contour
>allContoursS = Set.fromList allContours

\end{comment}