\begin{comment}

>{-# LANGUAGE TypeSynonymInstances #-}

-*- mode: haskell; c-basic-offset: 2; tab-width: 2; indent-tabs-mode: nil -*-

>import Unitary
>import Compound

>import qualified Data.Set as Set
>import Data.Set (Set, fromList)
>import Data.Maybe (isJust, fromMaybe)

>import Test.QuickCheck
>import Test.Framework (defaultMain, testGroup)
>import Test.Framework.Providers.QuickCheck2 (testProperty)
>import Test.Framework.Providers.HUnit (testCase)
>import Test.HUnit

\end{comment}

We now define a function for each reasoning rule.  In the following code we define a function \texttt{ruleIntroC} which is an implementation of Rule~\ref{rule:intro-contour} \textit{Introduction of a Contour Label}.  We can observe from its type signature that it takes a \texttt{Contour} label and a \texttt{Unitary} diagram and returns a new \texttt{Unitary} diagram.  The \textit{Rule of replacement}, of which we need no implementation, allows us to substitute the original \texttt{Unitary} diagram with the new syntactically equivalent \texttt{Unitary} diagram.  The functions \texttt{flattenSet}, \texttt{splitZone}, \texttt{splitZoneset}, \texttt{splitFoot} and \texttt{splitSpider} factor out important operations for the purpose of readability.

>flattenSet :: (Ord a) => Set (Set a) -> Set a
>flattenSet = Set.fold Set.union Set.empty

Splits a Zone in two by introducing a new Contour label.

>splitZone :: Contour -> Zone -> ZoneSet
>splitZone l z = Set.fromList [ z { zin  = Set.insert l (zin z) }
>                            , z { zout = Set.insert l (zout z) } ]

Splits each Zone in a ZoneSet in two.

>splitZoneset :: Contour -> ZoneSet -> ZoneSet
>splitZoneset l zs | Set.null zs = splitZone l (mkZone Set.empty Set.empty)
>                  | otherwise   = flattenSet (Set.map (splitZone l) zs)

If the habitat of a spider foot is expanded by introducing a contour label, then add the new zones to the spider habitat.

>splitFoot :: Contour -> Foot -> FootSet
>splitFoot l f = Set.map (Foot (rank f)) (splitZone l (habitat f))

Expand all feet in each of the identified spiders into the expanded habitat.

>splitSpider :: Contour -> SI -> SI
>splitSpider l si = SI (count si) fs
>  where
>  fs = flattenSet (Set.map (splitFoot l) (feet si))

The implementation of rule~\ref{rule:intro-contour} \textit{introduction of a contour label} is now straightforward.

>ruleIntroC :: Contour -> Unitary -> Unitary
>ruleIntroC l d = 
>  mkUnitary (Set.insert l (contours d))
>            (splitZoneset l (zones d))
>            (splitZoneset l (shaded d))
>            (Set.map (splitSpider l) (sids d)) 

The function \texttt{ruleIntroC} is an implementation of rule~\ref{rule:intro-contour}.  We now define a function to apply the \texttt{ruleIntroC} to the leaves of a \texttt{Compound} diagram for each \texttt{Contour} in a list of \texttt{Contour}s.  This allows us to algorithmically add all contours in $\mathcal{C}$ to a \texttt{Compound} diagram.

>introC :: [Contour] -> Compound -> Compound
>introC [] c = c
>introC ls c = 
>  applyToLeafIf 
>                 (\(Leaf d) -> (allContoursS /= (contours d))) f c
>  where
>  f (Leaf d) = Leaf (ruleIntroC 
>                 (head (Set.toList (allContoursS 
>                                       `Set.difference` (contours d)))) 
>                 d)

Rule~\ref{rule:introduce-missing-zone} \textit{Introduction of a Missing Zone} is implemented in \texttt{ruleIntroMz}.  We assume the existence of a function \texttt{powersetS :: Ord a => Set a -> Set (Set a)} which computes the powerset of a \texttt{Set a}.  The full implementation of all helper functions can be found in appendix~\ref{appendix:code}.

>ruleIntroMz :: Zone -> Unitary -> Unitary
>ruleIntroMz z d = 
>  mkUnitary (contours d)
>            (Set.insert z (zones d))
>            (Set.insert z (shaded d))
>            (sids d)

We provide an implementation of \texttt{introMz} which simply applies \texttt{ruleIntroMz} for each element in the set of all zones.

>introMz :: Compound -> Compound
>introMz c = fmap (\d' -> Set.fold ruleIntroMz d' (allZones d')) c
>  where
>  allZones d' = (Set.map (listAllZones (contours d')) 
>                            $ powersetS (contours d'))

In order to implement rule~\ref{rule:split-spiders} we require an implementation of the $\oplus$ and $\ominus$ operators.  These are implemented in the functions \texttt{addASpider} and \texttt{removeASpider} respectively.  In this implementation the rule we choose a specific bipartite partition of the \texttt{FootSet}.  We simply choose the singleton set consisting of the minimal element of the \texttt{FootSet} as one partition, the other partition follows.  The \texttt{Ord}er relation over a \texttt{FootSet}, from which the minimal element is derived, is itself automatically derived by the Haskell compiler.

>-- | Find all spider identifiers with a particular FootSet
>find :: FootSet -> SISet -> SISet
>find f p = Set.filter (\x -> f == (feet x)) p

>-- | Remove one occurrence of a spider with FootSet 
>-- from a diagram.
>removeASpider :: FootSet -> Unitary -> Unitary
>removeASpider p d = 
>  mkUnitary (contours d) 
>            (zones d) 
>            (shaded d) 
>            (Set.union addable (Set.difference (sids d) removable))
>    where
>    removable = find p (sids d)
>    -- if it's in removable, then decrement count, 
>    -- and where count <=0, throw it away
>    addable = Set.filter (\x -> (count x) >=1) 
>            (Set.map (\x -> (SI ((count x)-1) (feet x))) removable) 

>-- | Add an occurrence of a spider with FootSet to
>-- a diagram
>addASpider :: FootSet -> Unitary -> Unitary
>addASpider p d = d {sids = sis} 
>             where
>             ss = toSSet (sids d)
>             n = case (Set.minView (find p (sids d))) of
>                Nothing -> 1
>                Just (e, s) -> (count e) + 1
>             sis = toSISet (ss `Set.union` (Set.singleton (Spider n p)))

>ruleSplitSpiders :: FootSet -> Unitary -> Compound
>ruleSplitSpiders p d = Or 
>          (Leaf (addASpider p1 stripped_sis)) 
>          (Leaf (addASpider p2 stripped_sis))
>       where
>       stripped_sis  = removeASpider p d
>       (p1,p2) = Set.partition ((Set.findMin p)==) p

Again, we provide a generalisation of the split spiders rule, called \texttt{splitSpiders}, which recursively applies \texttt{ruleSplitSpider} to the \texttt{Unitary} components of a \texttt{Compound} diagram.  The recursion terminates when \texttt{findSplittableSpider} can no-longer find a spider in a \texttt{FootSet} with two or more feet.

>-- | Find a spider with two or more feet
>findSplitableSpider :: SISet -> Maybe FootSet
>findSplitableSpider sis = 
>  case s of
>    Nothing -> Nothing
>    Just (e, s') -> Just e
>  where
>    s = Set.minView 
>          (Set.filter (\x-> (Set.size x) >=2) (Set.map feet sis))

>splitSpiders :: Compound -> Compound
>splitSpiders d = 
>  applyToLeafIf (\(Leaf d') -> 
>                    isJust (findSplitableSpider (sids d')))
>                (\(Leaf d') -> 
>                    let (Just p') = findSplitableSpider (sids d') in 
>                    ruleSplitSpiders p' d')
>                d

The implementation of rule~\ref{rule:conjoin-stuff} \textit{Separate Order and Bounds} follows.

>-- | Get the subset of @\alpha@-spiders that are ordered.
>extractOrderedAlphaSpiders :: Set AlphaSI -> Set AlphaSI
>extractOrderedAlphaSpiders sis = 
>  Set.filter (isJust . rank . alphaFoot) sis

>-- | Remove integer ranks from all spiders, making sure to 
>-- correctly update spider identifiers
>unorderAllSpiders :: Set AlphaSI -> Set AlphaSI
>unorderAllSpiders sis = 
>  Set.map (\s-> AlphaSI 
>                  (countEm (alphaFoot s)) 
>                  (Foot Nothing (habitat $ alphaFoot s))) 
>           sis
>  where
>  -- | Count the number of spiders (of all ranks) that share the same FootSet
>  countEm f = Set.fold (+) 0 
>                    (Set.map (alphaCount) 
>                       (Set.filter (\s -> (alphaFoot s) == f) sis))

Given a \texttt{Unitary} diagram there are two conditions under which it cannot be separated into order information and bounds information.  These are if 
\begin{itemize}
\item it contains only ordered spiders and no shading, or
\item it contains no ordered spiders.
\end{itemize}
The following function separates order information from bounds information when neither of the above conditions are satisfied.

>ruleSeparateOrderAndBounds :: Alpha -> AlphaCompound
>-- if we have a diagram containing only order information, 
>-- or only bound information, return it as a Leaf
>ruleSeparateOrderAndBounds d = 
>  if (extractOrderedAlphaSpiders (sids d)== (sids d) && (shaded d)==Set.empty)
>     ||  (extractOrderedAlphaSpiders (sids d)== Set.empty) 
>  then Leaf d
>  else And (Leaf d1) (Leaf d2)
>    where
>    d1 = mkAlpha (contours d) 
>                 (zones d) 
>                 Set.empty 
>                 (extractOrderedAlphaSpiders (sids d))
>    d2 = mkAlpha (contours d) 
>                 (zones d) 
>                 (shaded d) 
>                 (unorderAllSpiders (sids d))

We now present a recursive algorithm to apply \texttt{separateOrderAndBounds} to a \texttt{Compound} diagram.

>separateOrderAndBounds :: AlphaCompound -> AlphaCompound
>separateOrderAndBounds d = 
>  applyToLeafIf (\(Leaf d') -> not ((Leaf d') == (ruleSeparateOrderAndBounds d'))) 
>                (\(Leaf d') -> ruleSeparateOrderAndBounds d')
>                d

The following implements Rule~\ref{rule:factor-lowest-spider} \textit{Factor Lowest Spider}.

>-- | If the diagram contains two or more different 
>-- ranks of spider foot, return the lower rank.
>findLowestFactorable :: Set AlphaSI -> Maybe Int
>findLowestFactorable sis = 
>  case (length ranks) of
>    0 -> Nothing
>    1 -> Nothing
>    _ -> minimum ranks
>  where
>  ranks = 
>    Set.toList (Set.filter (\x -> Nothing/=x) (Set.map (rank . alphaFoot) sis))

>ruleFactorLowestSpider :: Alpha -> AlphaCompound
>ruleFactorLowestSpider d = 
>  case lowest of
>    Nothing -> Leaf d
>    _ -> Product (Leaf d1) (Leaf d2)
>  where
>  lowest = findLowestFactorable (sids d)
>  d1 = mkAlpha 
>         (contours d) 
>         (zones d) 
>         (shaded d) 
>         (Set.filter ((lowest ==) . rank . alphaFoot) (sids d))
>  d2 = mkAlpha 
>         (contours d)
>         (zones d)
>         (shaded d)
>         ((sids d) `Set.difference` (sids d1))

The implementation of \texttt{factorLowestSpider} recursively applies \\\texttt{ruleFactorLowestSpider} to the leaves of a \texttt{Compound} diagram.  The recursion terminates when we can no-longer find a factorable spider in the \texttt{Unitary} component.

>factorLowestSpider :: AlphaCompound -> AlphaCompound
>factorLowestSpider d = 
>  applyToLeafIf (\(Leaf d') -> isJust $ findLowestFactorable (sids d'))
>                (\(Leaf d') -> ruleFactorLowestSpider d')
>                d

The implementation of rule~\ref{rule:drop-spider-foot-order} \textit{drop spider foot order} is straightforward in both the \texttt{Unitary} and \texttt{Compound} case.

>ruleDropSpiderFootOrder :: Alpha -> Alpha
>ruleDropSpiderFootOrder d = 
>  mkAlpha (contours d) 
>          (zones d) 
>          (shaded d) 
>          (unorderAllSpiders $ sids d)

>dropSpiderFootOrder :: AlphaCompound -> AlphaCompound
>dropSpiderFootOrder c = fmap ruleDropSpiderFootOrder c

\begin{comment}

>prop_one_rule_intro_c :: Unitary -> Bool
>prop_one_rule_intro_c d1 = (((Set.size(contours d2)) == (Set.size(contours d1))+2) 
>      && (Set.size (zones d2)) == 4*(Set.size (zones d1))) || (zones d1)==Set.empty -- if the zones are empty, then there's nothing to split
>      where
>      d2 = ruleIntroC "Z" (ruleIntroC "Y" d1)

>prop_sym_rule_intro_c :: Unitary -> Bool
>prop_sym_rule_intro_c d =  (ruleIntroC "Z" (ruleIntroC "Y" d))==(ruleIntroC "Y" (ruleIntroC "Z" d))

>assertForLeaf :: (D a) -> (a -> Bool)  -> Bool
>assertForLeaf (Leaf d) f        = f d
>assertForLeaf (And     d1 d2) f = (assertForLeaf d1 f) && (assertForLeaf d2 f)
>assertForLeaf (Or      d1 d2) f = (assertForLeaf d1 f) && (assertForLeaf d2 f)
>assertForLeaf (Product d1 d2) f = (assertForLeaf d1 f) && (assertForLeaf d2 f)
>assertForLeaf (Not d) f         = (assertForLeaf d f)

>prop_intro_c :: Compound -> Bool
>-- This list is the same as the set that Arbitrary Unitarys can draw from
>prop_intro_c d = assertForLeaf (introC allContours d) (\d' -> (Set.fromList allContours) == contours d')

>prop_sym_rule_intro_mz :: UnitaryAndZone2 -> Bool
>prop_sym_rule_intro_mz (UnitaryAndZone2 d z1 z2) =
>  ruleIntroMz z2 (ruleIntroMz z1 d) == ruleIntroMz z1 (ruleIntroMz z2 d)

>prop_introMZToVenn :: Compound -> Bool
>prop_introMZToVenn d = let d' = introMz d in
>  assertForLeaf d' (\x -> Set.size(zones x) == 2^(Set.size (contours x)))

>prop_removeASpider :: UnitaryAndElem -> Bool
>prop_removeASpider (UnitaryAndElem d s) =
>  case s of
>    Nothing -> True
>    Just s' -> 
>      fooSize d s' - 1 == fooSize d' s'
>      where
>      d' = removeASpider (feet s') d

>prop_addASpider :: UnitaryAndElem -> Bool
>prop_addASpider (UnitaryAndElem d s) =
>  case s of
>    Nothing -> True
>    Just s' -> (fooSize d s' + 1) == (fooSize d' s')
>      where
>      d' = addASpider (feet s') d

>-- Factoring this out seems to make the meanings of the tests clearer
>fooSize d s = sum . Set.toList . Set.map count . find (feet s) . sids $ d

>prop_sym_removeASpider :: UnitaryAndElem2 -> Bool
>prop_sym_removeASpider (UnitaryAndElem2 _ Nothing _) = True
>prop_sym_removeASpider (UnitaryAndElem2 _ _ Nothing) = True
>prop_sym_removeASpider (UnitaryAndElem2 d (Just s1) (Just s2)) =
>  (removeASpider p2 (removeASpider p1 d)) == (removeASpider p1 (removeASpider p2 d))
>           where
>--           allZones = Set.map (listAllZones (contours d)) (powersetS (contours d))
>           p1 = feet s1
>           p2 = feet s2

>prop_sym_addASpider :: UnitaryAndElem2 -> Bool
>prop_sym_addASpider (UnitaryAndElem2 _ Nothing _) = True
>prop_sym_addASpider (UnitaryAndElem2 _ _ Nothing) = True
>prop_sym_addASpider (UnitaryAndElem2 d (Just s1) (Just s2)) =
>  (addASpider p2 (addASpider p1 d)) == (addASpider p1 (addASpider p2 d))
>           where
>--           allZones = Set.map (listAllZones (contours d)) (powersetS (contours d))
>           p1 = feet s1
>           p2 = feet s2

>prop_id_ar_a_spider :: UnitaryAndElem -> Bool
>prop_id_ar_a_spider (UnitaryAndElem _ Nothing) = True
>prop_id_ar_a_spider (UnitaryAndElem d (Just s)) =
>  (removeASpider p $ addASpider p d) == (addASpider p $ removeASpider p d)
>           where
>--           allZones = Set.map (listAllZones (contours d)) (powersetS (contours d))
>           p = feet s

>prop_ruleSplitSpiders :: UnitaryAndElem -> Bool
>prop_ruleSplitSpiders (UnitaryAndElem _ Nothing)  = True
>prop_ruleSplitSpiders (UnitaryAndElem d (Just s)) = 
>  (d == (mergeSpiders p d1)) && (d == (mergeSpiders p' d2))
>    where
>    (Or (Leaf d1) (Leaf d2)) = ruleSplitSpiders (feet s) d
>    -- We know a-priori what will get partitioned (from the rule implementation)  
>    (p,p') = Set.partition ((Set.findMin (feet s))==) (feet s)
>    mergeSpiders q e = addASpider (p `Set.union` p') (removeASpider q e)

>getLeaves :: Ord a => D a -> Set a -> Set a
>getLeaves (Leaf d)        ls = Set.insert d ls
>getLeaves (And d1 d2)     ls = (getLeaves d1 ls) `Set.union` (getLeaves d2 ls)
>getLeaves (Or d1 d2)      ls = (getLeaves d1 ls) `Set.union` (getLeaves d2 ls)
>getLeaves (Product d1 d2) ls = (getLeaves d1 ls) `Set.union` (getLeaves d2 ls)
>getLeaves (Not d)         ls = (getLeaves d ls)

>prop_findSplitableSpider :: Compound -> Bool
>prop_findSplitableSpider c = 
>  Set.fold (&&) True (Set.map (\x -> case x of Nothing -> True; Just x' -> 2 <= Set.size x') ps)
>  where
>  ps = Set.map (findSplitableSpider . sids) (getLeaves c Set.empty)

>newtype TinyInt = TinyInt Int deriving Show
>instance Arbitrary TinyInt where
>  arbitrary = TinyInt `fmap` elements [1..10]

>prop_idem_extract_unordered_spiders :: Alpha -> TinyInt -> TinyInt -> Bool
>prop_idem_extract_unordered_spiders d (TinyInt n1) (TinyInt n2) = sis == sis'
>            where
>            -- The 0^th application of iterate f x is x, hence the +1
>            sis  = (iterate (extractOrderedAlphaSpiders ) (sids d) )!! n1
>            sis' = (iterate (extractOrderedAlphaSpiders ) (sids d) )!! n2 

>prop_idem_unorderAllSpiders :: Alpha -> TinyInt -> TinyInt -> Bool
>prop_idem_unorderAllSpiders d (TinyInt n1) (TinyInt n2) = sis == sis'
>            where
>            sis  = (iterate (unorderAllSpiders ) (sids d) )!! n1
>            sis' = (iterate (unorderAllSpiders ) (sids d) )!! n2 

>prop_unorderAllSpiders :: Alpha -> Bool
>prop_unorderAllSpiders d = (Set.empty == (Set.filter (\si -> Nothing /= (rank $ alphaFoot si)) sis'))
>  where
>  sis' = unorderAllSpiders (sids d)

>tests = [
>         testGroup "Unitary Rules" [
>            testProperty "Invariants for Rule Intro C"  prop_one_rule_intro_c
>          , testProperty "Symmetry for Rule Intro C"   prop_sym_rule_intro_c
>          , testProperty "Recursive application of Rule Intro C" prop_intro_c
>          , testProperty "Symmetry for Rule MZ"        prop_sym_rule_intro_mz
>          , testProperty "Recursive application of Rule MZ"      prop_introMZToVenn
>         ],
>         testGroup "Compound Rules" [
>            testProperty "Remove a spider for Rule split spiders" prop_removeASpider
>          , testProperty "Add a spider for Rule split spiders"    prop_addASpider
>          , testProperty "Symmetry of Remove a spider"            prop_sym_removeASpider
>          , testProperty "Symmetry of Add a spider"               prop_sym_addASpider
>          , testProperty "Add/Remove a spider identity"           prop_id_ar_a_spider
>          , testProperty "Rule Split Spiders"                     prop_ruleSplitSpiders
>          , testProperty "Find splittable spider "                prop_findSplitableSpider
>          , testProperty "Unorder spiders in an Alpha"            prop_unorderAllSpiders
>         ]
>      ]

>genDiagram :: Compound
>genDiagram = Leaf (mkUnitary (Set.fromList ["P", "Q", "R","W","X"]) (Set.fromList [p, notp]) Set.empty (Set.fromList [s1, s2]))
>     where
>          p = mkZone (Set.singleton "P") (Set.empty)
>          notp = mkZone (Set.empty) (Set.singleton "P")
>          h = Set.fromList [Foot (Just 1) p, Foot Nothing notp, Foot Nothing p, Foot (Just 2) notp]
>          s1 = SI 2 h
>          s2 = SI 1 (Set.fromList [Foot (Just 2) p])

\end{comment}

Our top-level driver code is now straightforward.  We assume the existence of functions \texttt{genDiagram :: Compound} and \texttt{allContours :: [Contour]} where \texttt{genDiagram} returns an arbitrary \texttt{Compound} diagram and \texttt{allContours} is the implementation of $\mathcal{C}$.  The variable names in the code are in one-to-one correspondence with the algorithm steps presented in figure~\ref{fig:diagram-normalisation-process}, for example, \texttt{dAlpha} corresponds to $D_{\alpha}$.

>main :: IO()
>main = do  defaultMain tests
>           print dBullet
>     where
>     dC = introC allContours genDiagram
>     dZ = introMz dC 
>     dAlpha = fmap unitaryToAlpha (splitSpiders dZ)
>     dBullet = dropSpiderFootOrder 
>             $ factorLowestSpider 
>             $ separateOrderAndBounds dAlpha
