-- Copyright (c) David Amos, 2008. All rights reserved.

module Math.Algebra.Group.SchreierSims where

import qualified Data.List as L
import Data.Maybe (isNothing, isJust)
import qualified Data.Set as S
import qualified Data.Map as M
import Math.Algebra.Group.PermutationGroup hiding (elts, order, orderBSGS, gens, isMember, isSubgp, isNormal, reduceGens, normalClosure, commutatorGp, derivedSubgp)
import Math.Common.ListSet (toListSet)
import Math.Core.Utils hiding (elts)


-- COSET REPRESENTATIVES FOR STABILISER OF A POINT

-- Given a group G = <gs>, and a point x, find (right) coset representatives for Gx (stabiliser of x) in G
-- In other words, for each x' in the orbit of x under G, we find a g <- G taking x to x'
-- The code is similar to the code for calculating orbits, but modified to keep track of the group elements that we used to get there
cosetRepsGx :: Ord k => [Permutation k] -> k -> M.Map k (Permutation k)
cosetRepsGx gs x = cosetRepsGx' gs M.empty (M.singleton x 1) where
    cosetRepsGx' gs interior boundary
        | M.null boundary = interior
        | otherwise =
            let interior' = M.union interior boundary
                boundary' = M.fromList [(p .^ g, h*g) | g <- gs, (p,h) <- M.toList boundary] M.\\ interior'
            in cosetRepsGx' gs interior' boundary'


-- SCHREIER GENERATORS

-- toSet xs = (map head . group . sort) xs

-- Generators for Gx, the stabiliser of x, given that G is generated by gs, and rs is a set of coset representatives for Gx in G. 
-- Schreier's Lemma states that if H < G = <S>, and R is a set of coset reps for H in G
-- then H is generated by { rs(rs)*^-1 | r <- R, s <- S } (where * means "the coset representative of")
-- In particular, with H = Gx, this gives us a way of finding a set of generators for Gx
schreierGeneratorsGx :: Ord k => (k, M.Map k (Permutation k)) -> [Permutation k] -> [Permutation k]
schreierGeneratorsGx (x,rs) gs = L.nub $ filter (/= 1) [schreierGenerator r g | r <- M.elems rs,  g <- gs]
    where schreierGenerator r g = let h = r * g
                                      h' = rs M.! (x .^ h)
                                  in h * inverse h'


-- SCHREIER-SIMS ALGORITHM

-- Given a list of right transversals for a stabiliser chain, sift a group element through it
-- Note, this version assumes the base is non-redundant
sift :: Ord k => [(k, M.Map k (Permutation k))] -> Permutation k -> Maybe (Permutation k)
sift _ 1 = Nothing
sift ((b,t):bts) g = case M.lookup (b .^ g) t of
                     Nothing -> Just g
                     -- Nothing -> sift bts g -- if we allow redundant levels
                     Just h -> sift bts (g * inverse h)
sift [] g = Just g -- g == 1 case already caught above


-- findBase gs = minimum $ concatMap supp gs
findBase gs = minimum $ map minsupp gs
{-
-- Find base and strong generating set using Schreier-Sims algorithm
bsgs gs | all (/= 1) gs = map fst $ ss [newLevel gs] []

newLevel s = let b = findBase s
                 t = cosetRepsGx s b
             in ((b,t),s)

ss (bad@((b,t),s):bads) goods =
    let bts = map fst goods
        sgs = schreierGeneratorsGx (b,t) s
        siftees = filter isJust $ map (sift bts) sgs
    in  if null siftees
        then ss bads (bad:goods)
        else let Just h = head siftees
             in if null goods
                then ss (newLevel [h] : bad : bads) []
                else let ((b_,t_),s_) = head goods
                         s' = h:s_
                         t' = cosetRepsGx s' b_
                     in ss (((b_,t'),s') : bad : bads) (tail goods)
ss [] goods = goods
-}


-- |Given generators for a permutation group, return a strong generating set.
-- The result is calculated using Schreier-Sims algorithm, and is relative to the base implied by the Ord instance
sgs :: (Ord a, Show a) => [Permutation a] -> [Permutation a]
sgs gs = toListSet $ concatMap snd $ ss bs gs
    where bs = toListSet $ concatMap supp gs

-- Find base and strong generating set using Schreier-Sims algorithm
-- !! This function is poorly named - it actually finds you a base and sets of transversals
-- This version guarantees to use bases in order
bsgs :: Ord a => [Permutation a] -> [(a, M.Map a (Permutation a))]
bsgs gs = bsgs' bs gs
    where bs = toListSet $ concatMap supp gs

-- This version lets you pass in bases in the order you want them (or [], and it will find its own)
bsgs' :: Ord a => [a] -> [Permutation a] -> [(a, M.Map a (Permutation a))]
bsgs' bs gs = map fst $ ss bs gs

-- For example, bsgs (_A 5) uses [1,2,3] as the bases, but bsgs' [] (_A 5) uses [1,3,2]

newLevel :: Ord a => [a] -> [Permutation a] -> ([a], ((a, M.Map a (Permutation a)), [Permutation a]))
newLevel (b:bs) s = (bs, newLevel' b s)
newLevel [] s = ([], newLevel' b s) where b = findBase s
newLevel' :: Ord a => a -> [Permutation a] -> ((a, M.Map a (Permutation a)), [Permutation a])
newLevel' b s = ((b,t),s) where t = cosetRepsGx s b

ss :: Ord a => [a] -> [Permutation a] -> [((a, M.Map a (Permutation a)), [Permutation a])]
ss bs gs = ss' bs' [level] []
    where (bs',level) = newLevel bs $ filter (/=1) gs

ss' bs (bad@((b,t),s):bads) goods =
    let bts = map fst goods
        sgs = schreierGeneratorsGx (b,t) s
        siftees = filter isJust $ map (sift bts) sgs
    in  if null siftees
        then ss' bs bads (bad:goods)
        else let Just h = head siftees
             in if null goods
                then let (bs', level) = newLevel bs [h]
                     in ss' bs' (level : bad : bads) []
                else let ((b_,t_),s_) = head goods
                         s' = h:s_
                         t' = cosetRepsGx s' b_
                     in ss' bs (((b_,t'),s') : bad : bads) (tail goods)
ss' _ [] goods = goods
{-
extendbsgs [] g = bsgs [g]
extendbsgs (((b,t),s):bts) g = ss (((b,t),g:s):bts) []

bsgs' gs = map fst $ foldl extendbsgs [] gs
-}

-- The above is written for simplicity.
-- Its efficiency could be improved by incrementally updating the transversals,
-- and keeping track of Schreier generators we have already tried.
-- (Remember to add new Schreier generators every time the generating set or transversal is augmented.)


-- USING THE SCHREIER-SIMS TRANSVERSALS

isMemberBSGS :: Ord k => [(k, M.Map k (Permutation k))] -> Permutation k -> Bool
isMemberBSGS bts g = isNothing $ sift bts g

-- By Lagrange's thm, every g <- G can be written uniquely as g = r_m ... r_1 (Seress p56)
-- Note that we have to reverse the list of coset representatives
eltsBSGS :: Num b => [(a, M.Map k b)] -> [b]
eltsBSGS bts = map (product . reverse) (cartProd ts)
	where ts = map (M.elems . snd) bts

cartProd :: [[a]] -> [[a]]
cartProd (set:sets) = [x:xs | x <- set, xs <- cartProd sets]
cartProd [] = [[]]

orderBSGS :: [(a1, M.Map k a2)] -> Integer
orderBSGS bts = product (map (toInteger . M.size . snd) bts)

-- |Given generators for a group, determine whether a permutation is a member of the group, using Schreier-Sims algorithm
isMember :: (Ord t, Show t) => [Permutation t] -> Permutation t -> Bool
isMember gs h = isMemberBSGS (bsgs gs) h

-- |Given generators for a group, return a (sorted) list of all elements of the group, using Schreier-Sims algorithm
elts :: (Ord t, Show t) => [Permutation t] -> [Permutation t]
elts [] = [1]
elts gs = eltsBSGS $ bsgs gs

-- |Given generators for a group, return the order of the group (the number of elements), using Schreier-Sims algorithm
order :: (Ord t, Show t) => [Permutation t] -> Integer
order [] = 1
order gs = orderBSGS $ bsgs gs

isSubgp :: (Foldable t, Ord k) => t (Permutation k) -> [Permutation k] -> Bool
isSubgp hs gs = all (isMemberBSGS gs') hs
    where gs' = bsgs gs

isNormal :: Ord k => [Permutation k] -> [Permutation k] -> Bool
isNormal hs gs = hs `isSubgp` gs
              && all (isMemberBSGS hs') [h~^g | h <- hs, g <- gs]
    where hs' = bsgs hs

index gs hs = order gs `div` order hs


-- given list of generators, try to find a shorter list
reduceGens :: Ord k => [Permutation k] -> [Permutation k]
reduceGens gs = fst $ reduceGensBSGS (filter (/=1) gs)

reduceGensBSGS :: Ord k => [Permutation k] -> ([Permutation k], [(k, M.Map k (Permutation k))])
reduceGensBSGS (g:gs) = reduceGens' ([g],bsgs [g]) gs where
    reduceGens' (gs,bsgsgs) (h:hs) =
        if isMemberBSGS bsgsgs h
        then reduceGens' (gs,bsgsgs) hs
        else reduceGens' (h:gs, bsgs $ h:gs) hs
    reduceGens' (gs,bsgsgs) [] = (reverse gs,bsgsgs)
reduceGensBSGS [] = ([],[])

-- normal closure of H in G
-- for efficiency, should be called with gs and hs already reduced sets of generators 
normalClosure :: Ord k => [Permutation k] -> [Permutation k] -> [Permutation k]
normalClosure gs hs = reduceGens $ hs ++ [h ~^ g | h <- hs, g <- gs']
    where gs' = gs ++ map inverse gs

-- commutator gp of H and K
commutatorGp :: Ord k => [Permutation k] -> [Permutation k] -> [Permutation k]
commutatorGp hs ks = normalClosure (hsks) [h^-1 * k^-1 * h * k | h <- hs', k <- ks']
    where hs' = reduceGens hs
          ks' = reduceGens ks
          hsks = reduceGens (hs' ++ ks')
          -- no point processing more potential generators than we have to

-- derived subgroup (or commutator subgroup)
derivedSubgp :: Ord k => [Permutation k] -> [Permutation k]
derivedSubgp gs = normalClosure gs' [g^-1 * h^-1 * g * h | g <- gs', h <- gs']
    where gs' = reduceGens gs
    -- == commutatorGp gs gs

{-
isPerfect gs = order gs == order (derivedSubgp gs)
-- We compare orders rather than the generators themselves, because derivedSubgp will usually find different generators


derivedSeries gs = derivedSeries' (gs, order gs) where
    derivedSeries' ([],1) = [[]]
    derivedSeries' (hs, orderhs) =
        let hs' = derivedSubgp hs
            orderhs' = order hs'
        in if orderhs' == orderhs
           then [hs]
           else hs : derivedSeries' (hs',orderhs')

lowerCentralSeries gs = lowerCentralSeries' (gs, order gs) where
    lowerCentralSeries' ([],1) = [[]]
    lowerCentralSeries' (hs, orderhs) =
        let hs' = commutatorGp gs hs
            orderhs' = order hs'
        in if orderhs' == orderhs
           then [hs]
           else hs : lowerCentralSeries' (hs',orderhs')
-}

