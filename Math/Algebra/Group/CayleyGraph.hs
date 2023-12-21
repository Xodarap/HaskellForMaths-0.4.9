-- Copyright (c) David Amos, 2010. All rights reserved.

{-# LANGUAGE NoMonomorphismRestriction #-}

module Math.Algebra.Group.CayleyGraph where

import Math.Core.Utils hiding (elts)

import Math.Algebra.Group.StringRewriting as SR
import Math.Combinatorics.Graph
-- import Math.Combinatorics.GraphAuts

import Math.Algebra.Group.PermutationGroup as P

import qualified Data.List as L


data Digraph a = DG [a] [(a,a)] deriving (Eq,Ord,Show)


cayleyDigraphP :: (Num a, Ord a) => [a] -> Digraph a
cayleyDigraphP gs = DG vs es where
    vs = P.elts gs
    es = [(v,v') | v <- vs, v' <- nbrs v ]
    nbrs v = L.sort [v * g | g <- gs]

-- |The Cayley graph (undirected) on the generators (and their inverses),
-- for a group given as permutations
cayleyGraphP :: (Ord a, Show a) => [Permutation a] -> Graph (Permutation a)
cayleyGraphP gs = graph (vs,es) where -- G vs es where
    vs = P.elts gs
    es = toSet [ L.sort [v,v'] | v <- vs, v' <- nbrs v ] -- toSet orders and removes duplicates
    nbrs v = [v * g | g <- gs]


cayleyDigraphS :: Ord a => ([a], [([a], [a])]) -> Digraph [a]
cayleyDigraphS (gs,rs) = DG vs es where
    rs' = knuthBendix rs
    vs = L.sort $ nfs (gs,rs') -- calling elts would mean we invoked knuthBendix twice
    es = [(v,v') | v <- vs, v' <- nbrs v ]
    nbrs v = L.sort [rewrite rs' (v ++ [g]) | g <- gs]

-- |The Cayley graph (undirected) on the generators (and their inverses),
-- for a group given as generators and relations
cayleyGraphS :: (Ord a) => ([a], [([a], [a])]) -> Graph [a]
cayleyGraphS (gs,rs) = graph (vs,es) where -- G vs es where
    rs' = knuthBendix rs
    vs = L.sort $ nfs (gs,rs') -- calling elts would mean we invoked knuthBendix twice
    es = toSet [ L.sort [v,v'] | v <- vs, v' <- nbrs v ] -- toSet orders and removes duplicates
    nbrs v = [rewrite rs' (v ++ [g]) | g <- gs]

-- it would be better if we could use shortlex ordering, but as it stands Graph will use lex ordering


-- for example, can check
-- isIso (cayleyGraphP [p [[1,2]], p [[2,3]], p [[3,4]]]) (cayleyGraphS (SR._S 4))



-- given sequence of transpositions, return group elt it represents
fromTranspositions :: [SGen] -> Permutation Int
fromTranspositions ts = product $ map (\(S i) -> p [[i,i+1]]) ts

-- given sequence of transpositions, return the permutation of [1..n] that it causes
fromTrans :: [SGen] -> [Int]
fromTrans ts = [i .^ (g^-1) | i <- [1..n] ] where
    g = fromTranspositions ts
    n = maximum $ supp g


bubblesort :: Ord a => [a] -> [a]
bubblesort [] = []
bubblesort xs = bubblesort' [] xs where
    bubblesort' ls (r1:r2:rs) = if r1 <= r2 then bubblesort' (r1:ls) (r2:rs) else bubblesort' (r2:ls) (r1:rs)
    bubblesort' ls [r] = bubblesort (reverse ls) ++ [r]

-- given a permutation of [1..n] (as a list), return the transpositions which led to it
toTrans :: Ord a => [a] -> [SGen]
toTrans [] = []
toTrans xs = toTrans' 1 [] [] xs where
    toTrans' i ts ls (r1:r2:rs) = 
        if r1 <= r2
        then toTrans' (i+1) ts (r1:ls) (r2:rs)         -- no swap needed
        else toTrans' (i+1) (S i : ts) (r2:ls) (r1:rs) -- swap needed
    toTrans' i ts ls [r] = toTrans (reverse ls) ++ ts
-- note that the ts are returned in reverse to the order that they were used
-- this is because we used them to *undo* the permutation - so we performed the *inverse*
-- to get the permutation that led to xs, we have to take the inverse again, which we do by reversing


-- given a permutation of [1..n] (as a group elt), factor it into transpositions
toTranspositions :: (Num a, Enum a, Ord a) => Permutation a -> [SGen]
toTranspositions 1 = []
toTranspositions g = toTrans [i .^ (g^-1) | i <- [1..n] ] where
    n = maximum $ supp g
-- The reason we have g^-1 rather than g is that
-- i .^ g == j tells us that i ends up in the j position whereas
-- i .^ (g^-1) == j tells us that j is what ends up in the i position
-- Clearly it's the latter we want
-- For example, if g = s1 s2 = p [[1,3,2]], then the effect of applying g to [1,2,3] is [2,3,1]


-- toTranspositions . fromList == toTrans
-- fromTranspositions . toTranspositions == id
-- toTransposition . fromTranspositions == id (for reduced expressions only)


inversions :: (Num b, Enum b, Ord b) => Permutation b -> [(b, b)]
inversions g = [(i,j) | i <- [1..n], j <- [i+1..n], i .^ g > j .^ g]
    where n = maximum $ supp g

-- it's clear that the word length == number of inversions,
-- since both are equal to bubblesort distance
-- (well actually, need proof that expression returned by bubblesort is shortest, but it's fairly obvious

