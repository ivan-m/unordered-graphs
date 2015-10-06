{-# LANGUAGE ConstraintKinds, FlexibleContexts, FlexibleInstances,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             StandaloneDeriving, TupleSections, TypeFamilies #-}

{- |
   Module      : Data.Graph.Unordered
   Description : Graphs with Hashable nodes
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com

Known limitations:

* Adding edges might not be the same depending on graph construction
  (if you add then delete a lot of edges, then the next new edge might
  be higher than expected).

 -}
module Data.Graph.Unordered
  ( -- * Graph datatype
    Graph
  , DirGraph
  , UndirGraph
  , ValidGraph
    -- ** Edge types
  , Edge (..)
  , DirEdge (..)
  , UndirEdge (..)
  , EdgeType (..)
  , NodeFrom (..)
  , DirAdj (..)
  , Identity (..)
    -- ** Graph Context
  , Context (..)
  , AdjLookup
  , Contextual (..)
  , ValidContext
  , FromContext (..)
  , ToContext (..)

    -- * Graph functions
    -- ** Graph Information
  , isEmpty

    -- *** Node information
  , order
  , ninfo
  , nodes
  , nodeDetails
  , lnodes

    -- *** Edge information
  , size
  , einfo
  , edges
  , edgeDetails
  , ledges
  , edgePairs
  , ledgePairs

    -- ** Graph construction
  , empty
  , mkGraph
  , buildGr
  , insNode
  , insEdge
    -- *** Merging
  , Mergeable
  , merge
  , mergeAs

    -- ** Graph deconstruction
  , delNode
  , delEdge
  , delEdgeLabel
  , delEdgesBetween
    -- *** Matching
  , Matchable
  , match
  , matchAs
  , matchAny
  , matchAnyAs

    -- ** Manipulation
  , nmap
  , emap
  ) where

import Data.Graph.Unordered.Internal

import           Control.Arrow         (first, second)
import           Data.Function         (on)
import           Data.Functor.Identity
import           Data.HashMap.Strict   (HashMap)
import qualified Data.HashMap.Strict   as HM
import           Data.List             (delete, foldl', groupBy, sortBy)
import           Data.Maybe            (listToMaybe)

-- -----------------------------------------------------------------------------

type DirGraph = Graph DirEdge

type UndirGraph = Graph UndirEdge

type AdjLookup n el = HashMap Edge (n,el)

-- -----------------------------------------------------------------------------

data DirEdge n = DE { fromNode :: !n
                    , toNode   :: !n
                    }
               deriving (Eq, Ord, Show, Read)

-- 2-element set
-- INVARIANT: always has length == 2.
-- TODO: compare against using a simple tuple.
newtype UndirEdge n = UE { ueElem :: [n] }
                    deriving (Eq, Ord, Show, Read)

data DirAdj n = ToNode   n
              | FromNode n
              deriving (Eq, Ord, Show, Read)

instance NodeFrom DirAdj where
  getNode (ToNode   n) = n
  getNode (FromNode n) = n

-- | Note that for loops, the result of 'otherN' will always be a
-- 'ToNode'.
instance EdgeType DirEdge where
  type AdjType DirEdge = DirAdj

  mkEdge = DE

  otherN n (DE u v)
    | n == u    = ToNode v
    | otherwise = FromNode u

  toEdge u (ToNode   v) = DE u v
  toEdge v (FromNode u) = DE u v

  edgeNodes (DE u v) = [u,v]

instance EdgeType UndirEdge where
  type AdjType UndirEdge = Identity

  mkEdge u v = UE [u,v]

  otherN n (UE vs) = Identity $ head (delete n vs)

  toEdge u (Identity v) = UE [u,v]

  edgeNodes = ueElem

-- -----------------------------------------------------------------------------

data Context at n nl el = Ctxt { cNode  :: !n
                               , cLabel :: !nl
                               , cAdj   :: !(AdjLookup (at n) el)
                               }

deriving instance (Eq n,   Eq nl,   Eq el,   Eq   (at n)) => Eq   (Context at n nl el)
deriving instance (Show n, Show nl, Show el, Show (at n)) => Show (Context at n nl el)
deriving instance (Read n, Read nl, Read el, Read (at n)) => Read (Context at n nl el)

class Contextual ctxt where
  type CNode   ctxt :: *
  type CAType  ctxt :: * -> *
  type CNLabel ctxt :: *
  type CELabel ctxt :: *

type ValidContext et n nl el ctxt = (Contextual ctxt
                                    ,n ~ CNode ctxt
                                    ,AdjType et ~ CAType ctxt
                                    ,nl ~ CNLabel ctxt
                                    ,el ~ CELabel ctxt
                                    )

instance Contextual (Context at n nl el) where
  type CNode   (Context at n nl el) = n
  type CAType  (Context at n nl el) = at
  type CNLabel (Context at n nl el) = nl
  type CELabel (Context at n nl el) = el

class (Contextual ctxt) => FromContext ctxt where

  fromContext :: Context (CAType ctxt) (CNode ctxt) (CNLabel ctxt) (CELabel ctxt)
                 -> ctxt

-- This isn't quite right: have to work out what to do with Edge identifiers.
class (Contextual ctxt) => ToContext ctxt where

  toContext :: ctxt -> Context (CAType ctxt) (CNode ctxt) (CNLabel ctxt) (CELabel ctxt)

instance FromContext (Context at n nl el) where
  fromContext = id

instance ToContext (Context at n nl el) where
  toContext   = id

instance Contextual (n, nl, AdjLookup (at n) el) where
  type CNode   (n, nl, AdjLookup (at n) el) = n
  type CAType  (n, nl, AdjLookup (at n) el) = at
  type CNLabel (n, nl, AdjLookup (at n) el) = nl
  type CELabel (n, nl, AdjLookup (at n) el) = el

instance FromContext (n, nl, AdjLookup (at n) el) where
  fromContext (Ctxt n nl adj) = (n,nl,adj)

instance ToContext (n, nl, AdjLookup (at n) el) where
  toContext (n,nl,adj) = Ctxt n nl adj

instance Contextual (n, nl, [(n,[el])]) where
  type CNode   (n, nl, [(n,[el])]) = n
  type CAType  (n, nl, [(n,[el])]) = AdjType UndirEdge
  type CNLabel (n, nl, [(n,[el])]) = nl
  type CELabel (n, nl, [(n,[el])]) = el

instance (Ord n) => FromContext (n, nl, [(n,[el])]) where
  fromContext ctxt = (cNode ctxt
                     ,cLabel ctxt
                     ,toLookup (cAdj ctxt))
    where
      toLookup = map (\cels -> (fst (head cels), map snd cels))
                 . groupBy ((==) `on` fst)
                 . sortBy (compare `on` fst)
                 . map (first runIdentity)
                 . HM.elems

-- Can't have a ToContext for (n, nl, [(n,[el])]) as we threw out the
-- Edge values.

-- -----------------------------------------------------------------------------

empty :: Graph et n nl el
empty = Gr HM.empty HM.empty minBound

isEmpty :: Graph et n nl el -> Bool
isEmpty = HM.null . nodeMap

-- | Number of nodes
order :: Graph et n nl el -> Int
order = HM.size . nodeMap

-- | Number of edges
size :: Graph et n nl el -> Int
size = HM.size . edgeMap

-- | Assumes the Contexts describe a graph in total, with the
-- outermost one first (i.e. @buildGr (c:cs) == c `merge` buildGr
-- cs@).
buildGr :: (ValidGraph et n) => [Context (AdjType et) n nl el] -> Graph et n nl el
buildGr = foldr merge empty

ninfo :: (ValidGraph et n) => Graph et n nl el -> n -> Maybe ([Edge], nl)
ninfo g = fmap (first HM.keys) . (`HM.lookup` nodeMap g)

einfo :: (ValidGraph et n) => Graph et n nl el -> Edge -> Maybe (et n, el)
einfo g = (`HM.lookup` edgeMap g)

nodes :: Graph et n nl el -> [n]
nodes = HM.keys . nodeMap

-- -----------------------------------------------------------------------------

type Matchable et n nl el ctxt = (ValidGraph et n
                                 ,FromContext ctxt
                                 ,ValidContext et n nl el ctxt
                                 )

-- | Note that for any loops, the resultant edge will only appear once
-- in the output 'cAdj' field.
match :: (ValidGraph et n) => n -> Graph et n nl el
         -> Maybe (Context (AdjType et) n nl el, Graph et n nl el)
match n g = getCtxt <$> HM.lookup n nm
  where
    nm = nodeMap g
    em = edgeMap g

    getCtxt (adj,nl) = (ctxt, g')
      where
        ctxt = Ctxt n nl adjM

        -- Note that loops will only appear once here.
        adjM = HM.map (first $ otherN n) (HM.intersection em adj)

        g' = g { nodeMap = nm'
               , edgeMap = em'
               }

        em' = em `HM.difference` adj

        adjNs = filter (/=n) -- take care of loops
                . map (getNode . fst)
                $ HM.elems adjM
        nm' = foldl' (flip $ HM.adjust (first (`HM.difference`adj)))
                     (HM.delete n nm)
                     adjNs

matchAs :: (Matchable et n nl el ctxt) => n -> Graph et n nl el
           -> Maybe (ctxt, Graph et n nl el)
matchAs n = fmap (first fromContext) . match n

matchAny :: (ValidGraph et n) => Graph et n nl el
            -> Maybe (Context (AdjType et) n nl el, Graph et n nl el)
matchAny g
  | isEmpty g = Nothing
  | otherwise = flip match g . head . HM.keys $ nodeMap g

matchAnyAs :: (Matchable et n nl el ctxt) => Graph et n nl el
              -> Maybe (ctxt, Graph et n nl el)
matchAnyAs = fmap (first fromContext) . matchAny

-- -----------------------------------------------------------------------------

type Mergeable et n nl el ctxt = (ValidGraph et n
                                 ,ToContext ctxt
                                 ,ValidContext et n nl el ctxt
                                 )

-- Assumes edge identifiers are valid
merge :: (ValidGraph et n) => Context (AdjType et) n nl el
         -> Graph et n nl el -> Graph et n nl el
merge ctxt g = Gr nm' em' nextE'
  where
    n = cNode ctxt

    adjM = cAdj ctxt

    adj = HM.map (adjCount n . getNode . fst) adjM

    nAdj = HM.toList
           . foldl' (HM.unionWith HM.union) HM.empty
           . map (uncurry toNAdj)
           . HM.toList
           $ adjM

    toNAdj e (av,_) = let v = getNode av
                      in HM.singleton v (HM.singleton e (adjCount n v))

    -- Can we blindly assume that max == last ?
    maxCE = fmap succ . listToMaybe . sortBy (flip compare) . HM.keys $ adjM

    nextE = nextEdge g
    nextE' = maybe nextE (max nextE) maxCE

    em = edgeMap g
    em' = em `HM.union` HM.map (first $ toEdge n) adjM

    nm = nodeMap g
    nm' = foldl' (\m (v,es) -> HM.adjust (first (`HM.union`es)) v m)
                 (HM.insert n (adj,cLabel ctxt) nm)
                 nAdj

mergeAs :: (Mergeable et n nl el ctxt) => ctxt -> Graph et n nl el
           -> Graph et n nl el
mergeAs = merge . toContext

-- -----------------------------------------------------------------------------

insNode :: (ValidGraph et n) => n -> nl -> Graph et n nl el -> Graph et n nl el
insNode n l g = g { nodeMap = HM.insert n (HM.empty, l) (nodeMap g) }

insEdge :: (ValidGraph et n) => (n,n,el) -> Graph et n nl el
           -> (Edge, Graph et n nl el)
insEdge (u,v,l) g = (e, Gr nm' em' (succ e))
  where
    e = nextEdge g

    nm' = addE u . addE v $ nodeMap g

    addE = HM.adjust (first $ HM.insert e (adjCount u v))

    em' = HM.insert e (mkEdge u v, l) (edgeMap g)

delNode :: (ValidGraph et n) => n -> Graph et n nl el -> Graph et n nl el
delNode n g = maybe g snd $ match n g

delEdge :: (ValidGraph et n) => Edge -> Graph et n nl el -> Graph et n nl el
delEdge e g = g { nodeMap = foldl' (flip delE) (nodeMap g) ens
                , edgeMap = HM.delete e (edgeMap g)
                }
  where
    ens = maybe [] (edgeNodes . fst) (HM.lookup e (edgeMap g))

    delE = HM.adjust (first $ HM.delete e)

-- TODO: care about directionality of edge.
delEdgeLabel :: (ValidGraph et n, Eq el) => (n,n,el) -> Graph et n nl el
                -> Graph et n nl el
delEdgeLabel (u,v,l) g
  | HM.null es = g
  | otherwise = g { nodeMap = delEs u . delEs v $ nm
                  , edgeMap = em `HM.difference` es
                  }
  where
    nm = nodeMap g

    em = edgeMap g

    es = maybe HM.empty (HM.filter isE . HM.intersection em . fst) $ HM.lookup u nm

    isE (et,el) = getNode (otherN u et) == v && el == l

    delEs = HM.adjust (first (`HM.difference`es))

delEdgesBetween :: (ValidGraph et n) => n -> n -> Graph et n nl el
                   -> Graph et n nl el
delEdgesBetween u v g
  | HM.null es = g
  | otherwise = g { nodeMap = delEs u . delEs v $ nm
                  , edgeMap = em `HM.difference` es
                  }
  where
    nm = nodeMap g
    em = edgeMap g
    es = maybe HM.empty (HM.filter isE . HM.intersection em . fst) $ HM.lookup u nm

    isE (et,_) = getNode (otherN u et) == v

    delEs = HM.adjust (first (`HM.difference`es))

-- -----------------------------------------------------------------------------

nmap :: (ValidGraph et n) => (nl -> nl') -> Graph et n nl el -> Graph et n nl' el
nmap f g = g { nodeMap = HM.map (second f) (nodeMap g) }

emap :: (ValidGraph et n) => (el -> el') -> Graph et n nl el -> Graph et n nl el'
emap f g = g { edgeMap = HM.map (second f) (edgeMap g) }
