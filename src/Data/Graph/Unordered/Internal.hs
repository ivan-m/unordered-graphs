{-# LANGUAGE ConstraintKinds, FlexibleContexts, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, TypeFamilies #-}

{- |
   Module      : Data.Graph.Unordered.Internal
   Description : Internal data definition
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Graph.Unordered.Internal where

import           Control.Arrow         (first, second)
import           Data.Functor.Identity
import           Data.Hashable         (Hashable)
import           Data.HashMap.Strict   (HashMap)
import qualified Data.HashMap.Strict   as HM
import           Data.List             (foldl')

-- -----------------------------------------------------------------------------

data Graph et n nl el = Gr { nodeMap  :: !(NodeMap n nl)
                           , edgeMap  :: !(EdgeMap et n el)
                           , nextEdge :: !Edge
                           }

-- NOTE: we don't include nextEdge in equality tests.
instance (Eq (et n), Eq n, Eq nl, Eq el) => Eq (Graph et n nl el) where
  g1 == g2 =    nodeMap g1 == nodeMap g2
             && edgeMap g1 == edgeMap g2

instance (EdgeType et, Show n, Show nl, Show el) => Show (Graph et n nl el) where
  showsPrec d g = showParen (d > 10) $
                    showString "mkGraph "
                    . shows (lnodes g)
                    . showString " "
                    . shows (ledgePairs g)

instance (ValidGraph et n, Read n, Read nl, Read el) => Read (Graph et n nl el) where
  readsPrec p = readParen (p > 10) $ \r -> do
    ("mkGraph", s) <- lex r
    (ns,t) <- reads s
    (es,u) <- reads t
    return (mkGraph ns es, u)

type NodeMap    n nl    = HashMap n    (Adj, nl)
type EdgeMap et n    el = HashMap Edge (et n, el)

newtype Edge = Edge { unEdge :: Word }
             deriving (Eq, Ord, Show, Read, Hashable, Enum, Bounded)

type Set n = HashMap n ()

-- The Int value is used for how many times that edge is attached to
-- the node: 1 for normal edges, 2 for loops.
--
-- If we change this to being a list, then the Eq instance for Graph can't be derived.
type Adj = HashMap Edge Int

adjCount :: (Eq n) => n -> n -> Int
adjCount u v
  | u == v    = 2
  | otherwise = 1

type ValidGraph et n = (Hashable n
                       ,Eq n
                       ,EdgeType et
                       )

-- | Assumes all nodes are in the node list.
mkGraph :: (ValidGraph et n) => [(n,nl)] -> [(n,n,el)] -> Graph et n nl el
mkGraph nlk elk = Gr nM eM nextE
  where
    addEs = zip [minBound..] elk

    eM = HM.fromList . map (second toE) $ addEs
    toE (u,v,el) = (mkEdge u v, el)

    adjs = foldl' (HM.unionWith HM.union) HM.empty (concatMap toAdjM addEs)
    toAdjM (e,(u,v,_)) = [toA u, toA v]
      where
        toA n = HM.singleton n (HM.singleton e (adjCount u v))

    nM = HM.mapWithKey (\n nl -> (HM.lookupDefault HM.empty n adjs, nl))
                      (HM.fromList nlk)

    -- TODO: can this be derived more efficiently?  Consider defining
    -- an alternate definition of zip...
    nextE
      | null addEs = minBound
      | otherwise  = succ . fst $ last addEs

-- -----------------------------------------------------------------------------

class (NodeFrom (AdjType et)) => EdgeType et where
  type AdjType et :: * -> *

  mkEdge :: n -> n -> et n

  -- | Assumes @n@ is one of the end points of this edge.
  otherN :: (Eq n) => n -> et n -> AdjType et n

  toEdge :: n -> AdjType et n -> et n

  -- | Returns a list of length 2.
  edgeNodes :: et n -> [n]

class NodeFrom at where
  getNode :: at n -> n

instance NodeFrom Identity where
  getNode = runIdentity

-- -----------------------------------------------------------------------------

nodeDetails :: Graph et n nl el -> [(n, ([Edge], nl))]
nodeDetails = map (second (first (concatMap (uncurry $ flip replicate) . HM.toList)))
              . HM.toList . nodeMap

lnodes :: Graph et n nl el -> [(n,nl)]
lnodes = map (second snd) . nodeDetails

edges :: Graph et n nl el -> [Edge]
edges = HM.keys . edgeMap

edgeDetails :: Graph et n nl el -> [(Edge, (et n, el))]
edgeDetails = HM.toList . edgeMap

ledges :: Graph et n nl el -> [(Edge, el)]
ledges = map (second snd) . edgeDetails

edgePairs :: (EdgeType et) => Graph et n nl el -> [(n, n)]
edgePairs = map (ePair . fst) . HM.elems . edgeMap
  where
    ePair et = let [u,v] = edgeNodes et
               in (u,v)

ledgePairs :: (EdgeType et) => Graph et n nl el -> [(n,n,el)]
ledgePairs = map eTriple . HM.elems . edgeMap
  where
    eTriple (et,el) = let [u,v] = edgeNodes et
                      in (u,v,el)
