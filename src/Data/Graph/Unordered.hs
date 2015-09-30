{-# LANGUAGE ConstraintKinds, FlexibleContexts, FlexibleInstances,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             StandaloneDeriving, TupleSections, TypeFamilies, ViewPatterns #-}

{- |
   Module      : Data.Graph.Unordered
   Description : Graphs with Hashable nodes
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com

Known limitations:

* Loops might not work properly.

 -}
module Data.Graph.Unordered where

import           Control.Arrow         (first, second, (***))
import           Data.Function         (on)
import           Data.Functor.Identity
import           Data.Hashable
import           Data.HashMap.Strict   (HashMap)
import qualified Data.HashMap.Strict   as M
import           Data.List             (delete, foldl', groupBy, sortBy)
import           Data.Maybe            (listToMaybe)

-- -----------------------------------------------------------------------------

type DirGraph = Graph DirEdge

type UndirGraph = Graph UndirEdge

data Graph et n nl el = Gr { nodeMap  :: !(NodeMap n nl)
                           , edgeMap  :: !(EdgeMap n et el)
                           , nextEdge :: !Edge
                           }
                      deriving (Eq, Show, Read)

type NodeMap n    nl    = HashMap n    (nl, Adj)
type EdgeMap n et    el = HashMap Edge (et n, el)

newtype Edge = Edge { unEdge :: Word }
             deriving (Eq, Ord, Show, Read, Hashable, Enum, Bounded)

type Set n = HashMap n ()

-- How to deal with loops?
type Adj = Set Edge

toAdj :: [Edge] -> Adj
toAdj = M.fromList . map (,())

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

class (NodeFrom (AdjType et)) => EdgeType et where
  type AdjType et :: * -> *

  mkEdge :: n -> n -> et n

  -- | Assumes @n@ is one of the end points of this edge.
  otherN :: (Eq n) => n -> et n -> AdjType et n

  toEdge :: n -> AdjType et n -> et n

class NodeFrom at where
  getNode :: at n -> n

instance NodeFrom Identity where
  getNode = runIdentity

data DirAdj n = ToNode   n
              | FromNode n
              deriving (Eq, Ord, Show, Read)

instance NodeFrom DirAdj where
  getNode (ToNode   n) = n
  getNode (FromNode n) = n

instance EdgeType DirEdge where
  type AdjType DirEdge = DirAdj

  mkEdge = DE

  -- How does this work with loops?  Repeat it?
  otherN n (DE u v)
    | n == u    = ToNode v
    | otherwise = FromNode u

  toEdge u (ToNode   v) = DE u v
  toEdge v (FromNode u) = DE u v

instance EdgeType UndirEdge where
  type AdjType UndirEdge = Identity

  mkEdge u v = UE [u,v]

  otherN n (UE vs) = Identity $ head (delete n vs)

  toEdge u (Identity v) = UE [u,v]

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
                 . M.elems

-- Can't have a ToContext for (n, nl, [(n,[el])]) as we threw out the
-- Edge values.

-- -----------------------------------------------------------------------------

empty :: Graph et n nl el
empty = Gr M.empty M.empty minBound

isEmpty :: Graph et n nl el -> Bool
isEmpty = M.null . nodeMap

-- -----------------------------------------------------------------------------

type Matchable et n nl el ctxt = (Hashable n
                                 ,Eq n
                                 ,EdgeType et
                                 ,FromContext ctxt
                                 ,ValidContext et n nl el ctxt
                                 )

match :: (Matchable et n nl el ctxt) => n -> Graph et n nl el
         -> Maybe (ctxt, Graph et n nl el)
match n g = getCtxt <$> M.lookup n nm
  where
    nm = nodeMap g
    em = edgeMap g

    getCtxt (nl,adj) = (fromContext ctxt, g')
      where
        ctxt = Ctxt n nl adjM
        -- TODO: what about loops? will only appear once here...
        adjM = M.map (first $ otherN n) (M.intersection em adj)

        g' = g { nodeMap = nm'
               , edgeMap = em'
               }

        em' = em `M.difference` adj

        adjNs = filter (/=n) -- take care of loops
                . map (getNode . fst)
                $ M.elems adjM
        nm' = foldl' (flip $ M.adjust (second (`M.difference`adj)))
                     (M.delete n nm)
                     adjNs

matchAny :: (Matchable et n nl el ctxt) => Graph et n nl el
            -> Maybe (ctxt, Graph et n nl el)
matchAny g
  | isEmpty g = Nothing
  | otherwise = flip match g . head . M.keys $ nodeMap g

-- -----------------------------------------------------------------------------

type Mergeable et n nl el ctxt = (Hashable n
                                 ,Eq n
                                 ,EdgeType et
                                 ,ToContext ctxt
                                 ,ValidContext et n nl el ctxt
                                 )

-- Assumes edge identifiers are valid
merge :: (Mergeable et n nl el ctxt) => ctxt -> Graph et n nl el
         -> Graph et n nl el
merge (toContext -> ctxt) g = Gr nm' em' nextE'
  where
    n = cNode ctxt

    adjM = cAdj ctxt

    adj = () <$ adjM

    -- Need to do M.unionWith concat or something

    nAdj = M.toList
           . foldl' (M.unionWith M.union) M.empty
           . map (uncurry (flip M.singleton) . ((`M.singleton` ()) *** getNode . fst))
           . M.toList
           $ adjM

    -- Can we blindly assume that max == last ?
    maxCE = fmap succ . listToMaybe . sortBy (flip compare) . M.keys $ adjM

    nextE = nextEdge g
    nextE' = maybe nextE (max nextE) maxCE

    em = edgeMap g
    em' = em `M.union` M.map (first $ toEdge n) adjM

    nm = nodeMap g
    nm' = foldl' (\m (v,es) -> M.adjust (second (`M.union`es)) v m)
                 (M.insert n (cLabel ctxt,adj) nm)
                 nAdj
