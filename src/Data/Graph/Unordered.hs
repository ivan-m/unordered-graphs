{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             StandaloneDeriving, TypeFamilies #-}

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

import           Control.Arrow         (first)
import           Data.Function         (on)
import           Data.Functor.Identity
import           Data.Hashable
import           Data.HashMap.Strict   (HashMap)
import qualified Data.HashMap.Strict   as M
import           Data.List             (delete)
import           Data.List             (groupBy, sortBy)

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

class EdgeType et where
  type AdjType et :: * -> *

  mkEdge :: n -> n -> et n

  -- | Assumes @n@ is one of the end points of this edge.
  otherN :: (Eq n) => n -> et n -> AdjType et n

data DirAdj n = ToNode   n
              | FromNode n
              deriving (Eq, Ord, Show, Read)

instance EdgeType DirEdge where
  type AdjType DirEdge = DirAdj

  mkEdge = DE

  -- How does this work with loops?  Repeat it?
  otherN n (DE u v)
    | n == u    = ToNode v
    | otherwise = FromNode u

instance EdgeType UndirEdge where
  type AdjType UndirEdge = Identity

  mkEdge u v = UE [u,v]

  otherN n (UE vs) = Identity $ head (delete n vs)

-- -----------------------------------------------------------------------------

data Context n at nl el = Ctxt { cNode  :: !n
                               , cLabel :: !nl
                               , cAdj   :: !(AdjLookup (at n) el)
                               }

deriving instance (Eq n,   Eq nl,   Eq el,   Eq   (at n)) => Eq   (Context n at nl el)
deriving instance (Show n, Show nl, Show el, Show (at n)) => Show (Context n at nl el)
deriving instance (Read n, Read nl, Read el, Read (at n)) => Read (Context n at nl el)

class Contextual ctxt where
  type CNode   ctxt :: *
  type CAType  ctxt :: * -> *
  type CNLabel ctxt :: *
  type CELabel ctxt :: *

class (Contextual ctxt) => FromContext ctxt where

  fromContext :: Context (CNode ctxt) (CAType ctxt) (CNLabel ctxt) (CELabel ctxt)
                 -> ctxt

-- This isn't quite right: have to work out what to do with Edge identifiers.
class (Contextual ctxt) => ToContext ctxt where

  toContext :: ctxt -> Context (CNode ctxt) (CAType ctxt) (CNLabel ctxt) (CELabel ctxt)

instance Contextual (Context n et nl el) where
  type CNode   (Context n et nl el) = n
  type CAType  (Context n et nl el) = et
  type CNLabel (Context n et nl el) = nl
  type CELabel (Context n et nl el) = el

instance FromContext (Context n et nl el) where
  fromContext = id

instance ToContext (Context n et nl el) where
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

match :: (Hashable n, EdgeType et, Contextual ctxt) => n -> Graph n et nl el
         -> Maybe (Context n (AdjType et) nl el)
