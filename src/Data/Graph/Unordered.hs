{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{- |
   Module      : Data.Graph.Unordered
   Description : Graphs with Hashable nodes
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Graph.Unordered where

import           Data.Hashable
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M

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

type Adj = [Edge]

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
  mkEdge :: n -> n -> et n

instance EdgeType DirEdge where
  mkEdge = DE

instance EdgeType UndirEdge where
  mkEdge u v = UE [u,v]
