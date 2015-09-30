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

  -- | Returns a list of length 2.
  edgeNodes :: et n -> [n]

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
                 . M.elems

-- Can't have a ToContext for (n, nl, [(n,[el])]) as we threw out the
-- Edge values.

-- -----------------------------------------------------------------------------

empty :: Graph et n nl el
empty = Gr M.empty M.empty minBound

isEmpty :: Graph et n nl el -> Bool
isEmpty = M.null . nodeMap

-- -----------------------------------------------------------------------------

type Matchable et n nl el ctxt = (ValidGraph et n
                                 ,FromContext ctxt
                                 ,ValidContext et n nl el ctxt
                                 )

match :: (ValidGraph et n) => n -> Graph et n nl el
         -> Maybe (Context (AdjType et) n nl el, Graph et n nl el)
match n g = getCtxt <$> M.lookup n nm
  where
    nm = nodeMap g
    em = edgeMap g

    getCtxt (nl,adj) = (ctxt, g')
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

matchAs :: (Matchable et n nl el ctxt) => n -> Graph et n nl el
           -> Maybe (ctxt, Graph et n nl el)
matchAs n = fmap (first fromContext) . match n

matchAny :: (ValidGraph et n) => Graph et n nl el
            -> Maybe (Context (AdjType et) n nl el, Graph et n nl el)
matchAny g
  | isEmpty g = Nothing
  | otherwise = flip match g . head . M.keys $ nodeMap g

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

mergeAs :: (Mergeable et n nl el ctxt) => ctxt -> Graph et n nl el
           -> Graph et n nl el
mergeAs = merge . toContext

-- -----------------------------------------------------------------------------

type ValidGraph et n = (Hashable n
                             ,Eq n
                             ,EdgeType et
                             )

insNode :: (ValidGraph et n) => n -> nl -> Graph et n nl el -> Graph et n nl el
insNode n l g = g { nodeMap = M.insert n (l, M.empty) (nodeMap g) }

insEdge :: (ValidGraph et n) => (n,n,el) -> Graph et n nl el
           -> (Edge, Graph et n nl el)
insEdge (u,v,l) g = (e, Gr nm' em' (succ e))
  where
    e = nextEdge g

    nm' = addE u . addE v $ nodeMap g

    addE = M.adjust (second $ M.insert e ())

    em' = M.insert e (mkEdge u v, l) (edgeMap g)

delNode :: (ValidGraph et n) => n -> Graph et n nl el -> Graph et n nl el
delNode n g = maybe g snd $ match n g

delEdge :: (ValidGraph et n) => Edge -> Graph et n nl el -> Graph et n nl el
delEdge e g = g { nodeMap = foldl' (flip delE) (nodeMap g) ens
                , edgeMap = M.delete e (edgeMap g)
                }
  where
    ens = maybe [] (edgeNodes . fst) (M.lookup e (edgeMap g))

    delE = M.adjust (second $ M.delete e)

-- TODO: care about directionality of edge.
delEdgeLabel :: (ValidGraph et n, Eq el) => (n,n,el) -> Graph et n nl el
                -> Graph et n nl el
delEdgeLabel (u,v,l) g
  | M.null es = g
  | otherwise = g { nodeMap = delEs u . delEs v $ nm
                  , edgeMap = em `M.difference` es
                  }
  where
    nm = nodeMap g

    em = edgeMap g

    es = maybe M.empty (M.filter isE . M.intersection em . snd) $ M.lookup u nm

    isE (et,el) = getNode (otherN u et) == v && el == l

    delEs = M.adjust (second (`M.difference`es))

delEdgesBetween :: (ValidGraph et n) => n -> n -> Graph et n nl el
                   -> Graph et n nl el
delEdgesBetween u v g
  | M.null es = g
  | otherwise = g { nodeMap = delEs u . delEs v $ nm
                  , edgeMap = em `M.difference` es
                  }
  where
    nm = nodeMap g
    em = edgeMap g
    es = maybe M.empty (M.filter isE . M.intersection em . snd) $ M.lookup u nm

    isE (et,_) = getNode (otherN u et) == v

    delEs = M.adjust (second (`M.difference`es))
