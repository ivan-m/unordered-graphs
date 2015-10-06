{-# LANGUAGE BangPatterns, ConstraintKinds, FlexibleContexts,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses,
             StandaloneDeriving, TupleSections #-}

{- |
   Module      : Data.Graph.Unordered.Algorithms.Clustering
   Description : Graph partitioning
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Graph.Unordered.Algorithms.Clustering where

import Data.Graph.Unordered
import Data.Graph.Unordered.Algorithms.Components
import Data.Graph.Unordered.Internal

import           Data.Bool           (bool)
import           Data.Function       (on)
import           Data.Hashable       (Hashable)
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.List           (delete, foldl', group, maximumBy, sort)
import           Data.Maybe          (fromMaybe)

-- -----------------------------------------------------------------------------

-- | Find communities in weighted graphs using the algorithm by
-- Blondel, Guillaume, Lambiotte and Lefebvre in their paper
-- <http://arxiv.org/abs/0803.0476 Fast unfolding of communities in large networks>.
bgll :: (ValidGraph et n, Fractional el) => Graph et n nl el -> [Graph et n nl el]
bgll g = undefined

data CGraph et n el = CG { comMap :: HashMap Community (Set [n])
                         , cGraph :: Graph et [n] Community el
                         }
                    deriving (Show, Read)

deriving instance (Eq n, Eq el, Eq (et [n])) => Eq (CGraph et n el)

newtype Community = C { getCommunity :: Word }
                  deriving (Eq, Ord, Show, Read, Enum, Bounded, Hashable)

type ValidC et n el = (ValidGraph et n, Fractional el, Ord el)

phaseOne :: (ValidC et n el) => Graph et [n] nl el -> Maybe (CGraph et n el)
phaseOne = recurseUntil moveAll . initCommunities

initCommunities :: (ValidC et n el) => Graph et [n] nl el -> CGraph et n el
initCommunities g = CG { comMap = cm
                       , cGraph = Gr { nodeMap  = nm'
                                     , edgeMap  = edgeMap g
                                     , nextEdge = nextEdge g
                                     }
                       }
  where
    nm = nodeMap g

    ((_,cm),nm') = mapAccumWithKeyL go (C minBound, HM.empty) nm

    go (!c,!cs) ns al = ( (succ c, HM.insert c (HM.singleton ns ()) cs)
                        , c <$ al
                        )

moveAll :: (ValidC et n el) => CGraph et n el -> Maybe (CGraph et n el)
moveAll cg = uncurry (bool Nothing . Just)
             $ foldl' go (cg,False) (nodes (cGraph cg))
  where
    go pr@(cg',_) = maybe pr (,True) . tryMove cg'

tryMove :: (ValidC et n el) => CGraph et n el -> [n] -> Maybe (CGraph et n el)
tryMove cg ns = moveTo <$> bestMove cg ns
  where
    cm = comMap cg
    g  = cGraph cg

    currentC = getC g ns

    currentCNs = cm HM.! currentC

    moveTo c = CG { comMap = HM.adjust (HM.insert ns ()) c cm'
                  , cGraph = nmapFor (const c) g ns
                  }
      where
        currentCNs' = HM.delete ns currentCNs

        cm' | HM.null currentCNs' = HM.delete currentC cm
            | otherwise           = HM.adjust (const currentCNs') currentC cm

bestMove :: (ValidC et n el) => CGraph et n el -> [n] -> Maybe Community
bestMove cg n
  | null vs    = Nothing
  | maxDQ <= 0 = Nothing
  | otherwise  = Just maxC
  where
    g = cGraph cg
    c = getC g n
    vs = neighbours g n
    cs = delete c . map head . group . sort . map (getC g) $ vs

    (maxC, maxDQ) = maximumBy (compare`on`snd)
                    . map ((,) <*> diffModularity cg n)
                    $ cs

getC :: (ValidC et n el) => Graph et [n] Community el -> [n] -> Community
getC g = fromMaybe (error "Node doesn't have a community!") . nlab g

-- This is the 𝝙Q function.  Assumed that @i@ is not within the community @c@.
diffModularity :: (ValidC et n el) => CGraph et n el -> [n] -> Community -> el
diffModularity cg i c = ((sumIn + kiIn)/m2 - sq ((sumTot + ki)/m2))
                        - (sumIn/m2 - sq (sumTot/m2) - sq (ki/m2))
  where
    g = cGraph cg
    nm = nodeMap g
    em = edgeMap g

    -- Nodes within the community
    cNs = fromMaybe HM.empty (HM.lookup c (comMap cg))

    -- Edges solely within the community
    cEMap = HM.filter (all (`HM.member`cNs) . edgeNodes . fst) em

    -- All edges incident with C
    incEs = HM.filter (any (`HM.member`cNs) . edgeNodes . fst) em

    -- Twice the weight of all edges in the graph (take into account both directions)
    m2 = eTot em

    -- Sum of weights of all edges within the community
    sumIn  = eTot cEMap
    -- Sum of weights of all edges incident with the community
    sumTot = eTot incEs

    iAdj = maybe HM.empty fst $ HM.lookup i nm

    ki   = kTot . HM.intersection em    $ iAdj
    kiIn = kTot . HM.intersection incEs $ iAdj

    -- 2* because the EdgeMap only contains one copy of each edge.
    eTot = (2*) . kTot

    kTot = (2*) . sum . map snd . HM.elems

    sq x = x * x

-- -----------------------------------------------------------------------------
-- StateL was copied from the source of Data.Traversable in base-4.8.1.0

mapAccumWithKeyL :: (a -> k -> v -> (a, y)) -> a -> HashMap k v -> (a, HashMap k y)
mapAccumWithKeyL f a m = runStateL (HM.traverseWithKey f' m) a
  where
    f' k v = StateL $ \s -> f s k v

-- left-to-right state transformer
newtype StateL s a = StateL { runStateL :: s -> (s, a) }

instance Functor (StateL s) where
    fmap f (StateL k) = StateL $ \ s -> let (s', v) = k s in (s', f v)

instance Applicative (StateL s) where
    pure x = StateL (\ s -> (s, x))
    StateL kf <*> StateL kv = StateL $ \ s ->
        let (s', f) = kf s
            (s'', v) = kv s'
        in (s'', f v)

-- -----------------------------------------------------------------------------

recurseUntil :: (a -> Maybe a) -> a -> Maybe a
recurseUntil f = fmap go . f
  where
    go a = maybe a go (f a)
