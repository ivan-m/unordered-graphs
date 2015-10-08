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
module Data.Graph.Unordered.Algorithms.Clustering
  (bgll
  ,EdgeMergeable
  ) where

import Data.Graph.Unordered
import Data.Graph.Unordered.Internal

import           Control.Arrow       (first, (***))
import           Control.Monad       (void)
import           Data.Bool           (bool)
import           Data.Function       (on)
import           Data.Hashable       (Hashable)
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.List           (delete, foldl', foldl1', group, maximumBy,
                                      sort)
import           Data.Maybe          (fromMaybe, mapMaybe)
import           Data.Proxy          (Proxy (Proxy))

-- -----------------------------------------------------------------------------

-- | Find communities in weighted graphs using the algorithm by
-- Blondel, Guillaume, Lambiotte and Lefebvre in their paper
-- <http://arxiv.org/abs/0803.0476 Fast unfolding of communities in large networks>.
bgll :: (ValidGraph et n, EdgeMergeable et, Fractional el, Ord el)
        => Graph et n nl el -> [[n]]
bgll g = maybe [nodes g] nodes (recurseUntil pass g')
  where
    pass = fmap phaseTwo . phaseOne

    -- HashMap doesn't allow directly mapping the keys
    g' = Gr { nodeMap  = HM.fromList . map ((: []) *** void) . HM.toList $ nodeMap g
            , edgeMap  = HM.map (first (fmap (: []))) (edgeMap g)
            , nextEdge = nextEdge g
            }

data CGraph et n el = CG { comMap :: HashMap Community (Set [n])
                         , cGraph :: Graph et [n] Community el
                         }
                    deriving (Show, Read)

deriving instance (Eq n, Eq el, Eq (et [n])) => Eq (CGraph et n el)

newtype Community = C Word
                  deriving (Eq, Ord, Show, Read, Enum, Bounded, Hashable)

type ValidC et n el = (ValidGraph et n, EdgeMergeable et, Fractional el, Ord el)

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
  | null cs    = Nothing
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

phaseTwo :: (ValidC et n el) => CGraph et n el -> Graph et [n] () el
phaseTwo cg = mkGraph ns es
  where
    nsCprs = map ((,) <*> concat . HM.keys) . HM.elems $ comMap cg

    nsToC = HM.fromList . concatMap (\(vs,c) -> map (,c) (HM.keys vs)) $ nsCprs

    emNCs = HM.map (first (fmap (nsToC HM.!))) (edgeMap (cGraph cg))

    es = compressEdgeMap Proxy emNCs
    ns = map (,()) (map snd nsCprs)

    -- eM' = map toCE
    --       . groupBy ((==)`on`fst)
    --       . sortBy (compare`on`fst)
    --       . map (first edgeNodes)
    --       . HM.elems
    --       $ edgeMap (cGraph cg)

    -- d

    -- toCE es = let ([u,v],_) = head es
    --           in (u,v, sum (map snd es))

-- The resultant (n,n) pairings will be unique
compressEdgeMap :: (ValidC et n el) => Proxy et -> EdgeMap et [n] el -> [([n],[n],el)]
compressEdgeMap p em = concatMap (\(u,vels) -> map (uncurry $ mkE u) (HM.toList vels))
                                 (HM.toList esUndir)
  where
    -- Mapping on edge orders as created
    esDir = foldl1' (HM.unionWith (HM.unionWith (+)))
            . map ((\(u,v,el) -> HM.singleton u (HM.singleton v el)) . edgeTriple)
            $ HM.elems em

    esUndir = fst $ foldl' checkOpp (HM.empty, esDir) (HM.keys esDir)

    mkE u v el
      | el < 0    = (v,u,applyOpposite p el)
      | otherwise = (u,v,el)

    checkOpp (esU,esD) u
      | HM.null uVs = (esU , esD' )
      | otherwise   = (esU', esD'')
      where
        uVs = esD HM.! u
        -- So we don't worry about loops.
        esD' = HM.delete u esD

        uAdj = mapMaybe (\v -> fmap (v,) . HM.lookup u =<< (HM.lookup v esD'))
                        (HM.keys (esD' `HM.intersection` uVs))

        esD'' = foldl' (flip $ HM.adjust (HM.delete u)) esD' (map fst uAdj)

        uVs' = foldl' toE uVs uAdj
        toE m (v,el) = HM.insertWith (+) v (applyOpposite p el) m

        esU' = HM.insert u uVs' esU

class (EdgeType et) => EdgeMergeable et where
  applyOpposite :: (Fractional el) => Proxy et -> el -> el

instance EdgeMergeable DirEdge where
  applyOpposite _ = negate

instance EdgeMergeable UndirEdge where
  applyOpposite _ = id

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
