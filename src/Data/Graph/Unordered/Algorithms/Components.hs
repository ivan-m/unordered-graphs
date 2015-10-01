{- |
   Module      : Data.Graph.Unordered.Algorithms.Components
   Description : Connected components
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Graph.Unordered.Algorithms.Components where

import           Data.Graph.Unordered

import           Control.Arrow (first)
import qualified Data.DList as DL
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.List (unfoldr,mapAccumL)
import           Data.Maybe (catMaybes)
import           Data.Tuple (swap)

-- -----------------------------------------------------------------------------

-- | Calculate connected components of a graph; edge directionality
-- doesn't matter.
components :: (ValidGraph et n) => Graph et n nl el -> [Graph et n nl el]
components = unfoldr getComponent

getComponent :: (ValidGraph et n) => Graph et n nl el
                -> Maybe (Graph et n nl el, Graph et n nl el)
getComponent g = uncurry getComponentFrom <$> matchAny g

getComponentFrom :: (ValidGraph et n) => Context (AdjType et) n nl el
                    -> Graph et n nl el -> (Graph et n nl el, Graph et n nl el)
getComponentFrom c = first (buildGr . (c:) . DL.toList)
                     . step (HS.singleton (cNode c)) (HS.fromList (adjN c))
  where
    step vis toVis g
      | HS.null toVis = (mempty,g)
      | otherwise     = first (DL.fromList cs`DL.append`) (step vis' toVis' g')
      where
        (g',mcs) = mapAccumL getC g (HS.toList toVis)

        cs = catMaybes mcs

        -- smaller set should be first for good performance
        vis' = toVis `HS.union` vis

        toVis' = (`HS.difference`vis')
                 . HS.fromList
                 . concatMap adjN
                 $ cs

    getC g n = maybe (g,Nothing) (swap . first Just) (match n g)
    adjN = map (getNode . fst) . HM.elems . cAdj
