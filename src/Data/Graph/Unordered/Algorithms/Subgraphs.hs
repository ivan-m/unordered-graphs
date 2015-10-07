{-# LANGUAGE MultiParamTypeClasses #-}

{- |
   Module      : Data.Graph.Unordered.Algorithms.Subgraphs
   Description : Functions dealing with sub-graphs
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Graph.Unordered.Algorithms.Subgraphs where

import Data.Graph.Unordered.Internal

import           Control.Arrow       (first)
import           Data.Function       (on)
import qualified Data.HashMap.Strict as HM

-- -----------------------------------------------------------------------------

subgraph :: (ValidGraph et n) => Graph et n nl el -> [n] -> Graph et n nl el
subgraph g ns = g { nodeMap = nm', edgeMap = em' }
  where
    nsS = mkSet ns

    em' = HM.filter (all (`HM.member` nsS) . edgeNodes . fst) (edgeMap g)

    nm' = HM.map (first (`HM.intersection`em')) . (`HM.intersection`nsS) $ nodeMap g

isSubGraphOf :: (ValidGraph et n, Eq (et n), Eq nl, Eq el)
                => Graph et n nl el -> Graph et n nl el -> Bool
isSubGraphOf gs g = isSubOn nodeMap && isSubOn edgeMap
  where
    isSubOn f = (isSub`on`f) gs g

    isSub ms m = ms == (m `HM.intersection` ms)
