{- |
   Module      : Data.Graph.Unordered.Algorithms.Components
   Description : Connected components
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Graph.Unordered.Algorithms.Components where

import Data.Graph.Unordered

import Data.List (unfoldr)

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
getComponentFrom c g = undefined
