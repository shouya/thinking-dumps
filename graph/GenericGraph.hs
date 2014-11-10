{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module GenericGraph
       (module GenericGraph,
        Ix,
       ) where

import Data.List (union, nub)
import qualified Data.Array as Array (bounds)
import Data.Array hiding (bounds)

import GraphClass

type Bounds v = (v, v)
type Edge   v = (v, v)

newtype GenericGraph v = GenericGraph { runGenericGraph :: Array v [v] }

instance (Ix v, Show v) => Show (GenericGraph v) where
  show (GenericGraph x) = show x

buildG :: (Ix v) => Bounds v -> [Edge v] -> GenericGraph v
buildG bounds edges' = GenericGraph $ array bounds vertexmap
  where edges = nub edges'
        vertices = (map fst edges) `union` (map snd edges)
        vertexmap = zip vertices (map connected vertices)
        connected v = map snd $ filter ((== v) . fst) edges

bounds :: (Ix v) => GenericGraph v -> Bounds v
bounds = Array.bounds . runGenericGraph

instance Ix n => Node n

instance Ix n => Graph GenericGraph n where
  adjacentNodes g v =  (runGenericGraph g) ! v

instance Ix n => FiniteGraph GenericGraph n where
  allNodes = indices . runGenericGraph
