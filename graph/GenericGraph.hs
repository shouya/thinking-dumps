
module GenericGraph
       (module GenericGraph,
        Ix,
       ) where

import Data.List (union)
import Data.Array hiding (bounds)
import qualified Data.Array as Array



type Bounds v = (v, v)
type Edge   v = (v, v)

newtype Graph v = Graph { unGraph :: Array v [v] }

instance (Ix v, Show v) => Show (Graph v) where
  show (Graph v) = show v

buildG :: (Ix v) => Bounds v -> [Edge v] -> Graph v
buildG bounds edges = Graph $ array bounds vertexmap
  where vertices = (map fst edges) `union` (map snd edges)
        vertexmap = zip vertices (map connected vertices)
        connected v = map snd $ filter ((== v) . fst) edges

bounds :: (Ix v) => Graph v -> Bounds v
bounds = Array.bounds . unGraph

edges :: (Ix v) => Graph v -> [Edge v]
edges = concat . map foo . assocs . unGraph
  where foo (v,vs) = map ((,) v) vs

adjacentVertices :: (Ix v) => Graph v -> v -> [v]
adjacentVertices g v = (unGraph g) ! v

edgesFor :: (Ix v) => v -> Graph v -> [Edge v]
edgesFor v g = map ((,) v) $ adjacentVertices g v
