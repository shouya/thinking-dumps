
module GenericGraph where

import Data.List (union)
import qualified Data.Array as Array (bounds)
import Data.Array hiding (bounds)


type Vertices v = [v]
type Bounds v = (v, v)
type Edge   v = (v, v)

newtype Graph v = Graph { unGraph :: Array v (Vertices v) }

instance (Ix v, Show v) => Show (Graph v) where
  show (Graph v) = show v

buildG :: (Ix v) => Bounds v -> [Edge v] -> Graph v
buildG bounds edges = Graph $ array bounds vertexmap
  where vertices = (map fst edges) `union` (map snd edges)
        vertexmap = zip vertices (map connected vertices)
        connected v = map snd $ filter ((== v) . fst) edges

bounds :: (Ix v) => Graph v -> Bounds v
bounds = Array.bounds . unGraph
