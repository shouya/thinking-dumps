module KOpt (algKOpt) where

-- unlike any-opt, this is a dynamic algorithm which employs great efficiency
-- and effect by incrementally looking for edges to swapping and dynamically
-- selecting the number of k for the best solution.


import TSPLib
import NearestNeighbor

import Data.List
import Data.Function
import Data.Maybe
import Data.Functor

import Debug.Trace

algKOpt :: TSPAlgorithm
algKOpt ns = pathToEdges $ fromMaybe prilimiary final
  where prilimiary = tracePath1' $ algNearestNeighbor ns
        allSteps = iterateM iterationStep (return prilimiary)
        steps    = sequence $ takeWhile isJust allSteps
        final    = last <$> steps


bestTour :: [Path] -> Path
bestTour = minimumBy (compare `on` pathLength)

-- tour must NOT include n
closestTo :: Node -> Path -> Maybe (Node, Node)
closestTo n tour = if fst result == n
                   then Nothing
                   else Just result
  where predPairs = zip (n:tour) (init tour)
        dist      = distance n . snd
        result    = minimumBy (compare `on` dist) predPairs

rearrangeTour :: Path -> Node -> Node -> Path
rearrangeTour tour@(t1:t2:_) t1' t2'
  | t1 /= t1' = error "invalid tour given"
  | t1 == t1' && t2 == t2' = tour
  | t1 == t1' && t2 /= t2' = reverse tour

rotateRoundPath :: Path -> Path
rotateRoundPath = wrapPathEnds . tail

tweakable :: Path -> Bool
tweakable (t1:t2:ts) =
  case closestTo t2 ts of
   Nothing     -> False
   Just (t3,_) -> distance t2 t3 < distance t1 t2

iterateM :: (Monad m) => (a -> m a) -> m a -> [m a]
iterateM f ma = ma : iterateM f (ma >>= f)

emptyListToNothing :: Maybe [a] -> Maybe [a]
emptyListToNothing m = m >>= foo
  where foo [] = Nothing
        foo xs = return xs

iterationStep :: Path -> Maybe Path
iterationStep tour = result >>= notUnchanged
  where numNodes       = length tour
        rotatedPaths   = take numNodes $ iterate rotateRoundPath tour
        tweakableTours = dropWhile (not . tweakable) rotatedPaths
        chosenTour     = listToMaybe tweakableTours
        incKOptTours   = iterateM swapStep chosenTour
        validKOptTours = sequence $ takeWhile isJust incKOptTours
        result         = bestTour . (tour:) <$> validKOptTours
        notUnchanged t = if t == tour then Nothing else return t

swapStep :: Path -> Maybe Path
swapStep tour = nextTour
  where (t1:t2:ts) = tour
        nextTour   = do
          (t4,t3) <- closestTo t2 ts
          let tourEdges = traceEdges $ pathToEdges tour
              tmpEdges  = traceEdges $ [(t1, t4), (t2, t3)] ++
                          (tourEdges \\ [(t4, t3), (t1, t2)])
              tourPath  = tracePath' tmpEdges t1
            in return $ rearrangeTour tourPath t1 t4
