{-# LANGUAGE TupleSections #-}

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
closesrTo :: Node -> Node -> Path -> [Node] -> Maybe (Node, Node)
closesrTo t1 t2 tour reservedNodes = result
  where predPairs = zip tour (tail tour)
        dist      = distance t2 . snd
        t1t2Dist  = distance t1 t2
        invalid x = dist x >= t1t2Dist || snd x `elem` reservedNodes
        result    = listToMaybe $ dropWhile invalid predPairs

rearrangeTour :: Path -> Node -> Node -> Path
rearrangeTour tour@(t1:t2:_) t1' t2'
  | t1 /= t1' = error "invalid tour given"
  | t1 == t1' && t2 == t2' = tour
  | t1 == t1' && t2 /= t2' = reverse tour

rotateRoundPath :: Path -> Path
rotateRoundPath = wrapPathEnds . tail

tweakable :: Path -> Bool
tweakable (t1:t2:ts) =
  case closesrTo t1 t2 ts [] of
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
        chosenTour     = (,[]) <$> listToMaybe tweakableTours
        incKOptTours   = iterateM swapStep chosenTour
        validKOptTours = sequence $ takeWhile isJust incKOptTours
        result         = bestTour . (tour:) . map fst <$> validKOptTours
        notUnchanged t = if t == tour then Nothing else return t

swapStep :: (Path, [Node]) -> Maybe (Path, [Node])
swapStep (tour, reservedNodes) = nextTour
  where (t1:t2:ts) = tour
        nextTour   = do
          (t4,t3) <- closesrTo t1 t2 ts reservedNodes
          let tourEdges = pathToEdges tour
              tmpEdges  = [(t1, t4), (t2, t3)] ++
                          (tourEdges \\ [(t4, t3), (t1, t2)])
              tourPath  = tracePath' tmpEdges t1
              keptNodes = t2 : reservedNodes
            in return (rearrangeTour tourPath t1 t4, keptNodes)
