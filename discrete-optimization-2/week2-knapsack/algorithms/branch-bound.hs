{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

import Knapsack

import Data.Maybe (fromJust)
import Control.Monad
import Control.Monad.State.Lazy hiding (State)
import qualified Control.Monad.State.Lazy as S
import Control.Monad.Fix
import qualified Data.Sequence as Q
import Data.Sequence (Seq, (><))


------- Part 1: Heuristic upper bound estimation --------

data ScoredItem = ScoredItem { siScore :: Float
                             , siItem  :: Item
                             }

accumItemValueUntilExceed :: Weight -> [Item] -> Float
accumItemValueUntilExceed 0   xs = 0
accumItemValueUntilExceed _c  [] = 0
accumItemValueUntilExceed cap (Item { value, weight }:xs)
  | cap >  weight = value + accumItemValueUntilExceed (cap - weight) xs
  | cap == weight = value
  | cap <  weight = (fromIntegral cap / fromIntegral weight) *
                    fromIntegral value

calcEstimate :: Problem -> Float
calcEstimate prob@Problem { capacity, givenItems } =
  fmap tr givenItems
  & sortBy (comparing siScore)
  & fmap siItem
  & takeItemUntilExceed capacity
  where bestVWRatio item = ScoredItem { siScore = fromIntegral (value item) /
                                                  fromIntegral (weight item)
                                      , siItem = item
                                      }

------- Part 2: Solution space searching ----------

data PartialSolution = PartialSolution
  { remaining      :: [Item]
  , chosen         :: [Item]
  , valueSoFar     :: Value
  , weightSoFar    :: Weight
  , expectedValue  :: Value
  }

data Intermediate = Intermediate
  { bestSolutionSoFar :: PartialSolution
  , capacity          :: Weight
  }

type State = S.State Intermediate

pick :: PartialSolution -> PartialSolution
pick sol@PartialSolution { .. } = sol { chosen = item : chosen
                                      , remaining = tail remaining
                                      , valueSoFar = value item + valueSoFar
                                      , weightSoFar = weight item + weightSoFar
                                      , expectedValue
                                      }
  where item = head remaining

dontPick :: PartialSolution -> PartialSolution
dontPick sol@PartialSolution { .. } =
  sol { chosen
      , remaining = tail remaining
      , valueSoFar
      , weightSoFar
      , expectedValue = expectedValue - (value item)
      }
  where item = head remaining

evaluatePartial :: PartialSolution -> State (Seq PartialSolution)
evaluatePartial sol@PartialSolution { .. }
  -- this is a complete solution
  | null remaining = do
      bestValue <- gets (valueSoFar . bestSolutionSoFar)
      when (valueSoFar >= bestSolutionSoFar) $ put sol
      return Q.empty

  -- when the solution is not completed yet
  | otherwise      = do
      let Item { value, weight } = head remaining
          rest = tail remaining

      bestValue <- gets (valueSoFar . bestSolutionSoFar)
      cap <- gets Main.capacity

      let picking = if weight + weightSoFar <= cap
                    then Q.singleton (pick sol)
                    else Q.empty
      let notPicking = if expectedValue - value >= bestValue
                       then Q.singleton (dontPick sol)
                       else Q.empty
      return $ picking >< notPicking


step :: Seq PartialSolution -> State (Seq PartialSolution)
step xs
  | Q.null xs = return ()
  | otherwise = do
      let sol = fromJust $ lookup 1 xs
          rest = drop 1 xs
      newElems <- evaluatePartial
      retrun $ rest >< newElems

initPartialSolution :: Value -> [Item] -> PartialSolution
initPartialSolution v xs = PartialSolution
  { remaining   = xs
  , chosen      = []
  , valueSoFar  = 0
  , weightSoFar = 0
  , expectedValue = v
  }


-- quick and dirty trick, since I don't want to deal with Maybe
initBestSolution :: PartialSolution
initBestSolution = PartialSolution
  { remaining   = []
  , chosen      = []
  , valueSoFar  = 0
  , weightSoFar = 0
  , expectedValue = 0
  }

branchAndBound :: Algorithm
branchAndBound prob@Problem { capacity, givenItems } =
  solution prob selectedItems Optimal
  where estimatedValue = ceiling $ calcEstimate prob
        initQueue = Q.singleton (initPartialSolution estimatedValue givenItems)
        initState = Intermediate { capacity, bestSolutionSoFar=initBestSolution }
        recState xs = if Q.null xs
                      then return ()
                      else step xs >>= recState
        finalPartialSolution = execState (recState initQueue) initState
        selectedItems = chosen finalPartialSolution


main :: IO ()
main = solveBy branchAndBound
