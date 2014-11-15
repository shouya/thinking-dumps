{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ProgFun.Bloxorz where

import Prelude hiding (Left, Right)
import GraphClass
import BFS

type Pos = (Int, Int)
type Block = (Pos, Pos)


terrian :: Pos -> Bool
terrian (x,y) = inBounds (x,y)

bounds :: Pos
bounds = (4, 4)

showBlock :: Block -> String
showBlock (a,b) = concat $
                  [[ case () of
                        _ | (x, y) == a || (x, y) == b -> '#'
                          | terrian (x, y)             -> 'o'
                          | otherwise                  -> ' '
                   | y <- [0..(fst bounds)]] ++ "\n"
                  | x <- [0..(snd bounds)]]


isStanding :: Block -> Bool
isStanding (a,b) = a == b

isHorizontal :: Block -> Bool
isHorizontal (a,b) = not (isStanding (a,b)) &&
                     fst a == fst b

isLegal :: Block -> Bool
isLegal (a,b) = terrian  a && terrian  b &&
                inBounds a && inBounds b

inBounds :: Pos -> Bool
inBounds (x, y) = x >= 0  && y >= 0 &&
                  x <= bx && y <= by
  where (bx, by) = bounds


data Dir = Left | Right | Up | Down
         deriving (Show, Ord, Eq)

directions :: [Dir]
directions = [Left, Right, Up, Down]

type MoveMatrix = ((Int, Int), (Int, Int))

moveMatrix :: Dir -> Block -> MoveMatrix
moveMatrix Left blk
  | isStanding blk   = ((0,-2),(0,-1))
  | isHorizontal blk = ((0,-1),(0,-2))
  | otherwise        = ((0,-1),(0,-1))

moveMatrix Right blk
  | isStanding blk   = ((0,1),(0,2))
  | isHorizontal blk = ((0,2),(0,1))
  | otherwise        = ((0,1),(0,1))

moveMatrix Up blk
  | isStanding blk   = ((-2,0),(-1,0))
  | isHorizontal blk = ((-1,0),(-1,0))
  | otherwise        = ((-1,0),(-2,0))

moveMatrix Down blk
  | isStanding blk   = ((1,0),(2,0))
  | isHorizontal blk = ((1,0),(1,0))
  | otherwise        = ((2,0),(1,0))


moveBlockByMatrix :: MoveMatrix -> Block -> Block
moveBlockByMatrix ((dx1,dy1),(dx2,dy2)) ((x1,y1),(x2,y2)) =
  ((x1 + dx1, y1 + dy1), (x2 + dx2, y2 + dy2))


move :: Dir -> Block -> Block
move dir b = moveBlockByMatrix (moveMatrix dir b) b

possibleMoves :: Block -> [LEdge Block Dir]
possibleMoves b = filter (isLegal . target) $
                  map (\dir -> ((b, move dir b), dir)) directions


instance Node Block
-- instance BFSNode Block

data T = T

instance Graph T Block Dir where
  edgesFor T = possibleMoves


l :: Maybe [Dir]
l = bfsSearch T beg end
  where beg = ((0,0),(0,0)) :: Block
        end = ((0,3),(0,3)) :: Block
