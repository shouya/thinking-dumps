{-# LANGUAGE GADTs #-}
module DFA where

import Data.List
import Text.Printf

import State
import Input



type DFATransFunc s i = s -> i -> s

data DFA s i where
  DFA :: (State s, Input i) => s -> [s] -> (DFATransFunc s i) -> DFA s i

type DFATransTable s i = [(s, i, s)]


evalDFA :: DFA s i -> [i] -> s
evalDFA (DFA startState _ tf) xs = foldl tf startState xs

transFuncToTable :: (State s, Input i) =>
                    DFATransFunc s i -> DFATransTable s i
transFuncToTable func = [(s, i, func s i) |
                              s <- allStates,
                              i <- allInputs]

transTableToFunc :: (State s, Input i, Eq s, Eq i) =>
                    DFATransTable s i -> DFATransFunc s i
transTableToFunc tbl s i =
  case find matchSI tbl of
    Just (_,_,s') -> s'
    Nothing       -> maybe undefined id failState
  where matchSI (s', i', _) = s' == s && i' == i


-- Visualize a DFA with Dot language
visualizeDot :: (Eq s, Eq i, Show s, Show i) => DFA s i -> String
visualizeDot (DFA ss as t) =
  "digraph dfa {\n" ++
  "rankdir=LR;\n" ++
  "node [shape=doublecircle];" ++
  acceptstatelist ++ ";\n\n" ++
  "node [shape=circle];\n" ++
  nodelist ++ ";\n\n" ++
  "\"\" [shape=none,height=0.0,width=0.0];\n" ++
  startnode ++ ";\n\n" ++
  translist ++ ";\n" ++
  "}\n"
  where statemap = zip allStates (map (\n -> "node_" ++ show n) [1..])
        nodelist = intercalate ";\n" $ map nodeToStr statemap
        nodeToStr (s,n) = printf "%s [label=\"%s\"]" n (show s)
        stateToNode s = case lookup s statemap of Just a -> a; _ -> undefined
        transtbl = transFuncToTable t
        transToStr (s,i,s') = printf "%s -> %s [label=\"%s\"]"
                                     (stateToNode s) (stateToNode s') (show i)
        translist = intercalate ";\n" $ map transToStr $
                    filter (\(_,_,s) -> maybe True (\fs -> fs /= s) failState) $
                    transtbl
        acceptstatelist = intercalate " " $ map stateToNode as
        startnode = printf "\"\" -> %s" (stateToNode ss)
