module ArbitraryInsertion (algArbitraryInsertion) where

import TSPLib
import Insertion


algArbitraryInsertion :: TSPAlgorithm
algArbitraryInsertion = insertionAlgorithm select


select :: Path -> [Node] -> Node
select _ (n:_) = n
