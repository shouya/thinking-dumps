## Travelling Salesman Problem

I was reading the book
[The Traveling Salesman Problem: A Computational Study (Princeton Series in Applied Mathematics)](http://www.amazon.com/The-Traveling-Salesman-Problem-Computational/dp/0691129932)
(the chinese version:
[迷茫的旅行商：一个无处不在的计算机算法问题](http://www.amazon.cn/%E8%BF%B7%E8%8C%AB%E7%9A%84%E6%97%85%E8%A1%8C%E5%95%86-%E4%B8%80%E4%B8%AA%E6%97%A0%E5%A4%84%E4%B8%8D%E5%9C%A8%E7%9A%84%E8%AE%A1%E7%AE%97%E6%9C%BA%E7%AE%97%E6%B3%95%E9%97%AE%E9%A2%98-%E7%BE%8E-William-J-Cook/dp/B00M2DL24Q/)). There
are several algorithms mentioned in the book. I feel itch to try
implement them out as I read those algorithms. So comes this project.

### Roadmap

The project includes the implementations of differenting algorithms
solving the TSP. Here's a list of algorithms I planned to work on:

* [X] Brutal force algorithm
* [X] Nearest-neighbor algorithm
* [ ] Greedy algorithm
* [ ] Insertion algorithm
 * [ ] Cheapest
 * [ ] Farthest
 * [ ] Nearest
 * [ ] Random
* [ ] 2-Opt Algorithm
* [ ] 3-Opt Algorithm

All codes will be written in Haskell.

### Components

This project contains multiple parts.

#### TSPLib.hs

Library utilities for TSP problem, includes definitions
of basic concepts, eg. `Node`, `Edge`, and basic functions,
eg. `distance`.

When run directly, its reads input for nodes and generate the input of
TSP graph for visualizing the nodes. You can pipe this with `TSPGraph`
to view the visualized input in the following way:

```bash
$ cat data/simple-1.txt | runghc TSPLib.hs | runghc TSPGraph.hs
```

#### TSPGraph.hs

Library to visualize TSP solution. It provides `presentUI` function:

```haskell
presentUI :: [Node] -> [Edge] -> IO ()
```

this function will show up a window with the nodes and edges
visualized and block the process.

This library can be run alone as well. It will read the nodes and
edges with a specific format from stdin, and display them. The format
is basically:

```
<number of nodes> <number of edges>
<x1> <y1>               -- nodes, in the given number
...
<x1> <y1> <x2> <y2>     -- edges, in the given number
...
```

Below is the result by applying the NearestNeighbor algorithm with a
random input with 300 nodes.

![TSPGraph](http://i.imgur.com/5diQ8bt.png)

#### RandomDataGen.hs

This is a command line tool that helps to generate a group of
data. The synopsis looks like:

```
runghc RandomDataGen.hs <max-x> <max-y> <number-of-nodes>
```

It will spit the generated nodes to the standard output, in `TSPLib`
parsable format. The generated nodes are garenteed unique.


#### TestAlgorithm.hs

This is a command line tool that helps to test an algorithm. You
should specify the algorithm's name as its argument, and dump the
inputing nodes to its stdin. Then it will compute the paths with the
specified algorithm and with `TSPGraph.hs`.


#### Algorithms

Other files in this projecting with suffix `.hs` are the algorithms
implemented.


### References
* [Wikipedia](http://en.wikipedia.org/wiki/Travelling_salesman_problem)
* [The Traveling Salesman Problem: A Computational Study (Princeton Series in Applied Mathematics)](http://www.amazon.com/The-Traveling-Salesman-Problem-Computational/dp/0691129932)
