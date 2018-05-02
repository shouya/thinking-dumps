include "globals.mzn";

int: n_nodes;
int: n_edges;

set of int: node_set = 0..(n_nodes-1);
set of int: edge_set = 1..n_edges;
array[edge_set, 1..2] of node_set: edges;

array[0..(n_nodes-1)] of var int: c;

constraint forall (i in node_set) (c[i] >= 0);
constraint forall (i in edge_set)
  (c[edges[i, 1]] != c[edges[i, 2]]);


% constraint max(c) >= 80;
solve minimize max(c);

output [show(max(c)+1), " 1", "\n",
        join(" ", [show(x) | x in c])];