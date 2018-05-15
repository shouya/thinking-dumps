include "globals.mzn";

int: n_nodes;
int: n_edges;

set of int: node_set = 0..(n_nodes-1);
set of int: edge_set = 1..n_edges;
set of int: color_range = 0..150;
array[edge_set, 1..2] of node_set: edges;

array[int] of int: orig_nodes;

array[0..(n_nodes-1)] of var color_range: c;

constraint forall (i in node_set) (c[i] >= 0);
constraint forall (i in edge_set)
  (c[edges[i, 1]] != c[edges[i, 2]]);

% breaking color symmetry
constraint c[n_nodes-1] = 0;
constraint forall (i in 0..n_nodes-2)
  (c[i] <= max([c[j] | j in i+1..n_nodes-1]) + 1);
% constraint forall (i in 0..3)
%   (c[n_nodes-1-i] <= i);


% constraint max(c) >= 80;
solve :: int_search(c, input_order, indomain_min, complete)
  minimize max(c);

output [show(max(c)+1), " 1", "\n",
        join(" ", [show(c[n]) | n in orig_nodes]), "\n"
        ];