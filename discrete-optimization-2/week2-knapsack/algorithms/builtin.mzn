include "globals.mzn";

int: n; % num of items
int: k; % capacity
set of int: num = 1..n;

array[num] of int: ws; % weights of items
array[num] of int: vs; % values of items

var int: W; % total weight
var int: V; % total value
array[num] of var {0,1}: xs;

constraint knapsack(ws, vs, xs, W, V);
constraint W < k;

solve :: int_search(xs, first_fail, indomain_min, complete)
  maximize V;

output [show(V), " ", show(1), "\n",
        join(" ", [show(x) | x in xs])
       ];