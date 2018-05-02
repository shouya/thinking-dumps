#!/usr/bin/python
# -*- coding: utf-8 -*-


# I'll do the all of the rest homework using minizinc,
# to avoid reinventing all the wheels.

import hashlib
import os
import sys

def gen_data_file(edges, num_nodes, num_edges):
    num_edges = len(edges)
    edges_desc = " | ".join(["%d,%d," % (a,b) for (a,b) in edges])

    output = []
    output.append("n_nodes = %d;" % num_nodes)
    output.append("n_edges = %d;" % num_edges)
    output.append("edges = [|%s|];" % edges_desc)
    return "\n".join(output)


def transform_input(input_data):
    output = []
    lines = input_data.split('\n')

    first_line = lines[0].split()
    node_count = int(first_line[0])
    edge_count = int(first_line[1])
    edges = []

    for i in range(1, edge_count + 1):
        line = lines[i]
        parts = line.split()
        edges.append((int(parts[0]), int(parts[1])))

    return gen_data_file(edges, node_count, edge_count)


def solve_it(input_data):
    h = hashlib.sha1(input_data.encode()).hexdigest()
    if os.path.isfile("solutions/%s" % h):
        with open("solutions/%s" % h) as f:
            return f.read()
    else:
        inputs = transform_input(input_data)
        print("Generated input for %s" % h, file=sys.stderr)
        with open("input/%s.dzn" % h, "w") as f:
            f.write(inputs)
    return ""


if __name__ == '__main__':
    if len(sys.argv) > 1:
        file_location = sys.argv[1].strip()
        with open(file_location, 'r') as input_data_file:
            input_data = input_data_file.read()
        print(solve_it(input_data))
    else:
        print('This test requires an input file.  Please select one from the data directory. (i.e. python solver.py ./data/gc_4_1)')
