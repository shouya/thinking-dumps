#!/usr/bin/python2
# -*- coding: utf-8 -*-

import os
import sys

if __name__ == '__main__':
    if len(sys.argv) > 1:
        file_loc = sys.argv[1].strip()
        os.system('runghc solver.hs ' + file_loc)
    else:
        print 'This test requires an input file.  Please select one from the data directory. (i.e. python solver.py ./data/ks_4_0)'
