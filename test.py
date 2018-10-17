#!/usr/bin/python

import z3
import bvsampler

x = z3.BitVec('x', 16)

sample = bvsampler.bvsampler(z3.And(x > 1000, x < 10000, z3.Or(x < 4000, x > 5000)), x)

for x in sample:
    y = bvsampler.cast_long_to_str(x,16)
    print('possible solution: ' + y)
