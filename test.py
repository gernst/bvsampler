#!/usr/bin/python

import z3
import bvsampler

x = z3.BitVec('x', 16)
a = z3.BitVecVal(131, 16)
b = z3.BitVecVal(5000, 16)

sample = bvsampler.bvsampler(z3.And(x > a, x < b), x)

for x in sample:
     print('possible solution: ' + str(x))
