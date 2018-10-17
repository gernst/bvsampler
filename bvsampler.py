#!/usr/bin/python

import random
import z3

# Author: Gidon Ernst, gidon.ernst (*) gmail.com

# Approach taken from:
#   Rafael Dutra, Kevin Laeufer, Jonathan Bachrach and Koushik Sen:
#   Efficient Sampling of SAT Solutions for Testing, ICSE 2018.
#   https://github.com/RafaelTupynamba/quicksampler/

# https://stackoverflow.com/questions/39299015/sum-of-all-the-bits-in-a-bit-vector-of-z3
def bvcount(b):
    n = b.size()
    bits = [ z3.Extract(i, i, b) for i in range(n) ]
    bvs  = [ z3.Concat(z3.BitVecVal(0, n - 1), b) for b in bits ]
    nb   = reduce(lambda a, b: a + b, bvs)
    return nb

MAX_LEVEL = 6

def BVSampler(constraints, target):
    solver = z3.Optimize()
    solver.add(constraints)

    n = target.size()

    results = set()

    while True:
        guess  = z3.BitVecVal(random.getrandbits(n), n)
        result = z3.BitVec('result', n)
        delta  = z3.BitVec('delta',  n)
        solver.add(result == target)
        solver.add(result ^ delta == guess)
        solver.minimize(bvcount(delta))

        if solver.check() != z3.sat:
            break

        model   = solver.model()
        result0 = model[result].as_long()

        results.add(result0)
        yield result0

        # print('solver: ' + str(solver))
        # print('guess: ' + str(guess))
        # print('model: ' + str(model))

        mutations = {}
        
        solver.push()

        for i in range(n):
            # print('mutating bit ' + str(i))
            solver.push()
            solver.add(z3.Extract(i, i, delta) == 0x1)

            if solver.check() == z3.sat:
                model   = solver.model()
                result1 = model[result].as_long()

                if result1 not in results:
                    results.add(result1)
                    yield result1

                new_mutations = {}
                new_mutations[result1] = 1

                for value in mutations:
                    level = mutations[value]
                    if level > MAX_LEVEL:
                        continue

                    candidate = (result0 ^ ((result0^value) | (result0^result1)))
                    # print('yielding candidate ' + str(candidate) + ' at level ' + str(level))
                    if candidate not in results:
                        results.add(candidate)
                        yield candidate

                    new_mutations[candidate] = level + 1

                mutations.update(new_mutations)

            solver.pop()

        solver.pop()
