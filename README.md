# BVSampler

Efficient Sampling of Bitvector Solutions for Testing

This is a Python reimplementation of [QuickSampler](https://github.com/RafaelTupynamba/quicksampler/)
that works on bitvector constraints instead of propositional SAT problems.

All credit for the idea goes to Rafael Dutra, Kevin Laeufer, Jonathan Bachrach and Koushik Sen, UC Berkeley.
Check out their [ICSE'2018 paper](https://people.eecs.berkeley.edu/~rtd/papers/quicksampler.pdf) on the approach.

**WARNING**: The generated samples are currently not checked for whether they satisfy the given constraints!

## Requirements

- Python 2.7
- Z3 + Python binding

## Example 

    x = z3.BitVec('x', 8)
    a = z3.BitVecVal(10, 8)
    b = z3.BitVecVal(20, 8)

    sample = BVSampler(z3.And(x > a, x < b), x + 5)

    for x in sample:
      print('possible solution: ' + str(x))

The implementation consists of a single large generator in `BVSampler(constraints, target)`, which takes a bunch of constraints and a target, which is a bitvector expression that we want to find solutions for.

## Approach

The approach is exactly the same as in QuickSampler. The minimization query is based on naively [counting the number of bits](https://stackoverflow.com/questions/39299015/sum-of-all-the-bits-in-a-bit-vector-of-z3) that are set in the delta.
