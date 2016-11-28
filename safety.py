#!/usr/bin/env python

import z3

s = z3.Solver()

x_in = z3.BitVec('x_in', 32)
x1 = z3.BitVec('x1', 32)

ite0 = z3.If(x_in < 0, x1 == -x_in, x1 == x_in)
s.add(ite0)

lte_1024 = x1 <= 1024
s.add(lte_1024)

s.add(z3.Or(x1 < 0, x1 > 1024))

if s.check() == z3.sat:
    m = s.model()
    sat_val = int("%s" % m[x_in])
    print "Assertion violated with an input of 0x%x" % sat_val
else:
    print "Verification successful"
