#!/usr/bin/env python

import logging
import time

import z3

logging.basicConfig(level=logging.DEBUG)
log = logging.getLogger(__name__)


def get_model():
    s = z3.Solver()

    w = z3.BitVec("w", 32)
    h = z3.BitVec("h", 32)
    v0 = z3.BitVec("v0", 32)
    v1 = z3.BitVec("v1", 32)

    s.add(v0 == ((w + 31) >> 3) & z3.BitVecVal(0xfffffffc, 32))
    s.add(w > 0)
    s.add(h > 0)
    s.add(h * v0 > 0)
    s.add(z3.BitVecVal(0x07300000, 32) / v0 > h)
    s.add(
            v1 == ((v0 * h) + z3.BitVecVal(15, 32)) &
            z3.BitVecVal(0xfffffff0, 32))

    return s, v1

lb = 0
val_at_most = ub = 0xffffffff
q = 0

# Walk the val_at_most and lb towards each other. The val_at_most represents
# the last value which we know the lower bound definitely is equal to, or lower
# than.
start = time.time()
while val_at_most != lb:
    s, v = get_model()

    log.debug("val_at_most: 0x%x, lb: 0x%x, ub: 0x%x", val_at_most, lb, ub)
    log.debug("Checking v < 0x%x ... ", ub)
    s.add(z3.ULT(v, ub))

    q += 1
    if s.check() == z3.sat:
        log.debug("... SAT")
        val_at_most = ub - 1
        ub = lb + (ub - lb) // 2
    else:
        log.debug("... UNSAT")
        lb = ub
        if val_at_most - lb == 1:
            ub = val_at_most
        else:
            ub = lb + (val_at_most - lb) / 2

end = time.time()

log.debug("val_at_most: 0x%x, lb: 0x%x, ub: 0x%x", val_at_most, lb, ub)
log.info("Min: 0x%x (%d queries, %02fs)", lb, q, end - start)

val_at_least = lb = 0
ub = 0xffffffff
q = 0

# Walk the val_at_least and ub towards each other. The val_at_least represents
# the value which we know the upper bound definitely is equal to, or greater
# than.
start = time.time()
while val_at_least != ub:
    s, v = get_model()

    log.debug("val_at_least: 0x%x, ub: 0x%x, lb: 0x%x", val_at_least, ub, lb)
    log.debug("Checking v > 0x%x ... ", lb)
    s.add(z3.UGT(v, lb))

    q += 1
    if s.check() == z3.sat:
        log.debug("... SAT")
        val_at_least = lb + 1
        lb += (ub - lb) // 2
    else:
        log.debug("... UNSAT")
        ub = lb
        if ub - val_at_least == 1:
            lb = val_at_least
        else:
            lb = ub - (ub - val_at_least) / 2

end = time.time()

log.debug("val_at_least: 0x%x, ub: 0x%x, lb: 0x%x", val_at_least, ub, lb)
log.info("Max: 0x%x (%d queries, %02fs)", ub, q, end - start)
