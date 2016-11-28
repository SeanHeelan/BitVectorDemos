(set-logic QF_ABV)

(declare-fun v () (_ BitVec 32))
(declare-fun mask () (_ BitVec 32))
(declare-fun m0 () (_ BitVec 32))
(declare-fun m1 () (_ BitVec 32))

(assert (= m0 (ite (bvsgt v #x00000000) v (bvmul v #xffffffff))))
(assert (= mask (bvashr v #x0000001f)))
(assert (= m1 (bvsub (bvxor v mask) mask)))

(assert (not (= m0 m1)))
(check-sat)
