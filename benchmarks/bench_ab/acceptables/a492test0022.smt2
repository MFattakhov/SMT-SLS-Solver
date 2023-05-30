(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun a_0 () (_ BitVec 32))
(declare-fun a_1 () (_ BitVec 32))
(declare-fun a_2 () (_ BitVec 32))
(assert (not (bvult a_1 a_0)))
(assert (bvult a_2 a_1))
(assert (bvult a_2 a_0))
(assert (bvult (_ bv10 32) a_1))
(assert (bvult (_ bv10 32) a_0))
(assert (bvult (_ bv10 32) a_2))
(check-sat)
(exit)
