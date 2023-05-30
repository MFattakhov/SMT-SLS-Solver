(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun smt_fresh_symbolic_value () (_ BitVec 32))
(declare-fun smt_fresh_symbolic_value_1 () (_ BitVec 32))
(declare-fun smt_fresh_symbolic_value_2 () (_ BitVec 32))
(assert (not (not (= smt_fresh_symbolic_value (_ bv0 32)))))
(assert (not (not (= smt_fresh_symbolic_value_1 (_ bv0 32)))))
(assert (not (not (= smt_fresh_symbolic_value_2 (_ bv0 32)))))
(check-sat)
(exit)
