(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun n () (_ BitVec 32))
(declare-fun c () (_ BitVec 8))
(assert (not (bvult n (_ bv16 32))))
(check-sat)
(exit)
