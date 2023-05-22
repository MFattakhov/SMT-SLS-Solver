(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (not (= (bvand a (_ bv16 32)) (_ bv0 32))))
(assert (not (bvult a (bvlshr b (_ bv1 32)))))
(assert (not (not (= (bvand a (_ bv8 32)) (_ bv0 32)))))
(assert (not (not (= (bvand a (_ bv4 32)) (_ bv0 32)))))
(check-sat)
(exit)
