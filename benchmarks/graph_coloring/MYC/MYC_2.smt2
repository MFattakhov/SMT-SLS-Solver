(set-info :category "industrial")
(set-info :status sat)
(declare-fun x1 () (_ BitVec 32))
(declare-fun x2 () (_ BitVec 32))
(declare-fun x3 () (_ BitVec 32))
(declare-fun x4 () (_ BitVec 32))
(declare-fun x5 () (_ BitVec 32))
(declare-fun x6 () (_ BitVec 32))
(declare-fun x7 () (_ BitVec 32))
(declare-fun x8 () (_ BitVec 32))
(declare-fun x9 () (_ BitVec 32))
(declare-fun x10 () (_ BitVec 32))
(declare-fun x11 () (_ BitVec 32))
(declare-fun x12 () (_ BitVec 32))
(declare-fun x13 () (_ BitVec 32))
(declare-fun x14 () (_ BitVec 32))
(declare-fun x15 () (_ BitVec 32))
(declare-fun x16 () (_ BitVec 32))
(declare-fun x17 () (_ BitVec 32))
(declare-fun x18 () (_ BitVec 32))
(declare-fun x19 () (_ BitVec 32))
(declare-fun x20 () (_ BitVec 32))
(declare-fun x21 () (_ BitVec 32))
(declare-fun x22 () (_ BitVec 32))
(declare-fun x23 () (_ BitVec 32))
(assert (bvult x1 (_ bv5 32)))
(assert (bvult x2 (_ bv5 32)))
(assert (bvult x3 (_ bv5 32)))
(assert (bvult x4 (_ bv5 32)))
(assert (bvult x5 (_ bv5 32)))
(assert (bvult x6 (_ bv5 32)))
(assert (bvult x7 (_ bv5 32)))
(assert (bvult x8 (_ bv5 32)))
(assert (bvult x9 (_ bv5 32)))
(assert (bvult x10 (_ bv5 32)))
(assert (bvult x11 (_ bv5 32)))
(assert (bvult x12 (_ bv5 32)))
(assert (bvult x13 (_ bv5 32)))
(assert (bvult x14 (_ bv5 32)))
(assert (bvult x15 (_ bv5 32)))
(assert (bvult x16 (_ bv5 32)))
(assert (bvult x17 (_ bv5 32)))
(assert (bvult x18 (_ bv5 32)))
(assert (bvult x19 (_ bv5 32)))
(assert (bvult x20 (_ bv5 32)))
(assert (bvult x21 (_ bv5 32)))
(assert (bvult x22 (_ bv5 32)))
(assert (bvult x23 (_ bv5 32)))
(assert (not (= x1 x2)))
(assert (not (= x1 x4)))
(assert (not (= x1 x7)))
(assert (not (= x1 x9)))
(assert (not (= x1 x13)))
(assert (not (= x1 x15)))
(assert (not (= x1 x18)))
(assert (not (= x1 x20)))
(assert (not (= x2 x3)))
(assert (not (= x2 x6)))
(assert (not (= x2 x8)))
(assert (not (= x2 x12)))
(assert (not (= x2 x14)))
(assert (not (= x2 x17)))
(assert (not (= x2 x19)))
(assert (not (= x3 x5)))
(assert (not (= x3 x7)))
(assert (not (= x3 x10)))
(assert (not (= x3 x13)))
(assert (not (= x3 x16)))
(assert (not (= x3 x18)))
(assert (not (= x3 x21)))
(assert (not (= x4 x5)))
(assert (not (= x4 x6)))
(assert (not (= x4 x10)))
(assert (not (= x4 x12)))
(assert (not (= x4 x16)))
(assert (not (= x4 x17)))
(assert (not (= x4 x21)))
(assert (not (= x5 x8)))
(assert (not (= x5 x9)))
(assert (not (= x5 x14)))
(assert (not (= x5 x15)))
(assert (not (= x5 x19)))
(assert (not (= x5 x20)))
(assert (not (= x6 x11)))
(assert (not (= x6 x13)))
(assert (not (= x6 x15)))
(assert (not (= x6 x22)))
(assert (not (= x7 x11)))
(assert (not (= x7 x12)))
(assert (not (= x7 x14)))
(assert (not (= x7 x22)))
(assert (not (= x8 x11)))
(assert (not (= x8 x13)))
(assert (not (= x8 x16)))
(assert (not (= x8 x22)))
(assert (not (= x9 x11)))
(assert (not (= x9 x12)))
(assert (not (= x9 x16)))
(assert (not (= x9 x22)))
(assert (not (= x10 x11)))
(assert (not (= x10 x14)))
(assert (not (= x10 x15)))
(assert (not (= x10 x22)))
(assert (not (= x11 x17)))
(assert (not (= x11 x18)))
(assert (not (= x11 x19)))
(assert (not (= x11 x20)))
(assert (not (= x11 x21)))
(assert (not (= x12 x23)))
(assert (not (= x13 x23)))
(assert (not (= x14 x23)))
(assert (not (= x15 x23)))
(assert (not (= x16 x23)))
(assert (not (= x17 x23)))
(assert (not (= x18 x23)))
(assert (not (= x19 x23)))
(assert (not (= x20 x23)))
(assert (not (= x21 x23)))
(assert (not (= x22 x23)))
(check-sat)
(exit)
