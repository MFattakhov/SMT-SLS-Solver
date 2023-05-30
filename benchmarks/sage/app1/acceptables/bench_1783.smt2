(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T1_20 () (_ BitVec 8))
(assert (and true (bvule T1_20 (_ bv57 8)) (bvule (_ bv48 8) T1_20)))
(check-sat)
(exit)
