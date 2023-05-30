(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
 Patrice Godefroid, SAGE (systematic dynamic test generation)
 For more information: http://research.microsoft.com/en-us/um/people/pg/public_psfiles/ndss2008.pdf
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun T1_96 () (_ BitVec 8))
(assert (and true (bvult (_ bv122 8) T1_96) (bvule (_ bv97 8) T1_96)))
(check-sat)
(exit)
