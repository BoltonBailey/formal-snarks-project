(set-info :smt-lib-version 2.6)
(set-logic QF_FF)
(set-info :source |Abstract ToySnark soundness, from the FormalSnarksProject Lean development.
Query: does a cheating assignment exist that satisfies every verifier coefficient
equation while falsifying the extracted relation? unsat = sound.|)
(set-info :category "crafted")
(set-info :status unknown)
(define-sort F () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))

(declare-fun Pf_alpha () F)
(declare-fun Pf_beta () F)
(declare-fun x () F)
(declare-fun y () F)
(declare-fun z () F)

; 3 generator equations (verifier toxic-waste coefficients)
(assert (= (ff.add (ff.mul Pf_alpha y) (ff.mul Pf_beta x) (ff.mul (ff.neg (as ff1 F)) z)) (as ff0 F)))
(assert (= (ff.mul Pf_alpha x) (as ff0 F)))
(assert (= (ff.mul Pf_beta y) (as ff0 F)))

; the extracted relation (A*y = z or B*x = z, as a product) must be violated for a break
(assert (not (= (ff.add (ff.mul Pf_alpha Pf_beta x y) (ff.mul (ff.neg (as ff1 F)) Pf_alpha y z) (ff.mul (ff.neg (as ff1 F)) Pf_beta x z) (ff.mul z z)) (as ff0 F))))

(check-sat)
