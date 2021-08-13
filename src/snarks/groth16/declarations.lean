/-
Author: Bolton Bailey
-/
import data.mv_polynomial.basic
import data.polynomial.div
import data.polynomial.field_division
import algebra.polynomial.big_operators
import polynomial_tactic
-- import .general_lemmas.polynomial_mv_sv_cast
-- import .general_lemmas.mv_divisability
-- import .general_lemmas.single_antidiagonal
-- import .general_lemmas.polynomial_smul_eq_C_mul
import .vars
-- import tactic.wlog

/-!
# Knowledge Soundness

This file proves the knowledge-soundness property of the 
[Groth16](https://eprint.iacr.org/2016/260.pdf) system.

Specifically, we prove this property for the NILP system 
described in section 3.1 of that paper.

Furthermore, we carry out the reduction to non-laurent polynomials by multiplying through the CRS with γδ.

We choose r,s to be 0, todo, allow other values

-/

open_locale big_operators classical


namespace groth16

section groth16

open mv_polynomial

noncomputable theory


end groth16

end groth16