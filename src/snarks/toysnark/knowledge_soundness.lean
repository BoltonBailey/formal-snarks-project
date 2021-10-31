/-
Author: Bolton Bailey
-/

import .vars
import ...attributes
import ...integral_domain_tactic

/-!
# Knowledge Soundness

This file proves the knowledge-soundness property of a very trivial SNARK
-/

open_locale big_operators classical

section

open mv_polynomial vars

noncomputable theory

universes u


/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]

-- TODO

/-- Checks whether a statement witness pair satisfies the SSP -/
def satisfying (a b c d e : F) := a * d = e ∨ b * c = e



/-- The coefficients of the CRS elements in the algebraic adversary's representation -/
parameters {A B C D E  : F}




/-- Polynomial forms of the adversary's proof representation -/
def proof1 : mv_polynomial vars F := 
  mv_polynomial.C A * X vars.α
  +
  mv_polynomial.C B * X vars.β

def proof2 : mv_polynomial vars F := 
  mv_polynomial.C C * X vars.α
  +
  mv_polynomial.C D * X vars.β

def proof3 : mv_polynomial vars F := 
  mv_polynomial.C E * X vars.α * X vars.β



def verified  : Prop := proof1 * proof2 = proof3

open finsupp

/-- The main theorem for the soundness of the Groth '16 SNARK. 
Show that if the adversary polynomials obey the equations, 
then the coefficients give a satisfying witness. -/
theorem soundness : 
  verified
  -> (satisfying A B C D E)
:=
begin
  
  intros eqn,
  rw satisfying,
  
  rw verified at eqn,
  rw [proof1, proof2, proof3] at eqn,

  simp only [] with polynomial_nf_3 at eqn,

  have h20 := congr_arg (coeff (single α 2 + single β 0)) eqn,
  have h11 := congr_arg (coeff (single α 1 + single β 1)) eqn,
  have h02 := congr_arg (coeff (single α 0 + single β 2)) eqn,

  clear eqn,

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  simp only [] with finsupp_simp at *,

  tactic.integral_domain_tactic_3,
  repeat { apply or.inr, assumption, },
  repeat { apply or.inl, assumption, },

end 

end 



