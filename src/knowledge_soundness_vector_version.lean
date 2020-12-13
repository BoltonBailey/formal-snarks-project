/-
Author: Bolton Bailey
-/
import data.mv_polynomial.basic
import data.polynomial.div
import .mv_divisability

/-!
# Knowledge Soundness

This file proves the knowledge-soundness property of the 
[Baby SNARK](https://github.com/initc3/babySNARK) system, 
as described in section 5 of the paper.

-/

section

noncomputable theory


universes u


/-- An inductive type from which to index the variables of the 3-variable polynomials the proof manages -/
inductive vars : Type
| X : vars
| Y : vars
| Z : vars

/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]


/-- Helpers for representing X, Y, Z as 3-variable polynomials -/
def X_poly : mv_polynomial vars F := mv_polynomial.X vars.X
def Y_poly : mv_polynomial vars F := mv_polynomial.X vars.Y
def Z_poly : mv_polynomial vars F := mv_polynomial.X vars.Z


/-- Vector form of range function -/
def vector_range (k : ℕ) : vector ℕ k :=
⟨list.range k, by simp⟩
/- TODO ask mathlib maintainers to add vector.range to mathlib -/


/-- The naturals representing the number of gates in the circuit, the statement size, and witness size repectively-/ 
parameters {m n_stmt n_wit : ℕ}
def n := n_stmt + n_wit
-- NOTE: In the paper, n_stmt is l and n_wit is n-l. Here, n is defined from these values.


/-- u_stmt and u_wit are vectors of polynomials from the square span program -/
parameter {u_stmt : vector (polynomial F) n_stmt}
parameter {u_wit : vector (polynomial F) n_wit}
/-- and u is their concatenation -/
def u : (vector (polynomial F) n) := vector.append u_stmt u_wit
-- NOTE: u is usually a universe variable in lean, 
-- here it is a vector of polynomials to match the paper

/-- The polynomial divisibility by which is used to verify satisfaction of the SSP -/
def r : vector F m := (vector_range m).map (λ i, (i : F))
def t : polynomial F := (r.map (λ i : F, polynomial.X - polynomial.C i)).to_list.prod -- (X - r_1) ... (X - r_m)


/-- Checks whether a witness satisfies the SSP -/
def satisfying_wit (a_stmt : vector F n_stmt) (a_wit : vector F n_wit) := 
polynomial.mod_by_monic (((vector.map₂ has_scalar.smul (vector.append a_stmt a_wit) u).to_list.sum)^2) t = 1



/-- The crs elements as multivariate polynomials of the toxic waste samples -/
def crs_powers_of_τ : vector (mv_polynomial vars F) m := vector.map (λ i, X_poly^i) (vector_range m)
def crs_γ : mv_polynomial vars F := Z_poly
def crs_γβ : mv_polynomial vars F := Z_poly * Y_poly
def crs_β_ssps : vector (mv_polynomial vars F) n_wit := vector.map (λ p : polynomial F, (Y_poly) * p.eval₂ mv_polynomial.C X_poly) u_wit

/-- The statement polynomial that the verifier computes from the statement bits-/
def V_stmt (a_stmt : vector F n_stmt) : polynomial F 
:= (vector.map₂ has_scalar.smul a_stmt u_stmt).to_list.sum

/-- The coefficients of the CRS elements in the algebraic adversary's representation -/
parameters {b v h : vector F m}
parameters {b_γ v_γ h_γ b_γβ v_γβ h_γβ : F}
parameters {b' v' h' : vector F n_wit}

/-- Polynomial forms of the adversary's proof representation -/
def B_wit  : mv_polynomial vars F := 
  (vector.map₂ has_scalar.smul b crs_powers_of_τ).to_list.sum
  +
  b_γ • crs_γ
  +
  b_γβ • crs_γβ
  +
  (vector.map₂ has_scalar.smul b' crs_β_ssps).to_list.sum


def V_wit : mv_polynomial vars F := 
  (vector.map₂ has_scalar.smul v crs_powers_of_τ).to_list.sum
  +
  v_γ • crs_γ
  +
  v_γβ • crs_γβ
  +
  (vector.map₂ has_scalar.smul v' crs_β_ssps).to_list.sum

def H : mv_polynomial vars F := 
  (vector.map₂ has_scalar.smul h crs_powers_of_τ).to_list.sum
  +
  h_γ • crs_γ
  +
  h_γβ • crs_γβ
  +
  (vector.map₂ has_scalar.smul h' crs_β_ssps).to_list.sum


/-- Show that if the adversary polynomials obey the equations, then the coefficients give a satisfying witness -/
lemma case_1 (a_stmt : vector F n_stmt) : (B_wit = Y_poly * V_wit) -> (H * (t.eval₂ mv_polynomial.C X_poly) + mv_polynomial.C 1 = (V_wit + (V_stmt a_stmt).eval₂ mv_polynomial.C X_poly)^2) -> (satisfying_wit a_stmt b')
:=
begin
  intros eqnI eqnII,
  have h1 : (∀ m : vars →₀ ℕ, m vars.Y = 0 -> B_wit.coeff m = 0),
  /- TODO use lemma from mv_divisability -/

  have h2 : b = vector.repeat 0 m,

end



-- TODOs
-- define Prove function, taking crs and a
-- Define verify
-- NOTE: Currently we are not "in the exponent"




end