

import data.mv_polynomial.basic
import data.polynomial.div


section

noncomputable theory


universes u

parameter {F : Type u}
parameter [field F]


inductive vars : Type
| X : vars
| Y : vars
| Z : vars

-- Helpers for representing X, Y, Z as polynomials
def X_poly : mv_polynomial vars F := mv_polynomial.X vars.X
def Y_poly : mv_polynomial vars F := mv_polynomial.X vars.Y
def Z_poly : mv_polynomial vars F := mv_polynomial.X vars.Z

-- NOTE: In the paper, n_stmt is l and n_wit is n-l
parameters {m n_stmt n_wit : ℕ}
-- NOTE: u is usually a universe variable in lean
-- here, u is a vector of polynomials
parameter {u_stmt : vector (polynomial F) n_stmt}
parameter {u_wit : vector (polynomial F) n_wit}

-- toxic waste elements
-- constants τ β γ : F

-- Vector form of range function
-- TODO ask mathlib maintainers to add this to mathlib
def vector_range (k : ℕ) : vector ℕ k :=
⟨list.range k, by simp⟩


-- The crs elements as multivariate polynomials of the toxic waste samples
def crs_powers_of_τ : vector (mv_polynomial vars F) m := vector.map (λ i, X_poly^i) (vector_range m)
def crs_γ : mv_polynomial vars F := Z_poly
def crs_γβ : mv_polynomial vars F := Z_poly * Y_poly
def crs_β_ssps : vector (mv_polynomial vars F) n_wit := vector.map (λ p : polynomial F, (Y_poly) * p.eval₂ mv_polynomial.C X_poly) u_wit

def r : vector F m := (vector_range m).map (λ i, (i : F))
def t : polynomial F := (r.map (λ i : F, polynomial.X - polynomial.C i)).to_list.prod -- (X - r_1) ... (X - r_m)

#check crs_β_ssps
#check t

def V_stmt (a_stmt : vector F n_stmt) : polynomial F 
:= (vector.map₂ has_scalar.smul a_stmt u_stmt).to_list.sum


-- The coefficients of the CRS elements in the algebraic adversary's representation
parameters {b v h : vector F m}
parameters {b_γ v_γ h_γ b_γβ v_γβ h_γβ : F}
parameters {b' v' h' : vector F n_wit}

-- Polynomial forms of the adversary's proof representation
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

#check V_wit


def satisfying_wit (a_stmt : vector F n_stmt) (a_wit : vector F n_wit) := 
polynomial.mod_by_monic (((vector.map₂ has_scalar.smul a_wit u_wit).to_list.sum + (vector.map₂ has_scalar.smul a_stmt (u_stmt : vector (polynomial F) n_stmt)).to_list.sum)^2) t = 1

-- Show that if the adversary polynomials obey the equations, then
lemma case_1 (a_stmt : vector F n_stmt) : (B_wit = Y_poly * V_wit) -> (H * (t.eval₂ mv_polynomial.C X_poly) + mv_polynomial.C 1 = (V_wit + (V_stmt a_stmt).eval₂ mv_polynomial.C X_poly)^2) -> (satisfying_wit a_stmt b')
:=
begin
  intros eqnI eqnII,
  have h1 : (∀ m : vars →₀ ℕ, m vars.Y = 0 -> B_wit.coeff m = 0),
  have h2 : b = vector.repeat 0 m,

end



-- TODOs
-- define Prove function, taking crs and a
-- Define verify
-- NOTE: Currently we are not "in the exponent"


-- def X_monomial (n : ℕ) : mv_polynomial vars F
-- := 
-- mv_polynomial.monomial (finsupp.single var.X n) 1

-- -- The set of all polynomials of the form of 
-- #check crs_polynomials.to_set


end