/-
Author: <Redacted for anonymized submission>
-/
-- import snarks.groth16.declarations
import ...attributes
import ...integral_domain_tactic
import ...general_lemmas.polynomial_degree
import data.mv_polynomial.basic
import data.mv_polynomial.funext
import data.polynomial.field_division
import algebra.polynomial.big_operators
-- import ...attributes
import .vars

/-!
# Knowledge Soundness

This file proves the knowledge-soundness property of the Groth16 system for type III pairings, as 
presented in "Another Look at Extraction and Randomization of Groth’s zk-SNARK" by 
[Baghery et al.](https://eprint.iacr.org/2020/811.pdf).

-/

open_locale big_operators classical

section groth16

open mv_polynomial groth16

noncomputable theory

universes u


/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]

/-- The naturals representing:
  n_stmt - the statement size, 
  n_wit - the witness size -/ 
parameters {n_stmt n_wit n_var : ℕ}

/-- u_stmt and u_wit are fin-indexed collections of polynomials from the square span program -/
parameter {u_stmt : fin n_stmt → (polynomial F) }
parameter {u_wit : fin n_wit → (polynomial F) }
parameter {v_stmt : fin n_stmt → (polynomial F) }
parameter {v_wit : fin n_wit → (polynomial F) }
parameter {w_stmt : fin n_stmt → (polynomial F) }
parameter {w_wit : fin n_wit → (polynomial F) }


/-- The roots of the polynomial t -/
parameter {r : fin n_wit → F} 
/-- t is the polynomial divisibility by which is used to verify satisfaction of the SSP -/
def t : polynomial F := ∏ i in (finset.fin_range n_wit), (polynomial.X - polynomial.C (r i))
-- TODO this could potentially be spun off into a mathlib definition


/-- Checks whether a statement witness pair satisfies the SSP -/
def satisfying (a_stmt : fin n_stmt → F ) (a_wit : fin n_wit → F) := 
((∑ i in (finset.fin_range n_stmt), a_stmt i • u_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • u_wit i))
  * 
(∑ i in (finset.fin_range n_stmt), a_stmt i • v_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • v_wit i))
  -
(∑ i in (finset.fin_range n_stmt), a_stmt i • w_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • w_wit i)))
   %ₘ t = 0


run_cmd mk_simp_attr `crs
run_cmd tactic.add_doc_string `simp_attr.crs "Attribute for defintions of CRS elements"

/-- The crs elements 
These funtions are actually multivariate Laurent polynomials of the toxic waste samples, 
but we represent them here as functions on assignments of the variables to values.
-/
@[crs]
def crs_α  (f : groth16.vars → F) : polynomial F := polynomial.C (f vars.α)
@[crs]
def crs_β (f : groth16.vars → F) : polynomial F := polynomial.C (f vars.β)
@[crs]
def crs_γ (f : groth16.vars → F) : polynomial F := polynomial.C (f vars.γ)
@[crs]
def crs_δ (f : groth16.vars → F) : polynomial F := polynomial.C (f vars.δ)
@[crs]
def crs_powers_of_x (i : fin n_var) (f : groth16.vars → F) : polynomial F := ((polynomial.X)^(i : ℕ))
@[crs]
def crs_l (i : fin n_stmt) (f : groth16.vars → F) : polynomial F := 
polynomial.C (1 / f vars.γ) * (polynomial.C (f vars.β / f vars.γ) * u_stmt i
+
polynomial.C  (f vars.α / f vars.γ) * v_stmt i
+
(w_stmt i)) 
@[crs]
def crs_m (i : fin n_wit) (f : groth16.vars → F) : polynomial F := 
polynomial.C (1 / f vars.δ) * (polynomial.C  (f vars.β / f vars.δ) * (u_wit i)
+
polynomial.C  (f vars.α / f vars.δ) * (v_wit i)
+
(w_wit i)) 
@[crs]
def crs_n (i : fin (n_var - 1)) (f : groth16.vars → F) : polynomial F := 
(polynomial.X)^(i : ℕ) * t * polynomial.C (1 / f vars.δ)

/-- The coefficients of the CRS elements in the algebraic adversary's representation -/
parameters {A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ  : F}
parameters {A_x B_x C_x : fin n_var → F}
parameters {A_l B_l C_l : fin n_stmt → F}
parameters {A_m B_m C_m : fin n_wit → F}
parameters {A_h B_h C_h : fin (n_var-1) → F}


/-- Polynomial forms of the adversary's proof representation -/
def A : (groth16.vars → F) -> polynomial F := λ f,
  polynomial.C A_α * (crs_α f)


def B : (groth16.vars → F) -> polynomial F  :=  λ f,
  polynomial.C B_β * crs_β f


def C : (groth16.vars → F) -> polynomial F  :=  λ f,
  polynomial.C C_α * crs_α f



local notation `groth16polynomial` := mv_polynomial vars (polynomial F)


/-- The modified crs elements 
these are multivariate (non-Laurent!) polynomials of the toxic waste samples, 
obtained by multiplying the Laurent polynomial forms of the CRS through by γδ. 
We will later prove that the laurent polynomial equation is equivalent to a similar equation of the modified crs elements, allowing us to construct a proof in terms of polynomials -/
@[crs]
def crs'_α  : groth16polynomial := X vars.α * X vars.γ * X vars.δ
@[crs]
def crs'_β : groth16polynomial := X vars.β * X vars.γ * X vars.δ
@[crs]
def crs'_γ : groth16polynomial := X vars.γ * X vars.γ * X vars.δ
@[crs]
def crs'_δ : groth16polynomial := X vars.δ * X vars.γ * X vars.δ
@[crs]
def crs'_powers_of_x (i : fin n_var) : (groth16polynomial) := mv_polynomial.C (polynomial.X ^ (i : ℕ)) * X vars.γ * X vars.δ
-- I define prodcuts of these crs elements without the division, then later claim identities. Is this right?
@[crs]
def crs'_l (i : fin n_stmt) : (groth16polynomial) := 
(X vars.β * X vars.δ) * mv_polynomial.C (u_stmt i)
+
(X vars.α * X vars.δ) * mv_polynomial.C (v_stmt i)
+
X vars.δ * mv_polynomial.C (w_stmt i)
@[crs]
def crs'_m (i : fin n_wit) : (groth16polynomial) := 
(X vars.β * X vars.γ) * mv_polynomial.C (u_wit i)
+
(X vars.α * X vars.γ) * mv_polynomial.C (v_wit i)
+
X vars.γ * mv_polynomial.C (w_wit i)
@[crs]
def crs'_t (i : fin (n_var - 1)) : (groth16polynomial) := 
X vars.γ * mv_polynomial.C ((polynomial.X)^(i : ℕ) * t)


/-- Polynomial form of A in the adversary's proof representation -/
def A'  : groth16polynomial := 
  crs'_α * mv_polynomial.C (polynomial.C (A_α))
  +
  crs'_β * mv_polynomial.C (polynomial.C (A_β))


/-- Polynomial form of B in the adversary's proof representation -/
def B'  : groth16polynomial := 
  crs'_β * mv_polynomial.C (polynomial.C (B_β))


/-- Polynomial form of C in the adversary's proof representation -/
def C'  : groth16polynomial := 
  crs'_α * mv_polynomial.C (polynomial.C (C_α))
  +
  crs'_β * mv_polynomial.C (polynomial.C (C_β))
  + 
  crs'_δ * mv_polynomial.C (polynomial.C (C_δ))






lemma modification_equivalence (a_stmt : fin n_stmt → F ) : 
  A * B = C -> A' * B' = C'
:=
begin
  -- TODO different now that we switch to mv_poly vars (poly F)
  -- rw verified,
  -- rw verified',
  intro h,
  -- Apply functional extensionality
  simp [A', B', C'],
  rw function.funext_iff at h,
  simp [A, B, C] at h,


end

end groth16