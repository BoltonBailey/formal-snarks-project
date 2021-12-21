/-
Author: Bolton Bailey
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

-- TODO we open mv_polynomial, so we should be able to delete a lot of `mv_polynomial.`
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

/-- The CRS elements 
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
def A (f : groth16.vars → F) : polynomial F := 
  polynomial.C A_α * (crs_α f)
  +
  polynomial.C A_β * (crs_β f)
  +
  polynomial.C A_δ * crs_δ f
  +
  ∑ i in (finset.fin_range n_var), polynomial.C (A_x i) * (crs_powers_of_x i f)
  +
  ∑ i in (finset.fin_range n_stmt), polynomial.C (A_l i) * (crs_l i f)
  +
  ∑ i in (finset.fin_range n_wit), polynomial.C (A_m i) * (crs_m i f)
  +
  ∑ i in (finset.fin_range (n_var-1)), polynomial.C (A_h i) * (crs_n i f)

def B (f : groth16.vars → F) : polynomial F  := 
  polynomial.C B_β * crs_β f
  + 
  polynomial.C B_γ * crs_γ f
  +
  polynomial.C B_δ * crs_δ f
  +
  ∑ i in (finset.fin_range n_var), polynomial.C (B_x i) * (crs_powers_of_x i f)

def C (f : groth16.vars → F) : polynomial F  := 
  polynomial.C C_α * crs_α f
  +
  polynomial.C C_β * crs_β f
  +
  polynomial.C C_δ * crs_δ f
  +
  ∑ i in (finset.fin_range n_var), polynomial.C (C_x i) * (crs_powers_of_x i f)
  +
  ∑ i in (finset.fin_range n_stmt), polynomial.C (C_l i) * (crs_l i f)
  +
  ∑ i in (finset.fin_range n_wit), polynomial.C (C_m i) * (crs_m i f)
  +
  ∑ i in (finset.fin_range (n_var-1)), polynomial.C (C_h i) * (crs_n i f)


local notation `groth16polynomial` := mv_polynomial vars (polynomial F)


/-- The modified CRS elements 
these are multivariate (non-Laurent!) polynomials of the toxic waste samples, 
obtained by multiplying the Laurent polynomial forms of the CRS through by γ * δ. 
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
  + 
  crs'_δ * mv_polynomial.C (polynomial.C (A_δ))
  +
  X vars.γ * X vars.δ * mv_polynomial.C ∑ i in (finset.fin_range n_var), (polynomial.C (A_x i) * polynomial.X ^ (i : ℕ))
  +
  ∑ i in (finset.fin_range n_stmt), (crs'_l i) * mv_polynomial.C (polynomial.C (A_l i))
  +
  ∑ i in (finset.fin_range n_wit), (crs'_m i) * mv_polynomial.C (polynomial.C (A_m i))
  +
  ∑ i in (finset.fin_range (n_var - 1)), (crs'_t i) * mv_polynomial.C (polynomial.C (A_h i))

/-- Polynomial form of B in the adversary's proof representation -/
def B'  : groth16polynomial := 
  crs'_β * mv_polynomial.C (polynomial.C (B_β))
  + 
  crs'_γ * mv_polynomial.C (polynomial.C (B_γ))
  +
  crs'_δ * mv_polynomial.C (polynomial.C (B_δ))
  +
  X vars.γ * X vars.δ * mv_polynomial.C ∑ i in (finset.fin_range n_var), (polynomial.C (B_x i) * polynomial.X ^ (i : ℕ))

/-- Polynomial form of C in the adversary's proof representation -/
def C'  : groth16polynomial := 
  crs'_α * mv_polynomial.C (polynomial.C (C_α))
  +
  crs'_β * mv_polynomial.C (polynomial.C (C_β))
  + 
  crs'_δ * mv_polynomial.C (polynomial.C (C_δ))
  +
  X vars.γ * X vars.δ * mv_polynomial.C ∑ i in (finset.fin_range n_var), (polynomial.C (C_x i) * polynomial.X ^ (i : ℕ))
  +
  ∑ i in (finset.fin_range n_stmt), (crs'_l i) * mv_polynomial.C (polynomial.C (C_l i))
  +
  ∑ i in (finset.fin_range n_wit), (crs'_m i) * mv_polynomial.C (polynomial.C (C_m i))
  +
  ∑ i in (finset.fin_range (n_var - 1)), (crs'_t i) * mv_polynomial.C (polynomial.C (C_h i))



def verified (a_stmt : fin n_stmt → F ) : Prop := A * B = crs_α * crs_β + (∑ i in finset.fin_range n_stmt, a_stmt i • crs_l i ) * crs_γ + C * crs_δ

def verified' (a_stmt : fin n_stmt → F ) : Prop := A' * B' = crs'_α * crs'_β + (∑ i in finset.fin_range n_stmt, mv_polynomial.C (polynomial.C (a_stmt i)) * crs'_l i ) * crs'_γ + C' * crs'_δ

-- TODO use this for lots of profiling data
-- set_option profiler true

/--
This lemma proves that the verification procedure succeeding on the unmodified (Laurent) CRS 
elements implies that it succeeds with the modified (mv_polynomial) CRS elements. This lets us put 
our hypotheses in terms of mv_polynomial equations.
-/
lemma modification_equivalence (a_stmt : fin n_stmt → F ) : 
  verified a_stmt -> verified' a_stmt
:=
begin
  -- TODO a few conditions likely still need to be added, such as degree bounds and the values 
  -- being nonzero.
  sorry,
  -- rw verified,
  -- rw verified',
  -- intro h,
  -- rw function.funext_iff at h,
  -- -- Apply functional extensionality
  -- simp [A, B, C] at h,

  -- rw mv_polynomial.funext_iff,
  -- intro vars_evaluation,
  -- simp [A', B', C'] with crs,
  -- -- apply polynomial.funext, -- TODO prove a version of this lemma for degree bounded polynomials on non infinite fields.
  -- -- intro x_evaluation,
  -- -- simp,
  -- -- simp [A', B', C'],
  -- -- simp with crs,

  -- have h2 := h vars_evaluation,
  -- done,

end


open finsupp

-- From page 9-10 of Baghery et al., we take the coefficients of the relevant monomials.

-- TODO mv_polynomial.smul_eq_C_mul necessary?
lemma coeff1122 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  polynomial.C A_α * polynomial.C B_β = 1
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  -- done,
  -- simp only [] with polynomial_nf_3 at eqdn,
  -- simp only [mul_add, add_mul, finset.sum_add_distrib, C_mul_C, finset.sum_hom, mul_assoc, mul_sum_symm,rearrange_constants_right, rearrange_constants_right_with_extra, rearrange_sums_right, rearrange_sums_right_with_extra] at eqn,
  have congr_coeff1122 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.δ 2 + single vars.γ 2)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1122,
  simp only [] with finsupp_simp at congr_coeff1122,
  exact congr_coeff1122,
end


lemma coeff0222 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
 polynomial.C A_β * polynomial.C B_β = 0
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff0222 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.δ 2 + single vars.γ 2)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0222,
  simp only [] with finsupp_simp at  congr_coeff0222,
  exact congr_coeff0222,
end

lemma coeff1023 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  polynomial.C A_α * polynomial.C B_γ = 0
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff1023 := congr_arg (coeff (single vars.α 1 + single vars.β 0 + single vars.δ 2 + single vars.γ 3)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1023,
  simp only [] with finsupp_simp at  congr_coeff1023,
  exact congr_coeff1023,
end

lemma coeff0212 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
   (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) * polynomial.C B_β = 0
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff0212 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.δ 1 + single vars.γ 2)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0212,
  simp only [] with finsupp_simp at  congr_coeff0212,
  exact congr_coeff0212,
end

lemma coeff1112 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) * polynomial.C B_β = 0
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff1112 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.δ 1 + single vars.γ 2)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1112,
  simp only [] with finsupp_simp at  congr_coeff1112,
  exact congr_coeff1112,
end



lemma coeff0112 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) *
          ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : ℕ) +
        (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) * polynomial.C B_β +
      (∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : ℕ) * t * polynomial.C (A_h x)) *
        polynomial.C B_β =
    0
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff0112 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.δ 1 + single vars.γ 2)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0112,
  simp only [] with finsupp_simp at  congr_coeff0112,
  exact congr_coeff0112,
end

lemma coeff0012 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) * ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : ℕ) + (∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : ℕ) * t * polynomial.C (A_h x)) * ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : ℕ ) = 0
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff0012 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.δ 1 + single vars.γ 2)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0012,
  simp only [] with finsupp_simp at  congr_coeff0012,
  exact congr_coeff0012,
end


lemma coeff0221 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
   (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) * polynomial.C B_β = 0
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff0221 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.δ 2 + single vars.γ 1)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0221,
  simp only [] with finsupp_simp at  congr_coeff0221,
  exact congr_coeff0221,
end


lemma coeff1121 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) * polynomial.C B_β = 0
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff1121 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.δ 2 + single vars.γ 1)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1121,
  simp only [] with finsupp_simp at  congr_coeff1121,
  exact congr_coeff1121,
end


lemma coeff0121 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) * ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : ℕ) + (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) * polynomial.C B_β = 0
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff0121 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.δ 2 + single vars.γ 1)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0121,
  simp only [] with finsupp_simp at  congr_coeff0121,
  exact congr_coeff0121,
end


lemma coeff0021 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) *
      ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) =
    0
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff0021 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.δ 2 + single vars.γ 1)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0021,
  simp only [] with finsupp_simp at  congr_coeff0021,
  exact congr_coeff0021,
end

lemma coeff0122 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  polynomial.C A_β * ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : ℕ) + (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : ℕ)) * polynomial.C B_β + (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) * polynomial.C B_γ + (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) * polynomial.C B_δ 
  = ∑ (x : fin n_stmt) in finset.fin_range n_stmt, polynomial.C (a_stmt x) * u_stmt x + ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (C_m x)
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff0122 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.δ 2 + single vars.γ 2)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0122,
  simp only [] with finsupp_simp at  congr_coeff0122,
  exact congr_coeff0122,
end




lemma coeff1022 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
polynomial.C A_α * ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : ℕ ) + (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) * polynomial.C B_γ + (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) * polynomial.C B_δ = ∑ (x : fin n_stmt) in finset.fin_range n_stmt, polynomial.C (a_stmt x) * v_stmt x + ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (C_m x)
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff1022 := congr_arg (coeff (single vars.α 1 + single vars.β 0 + single vars.δ 2 + single vars.γ 2)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1022,
  simp only [] with finsupp_simp at  congr_coeff1022,
  exact congr_coeff1022,
end

lemma coeff0022 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : ℕ)) * ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : ℕ) + (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) * polynomial.C B_γ + (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) * polynomial.C B_δ + (∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : ℕ) * t * polynomial.C (A_h x)) * polynomial.C B_δ = ∑ (x : fin n_stmt) in finset.fin_range n_stmt, polynomial.C (a_stmt x) * w_stmt x + (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (C_m x) + ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : ℕ) * t * polynomial.C (C_h x))
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only [] with crs at eqn,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqn,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn,
  have congr_coeff0022 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.δ 2 + single vars.γ 2)) eqn,
  clear eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0022,
  simp only [] with finsupp_simp at  congr_coeff0022,
  exact congr_coeff0022,
end


lemma A_α_mul (p : polynomial F) : p * polynomial.C A_α  = polynomial.C A_α * p := by ring

lemma B_β_mul (p : polynomial F) : p * polynomial.C B_β  = polynomial.C B_β * p := by ring

-- TODO Add to Mathlib next to C_eq_zero
@[simp] lemma polynomial.C_eq_one (a : F) : polynomial.C a = 1 ↔ a = 1 :=
calc polynomial.C a = 1 ↔ polynomial.C a = polynomial.C 1 : by rw polynomial.C_1
         ... ↔ a = 1 : polynomial.C_inj


lemma simplifier1 (x : fin n_stmt) (a_stmt : fin n_stmt → F ) 
  : polynomial.C (a_stmt x) * u_stmt x = u_stmt x * polynomial.C (a_stmt x)
  :=
  by ring

lemma simplifier2 (x : fin n_stmt) (a_stmt : fin n_stmt → F ) 
  : polynomial.C (a_stmt x) * v_stmt x = v_stmt x * polynomial.C (a_stmt x)
  :=
  by ring

lemma polynomial.mul_mod_by_monic (t p : polynomial F) (mt : t.monic) : (t * p) %ₘ t = 0 :=
begin
  rw polynomial.dvd_iff_mod_by_monic_eq_zero,
  apply dvd_mul_right,
  exact mt,
end

/-- The main theorem for the soundness of the Groth '16 SNARK. 
This shows that if the adversary polynomials obey the equations that the verification suggests,
then the C_m coefficients give a satisfying witness. -/
theorem soundness (a_stmt : fin n_stmt → F ) : 
  verified a_stmt
  -> (satisfying a_stmt C_m)
:=
begin
  
  intros eqn,
  rw satisfying,
  simp only [polynomial.smul_eq_C_mul, rearrange_constants_right_hard],
  suffices : 
    (∑ (i : fin n_stmt) in finset.fin_range n_stmt, u_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.fin_range n_wit, u_wit i * polynomial.C (C_m i)) 
    * 
    (∑ (i : fin n_stmt) in finset.fin_range n_stmt, v_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.fin_range n_wit, v_wit i * polynomial.C (C_m i)) 
    = 
    (∑ (i : fin n_stmt) in finset.fin_range n_stmt, w_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.fin_range n_wit, w_wit i * polynomial.C (C_m i)) 
    +
    ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : ℕ) * t * polynomial.C (C_h x),
  {
    rw <-sub_eq_iff_eq_add' at this,
    have h := congr_arg (%ₘ t) this,
    simp only at h,
    rw h,
    clear this h,
    conv
    begin
      to_lhs,
      congr,
      congr,
      skip,
      funext,
      rw mul_comm,   
      rw <-mul_assoc,
      skip,   
    end,
    rw <-finset.sum_mul,
    rw mul_comm,
    apply polynomial.mul_mod_by_monic,
    rw t,
    apply monic_of_product_form,
  },

  -- Step 0: Modify the hypothesis to be an equation of mv_polynomials
  have eqn' := modification_equivalence a_stmt (eqn),

  -- Step 1: Obtain the coefficient equations of the mv_polynomials
  have h0012 := coeff0012 a_stmt eqn',
  have h0021 := coeff0021 a_stmt eqn',
  have h0022 := coeff0022 a_stmt eqn',
  have h0112 := coeff0112 a_stmt eqn',
  have h0121 := coeff0121 a_stmt eqn',
  have h0122 := coeff0122 a_stmt eqn',
  have h0212 := coeff0212 a_stmt eqn',
  have h0221 := coeff0221 a_stmt eqn',
  have h0222 := coeff0222 a_stmt eqn',
  have h1022 := coeff1022 a_stmt eqn',
  have h1023 := coeff1023 a_stmt eqn',
  have h1112 := coeff1112 a_stmt eqn',
  have h1121 := coeff1121 a_stmt eqn',
  have h1122 := coeff1122 a_stmt eqn',

  -- The below alternative to the above which avoids the pre-stated lemmas doesn't run fast. 
  -- TODO: Debug why.
  -- rw verified' at eqn',
  -- rw [A', B', C'] at eqn',
  -- simp only [] with crs at eqn',
  -- simp only [] with polynomial_nf_3 at eqn',

  -- have h0012 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.γ 1 + single vars.δ 2)) eqn',
  -- have h0021 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.γ 2 + single vars.δ 1)) eqn',
  -- have h0022 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.γ 2 + single vars.δ 2)) eqn',
  -- have h0112 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.γ 1 + single vars.δ 2)) eqn',
  -- have h0121 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.γ 2 + single vars.δ 1)) eqn',
  -- have h0122 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.γ 2 + single vars.δ 2)) eqn',
  -- have h0212 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.γ 1 + single vars.δ 2)) eqn',
  -- have h0221 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.γ 2 + single vars.δ 1)) eqn',
  -- have h0222 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.γ 2 + single vars.δ 2)) eqn',
  -- have h1022 := congr_arg (coeff (single vars.α 1 + single vars.β 0 + single vars.γ 2 + single vars.δ 2)) eqn',
  -- have h1023 := congr_arg (coeff (single vars.α 1 + single vars.β 0 + single vars.γ 2 + single vars.δ 3)) eqn',
  -- have h1112 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.γ 1 + single vars.δ 2)) eqn',
  -- have h1121 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.γ 2 + single vars.δ 1)) eqn',
  -- have h1122 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.γ 2 + single vars.δ 2)) eqn',

  -- clear eqn eqn',

  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  -- simp only [] with finsupp_simp at *,

  -- done,


  -- Step 2: Recursively simplify and case-analyze the equations
  
  trace "Moving Cs right",
  simp only [simplifier1, simplifier2] at *,

  trace "Grouping distributivity",
  simp only [<-mul_add, <-add_mul, <-add_assoc, add_mul_distrib, add_mul_distrib'] at *,

  trace "Main simplification",
  simp only [*] with integral_domain_simp at *,
  tactic.integral_domain_tactic_v5,

  -- Solve remaining four cases by hand
  { rw [<-h1022, <-h0122, <-h0022],
    simp only [B_β_mul],
    simp only [<-mul_assoc],
    simp only [A_α_mul],
    simp only [<-mul_assoc],
    rw h1122,
    ring, },
  -- { rw [h1022, <-h0122, h0022],
  --   ring, },
  -- { rw [<-h1022, <-h0122, <-h0022],
  --   simp only [B_β_mul],
  --   simp only [<-mul_assoc],
  --   simp only [A_α_mul],
  --   simp only [<-mul_assoc],
  --   rw h1122,
  --   ring, },
  -- { rw [h1022, <-h0122, h0022],
  --   ring, }, 



end 

end groth16



