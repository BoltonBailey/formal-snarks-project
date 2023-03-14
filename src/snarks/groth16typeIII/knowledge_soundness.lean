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
def t : polynomial F := ∏ i in (finset.univ : finset (fin n_wit)), (polynomial.X - polynomial.C (r i))
-- TODO this could potentially be spun off into a mathlib definition


/-- Checks whether a statement witness pair satisfies the SSP -/
def satisfying (a_stmt : fin n_stmt → F ) (a_wit : fin n_wit → F) := 
((∑ i in (finset.univ : finset (fin n_stmt)), a_stmt i • u_stmt i
  + (∑ i in (finset.univ : finset (fin n_wit)), a_wit i • u_wit i))
  * 
(∑ i in (finset.univ : finset (fin n_stmt)), a_stmt i • v_stmt i
  + (∑ i in (finset.univ : finset (fin n_wit)), a_wit i • v_wit i))
  -
(∑ i in (finset.univ : finset (fin n_stmt)), a_stmt i • w_stmt i
  + (∑ i in (finset.univ : finset (fin n_wit)), a_wit i • w_wit i)))
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
  ∑ i in ((finset.univ : finset (fin n_var))), polynomial.C (A_x i) * (crs_powers_of_x i f)
  +
  ∑ i in (finset.univ : finset (fin n_stmt)), polynomial.C (A_l i) * (crs_l i f)
  +
  ∑ i in (finset.univ : finset (fin n_wit)), polynomial.C (A_m i) * (crs_m i f)
  +
  ∑ i in (finset.univ : finset (fin (n_var-1))), polynomial.C (A_h i) * (crs_n i f)

def B (f : groth16.vars → F) : polynomial F  := 
  polynomial.C B_β * crs_β f
  + 
  polynomial.C B_γ * crs_γ f
  +
  polynomial.C B_δ * crs_δ f
  +
  ∑ i in ((finset.univ : finset (fin n_var))), polynomial.C (B_x i) * (crs_powers_of_x i f)

def C (f : groth16.vars → F) : polynomial F  := 
  polynomial.C C_α * crs_α f
  +
  polynomial.C C_β * crs_β f
  +
  polynomial.C C_δ * crs_δ f
  +
  ∑ i in ((finset.univ : finset (fin n_var))), polynomial.C (C_x i) * (crs_powers_of_x i f)
  +
  ∑ i in (finset.univ : finset (fin n_stmt)), polynomial.C (C_l i) * (crs_l i f)
  +
  ∑ i in (finset.univ : finset (fin n_wit)), polynomial.C (C_m i) * (crs_m i f)
  +
  ∑ i in (finset.univ : finset (fin (n_var-1))), polynomial.C (C_h i) * (crs_n i f)


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
  X vars.γ * X vars.δ * mv_polynomial.C ∑ i in ((finset.univ : finset (fin n_var))), (polynomial.C (A_x i) * polynomial.X ^ (i : ℕ))
  +
  ∑ i in (finset.univ : finset (fin n_stmt)), (crs'_l i) * mv_polynomial.C (polynomial.C (A_l i))
  +
  ∑ i in (finset.univ : finset (fin n_wit)), (crs'_m i) * mv_polynomial.C (polynomial.C (A_m i))
  +
  ∑ i in (finset.univ : finset (fin (n_var-1))), (crs'_t i) * mv_polynomial.C (polynomial.C (A_h i))

/-- Polynomial form of B in the adversary's proof representation -/
def B'  : groth16polynomial := 
  crs'_β * mv_polynomial.C (polynomial.C (B_β))
  + 
  crs'_γ * mv_polynomial.C (polynomial.C (B_γ))
  +
  crs'_δ * mv_polynomial.C (polynomial.C (B_δ))
  +
  X vars.γ * X vars.δ * mv_polynomial.C ∑ i in ((finset.univ : finset (fin n_var))), (polynomial.C (B_x i) * polynomial.X ^ (i : ℕ))

/-- Polynomial form of C in the adversary's proof representation -/
def C'  : groth16polynomial := 
  crs'_α * mv_polynomial.C (polynomial.C (C_α))
  +
  crs'_β * mv_polynomial.C (polynomial.C (C_β))
  + 
  crs'_δ * mv_polynomial.C (polynomial.C (C_δ))
  +
  X vars.γ * X vars.δ * mv_polynomial.C ∑ i in ((finset.univ : finset (fin n_var))), (polynomial.C (C_x i) * polynomial.X ^ (i : ℕ))
  +
  ∑ i in (finset.univ : finset (fin n_stmt)), (crs'_l i) * mv_polynomial.C (polynomial.C (C_l i))
  +
  ∑ i in (finset.univ : finset (fin n_wit)), (crs'_m i) * mv_polynomial.C (polynomial.C (C_m i))
  +
  ∑ i in (finset.univ : finset (fin (n_var-1))), (crs'_t i) * mv_polynomial.C (polynomial.C (C_h i))



def verified (a_stmt : fin n_stmt → F ) : Prop := A * B = crs_α * crs_β + (∑ i in (finset.univ : finset (fin n_stmt)), a_stmt i • crs_l i ) * crs_γ + C * crs_δ

def verified' (a_stmt : fin n_stmt → F ) : Prop := A' * B' = crs'_α * crs'_β + (∑ i in (finset.univ : finset (fin n_stmt)), mv_polynomial.C (polynomial.C (a_stmt i)) * crs'_l i ) * crs'_γ + C' * crs'_δ

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

set_option trace.simp_lemmas true

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
    (∑ (i : fin n_stmt) in finset.univ, u_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.univ, u_wit i * polynomial.C (C_m i)) 
    * 
    (∑ (i : fin n_stmt) in finset.univ, v_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.univ, v_wit i * polynomial.C (C_m i)) 
    = 
    (∑ (i : fin n_stmt) in finset.univ, w_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.univ, w_wit i * polynomial.C (C_m i)) 
    +
    ∑ (x : fin (n_var - 1)) in finset.univ, polynomial.X ^ (x : ℕ) * t * polynomial.C (C_h x),
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
  -- done,

  -- Step 1: Obtain the coefficient equations of the mv_polynomials

  rw verified' at eqn',
  rw [A', B', C'] at eqn',
  simp only [] with crs at eqn',
  -- simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn',

  have h0012 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.γ 1 + single vars.δ 2)) eqn',
  have h0021 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.γ 2 + single vars.δ 1)) eqn',
  have h0022 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.γ 2 + single vars.δ 2)) eqn',
  have h0112 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.γ 1 + single vars.δ 2)) eqn',
  have h0121 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.γ 2 + single vars.δ 1)) eqn',
  have h0122 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.γ 2 + single vars.δ 2)) eqn',
  have h0212 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.γ 1 + single vars.δ 2)) eqn',
  have h0221 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.γ 2 + single vars.δ 1)) eqn',
  have h0222 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.γ 2 + single vars.δ 2)) eqn',
  have h1022 := congr_arg (coeff (single vars.α 1 + single vars.β 0 + single vars.γ 2 + single vars.δ 2)) eqn',
  -- have h1023 := congr_arg (coeff (single vars.α 1 + single vars.β 0 + single vars.γ 2 + single vars.δ 3)) eqn', -- not needed
  have h1112 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.γ 1 + single vars.δ 2)) eqn',
  have h1121 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.γ 2 + single vars.δ 1)) eqn',
  have h1122 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.γ 2 + single vars.δ 2)) eqn',

  clear eqn eqn',

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122,
  simp only [] with finsupp_simp at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122,



  -- Step 2: Recursively simplify and case-analyze the equations
  
  trace "Moving Cs right",
  simp only [simplifier1, simplifier2] at *,

  trace "Grouping distributivity",
  simp only [<-mul_add, <-add_mul, <-add_assoc, add_mul_distrib, add_mul_distrib'] at *,

  -- done,

  trace "Main simplification",
  simp only [*] with integral_domain_simp at *,
  tactic.integral_domain_tactic_v4,

  -- done,


  -- Solve remaining cases by hand
  { rw [<-h1022, <-h0122, <-h0022],
    simp only [B_β_mul],
    simp only [<-mul_assoc],
    simp only [A_α_mul],
    simp only [<-mul_assoc],
    rw h1122,
    ring, },




end 

end groth16



