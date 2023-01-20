/-
Author: <Redacted for anonymized submission>
-/
-- import snarks.groth16.declarations
import ...attributes
import ...integral_domain_tactic
import ...general_lemmas.polynomial_degree
import ...general_lemmas.monomial_pow
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
[Baghery et al.](https://eprint.iacr.org/2020/811.pdf), for the Lipmaa SNARK

-/

open_locale big_operators classical

section lipmaa

-- TODO we open mv_polynomial, so we should be able to delete a lot of `mv_polynomial.`
open mv_polynomial

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



-- We choose the following exponents
-- def α : ℕ := 6 
-- def β : ℕ := 7
-- def γ : ℕ := 0
-- def δ : ℕ := 10
-- def η : ℕ := 5

def α : ℕ := 26 
def β : ℕ := 27
def γ : ℕ := 0
def δ : ℕ := 40
def η : ℕ := 24


/-- The roots of the polynomial t -/
parameter {r : fin n_wit → F} 
/-- l is the polynomial divisibility by which is used to verify satisfaction of the QAP -/
def l : polynomial F := ∏ i in (finset.fin_range n_wit), (polynomial.X - polynomial.C (r i))
-- TODO this could potentially be spun off into a mathlib definition


/-- Checks whether a statement witness pair satisfies the QAP -/
def satisfying (a_stmt : fin n_stmt → F ) (a_wit : fin n_wit → F) := 
((∑ i in (finset.fin_range n_stmt), a_stmt i • u_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • u_wit i))
  * 
(∑ i in (finset.fin_range n_stmt), a_stmt i • v_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • v_wit i))
  -
(∑ i in (finset.fin_range n_stmt), a_stmt i • w_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • w_wit i)))
   %ₘ l = 0

run_cmd mk_simp_attr `crs
run_cmd tactic.add_doc_string `simp_attr.crs "Attribute for defintions of CRS elements"

/-- The modified CRS elements, see fig 3 of the paper  -/
@[crs]
def crs'_P_all_wit_1 (i : fin n_wit) : mv_polynomial vars (polynomial F) := 
 (X vars.y) ^ (β - α + δ) * C (u_wit i) 
 + (X vars.y) ^ (β - α + γ) * C (v_wit i) 
 + (X vars.y) ^ (2 * β - α) * C (w_wit i) 
@[crs]
def crs'_P_α_1 : mv_polynomial vars (polynomial F) := 
 (X vars.y) ^ α
@[crs]
def crs'_P_powers_1 (i : fin n_var) : mv_polynomial vars (polynomial F) := 
 (X vars.y) ^ β * C (polynomial.X ^ (i : ℕ)) 
@[crs]
def crs'_P_l_1 (i : fin (n_var - 1)) : mv_polynomial vars (polynomial F) := 
 (X vars.y) ^ (2 * β - α) * C l * C (polynomial.X ^ (i : ℕ)) 
-- @[crs]
-- def crs'_P_γ_1 : mv_polynomial vars (polynomial F) := 
--  (X vars.y) ^ γ
@[crs]
def crs'_P_δ_1 : mv_polynomial vars (polynomial F) := 
 (X vars.y) ^ δ
@[crs]
def crs'_P_se_α_z_1 : mv_polynomial vars (polynomial F) := 
 (X vars.y) ^ α * (X vars.z) -- Only in S_qap^se
@[crs]
def crs'_P_se_powers_1 (i : fin n_var) : mv_polynomial vars (polynomial F) := 
 (X vars.y) ^ β * (X vars.z) * C (polynomial.X ^ (i : ℕ))  -- Only in S_qap^se
-- @[crs]
-- def crs'_P_α_2 : mv_polynomial vars (polynomial F) := 
--  (X vars.y) ^ α
@[crs]
def crs'_P_powers_2 (i : fin n_var) : mv_polynomial vars (polynomial F) := 
 (X vars.y) ^ β * C (polynomial.X ^ (i : ℕ)) -- same as crs'_P_powers_1

@[crs]
def crs'_V_all_stmt_1 (i : fin n_stmt) : mv_polynomial vars (polynomial F) := 
 (X vars.y) ^ (β - η + δ) * C (u_stmt i) 
 + (X vars.y) ^ (β - η + γ) * C (v_stmt i) 
 + (X vars.y) ^ (2 * β - η) * C (w_stmt i) 
-- @[crs]
-- def crs'_V_γ_1 : mv_polynomial vars (polynomial F) := 
--  (X vars.y) ^ γ -- Same as crs'_P_γ_1
@[crs]
def crs'_V_se_z_1 : mv_polynomial vars (polynomial F) := 
  (X vars.z) -- Only in S_qap^se
-- @[crs]
-- def crs'_V_α_2 : mv_polynomial vars (polynomial F) := 
--  (X vars.y) ^ α
@[crs]
def crs'_V_δ_2 : mv_polynomial vars (polynomial F) := 
  (X vars.y) ^ δ
@[crs]
def crs'_V_η_2 : mv_polynomial vars (polynomial F) := 
  (X vars.y) ^ η
@[crs]
def crs'_V_γ_δ_T : mv_polynomial vars (polynomial F) := 
  (X vars.y) ^ (γ + δ)

-- Elements both prover and verifier use

@[crs]
def crs'_γ_1 : mv_polynomial vars (polynomial F) := 
 (X vars.y) ^ γ
@[crs]
def crs'_α_2 : mv_polynomial vars (polynomial F) := 
 (X vars.y) ^ α


parameters {A_comp_crs'_P_all_wit_1 : fin n_wit → F}
parameters {A_comp_crs'_P_α_1 : F}
parameters {A_comp_crs'_P_powers_1 : fin n_var → F}
parameters {A_comp_crs'_P_l_1 : fin (n_var - 1) → F}
parameters {A_comp_crs'_γ_1 : F}
parameters {A_comp_crs'_P_δ_1 : F}
-- parameters {A_comp_crs'_P_se_α_z_1 : F}
-- parameters {A_comp_crs'_P_se_powers_1 : fin n_var → F}
parameters {A_comp_crs'_V_all_stmt_1 : fin n_stmt → F}
-- parameters {A_comp_crs'_V_γ_1 : F} -- Same as previous
-- parameters {A_comp_crs'_V_se_z_1 : F}


/-- Polynomial form of A in the adversary's proof representation -/
def A' : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs'_P_all_wit_1 i) * C (polynomial.C (A_comp_crs'_P_all_wit_1 i))
  +
  crs'_P_α_1 * C (polynomial.C (A_comp_crs'_P_α_1))
  +
  ∑ i in (finset.fin_range n_var), (crs'_P_powers_1 i) * C (polynomial.C (A_comp_crs'_P_powers_1 i))
  +
  ∑ i in (finset.fin_range (n_var - 1)), (crs'_P_l_1 i) * C (polynomial.C (A_comp_crs'_P_l_1 i))
  +
  crs'_γ_1 * C (polynomial.C (A_comp_crs'_γ_1))
  +
  crs'_P_δ_1 * C (polynomial.C (A_comp_crs'_P_δ_1))
  +
  ∑ i in (finset.fin_range n_stmt), (crs'_V_all_stmt_1 i) * C (polynomial.C (A_comp_crs'_V_all_stmt_1 i))


parameters {B_comp_crs'_α_2 : F}
parameters {B_comp_crs'_P_powers_2 : fin n_var → F}
-- parameters {B_comp_crs'_V_α_2 : F} -- Same as previous
parameters {B_comp_crs'_V_δ_2 : F}
parameters {B_comp_crs'_V_η_2 : F}

/-- Polynomial form of B in the adversary's proof representation -/
def B' : mv_polynomial vars (polynomial F) := 
  crs'_α_2 * C (polynomial.C (B_comp_crs'_α_2))
  +
  ∑ i in (finset.fin_range n_var), (crs'_P_powers_2 i) * C (polynomial.C (B_comp_crs'_P_powers_2 i))
  +
  crs'_V_δ_2 * C (polynomial.C (B_comp_crs'_V_δ_2))
  +
  crs'_V_η_2 * C (polynomial.C (B_comp_crs'_V_η_2))


parameters {C_comp_crs'_P_all_wit_1 : fin n_wit → F}
parameters {C_comp_crs'_P_α_1 : F}
parameters {C_comp_crs'_P_powers_1 : fin n_var → F}
parameters {C_comp_crs'_P_l_1 : fin (n_var - 1) → F}
parameters {C_comp_crs'_P_γ_1 : F}
parameters {C_comp_crs'_P_δ_1 : F}
-- parameters {C_comp_crs'_P_se_α_z_1 : F}
-- parameters {C_comp_crs'_P_se_powers_1 : fin n_var → F}
parameters {C_comp_crs'_V_all_stmt_1 : fin n_stmt → F}
-- parameters {C_comp_crs'_V_γ_1 : F} -- Same as previous
-- parameters {C_comp_crs'_V_se_z_1 : F}

/-- Polynomial form of C in the adversary's proof representation -/
def C' : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs'_P_all_wit_1 i) * C (polynomial.C (C_comp_crs'_P_all_wit_1 i))
  +
  crs'_P_α_1 * C (polynomial.C (C_comp_crs'_P_α_1))
  +
  ∑ i in (finset.fin_range n_var), (crs'_P_powers_1 i) * C (polynomial.C (C_comp_crs'_P_powers_1 i))
  +
  ∑ i in (finset.fin_range (n_var - 1)), (crs'_P_l_1 i) * C (polynomial.C (C_comp_crs'_P_l_1 i))
  +
  crs'_γ_1 * C (polynomial.C (C_comp_crs'_P_γ_1))
  +
  crs'_P_δ_1 * C (polynomial.C (C_comp_crs'_P_δ_1))
  +
  ∑ i in (finset.fin_range n_stmt), (crs'_V_all_stmt_1 i) * C (polynomial.C (C_comp_crs'_V_all_stmt_1 i))



def verified' (a_stmt : fin n_stmt → F ) : Prop :=
  (∑ i in finset.fin_range n_stmt, C (polynomial.C (a_stmt i)) * crs'_V_all_stmt_1 i ) * crs'_V_η_2 
  +
  C' * crs'_α_2 
  =
  (A' + crs'_γ_1) * (B' + crs'_V_δ_2) - crs'_V_γ_δ_T 

-- A, modified to be more like what we see in Baghery et al. - this includes athe extra y^γ we see 
-- that the verifier adds.

def A_mod_comp_crs_P_γ_1 := A_comp_crs'_γ_1 + 1

lemma A_mod_transform : 
  A' + crs'_γ_1 =
   ∑ i in (finset.fin_range n_wit), (crs'_P_all_wit_1 i) * C (polynomial.C (A_comp_crs'_P_all_wit_1 i))
  +
  crs'_P_α_1 * C (polynomial.C (A_comp_crs'_P_α_1))
  +
  ∑ i in (finset.fin_range n_var), (crs'_P_powers_1 i) * C (polynomial.C (A_comp_crs'_P_powers_1 i))
  +
  ∑ i in (finset.fin_range (n_var - 1)), (crs'_P_l_1 i) * C (polynomial.C (A_comp_crs'_P_l_1 i))
  +
  crs'_γ_1 * C (polynomial.C (A_mod_comp_crs_P_γ_1))
  +
  crs'_P_δ_1 * C (polynomial.C (A_comp_crs'_P_δ_1))
  +
  ∑ i in (finset.fin_range n_stmt), (crs'_V_all_stmt_1 i) * C (polynomial.C (A_comp_crs'_V_all_stmt_1 i)) :=
begin
  rw [A', A_mod_comp_crs_P_γ_1],
  simp only [mv_polynomial.C_add, ring_hom.map_add, ring_hom.map_one, mv_polynomial.C_1, mul_add, mul_one],
  abel,
end

-- B, modified to be more like what we see in Baghery et al. - this includes athe extra y^γ we see 
-- that the verifier adds. 

def B_mod_comp_crs_V_δ_2 := B_comp_crs'_V_δ_2 + 1

lemma B_mod_transform : 
  B' + crs'_V_δ_2 =
  crs'_α_2 * C (polynomial.C (B_comp_crs'_α_2))
  +
  ∑ i in (finset.fin_range n_var), (crs'_P_powers_2 i) * C (polynomial.C (B_comp_crs'_P_powers_2 i))
  +
  crs'_V_δ_2 * C (polynomial.C (B_mod_comp_crs_V_δ_2))
  +
  crs'_V_η_2 * C (polynomial.C (B_comp_crs'_V_η_2)) :=
begin
  rw [B', B_mod_comp_crs_V_δ_2],
  simp only [mv_polynomial.C_add, ring_hom.map_add, ring_hom.map_one, mv_polynomial.C_1, mul_add, mul_one],
  abel,
end


-- TODO use this for lots of profiling data
-- set_option profiler true

open finsupp

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

lemma A_mod_comp_crs_P_γ_1_mul (p : polynomial F) : p * polynomial.C A_mod_comp_crs_P_γ_1  = polynomial.C A_mod_comp_crs_P_γ_1 * p := by ring

lemma B_mod_comp_crs_V_δ_2_mul (p : polynomial F) : p * polynomial.C B_mod_comp_crs_V_δ_2  = polynomial.C B_mod_comp_crs_V_δ_2 * p := by ring


/-- The main theorem for the soundness of the Lipmaa SNARK. This fixed version does go through. -/
theorem soundness (a_stmt : fin n_stmt → F ) : 
  verified' a_stmt
  -> (satisfying a_stmt C_comp_crs'_P_all_wit_1)
:=
begin
  
  intros eqn',

  rw satisfying,
  simp only [polynomial.smul_eq_C_mul, rearrange_constants_right_hard],
  suffices : 
    (∑ (i : fin n_stmt) in finset.fin_range n_stmt, u_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.fin_range n_wit, u_wit i * polynomial.C (C_comp_crs'_P_all_wit_1  i)) 
    * 
    (∑ (i : fin n_stmt) in finset.fin_range n_stmt, v_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.fin_range n_wit, v_wit i * polynomial.C (C_comp_crs'_P_all_wit_1  i)) 
    = 
    (∑ (i : fin n_stmt) in finset.fin_range n_stmt, w_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.fin_range n_wit, w_wit i * polynomial.C (C_comp_crs'_P_all_wit_1  i)) 
    +
    ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), l * polynomial.X ^ (x : ℕ) * polynomial.C (C_comp_crs'_P_l_1 x),
  {
    rw <-sub_eq_iff_eq_add' at this,
    have h := congr_arg (%ₘ l) this,
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
    simp_rw mul_comm _ l,
    simp_rw mul_assoc,
    simp_rw mul_comm l _,
    rw <-finset.sum_mul,
    rw mul_comm,
    apply polynomial.mul_mod_by_monic,
    rw l,
    apply monic_of_product_form,
  },
  
  rw verified' at eqn',
  rw [A_mod_transform, B_mod_transform, C'] at eqn',
  simp only [] with crs at eqn',
  -- simp only [] with polynomial_nf_3 at eqn',
  simp only [α, β, γ, δ, η, algebra.id.smul_eq_mul, nat.succ_sub_succ, nat.sub_zero, nat.zero_mul, nat.mul_zero, nat.zero_add, nat.add_zero, nat.mul_succ, nat.add_succ] at eqn',
  -- done,
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, mv_polynomial.monomial_pow, finsupp.smul_single, one_pow, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqn',

  -- have h0 := congr_arg (coeff (single vars.y 0)) eqn',
  -- -- have h1 := congr_arg (coeff (single vars.y 1)) eqn',
  -- -- have h2 := congr_arg (coeff (single vars.y 2)) eqn',
  -- -- have h3 := congr_arg (coeff (single vars.y 3)) eqn',
  -- -- have h4 := congr_arg (coeff (single vars.y 4)) eqn',
  -- have h5 := congr_arg (coeff (single vars.y 5)) eqn',
  -- -- have h6 := congr_arg (coeff (single vars.y 6)) eqn',
  -- have h7 := congr_arg (coeff (single vars.y 7)) eqn',
  -- -- have h8 := congr_arg (coeff (single vars.y 8)) eqn',
  -- -- have h9 := congr_arg (coeff (single vars.y 9)) eqn',
  -- have h10 := congr_arg (coeff (single vars.y 10)) eqn',
  -- -- have h11 := congr_arg (coeff (single vars.y 11)) eqn',
  -- -- have h12 := congr_arg (coeff (single vars.y 12)) eqn',
  -- -- have h13 := congr_arg (coeff (single vars.y 13)) eqn',
  -- have h14 := congr_arg (coeff (single vars.y 14)) eqn',
  -- -- have h15 := congr_arg (coeff (single vars.y 15)) eqn',
  -- -- have h16 := congr_arg (coeff (single vars.y 16)) eqn',
  -- have h17 := congr_arg (coeff (single vars.y 17)) eqn',
  -- have h18 := congr_arg (coeff (single vars.y 18)) eqn',
  -- -- have h19 := congr_arg (coeff (single vars.y 19)) eqn',
  -- have h20 := congr_arg (coeff (single vars.y 20)) eqn',
  -- -- have h21 := congr_arg (coeff (single vars.y 21)) eqn',
  -- -- have h22 := congr_arg (coeff (single vars.y 22)) eqn',
  -- -- have h23 := congr_arg (coeff (single vars.y 23)) eqn',
  -- -- have h24 := congr_arg (coeff (single vars.y 24)) eqn',
  -- -- have h25 := congr_arg (coeff (single vars.y 25)) eqn',
  -- -- have h26 := congr_arg (coeff (single vars.y 26)) eqn',
  -- -- have h27 := congr_arg (coeff (single vars.y 27)) eqn',


-- def α : ℕ := 26 
-- def β : ℕ := 27
-- def γ : ℕ := 0
-- def δ : ℕ := 40
-- def η : ℕ := 24

  -- #eval 2 * β - (β-γ) * 0 + (δ-β) * 0 - (β-η) * 1 - (β-α) * 2
  -- #eval 2 * β - (β-γ) * 0 + (δ-β) * 0 - (β-η) * 2 - (β-α) * 1
  -- #eval 2 * β - (β-γ) * 0 + (δ-β) * 0 - (β-η) * 2 - (β-α) * 2
  -- #eval 2 * β - (β-γ) * 0 + (δ-β) * 1 - (β-η) * 1 - (β-α) * 2
  -- #eval 2 * β - (β-γ) * 0 + (δ-β) * 1 - (β-η) * 2 - (β-α) * 1
  -- #eval 2 * β - (β-γ) * 0 + (δ-β) * 1 - (β-η) * 2 - (β-α) * 2
  -- #eval 2 * β - (β-γ) * 0 + (δ-β) * 2 - (β-η) * 1 - (β-α) * 2
  -- #eval 2 * β - (β-γ) * 0 + (δ-β) * 2 - (β-η) * 2 - (β-α) * 1
  -- #eval 2 * β - (β-γ) * 0 + (δ-β) * 2 - (β-η) * 2 - (β-α) * 2
  -- #eval 2 * β - (β-γ) * 1 + (δ-β) * 0 - (β-η) * 2 - (β-α) * 2
  -- -- #eval 2 * β - (β-γ) * 1 + (δ-β) * 0 - (β-η) * 2 - (β-α) * 3
  -- #eval 2 * β - (β-γ) * 1 + (δ-β) * 1 - (β-η) * 1 - (β-α) * 2
  -- #eval 2 * β - (β-γ) * 1 + (δ-β) * 1 - (β-η) * 2 - (β-α) * 1
  -- #eval 2 * β - (β-γ) * 1 + (δ-β) * 1 - (β-η) * 2 - (β-α) * 2,


  have h0012 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 0 + (δ-β) * 0 + (β-η) * 1 + (β-α) * 0))) eqn',
  have h0021 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 0 + (δ-β) * 0 + (β-η) * 0 + (β-α) * 1))) eqn',
  have h0022 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 0 + (δ-β) * 0 + (β-η) * 0 + (β-α) * 0))) eqn',
  -- have h0022 := congr_arg (coeff (single vars.y (46))) eqn',
  have h0112 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 0 + (δ-β) * 1 + (β-η) * 1 + (β-α) * 0))) eqn',
  have h0121 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 0 + (δ-β) * 1 + (β-η) * 0 + (β-α) * 1))) eqn',
  have h0122 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 0 + (δ-β) * 1 + (β-η) * 0 + (β-α) * 0))) eqn',
  have h0212 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 0 + (δ-β) * 2 + (β-η) * 1 + (β-α) * 0))) eqn',
  have h0221 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 0 + (δ-β) * 2 + (β-η) * 0 + (β-α) * 1))) eqn',
  have h0222 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 0 + (δ-β) * 2 + (β-η) * 0 + (β-α) * 0))) eqn',
  have h1022 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 1 + (δ-β) * 0 + (β-η) * 0 + (β-α) * 0))) eqn',
  -- have h1023 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 1 + (δ-β) * 0 + (β-η) * 0 - (β-α) * 3))) eqn',
  have h1112 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 1 + (δ-β) * 1 + (β-η) * 1 + (β-α) * 0))) eqn',
  have h1121 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 1 + (δ-β) * 1 + (β-η) * 0 + (β-α) * 1))) eqn',
  have h1122 := congr_arg (coeff (single vars.y (2 * β - (β-γ) * 1 + (δ-β) * 1 + (β-η) * 0 + (β-α) * 0))) eqn',

  simp only [α, β, η, δ, γ, algebra.id.smul_eq_mul, nat.succ_sub_succ, nat.sub_zero, nat.zero_mul, nat.mul_zero, nat.zero_add, nat.add_zero, nat.mul_succ, nat.add_succ] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122,

  -- done,


  clear eqn',
  -- clear h0012 h0021 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122,

  -- done,


  simp only [finsupp_vars_eq_ext, mv_polynomial.coeff_sub] with coeff_simp finsupp_eq at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122,

  -- simp only [finsupp_vars_eq_ext, mv_polynomial.coeff_sub] with coeff_simp finsupp_eq at h0022,

  -- simp only [algebra.id.smul_eq_mul, nat.succ_sub_succ, nat.sub_zero, nat.zero_mul, nat.mul_zero, nat.mul_succ, nat.add_succ] with finsupp_simp at h0022,
  simp only [algebra.id.smul_eq_mul, nat.succ_sub_succ, sub_zero, nat.zero_mul, nat.mul_zero, nat.mul_succ, nat.add_succ] with finsupp_simp at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122,


  -- abel at *,
  rw sub_eq_zero at h1122,




  done,

  -- Step 2: Recursively simplify and case-analyze the equations
  
  trace "Moving Cs right",
  simp only [simplifier1, simplifier2] at *,

  trace "Grouping distributivity",
  simp only [<-mul_add, <-add_mul, <-add_assoc, add_mul_distrib, add_mul_distrib'] at *,

  have h1022' : 
    polynomial.C A_mod_comp_crs_P_γ_1 *
      ∑ (x : fin n_var) in finset.fin_range n_var,
        polynomial.X ^ (x : ℕ) * polynomial.C (B_comp_crs'_P_powers_2 x) +
      (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_comp_crs'_V_all_stmt_1 x)) *
        polynomial.C B_comp_crs'_V_η_2 +
    (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_comp_crs'_P_all_wit_1 x)) *
          polynomial.C B_comp_crs'_α_2 =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (a_stmt x) +
      ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (C_comp_crs'_P_all_wit_1 x),
  {
    rw h1022,
    ring,
  },

  have h0122' : 
    polynomial.C A_comp_crs'_P_δ_1 *
      ∑ (x : fin n_var) in finset.fin_range n_var,
        polynomial.X ^ (x : ℕ) * polynomial.C (B_comp_crs'_P_powers_2 x) +
    (∑ (x : fin n_var) in finset.fin_range n_var,
       polynomial.X ^ (x : ℕ) * polynomial.C (A_comp_crs'_P_powers_1 x)) *
            polynomial.C B_mod_comp_crs_V_δ_2 +
    (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_comp_crs'_V_all_stmt_1 x)) *
        polynomial.C B_comp_crs'_V_η_2 +
    (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_comp_crs'_P_all_wit_1 x)) *
              polynomial.C B_comp_crs'_α_2  =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (a_stmt x) +
      ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (C_comp_crs'_P_all_wit_1 x),
  {
    rw h0122,
    ring,
  },

  have h0022' : 
    (∑ (x : fin n_var) in finset.fin_range n_var,
      polynomial.X ^ (x : ℕ) * polynomial.C (A_comp_crs'_P_powers_1 x)) *
    ∑ (x : fin n_var) in finset.fin_range n_var,
      polynomial.X ^ (x : ℕ) * polynomial.C (B_comp_crs'_P_powers_2 x) +
    (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_comp_crs'_V_all_stmt_1 x)) *
        polynomial.C B_comp_crs'_V_η_2 +
    polynomial.C B_comp_crs'_α_2  * 
      ((∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_comp_crs'_P_all_wit_1 x)) +
       (∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1),
         l * polynomial.X ^ (x : ℕ) * polynomial.C (A_comp_crs'_P_l_1 x)))
    =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (a_stmt x) +
        ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (C_comp_crs'_P_all_wit_1 x) +
      ∑ (x : fin (n_var - 1)) in
        finset.fin_range (n_var - 1),
        l * polynomial.X ^ (x : ℕ) * polynomial.C (C_comp_crs'_P_l_1 x),
  {
    rw h0022,
    ring,
  },

  clear h0122 h1022 h0022,

  -- hack rewrites to get things the same as in the groth16typeIII 
  rw eq_comm at h0012 h0021 h0112 h0121 h0212 h0221 h0222 h1112 h1121 h1122 h0122' h1022' h0022',

  rw eq_comm at h0021 h0022' h0121 h0012 h0112 h0122' h1022' h0212 h0221 h0222 h1112 h1121 h1122,

  -- done,

  trace "Main simplification",
  simp only [*] with integral_domain_simp at *,

  -- have hγη : (1 + polynomial.C A_comp_crs'_P_γ_1) * polynomial.C B_comp_crs'_V_η_2 = 0,
  -- { rw add_mul, rw <-h5, ring, },
  -- rw mul_eq_zero at hγη,

  -- have hδδ : polynomial.C A_comp_crs'_P_δ_1 * (1 + polynomial.C B_comp_crs'_V_δ_2) = 0,
  -- { rw mul_add, rw <-h0222, ring, },
  -- rw mul_eq_zero at hδδ,

  -- have hγδ : (1 + polynomial.C A_comp_crs'_P_γ_1) * (1 + polynomial.C B_comp_crs'_V_δ_2) = 1,
  -- { rw <-sub_eq_zero, rw <-h1122, ring, },

  -- have hββ := h14,
  -- have hβγ := h7,
  -- have hβδ := h17,
  -- have hγγ := h0,
  -- have hγδ := h10,

  -- clear h0 h5 h7 h10 h14 h17 h20,




  tactic.integral_domain_tactic_v4,

  -- rw <-hβγ,
  -- rw <-hβδ,
  -- rw <-hββ,


  -- done,

  -- Solve remaining four cases by hand
  { rw [<-h1022', <-h0122', <-h0022'],
    simp only [B_mod_comp_crs_V_δ_2_mul],
    simp only [<-mul_assoc],
    simp only [A_mod_comp_crs_P_γ_1_mul],
    simp only [<-mul_assoc],
    rw h1122,
    ring, },




end 

end lipmaa



