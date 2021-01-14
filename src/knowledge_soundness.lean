/-
Author: Bolton Bailey
-/
import data.mv_polynomial.basic
import data.polynomial.div
import data.polynomial.field_division
import .mv_divisability
import .vars

/-!
# Knowledge Soundness

This file proves the knowledge-soundness property of the 
[Baby SNARK](https://github.com/initc3/babySNARK) system, 
as described in section 5 of the paper.

-/

section

noncomputable theory


universes u


-- /-- An inductive type from which to index the variables of the 3-variable polynomials the proof manages -/
-- @[derive decidable_eq]
-- inductive vars : Type
-- | X : vars
-- | Y : vars
-- | Z : vars

/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]


/-- Helpers for representing X, Y, Z as 3-variable polynomials -/
def X_poly : mv_polynomial vars F := mv_polynomial.X vars.X
def Y_poly : mv_polynomial vars F := mv_polynomial.X vars.Y
def Z_poly : mv_polynomial vars F := mv_polynomial.X vars.Z

/-- Lemmas for handling these these as monomials -/
lemma X_poly_mon : X_poly = mv_polynomial.monomial (finsupp.single vars.X 1) 1
:= 
begin
  rw X_poly,
  rw mv_polynomial.X,
end
lemma Y_poly_mon : Y_poly = mv_polynomial.monomial (finsupp.single vars.Y 1) 1
:= 
begin
  rw Y_poly,
  rw mv_polynomial.X,
end
lemma Z_poly_mon : Z_poly = mv_polynomial.monomial (finsupp.single vars.Z 1) 1
:= 
begin
  rw Z_poly,
  rw mv_polynomial.X,
end


-- /-- Vector form of range function -/
-- def vector_range (k : ℕ) : vector ℕ k :=
-- ⟨list.range k, by simp⟩
-- /- TODO ask mathlib maintainers to add vector.range to mathlib -/
-- -- mathlib people suggest using fin n \to R instead of vectors


/-- The naturals representing the number of gates in the circuit, the statement size, and witness size repectively-/ 
parameters {m n_stmt n_wit : ℕ}
def n := n_stmt + n_wit
-- NOTE: In the paper, n_stmt is l and n_wit is n-l. Here, n is defined from these values.


/-- u_stmt and u_wit are fin-indexed collections of polynomials from the square span program -/
parameter {u_stmt : fin n_stmt → (polynomial F) }
parameter {u_wit : fin n_wit → (polynomial F) }



/-- The polynomial divisibility by which is used to verify satisfaction of the SSP -/
def r : fin m → F := (λ i, (i : F))
/-- (X - r_1) ... (X - r_m) -/
def t : polynomial F := finset.prod (finset.fin_range m) (λ i, polynomial.X - polynomial.C (i.1 : F))

def mv_t : mv_polynomial vars F := t.eval₂ mv_polynomial.C X_poly

-- /-- Checks whether a witness satisfies the SSP -/
-- def satisfying_wit (a_stmt : fin n_stmt → F ) (a_wit : fin n_wit → F) := 
-- polynomial.mod_by_monic ((finset.sum (finset.fin_range n_stmt) (λ i, a_stmt i • u_stmt i))^2) t = 1

/-- Checks whether a witness satisfies the SSP -/
def satisfying_wit (a_stmt : fin n_stmt → F ) (a_wit : fin n_wit → F) := 
((finset.sum (finset.fin_range n_stmt) (λ i, a_stmt i • u_stmt i))^2) % t = 1

-- TODO rewrite without lambdas
/-- The crs elements as multivariate polynomials of the toxic waste samples -/
def crs_powers_of_τ : fin m → (mv_polynomial vars F) := (λ i, X_poly^(i : ℕ))
def crs_γ : mv_polynomial vars F := Z_poly
def crs_γβ : mv_polynomial vars F := Z_poly * Y_poly
def crs_β_ssps : fin n_wit → (mv_polynomial vars F) := (λ i, (Y_poly) * (u_wit i).eval₂ mv_polynomial.C X_poly) 

/-- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def V_stmt_sv (a_stmt : fin n_stmt → F) : polynomial F 
:= finset.sum (finset.fin_range n_stmt) (λ i, a_stmt i • u_stmt i)

/-- V_stmt as a multivariable polynomial of vars.X -/
def V_stmt (a_stmt : fin n_stmt → F) : mv_polynomial vars F 
:= (V_stmt_sv a_stmt).eval₂ mv_polynomial.C X_poly

/-- The coefficients of the CRS elements in the algebraic adversary's representation -/
parameters {b v h : fin m → F}
parameters {b_γ v_γ h_γ b_γβ v_γβ h_γβ : F}
parameters {b' v' h' : fin n_wit → F}

-- TODO use unicode for finset.sum

/-- Polynomial forms of the adversary's proof representation -/
def B_wit  : mv_polynomial vars F := 
  finset.sum (finset.fin_range m) (λ i, (b i) • (crs_powers_of_τ i))
  +
  b_γ • crs_γ
  +
  b_γβ • crs_γβ
  +
  finset.sum (finset.fin_range n_wit) (λ i, (b' i) • (crs_β_ssps i))

def V_wit : mv_polynomial vars F := 
  finset.sum (finset.fin_range m) (λ i, (v i) • (crs_powers_of_τ i))
  +
  v_γ • crs_γ
  +
  v_γβ • crs_γβ
  +
  finset.sum (finset.fin_range n_wit) (λ i, (v' i) • (crs_β_ssps i))

def H : mv_polynomial vars F := 
  finset.sum (finset.fin_range m) (λ i, (h i) • (crs_powers_of_τ i))
  +
  h_γ • crs_γ
  +
  h_γβ • crs_γβ
  +
  finset.sum (finset.fin_range n_wit) (λ i, (h' i) • (crs_β_ssps i))


-- TODO move helper lemmas to another file?

/-- Helper lemma for main theorem -/
lemma helper_lemma_1 (j : fin m) : (λ x : fin m, mv_polynomial.coeff (finsupp.single vars.X ↑j) (b x • X_poly ^ (x : ℕ))) 
= (λ x : fin m, ite (x = j) (b x) 0)
:=
begin
  apply funext,
  intro x,
  rw X_poly,
  rw mv_polynomial.X_pow_eq_single,
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.C_mul_monomial,
  rw mul_one,
  -- rw mv_polynomial.coeff_C_mul,
  rw mv_polynomial.coeff_monomial,
  by_cases x = j,
  have h1 : finsupp.single vars.X ↑x = finsupp.single vars.X ↑j,
  rw h,
  rw h1,
  rw if_pos,
  rw if_pos,
  exact h,
  refl,
  rw if_neg,
  rw if_neg,
  exact h,
  rw finsupp.single_eq_single_iff,
  simp,
  intro foo,
  cases foo,
  have h5 : x = j,
  apply (fin.eq_iff_veq x j).2,
  exact foo,
  exact h (h5),
  have h6 : ↑x = ↑j,
  rw foo.left,
  rw foo.right,
  have h5 : x = j,
  apply (fin.eq_iff_veq x j).2,
  exact h6,
  exact h h5,
  -- TODO rename foo, h5, h6
end

/-- Helper lemma for main theorem -/
lemma helper_lemma_2 (j : fin m) : (λ (x : fin n_wit), mv_polynomial.coeff (finsupp.single vars.X ↑j) (b' x • (mv_polynomial.monomial (finsupp.single vars.Y 1) 1 * polynomial.eval₂ mv_polynomial.C X_poly (u_wit x))))
= (λ x : fin n_wit, 0)
:=
begin
  apply funext,
  intro x,
  rw X_poly,
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.coeff_C_mul,
  simp,
  right,
  rw mul_comm,
  rw ← Y_poly_mon,
  rw Y_poly,
  rw mv_polynomial.mul_var_no_constant,
  rw finsupp.single_apply,
  rw if_neg,
  simp,
end

/-- Helper lemma for main theorem -/
lemma helper_lemma_3 : (λ x : fin m, mv_polynomial.coeff (finsupp.single vars.Z 1) (b x • X_poly ^ (x : ℕ))) 
= (λ x : fin m,  0)
:=
begin
  apply funext,
  intro x,
  rw X_poly,
  rw mv_polynomial.X_pow_eq_single,
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.C_mul_monomial,
  rw mul_one,
  -- rw mv_polynomial.coeff_C_mul,
  rw mv_polynomial.coeff_monomial,
  rw if_neg,
  rw finsupp.single_eq_single_iff,
  simp,
end

/-- Helper lemma for main theorem -/
lemma helper_lemma_4 : (λ (x : fin n_wit), mv_polynomial.coeff (finsupp.single vars.Z 1) (b' x • (mv_polynomial.monomial (finsupp.single vars.Y 1) 1 * polynomial.eval₂ mv_polynomial.C X_poly (u_wit x))))
= (λ x : fin n_wit, 0)
:=
begin
  apply funext,
  intro x,
  rw X_poly,
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.coeff_C_mul,
  simp,
  right,
  rw mul_comm,
  rw ← Y_poly_mon,
  rw Y_poly,
  rw mv_polynomial.mul_var_no_constant,
  rw finsupp.single_apply,
  rw if_neg,
  simp,
end

lemma helper_lemma_5 : (∀ i, b i = 0) -> (λ (i : fin m), b i • crs_powers_of_τ i) = (λ (i : fin m), 0)
:=
begin
  intro tmp,
  apply funext,
  intro x,
  rw tmp x,
  simp,
end

lemma helper_lemma_6 : (λ (x : fin m), mv_polynomial.coeff (finsupp.single vars.Z 2) (h x • crs_powers_of_τ x)) = λ x, 0
:=
begin
  apply funext,
  intro x,
  rw crs_powers_of_τ,
  rw X_poly,
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.coeff_C_mul,
  simp,
  rw mv_polynomial.X_pow_eq_single,
  rw mv_polynomial.coeff_monomial,
  rw if_neg,
  simp,
  rw finsupp.single_eq_single_iff,
  simp,
  intro,
  exact two_ne_zero,
end

/-- The antidiagonal of Z^2 consists of three elements -/
lemma square_antidiagonal : (finsupp.single vars.Z 2).antidiagonal.support = 
{
  (finsupp.single vars.Z 0, finsupp.single vars.Z 2), 
  (finsupp.single vars.Z 1, finsupp.single vars.Z 1), 
  (finsupp.single vars.Z 2, finsupp.single vars.Z 0), 
}
:=
begin
  rw finset.ext_iff,
  intro a,
  rw finsupp.mem_antidiagonal_support,
  split,
  intro h,
  simp,
  have h1 : ∃ i , a.fst = finsupp.single vars.Z i ∧ i ≤ 2 ∧ a.snd = finsupp.single vars.Z (2-i),
  use a.fst vars.Z,
  split,
  rw finsupp.ext_iff,
  intro a1,
  by_cases h2 : a1 = vars.Z,
  rw h2,
  rw finsupp.single_apply,
  rw if_pos,
  simp,
  rw finsupp.single_apply,
  rw if_neg,
  rw finsupp.ext_iff at h,
  let h3 := h a1,
  rw finsupp.single_apply at h3,
  rw if_neg at h3,
  rw finsupp.add_apply at h3,
  rw add_eq_zero_iff at h3,
  exact h3.left,
  intro h4,
  rw h4 at h2,
  exact h2 (refl a1),
  intro h4,
  rw h4 at h2,
  exact h2 (refl a1),
  rw finsupp.ext_iff at h,
  let h5 := h vars.Z,
  rw finsupp.single_apply at h5,
  rw if_pos at h5,
  rw finsupp.add_apply at h5,
  split,
  exact nat.le.intro h5,
  rw finsupp.ext_iff,
  intro a1,
  by_cases h2 : a1 = vars.Z,
  rw h2,
  rw finsupp.single_apply,
  rw if_pos,
  exact (norm_num.sub_nat_pos 2 ((a.fst) vars.Z) ((a.snd) vars.Z) h5).symm,
  refl,
  rw finsupp.single_apply,
  rw if_neg,
  let h6 := h a1,
  rw finsupp.single_apply at h6,
  rw if_neg at h6,
  rw finsupp.add_apply at h6,
  rw add_comm at h6,
  exact nat.eq_zero_of_add_eq_zero_right h6,
    intro h4,
  rw h4 at h2,
  exact h2 (refl a1),
    intro h4,
  rw h4 at h2,
  exact h2 (refl a1),
  refl,
  -- h1 done
  cases h1,
  cases h1_h,
  cases h1_h_right,



  -- case 2,
  have h6 := eq_or_lt_of_le h1_h_right_left,
  cases h6,
  right,
  right,
  rw h6 at h1_h_left,
  rw h6 at h1_h_right_right,
  have h7 : a.snd = 0,
  rw h1_h_right_right,
  have h8 : 2-2 = 0,
  simp,
  rw h8,
  simp,
  exact prod.ext h1_h_left h7,
  have h6_2 : h1_w ≤ 1,
  exact nat.lt_succ_iff.mp h6,
  clear h6,
  -- case 1
  have h6 := eq_or_lt_of_le h6_2,
  cases h6,
  right,
  left,
  rw h6 at h1_h_left,
  rw h6 at h1_h_right_right,
  have h7 : a.snd = finsupp.single vars.Z (1),
  rw h1_h_right_right,
  have h8 : 2-1 = 1,
  simp,
  exact prod.ext h1_h_left h7,
  clear h6_2,
  have h6_2 : h1_w ≤ 0,
  exact nat.lt_succ_iff.mp h6,
  clear h6,
  -- case 0
  have h6 := eq_or_lt_of_le h6_2,
  cases h6,
  left,
  rw h6 at h1_h_left,
  rw h6 at h1_h_right_right,
  have h7 : a.snd = finsupp.single vars.Z (2),
  rw h1_h_right_right,
  have h8 : 2-0 = 2,
  simp,
  simp at h1_h_left,
  exact prod.ext h1_h_left h7,
  have f : false,
  exact nat.not_lt_zero h1_w h6,
  exfalso,
  exact f,

  -- FOrward case
  simp,
  intro h,
  cases h,
  have h1 : a.fst = 0,
  exact (congr_arg prod.fst h).trans rfl,
  have h2 : a.snd = finsupp.single vars.Z 2,
  exact (congr_arg prod.snd h).trans rfl,
  rw [h1, h2],
  simp,
  cases h,
  have h1 : a.fst = finsupp.single vars.Z 1,
  exact (congr_arg prod.fst h).trans rfl,
  have h2 : a.snd = finsupp.single vars.Z 1,
  exact (congr_arg prod.snd h).trans rfl,
  rw [h1, h2],
  rw ← finsupp.single_add,
  have h1 : a.fst = finsupp.single vars.Z 2,
  exact (congr_arg prod.fst h).trans rfl,
  have h2 : a.snd = 0,
  exact (congr_arg prod.snd h).trans rfl,
  rw [h1, h2],
  simp,


end


-- TODO encapsulate all evals in their own multivariablification varaibles

/-- Show that if the adversary polynomials obey the equations, then the coefficients give a satisfying witness -/
lemma case_1 (a_stmt : fin n_stmt → F ) : 
  (B_wit = V_wit * Y_poly) 
  -> (H * mv_t + mv_polynomial.C 1 = (V_wit + V_stmt a_stmt)^2) 
  -> (satisfying_wit a_stmt b')
:=
begin
  intros eqnI eqnII,
  -- B_wit has no terms with no Y component
  have h1 : (∀ m : vars →₀ ℕ, m vars.Y = 0 -> B_wit.coeff m = 0),
  rw eqnI,
  apply mv_polynomial.mul_var_no_constant V_wit vars.Y,
  have h2 : ∀ i : fin m, b i = 0,
  have h2_1 : (∀ (i : fin m), B_wit.coeff (finsupp.single vars.X i) = b i),
  intro j,
  rw B_wit,
  simp,
  rw [crs_powers_of_τ, crs_γ, crs_γβ, crs_β_ssps],
  simp,
  repeat {rw mv_polynomial.smul_eq_C_mul},
  repeat {rw mv_polynomial.coeff_C_mul},
  repeat {rw mv_polynomial.coeff_sum},
  rw Y_poly_mon,
  rw Z_poly_mon,
  rw mv_polynomial.monomial_mul,
  repeat {rw mv_polynomial.coeff_monomial},
  rw if_neg,
  rw if_neg,
  simp,
  rw helper_lemma_1,
  rw finset.sum_ite,
  simp,
  rw finset.filter_eq',
  rw if_pos,
  rw finset.sum_singleton,
  rw helper_lemma_2,
  simp,
  simp,
  rw finsupp.ext_iff,
  simp,
  refine ⟨vars.Y, _ ⟩,
  repeat { rw finsupp.single_apply },
  simp,
  rw finsupp.single_eq_single_iff,
  simp,
  -- h2_1 done
  intro i,
  have tmp := h2_1 i,
  rw ← tmp,
  rw eqnI,
  apply mv_polynomial.mul_var_no_constant,
  rw finsupp.single_apply,
  rw if_neg,
  simp,
  -- h2 done
  have h3 : b_γ = 0,
  have h3_1 : B_wit.coeff (finsupp.single vars.Z 1) = b_γ,
  rw B_wit,
  simp,
  rw [crs_powers_of_τ, crs_γ, crs_γβ, crs_β_ssps],
  simp,
  repeat {rw mv_polynomial.smul_eq_C_mul},
  repeat {rw mv_polynomial.coeff_C_mul},
  repeat {rw mv_polynomial.coeff_sum},
  rw Y_poly_mon,
  rw Z_poly_mon,
  rw mv_polynomial.monomial_mul,
  repeat {rw mv_polynomial.coeff_monomial},
  rw if_pos,
  rw if_neg,
  -- simp,
  rw helper_lemma_3,
  -- simp,
  rw helper_lemma_4,
  simp,
  rw finsupp.ext_iff,
  simp,
  refine ⟨vars.Y, _ ⟩,
  repeat { rw finsupp.single_apply },
  simp,
  -- h3_1 done
  rw ← h3_1,
  rw eqnI,
  apply mv_polynomial.mul_var_no_constant,
  rw finsupp.single_apply,
  rw if_neg,
  simp,
  -- h3 done
  have h4 : B_wit = b_γβ • crs_γβ + finset.sum (finset.fin_range n_wit) (λ i, (b' i) • (crs_β_ssps i)),
  rw B_wit,
  rw helper_lemma_5 h2,
  rw h3,
  simp,
  -- h4 done
  have h5 : V_wit = b_γβ • Z_poly + finset.sum (finset.fin_range n_wit) (λ i, (b' i) • ((u_wit i).eval₂ mv_polynomial.C X_poly)),
  have h5_1 : B_wit = Y_poly * (b_γβ • Z_poly + finset.sum (finset.fin_range n_wit) (λ i, (b' i) • ((u_wit i).eval₂ mv_polynomial.C X_poly))),
  rw h4,
  rw crs_γβ,
  rw crs_β_ssps,
  rw mul_add,
  have h5_1_1 : b_γβ • (Z_poly * Y_poly) = Y_poly * b_γβ • Z_poly,
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.smul_eq_C_mul,
  rw mul_comm,
  ring,
  -- h5_1_1 done
  rw h5_1_1,
  rw finset.mul_sum,
  simp,
  -- h5_1 done
  rw eqnI at h5_1,
  rw mul_comm at h5_1,
  exact mv_polynomial.left_cancel_X_mul vars.Y h5_1,
  -- h5 done
  have h6 : b_γβ = 0,
  let eqnII' := eqnII,
  rw h5 at eqnII',
  have h6_1 : (H * mv_t + mv_polynomial.C 1).coeff (finsupp.single vars.Z 2) = ((b_γβ • Z_poly + (finset.fin_range n_wit).sum (λ (i : fin n_wit), b' i • polynomial.eval₂ mv_polynomial.C X_poly (u_wit i)) + V_stmt a_stmt) ^ 2).coeff (finsupp.single vars.Z 2),
  rw eqnII',
  -- h6_1 done
  have h6_2 : (H * mv_t + mv_polynomial.C 1).coeff (finsupp.single vars.Z 2) = 0,
  rw mv_polynomial.coeff_add,
  rw mv_polynomial.coeff_C,
  rw if_neg,
  rw mv_polynomial.coeff_mul,
  rw square_antidiagonal,
  rw finset.sum_insert,
  rw finset.sum_insert,
  rw finset.sum_singleton,
  simp,
  have h6_2_1 : mv_polynomial.coeff (finsupp.single vars.Z 2) mv_t = 0,
  rw mv_t,
  rw polynomial.eval₂,
  rw finsupp.sum,
  rw mv_polynomial.coeff_sum,
  apply finset.sum_eq_zero,
  intro x,
  intro tmp,
  simp,
  right,
  rw X_poly,
  rw mv_polynomial.X_pow_eq_single,
  rw mv_polynomial.coeff_monomial,
  rw if_neg,
  rw finsupp.single_eq_single_iff,
  simp,
  intro,       
  exact two_ne_zero,
  have h6_2_2 : mv_polynomial.coeff (finsupp.single vars.Z 1) mv_t = 0,
  rw mv_t,
  rw polynomial.eval₂,
  rw finsupp.sum,
  rw mv_polynomial.coeff_sum,
  apply finset.sum_eq_zero,
  intro x,
  intro tmp,
  simp,
  right,
  rw X_poly,
  rw mv_polynomial.X_pow_eq_single,
  rw mv_polynomial.coeff_monomial,
  rw if_neg,
  rw finsupp.single_eq_single_iff,
  simp,
  have h6_2_3 : mv_polynomial.coeff (finsupp.single vars.Z 2) H = 0,
  rw H,
  simp,
  rw mv_polynomial.coeff_sum,
  rw helper_lemma_6,
  rw finset.sum_const_zero,
  rw [crs_γ, crs_γβ],
  simp,


  
  -- todo

  have h6_3 : ((b_γβ • Z_poly + (finset.fin_range n_wit).sum (λ (i : fin n_wit), b' i • polynomial.eval₂ mv_polynomial.C X_poly (u_wit i)) + V_stmt a_stmt) ^ 2).coeff (finsupp.single vars.Z 2) = b_γβ ^ 2,

  rw pow_succ,
  rw pow_one,
  rw mv_polynomial.coeff_mul,


    -- now put it all together


  -- Plug h5 into eqnII and look at the coeff (single Z 2) of both sides.


  -- suffices tmp: ¬(finsupp.single vars.Z 1 + finsupp.single vars.Y 1) vars.Y = (finsupp.single vars.X ↑j) vars.Y,
  -- rw finsupp.eq_single_iff,

  -- simp,



  

  have h3 : b_γ = 0,


end



-- TODOs
-- define Prove function, taking crs and a
-- Define verify
-- NOTE: Currently we are not "in the exponent"




end