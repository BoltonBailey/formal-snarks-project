/-
Author: Bolton Bailey
-/
import data.mv_polynomial.basic
import data.polynomial.div
import data.polynomial.field_division
import algebra.polynomial.big_operators
import .general_lemmas.polynomial_mv_sv_cast
import .general_lemmas.mv_divisability
import .vars

/-!
# Knowledge Soundness

This file proves the knowledge-soundness property of the 
[Baby SNARK](https://github.com/initc3/babySNARK) system, 
as described in section 5 of the paper.

NOTE: Currently we are not "in the exponent", we just prove things ignoring an explicit formalization of the Algebraic Group Model. Perhaps with more development, we can i

TODO: Many of the lemmas are poorly named, this file should be given a once-over to rename the lemmas'

TODO: remove lambdas where possible

TODO: Abstract more lemmas from the main theorem. A nice goal would be to make it so that the main points in the proof from the paper appear as have statements, with a comment giving an english description of the statement

-/

open_locale big_operators

section

noncomputable theory


universes u


/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]


/-- Helper for converting mv_polynomial to single -/
@[simp]
def singlify : vars -> polynomial F
| vars.X := polynomial.X 
| vars.Y := 1
| vars.Z := 1


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


/-- The naturals representing the number of gates in the circuit, the statement size, and witness size repectively-/ 
parameters {m n_stmt n_wit : ℕ}
def n := n_stmt + n_wit

-- NOTE: In the paper, n_stmt is l and n_wit is n-l. Here, n is defined from these values.

/-- u_stmt and u_wit are fin-indexed collections of polynomials from the square span program -/
parameter {u_stmt : fin n_stmt → (polynomial F) }
parameter {u_wit : fin n_wit → (polynomial F) }


/-- The roots of the polynomial t -/
parameter {r : fin m → F} 
/-- The polynomial divisibility by which is used to verify satisfaction of the SSP -/
def t : polynomial F := finset.prod (finset.fin_range m) (λ i, polynomial.X - polynomial.C (r i))


/-- t has degree m -/
lemma nat_degree_t : t.nat_degree = m
:=
begin
  -- rw polynomial.nat_degree,
  rw t,
  rw polynomial.nat_degree_prod,
  simp,
  intros i hi,
  exact polynomial.X_sub_C_ne_zero (r i),
end

lemma monic_t : t.monic
:=
begin
  rw t,
  rw polynomial.monic,
  rw polynomial.leading_coeff_prod,
  have h1 : ∀ i : fin m, (polynomial.C 1 * polynomial.X + polynomial.C (- r i)).leading_coeff = 1,
    intro i,
    apply polynomial.leading_coeff_X_add_C (1 : F) (-(r i)),
    simp,
  simp at h1,
  have h2 : ∀ i,  polynomial.X + -polynomial.C (r i) = polynomial.X - polynomial.C (r i),
    intro i,
    ring,
  -- rw add_sub
  conv
  begin
    to_lhs,
    congr,
    skip,
    funext,
    rw ←h2,
    rw h1,
  end,
  rw finset.prod_const_one,

end

lemma degree_t_pos : 0 < m → 0 < t.degree 
:=
begin
  intro hm,
  suffices h : t.degree = some m,
  rw h,
  apply with_bot.some_lt_some.2,
  exact hm,

  have h := nat_degree_t,
  rw polynomial.nat_degree at h,

  induction h1 : t.degree,

  rw h1 at h,
  rw option.get_or_else at h,
  rw h at hm,
  have h2 := has_lt.lt.false hm,
  exfalso,
  exact h2,

  rw h1 at h,
  rw option.get_or_else at h,
  rw h,

  -- -- rw option.get_or_else at h,
  -- have h1: t.degree.is_some = tt,
end


/-- Multivariable version of t -/
def mv_t : mv_polynomial vars F := t.eval₂ mv_polynomial.C X_poly


/-- Converting a single variable polynomial to a multivariable polynomial and back yields the same polynomial -/
lemma my_multivariable_to_single_variable (p : polynomial F) : ((p.eval₂ mv_polynomial.C X_poly).eval₂ polynomial.C singlify) = p 
:=
begin
  apply multivariable_to_single_variable,
  simp,
end



/-- The crs elements as multivariate polynomials of the toxic waste samples -/
def crs_powers_of_τ : fin m → (mv_polynomial vars F) := (λ i, X_poly^(i : ℕ))
def crs_γ : mv_polynomial vars F := Z_poly
def crs_γβ : mv_polynomial vars F := Z_poly * Y_poly
def crs_β_ssps : fin n_wit → (mv_polynomial vars F) := (λ i, (Y_poly) * (u_wit i).eval₂ mv_polynomial.C X_poly) 


/-- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def V_stmt_sv (a_stmt : fin n_stmt → F) : polynomial F 
:= ∑ i in (finset.fin_range n_stmt), a_stmt i • u_stmt i


/-- V_stmt as a multivariable polynomial of vars.X -/
def V_stmt (a_stmt : fin n_stmt → F) : mv_polynomial vars F 
:= (V_stmt_sv a_stmt).eval₂ mv_polynomial.C X_poly

-- /-- V_stmt as a multivariable polynomial of vars.X in sum form -/
-- lemma V_stmt_sum_form (a_stmt : fin n_stmt → F) : V_stmt a_stmt
-- = ∑ i in (finset.fin_range n_stmt), (a_stmt i) • ((u_stmt i).eval₂ mv_polynomial.C X_poly)
-- :=
-- begin
--   rw V_stmt,
--   rw V_stmt_sv,
--   rw polynomial.eval₂_finset_sum,
--   simp,
--   conv
--   begin
--     to_lhs,
--     congr,
--     skip,
--     funext,
--     rw mv_polynomial.smul_eq_C_mul,
--   end,
-- end


/-- Checks whether a witness satisfies the SSP -/
def satisfying_wit (a_stmt : fin n_stmt → F ) (a_wit : fin n_wit → F) := 
(V_stmt_sv a_stmt
  + (∑ i in (finset.fin_range n_wit), a_wit i • u_wit i))^2 %ₘ t = 1

/-- The coefficients of the CRS elements in the algebraic adversary's representation -/
parameters {b v h : fin m → F}
parameters {b_γ v_γ h_γ b_γβ v_γβ h_γβ : F}
parameters {b' v' h' : fin n_wit → F}


/-- Polynomial forms of the adversary's proof representation -/
def B_wit  : mv_polynomial vars F := 
  ∑ i in (finset.fin_range m), (b i) • (crs_powers_of_τ i)
  +
  b_γ • crs_γ
  +
  b_γβ • crs_γβ
  +
  ∑ i in (finset.fin_range n_wit),  (b' i) • (crs_β_ssps i)


def V_wit : mv_polynomial vars F := 
  ∑ i in (finset.fin_range m), (v i) • (crs_powers_of_τ i)
  +
  v_γ • crs_γ
  +
  v_γβ • crs_γβ
  +
  ∑ i in (finset.fin_range n_wit), (v' i) • (crs_β_ssps i)

def H : mv_polynomial vars F := 
  ∑ i in (finset.fin_range m), (h i) • (crs_powers_of_τ i)
  +
  h_γ • crs_γ
  +
  h_γβ • crs_γβ
  +
  ∑ i in (finset.fin_range n_wit), (h' i) • (crs_β_ssps i)


/-- V as a multivariable polynomial -/
def V (a_stmt : fin n_stmt → F) : mv_polynomial vars F 
:= V_stmt a_stmt + V_wit


-- Single variable form ov V_wit
def V_wit_sv : polynomial F 
:= ∑ i in finset.fin_range n_wit, b' i • u_wit i

-- TODO move helper lemmas to another file?

/-- Helper lemma for main theorem -/
lemma helper_1 (j : fin m) : (λ x : fin m, mv_polynomial.coeff (finsupp.single vars.X ↑j) (b x • X_poly ^ (x : ℕ))) 
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
end

/-- Helper lemma for main theorem -/
lemma helper_2 (j : fin m) : (λ (x : fin n_wit), mv_polynomial.coeff (finsupp.single vars.X ↑j) (b' x • (mv_polynomial.monomial (finsupp.single vars.Y 1) 1 * polynomial.eval₂ mv_polynomial.C X_poly (u_wit x))))
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
  rw mul_var_no_constant,
  rw finsupp.single_apply,
  rw if_neg,
  simp,
end

/-- Helper lemma for main theorem -/
lemma helper_3 : (λ x : fin m, mv_polynomial.coeff (finsupp.single vars.Z 1) (b x • X_poly ^ (x : ℕ))) 
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
lemma helper_4 : (λ (x : fin n_wit), mv_polynomial.coeff (finsupp.single vars.Z 1) (b' x • (mv_polynomial.monomial (finsupp.single vars.Y 1) 1 * polynomial.eval₂ mv_polynomial.C X_poly (u_wit x))))
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
  rw mul_var_no_constant,
  rw finsupp.single_apply,
  rw if_neg,
  simp,
end

lemma helper_5 : (∀ i, b i = 0) -> (λ (i : fin m), b i • crs_powers_of_τ i) = (λ (i : fin m), 0)
:=
begin
  intro tmp,
  apply funext,
  intro x,
  rw tmp x,
  simp,
end

lemma helper_6 : (λ (x : fin m), mv_polynomial.coeff (finsupp.single vars.Z 2) (h x • crs_powers_of_τ x)) = λ x, 0
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

lemma helper_7 : (λ (x : fin n_wit), mv_polynomial.coeff (finsupp.single vars.Z 2) (h' x • crs_β_ssps x)) = λ x, 0
:=
begin
  apply funext,
  intro x,
  rw crs_β_ssps,
  rw X_poly,
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.coeff_C_mul,
  simp,
  right,
  rw mul_comm,
  rw Y_poly,
  rw mul_var_no_constant,
  rw finsupp.single_apply,
  rw if_neg,
  simp,
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
  simp at h1_h_left,
  exact prod.ext h1_h_left h7,
  have f : false,
  exact nat.not_lt_zero h1_w h6,
  exfalso,
  exact f,

  -- Forward case
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

/-- Lemmas that denote bigger steps in the proof -/

lemma h6_2_1 : mv_polynomial.coeff (finsupp.single vars.Z 2) mv_t = 0
:=
begin
  rw mv_t,
  rw polynomial.eval₂,
  rw finsupp.sum,
  rw mv_polynomial.coeff_sum,
  apply finset.sum_eq_zero,
  intro x,
  intro tmp,
  -- simp,
  -- right,
  rw X_poly,
  rw ←mv_polynomial.single_eq_C_mul_X,
  rw mv_polynomial.coeff_monomial,
  rw if_neg,
  rw finsupp.single_eq_single_iff,
  simp,
  intro,       
  exact dec_trivial,
end


lemma h6_2_2 :  mv_polynomial.coeff (finsupp.single vars.Z 1) mv_t = 0
:=
begin
  rw mv_t,
  rw polynomial.eval₂,
  rw finsupp.sum,
  rw mv_polynomial.coeff_sum,
  apply finset.sum_eq_zero,
  intro x,
  intro tmp,
  -- simp,
  -- right,
  rw X_poly,
  rw ←mv_polynomial.single_eq_C_mul_X,
  rw mv_polynomial.coeff_monomial,
  rw if_neg,
  rw finsupp.single_eq_single_iff,
  simp,
end

lemma h6_2_3 : mv_polynomial.coeff (finsupp.single vars.Z 2) H = 0
:=
begin
  rw H,
  simp,
  rw mv_polynomial.coeff_sum,
  rw helper_6,
  rw finset.sum_const_zero,
  rw [crs_γ, crs_γβ],
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
  rw helper_7,
  rw finset.sum_const_zero,
  rw finsupp.ext_iff,
  rw not_forall,
  use vars.Y,
  rw finsupp.add_apply,
  repeat {rw finsupp.single_apply},
  rw if_neg,
  rw if_pos,
  rw if_neg,
  simp,
  simp,
  simp,
  rw finsupp.single_eq_single_iff,
  simp,
  exact dec_trivial,
end

lemma h6_2 : (H * mv_t + mv_polynomial.C 1).coeff (finsupp.single vars.Z 2) = 0
:=
begin
  rw mv_polynomial.coeff_add,
  rw mv_polynomial.coeff_C,
  rw if_neg,
  rw mv_polynomial.coeff_mul,
  rw square_antidiagonal,
  rw finset.sum_insert,
  rw finset.sum_insert,
  rw finset.sum_singleton,
  simp,

  rw [h6_2_1, h6_2_2, h6_2_3],
  simp,
  -- Prove that {(Z^0, Z^2), (Z^1, Z^1), (Z^2, Z^0)} is actually a set of three distinct elements
  rw finset.mem_singleton,
  rw prod.ext_iff,
  rw decidable.not_and_iff_or_not,
  left,
  rw finsupp.single_eq_single_iff,
  simp,
  exact dec_trivial,
  rw finset.mem_insert,
  rw decidable.not_or_iff_and_not,
  split,
  rw prod.ext_iff,
  rw decidable.not_and_iff_or_not,
  left,
  rw finsupp.single_eq_single_iff,
  simp,
  rw finset.mem_singleton,
  rw prod.ext_iff,
  rw decidable.not_and_iff_or_not,
  left,
  rw finsupp.single_eq_single_iff,
  simp,
  exact dec_trivial,
  rw finsupp.ext_iff,
  rw not_forall,
  use vars.Z,
  simp,
  exact dec_trivial,

end

lemma h6_3_1 : mv_polynomial.coeff (finsupp.single vars.Z 2) (b_γβ • Z_poly) = 0
:=
begin
  rw Z_poly,
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.coeff_C_mul,
  rw mv_polynomial.coeff_X',
  rw if_neg,
  simp,
  rw finsupp.single_eq_single_iff,
  simp,
  exact dec_trivial,
end

lemma h6_3_2_1 : (λ (i : fin n_wit), mv_polynomial.coeff (finsupp.single vars.Z 2) (b' i • polynomial.eval₂ mv_polynomial.C X_poly (u_wit i))) = (λ i, 0)
:=
begin
  funext,
  rw polynomial.eval₂,
  rw finsupp.sum,
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.coeff_C_mul,
  rw mv_polynomial.coeff_sum,
  simp,
  right,
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
  exact dec_trivial,
end


lemma h6_3_2 : mv_polynomial.coeff (finsupp.single vars.Z 2)
  (∑ i in (finset.fin_range n_wit), b' i • polynomial.eval₂ mv_polynomial.C X_poly (u_wit i)) = 0
:=
begin
  rw mv_polynomial.coeff_sum,
  rw h6_3_2_1,
  rw finset.sum_const_zero,
end

lemma h6_3_3 (a_stmt : fin n_stmt -> F) : mv_polynomial.coeff (finsupp.single vars.Z 2) 
  (∑ i in finset.fin_range n_stmt, a_stmt i • polynomial.eval₂ mv_polynomial.C X_poly (u_stmt i)) = 0
:=
begin
  -- rw V_stmt,
  -- rw polynomial.eval₂,
  -- rw finsupp.sum,
  rw mv_polynomial.coeff_sum,
  -- simp,
  apply finset.sum_eq_zero,
  intro x,
  intro tmp,
  -- rw polynomial.smul,
  -- simp,
  -- right,
  rw polynomial.eval₂,
  rw finsupp.smul_sum,
  rw finsupp.sum,
  rw mv_polynomial.coeff_sum,
  apply finset.sum_eq_zero,
  intro x_1,
  intro tmp2,

  -- rw mv_polynomial.,
  rw X_poly,
  -- rw mv_polynomial.X,
  -- rw polynomial.smul_eq_C_mul,
  rw mv_polynomial.smul_eq_C_mul,
  simp,
  right,
  right,
  -- sorry,
  rw mv_polynomial.X_pow_eq_single,
  rw mv_polynomial.coeff_monomial,
  rw if_neg,
  rw finsupp.single_eq_single_iff,
  simp,
  intro,
  exact dec_trivial,  
end

lemma h6_3_4 : mv_polynomial.coeff (finsupp.single vars.Z 1) (b_γβ • Z_poly) = b_γβ
:=
begin
  rw Z_poly,
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.coeff_C_mul,
  rw mv_polynomial.coeff_X,
  simp,
end

lemma h6_3_5_1 : (λ (i : fin n_wit), mv_polynomial.coeff (finsupp.single vars.Z 1) (b' i • polynomial.eval₂ mv_polynomial.C X_poly (u_wit i))) = (λ i, 0)
:=
begin
  funext,
  rw polynomial.eval₂,
  rw finsupp.sum,
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.coeff_C_mul,
  rw mv_polynomial.coeff_sum,
  simp,
  right,
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
end

lemma h6_3_5 : mv_polynomial.coeff (finsupp.single vars.Z 1) (∑ i in(finset.fin_range n_wit), b' i • polynomial.eval₂ mv_polynomial.C X_poly (u_wit i)) = 0
:=
begin
  rw mv_polynomial.coeff_sum,
  rw h6_3_5_1,
  rw finset.sum_const_zero,
end

lemma h6_3_6 (a_stmt : fin n_stmt -> F): mv_polynomial.coeff (finsupp.single vars.Z 1) 
  (∑ (i : fin n_stmt) in finset.fin_range n_stmt,
  a_stmt i • polynomial.eval₂ mv_polynomial.C X_poly (u_stmt i)) = 0 
:=
begin
  -- rw V_stmt,
  -- rw polynomial.eval₂,
  -- rw finsupp.sum,
  -- rw mv_polynomial.coeff_sum,
  -- simp,
  -- apply finset.sum_eq_zero,
  -- intro x,
  -- intro tmp,
  -- simp,
  -- right,
  -- rw X_poly,
  -- rw mv_polynomial.X_pow_eq_single,
  -- rw mv_polynomial.coeff_monomial,
  -- rw if_neg,
  -- rw finsupp.single_eq_single_iff,
  -- simp,
    -- rw V_stmt,
  -- rw polynomial.eval₂,
  -- rw finsupp.sum,
  rw mv_polynomial.coeff_sum,
  -- simp,
  apply finset.sum_eq_zero,
  intro x,
  intro tmp,
  -- rw polynomial.smul,
  -- simp,
  -- right,
  rw polynomial.eval₂,
  rw finsupp.smul_sum,
  rw finsupp.sum,
  rw mv_polynomial.coeff_sum,
  apply finset.sum_eq_zero,
  intro x_1,
  intro tmp2,

  -- rw mv_polynomial.,
  rw X_poly,
  -- rw mv_polynomial.X,
  -- rw polynomial.smul_eq_C_mul,
  rw mv_polynomial.smul_eq_C_mul,
  simp,
  right,
  right,
  -- sorry,
  rw mv_polynomial.X_pow_eq_single,
  rw mv_polynomial.coeff_monomial,
  rw if_neg,
  rw finsupp.single_eq_single_iff,
  simp,
end


lemma h6_3 (a_stmt : fin n_stmt -> F) : (
    (b_γβ • Z_poly 
      + ∑ (i : fin n_stmt) in finset.fin_range n_stmt, a_stmt i • polynomial.eval₂ mv_polynomial.C X_poly (u_stmt i) 
      + ∑ (i : fin n_wit) in finset.fin_range n_wit, b' i • polynomial.eval₂ mv_polynomial.C X_poly (u_wit i)
    ) ^ 2).coeff (finsupp.single vars.Z 2) = b_γβ ^ 2
:=
begin
  rw pow_succ,
  rw pow_one,
  rw mv_polynomial.coeff_mul,
  rw square_antidiagonal,

  rw finset.sum_insert,
  rw finset.sum_insert,
  rw finset.sum_singleton,
  simp,
  rw h6_3_1, 
  rw h6_3_2, 
  rw h6_3_3,
  rw h6_3_4, 
  rw h6_3_5, 
  rw h6_3_6,
  simp,
  rw pow_succ,
  rw pow_one,
  -- Prove that {(Z^0, Z^2), (Z^1, Z^1), (Z^2, Z^0)} is actually a set of three distinct elements
  rw finset.mem_singleton,
  rw prod.ext_iff,
  rw decidable.not_and_iff_or_not,
  left,
  rw finsupp.single_eq_single_iff,
  simp,
  exact dec_trivial,
  rw finset.mem_insert,
  rw decidable.not_or_iff_and_not,
  split,
  rw prod.ext_iff,
  rw decidable.not_and_iff_or_not,
  left,
  rw finsupp.single_eq_single_iff,
  simp,
  rw finset.mem_singleton,
  rw prod.ext_iff,
  rw decidable.not_and_iff_or_not,
  left,
  rw finsupp.single_eq_single_iff,
  simp,
  exact dec_trivial,
end

lemma h11 (a_stmt) (V_wit_eq : V_wit = polynomial.eval₂ mv_polynomial.C X_poly (∑ i in (finset.fin_range n_wit), b' i • u_wit i)) : (V_stmt_sv a_stmt + V_wit_sv) ^ 2 = mv_polynomial.eval₂ polynomial.C singlify ((V_stmt a_stmt + V_wit) ^ 2)
:=
begin
  have h11_1 : (V_stmt a_stmt + V_wit) ^ 2 = polynomial.eval₂ mv_polynomial.C X_poly ((V_stmt_sv a_stmt + V_wit_sv) ^ 2),
  rw polynomial.eval₂_pow,
  rw polynomial.eval₂_add,
  rw V_stmt,
  rw V_wit_sv,
  rw V_wit_eq,
  -- h11_1 done
  rw h11_1,
  rw X_poly,
  rw multivariable_to_single_variable vars vars.X singlify,
  simp,
end



lemma h2_1 : (∀ (i : fin m), B_wit.coeff (finsupp.single vars.X i) = b i) :=
begin
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
  rw helper_1,
  rw finset.sum_ite,
  simp,
  rw finset.filter_eq',
  rw if_pos,
  rw finset.sum_singleton,
  rw helper_2,
  simp,
  simp,
  rw finsupp.ext_iff,
  simp,
  refine ⟨vars.Y, _ ⟩,
  repeat { rw finsupp.single_apply },
  simp,
  rw finsupp.single_eq_single_iff,
  simp,
end


lemma h3_1 : B_wit.coeff (finsupp.single vars.Z 1) = b_γ
:=
begin
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
  rw helper_3,
  rw helper_4,
  simp,
  rw finsupp.ext_iff,
  simp,
  refine ⟨vars.Y, _ ⟩,
  repeat { rw finsupp.single_apply },
  simp,
end


lemma h5_1_1 : b_γβ • (Z_poly * Y_poly) = Y_poly * b_γβ • Z_poly :=
begin
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.smul_eq_C_mul,
  rw mul_comm,
  ring,
end


/-- Show that if the adversary polynomials obey the equations, then the coefficients give a satisfying witness. This theorem appears in the Baby SNARK paper as Theorem 1 case 1.-/
theorem case_1 (a_stmt : fin n_stmt → F ) : 
  (0 < m)
  -> (B_wit = V_wit * Y_poly) 
  -> (H * mv_t + mv_polynomial.C 1 = (V a_stmt)^2) 
  -> (satisfying_wit a_stmt b')
:=
begin
  intros hm eqnI eqnII,
  -- "B_wit only has terms with a Y component"
  have h1 : (∀ m : vars →₀ ℕ, m vars.Y = 0 -> B_wit.coeff m = 0),
    rw eqnI,
    apply mul_var_no_constant V_wit vars.Y,
  -- "b_0 b_1, ..., b_m, ... are all zero"
  have h2 : ∀ i : fin m, b i = 0,
    intro i,
    have tmp := h2_1 i,
    rw ← tmp,
    rw eqnI,
    apply mul_var_no_constant,
    rw finsupp.single_apply,
    rw if_neg,
    simp,
  -- b_γ = 0
  have h3 : b_γ = 0,
    rw ← h3_1,
    rw eqnI,
    apply mul_var_no_constant,
    rw finsupp.single_apply,
    rw if_neg,
    simp,
  -- "We can write B_wit as ..."
  have h4 : B_wit = b_γβ • crs_γβ + ∑ i in (finset.fin_range n_wit), (b' i) • (crs_β_ssps i),
    rw B_wit,
    rw helper_5 h2,
    rw h3,
    simp,
  -- "... we also see that V_wit must not have any Y terms at all"
  have h5 : V_wit = b_γβ • Z_poly + ∑ i in (finset.fin_range n_wit), (b' i) • ((u_wit i).eval₂ mv_polynomial.C X_poly),
    apply left_cancel_X_mul vars.Y,
    rw ←Y_poly,
    rw mul_comm,
    rw ←eqnI,
    rw h4,
    rw crs_γβ,
    rw crs_β_ssps,
    rw mul_add,
    rw h5_1_1,
    rw finset.mul_sum,
    simp,
  -- "... write V(.) as follows ..."
  have h6 : V a_stmt = b_γβ • Z_poly 
      + ∑ i in (finset.fin_range n_stmt), (a_stmt i) • ((u_stmt i).eval₂ mv_polynomial.C X_poly)
      + ∑ i in (finset.fin_range n_wit), (b' i) • ((u_wit i).eval₂ mv_polynomial.C X_poly),
    rw V,
    rw V_stmt,
    rw h5,
    rw V_stmt_sv,
    rw polynomial.eval₂_finset_sum,
    simp only [polynomial.eval₂_smul],
    -- conv
    -- begin
    --   to_lhs,
    --   congr,
    --   congr,
    --   skip,
    --   funext,
    --   -- rw mv_polynomial.smul_eq_C_mul,
    -- end,
    simp only [←mv_polynomial.smul_eq_C_mul],
    ring,
  -- ... we can conclude that b_γβ = 0.
  have h7 : b_γβ = 0,
    let eqnII' := eqnII,
    -- rw V at eqnII',
    -- rw h5 at eqnII',
    rw h6 at eqnII',
    have h6_1 := congr_arg (mv_polynomial.coeff (finsupp.single vars.Z 2)) eqnII',
    -- have h6_1 : (H * mv_t + mv_polynomial.C 1).coeff (finsupp.single vars.Z 2) = (( V_stmt a_stmt + b_γβ • Z_poly + ∑ i in (finset.fin_range n_wit), b' i • polynomial.eval₂ mv_polynomial.C X_poly (u_wit i)) ^ 2).coeff (finsupp.single vars.Z 2),
    --   rw eqnII',
    --   rw add_assoc,
    -- h6_1 done
    -- rw h6_2 at h6_1,
    rw h6_2 at h6_1,
    rw h6_3 at h6_1,
    exact pow_eq_zero (eq.symm h6_1),
  -- Finally, we arrive at the conclusion that the coefficients define a satisfying witness such that ...
  have h8 : V a_stmt = 
      ∑ i in (finset.fin_range n_stmt), (a_stmt i) • ((u_stmt i).eval₂ mv_polynomial.C X_poly)
      + ∑ i in (finset.fin_range n_wit), (b' i) • ((u_wit i).eval₂ mv_polynomial.C X_poly),
    rw h6,
    rw h7,
    simp,
  -- TODO use h8 in the following

  -- rw h7 at h5,
  -- simp at h5,
  -- TODO is there a more efficient way to simply say (evaluate f on both sides of this hypothesis)? Yes the congr tactic does this
  have h10 : ((H * mv_t + mv_polynomial.C 1).eval₂ polynomial.C singlify) %ₘ t = (((V a_stmt)^2).eval₂ polynomial.C singlify) %ₘ t,
    rw eqnII,
    -- rw V,
  -- h10 done
  rw mv_polynomial.eval₂_add at h10,
  rw mv_polynomial.eval₂_mul at h10,
  rw satisfying_wit,
  rw ←V_wit_sv,
  -- rw ←V,
  rw h11,
  rw ←V,
  rw ←h10,
  rw mv_t,
  rw my_multivariable_to_single_variable t,
  have h12: mv_polynomial.C 1 = (polynomial.C 1 : polynomial F).eval₂ mv_polynomial.C X_poly,
    rw polynomial.eval₂_C,
  -- h12 done
  rw h12,
  rw my_multivariable_to_single_variable,
  have h13 : (mv_polynomial.eval₂ polynomial.C singlify H * t + polynomial.C 1 : polynomial F) /ₘ t = (mv_polynomial.eval₂ polynomial.C singlify H : polynomial F) ∧ (mv_polynomial.eval₂ polynomial.C singlify H * t + polynomial.C 1 : polynomial F) %ₘ t = (polynomial.C 1 : polynomial F),
    apply polynomial.div_mod_by_monic_unique,
    exact monic_t,
    split,
    rw [add_comm, mul_comm],
    rw polynomial.degree_C,
    exact degree_t_pos hm,
    exact one_ne_zero,
  -- h13 done
  rw h13.2,
  simp,
  rw h5,
  rw h7,
  simp,
  rw polynomial.eval₂_finset_sum,
  conv
  begin
    to_rhs,
    congr,
    skip,
    funext,
    simp,
  end,
  conv
  begin
    to_lhs,
    congr,
    skip,
    funext,
    rw mv_polynomial.smul_eq_C_mul,
  end,
end


end
