/-
Author: Bolton Bailey
-/
import data.mv_polynomial.basic
import data.polynomial.div
import data.polynomial.field_division
import algebra.polynomial.big_operators
import ...general_lemmas.polynomial_mv_sv_cast
import ...general_lemmas.mv_divisability
import ...general_lemmas.single_antidiagonal
import ...general_lemmas.polynomial_smul_eq_C_mul
import ...general_lemmas.single_injective
import .vars
import ...polynomial_tactic

/-!
# Knowledge Soundness

This file proves the knowledge-soundness property of the 
[Baby SNARK](https://github.com/initc3/babySNARK) system, 
as described in section 5 of the paper.

NOTE: Currently we are not "in the exponent", we just prove things ignoring an explicit formalization of the Algebraic Group Model. Perhaps with more development, we can incorporate more of the background of this assumption

TODO: Many of the lemmas are poorly named, this file should be given a once-over to rename the lemmas'

TODO: remove lambdas where possible

TODO: Abstract more lemmas from the main theorem. A nice goal would be to make it so that the main points in the proof from the paper appear as have statements, with a comment giving an english description of the statement

TODO : move all mv forms of polynomial defs later and name them consistently

-/

open_locale big_operators

section

noncomputable theory


universes u


/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]

/-- The naturals representing:
  m - the number of gates in the circuit, 
  n_stmt - the statement size, 
  n_wit - the witness size -/ 
parameters {m n_stmt n_wit : ℕ}
def n := n_stmt + n_wit

-- NOTE: In the paper, n_stmt is l and n_wit is n-l. Here, n is defined from these values.

/-- u_stmt and u_wit are fin-indexed collections of polynomials from the square span program -/
parameter {u_stmt : fin n_stmt → (polynomial F) }
parameter {u_wit : fin n_wit → (polynomial F) }


/-- The roots of the polynomial t -/
parameter {r : fin m → F} 
/-- t is the polynomial divisibility by which is used to verify satisfaction of the SSP -/
def t : polynomial F := ∏ i in (finset.fin_range m), (polynomial.X - polynomial.C (r i))
-- TODO this and the following lemmas about this could potentially be spun off 
-- make a `monic_from_roots` function for mathlib

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
  apply polynomial.monic_prod_of_monic,
  intros i hi,
  exact polynomial.monic_X_sub_C (r i),
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
end



-- Single variable form of V_wit
def V_wit_sv (a_wit : fin n_wit → F) : polynomial F 
:= ∑ i in finset.fin_range n_wit, a_wit i • u_wit i

/-- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def V_stmt_sv (a_stmt : fin n_stmt → F) : polynomial F 
:= ∑ i in (finset.fin_range n_stmt), a_stmt i • u_stmt i

/-- Checks whether a statement witness pair satisfies the SSP -/
def satisfying (a_stmt : fin n_stmt → F ) (a_wit : fin n_wit → F) := 
(∑ i in (finset.fin_range n_stmt), a_stmt i • u_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • u_wit i))^2 %ₘ t = 1



/- Multivariable polynomial definititons and ultilities -/


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

/-- Multivariable version of t -/
def t_mv : mv_polynomial vars F := t.eval₂ mv_polynomial.C X_poly

/-- V_stmt as a multivariable polynomial of vars.X -/
def V_stmt_mv (a_stmt : fin n_stmt → F) : mv_polynomial vars F 
:= (V_stmt_sv a_stmt).eval₂ mv_polynomial.C X_poly


/-- Converting a single variable polynomial to a multivariable polynomial and back yields the same polynomial -/
lemma my_multivariable_to_single_variable (p : polynomial F) : ((p.eval₂ mv_polynomial.C X_poly).eval₂ polynomial.C singlify) = p 
:=
begin
  apply multivariable_to_single_variable,
  simp,
end

/-- The crs elements as multivariate polynomials of the toxic waste samples -/
def crs_powers_of_τ (i : fin m) : (mv_polynomial vars F) := X_poly^(i : ℕ)
def crs_γ : mv_polynomial vars F := Z_poly
def crs_γβ : mv_polynomial vars F := Z_poly * Y_poly
def crs_β_ssps (i : fin n_wit) : (mv_polynomial vars F) := (Y_poly) * (u_wit i).eval₂ mv_polynomial.C X_poly

/-- The coefficients of the CRS elements in the algebraic adversary's representation -/
parameters {b v h : fin m → F}
parameters {b_γ v_γ h_γ b_γβ v_γβ h_γβ : F}
parameters {b' v' h' : fin n_wit → F}

/-- Polynomial forms of the adversary's proof representation -/
def B_wit : mv_polynomial vars F := 
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
:= V_stmt_mv a_stmt + V_wit

/- Lemmas for proof -/

lemma h2_1 : (∀ (i : fin m), B_wit.coeff (finsupp.single vars.X i) = b i) :=
begin
  intro j,
  rw B_wit,
  simp [crs_powers_of_τ, crs_γ, crs_γβ, crs_β_ssps],
  simp [X_poly, Y_poly, Z_poly],
  simp with coeff_simp,
  unfold_coes,
  --TODO is this best?
  -- TODO improve ite_finsupp_simplify with this
  -- simp [],
  -- ite_finsupp_simplify,
  simp only [single_injective_iff],
  simp [finsupp.single_eq_single_iff, ←fin.eq_iff_veq],
end


lemma h3_1 : B_wit.coeff (finsupp.single vars.Z 1) = b_γ
:=
begin
  rw B_wit,
  simp [crs_powers_of_τ, crs_γ, crs_γβ, crs_β_ssps],
  simp [X_poly, Y_poly, Z_poly],
  simp? with coeff_simp,
  -- -- simp? [-finsupp.single_nat_sub],
  -- simp?,
  ite_finsupp_simplify,
  -- simp only with coeff_simp,
  -- ite_finsupp_simplify,


end

lemma h4_1 : (∀ i, b i = 0) -> (λ (i : fin m), b i • crs_powers_of_τ i) = (λ (i : fin m), 0)
:=
begin
  intro tmp,
  apply funext,
  intro x,
  rw tmp x,
  simp,
end


lemma h5_1 : b_γβ • (Z_poly * Y_poly) = Y_poly * b_γβ • Z_poly :=
begin
  rw mv_polynomial.smul_eq_C_mul,
  rw mv_polynomial.smul_eq_C_mul,
  ring,
end

lemma h6_2 : (H * t_mv + mv_polynomial.C 1).coeff (finsupp.single vars.Z 2) = 0
:=
begin
  rw mv_polynomial.coeff_add,
  rw mv_polynomial.coeff_C,
  rw if_neg,
  rw mv_polynomial.coeff_mul,
  rw single_2_antidiagonal,
  rw finset.sum_insert,
  rw finset.sum_insert,
  rw finset.sum_singleton,
  simp [H, t_mv, crs_powers_of_τ, crs_γ, crs_γβ, crs_β_ssps, X_poly, Y_poly, Z_poly],
  simp only with coeff_simp polynomial_nf, 
  -- unfold_coes,

  ite_finsupp_simplify,
  -- simp only with coeff_simp,

  simp [-finsupp.single_zero, finsupp.single_eq_single_iff],
  -- dec_trivial,

  rw finsupp.eq_single_iff,
  dec_trivial,

end

-- TODO check all lemmas are used

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
  rw single_2_antidiagonal,

  rw finset.sum_insert,
  rw finset.sum_insert,
  rw finset.sum_singleton,

  -- NOTE The simp only with coeff_simp and ite_finsupp_simplify tactic work here
  --      But I used to get deterministic timeout - i fixed this by making simp only with coeff_simp do simp only instead
  --
  simp [X_poly, Y_poly, Z_poly],
  simp only with coeff_simp polynomial_nf,
  -- simp only with coeff_simp,
  ite_finsupp_simplify,
  rw pow_succ,
  rw pow_one,

  simp,
  simp [-finsupp.single_zero, finsupp.single_eq_single_iff],
  -- finish,
end


/-- This function represents the exctractor in the AGM. -/
def extractor : fin n_wit -> F := b'

/-- Show that if the adversary polynomials obey the equations, 
then the coefficients give a satisfying witness. 
This theorem appears in the Baby SNARK paper as Theorem 1 case 1. -/
theorem case_1 (a_stmt : fin n_stmt → F ) : 
  (0 < m)
  -> (B_wit = V_wit * Y_poly)
  -> (H * t_mv + mv_polynomial.C 1 = (V a_stmt)^2) 
  -> (satisfying a_stmt extractor)
:=
begin
  rw extractor,
  intros hm eqnI eqnII,
  -- TODO eqnI should have a Z term on both sides
  -- "B_wit only has terms with a Y component"
  have h1 : (∀ m : vars →₀ ℕ, m vars.Y = 0 -> B_wit.coeff m = 0),
    rw eqnI,
    apply mul_var_no_constant V_wit vars.Y,
  -- "b_0 b_1, ..., b_m, ... are all zero"
  have h2 : ∀ i : fin m, b i = 0,
    intro i,
    rw ← (h2_1 i),
    rw eqnI,
    apply mul_var_no_constant,
    rw finsupp.single_apply,
    simp,
  -- b_γ = 0
  have h3 : b_γ = 0,
    rw ← h3_1,
    rw eqnI,
    apply mul_var_no_constant,
    rw finsupp.single_apply,
    simp,
  -- "We can write B_wit as ..."
  have h4 : B_wit = b_γβ • crs_γβ + ∑ i in (finset.fin_range n_wit), (b' i) • (crs_β_ssps i),
    rw B_wit,
    rw h4_1 h2,
    rw h3,
    simp,
  -- "... we also see that V_wit must not have any Y terms at all"
  have h5 : V_wit = b_γβ • Z_poly + ∑ i in (finset.fin_range n_wit), (b' i) • ((u_wit i).eval₂ mv_polynomial.C X_poly),
    apply left_cancel_X_mul vars.Y,
    rw ←Y_poly,
    rw mul_comm,
    rw ←eqnI,
    rw h4,
    simp only [crs_γβ, crs_β_ssps],
    rw mul_add,
    rw h5_1,
    rw finset.mul_sum,
    simp,
  -- "... write V(.) as follows ..."
  have h6 : V a_stmt = b_γβ • Z_poly 
      + ∑ i in (finset.fin_range n_stmt), (a_stmt i) • ((u_stmt i).eval₂ mv_polynomial.C X_poly)
      + ∑ i in (finset.fin_range n_wit), (b' i) • ((u_wit i).eval₂ mv_polynomial.C X_poly),
    rw V,
    rw V_stmt_mv,
    rw h5,
    rw V_stmt_sv,
    rw polynomial.eval₂_finset_sum,
    simp only [polynomial.eval₂_smul],
    simp only [←mv_polynomial.smul_eq_C_mul],
    ring,
  -- ... we can conclude that b_γβ = 0.
  have h7 : b_γβ = 0,
    let eqnII' := eqnII,
    rw h6 at eqnII',
    have h6_1 := congr_arg (mv_polynomial.coeff (finsupp.single vars.Z 2)) eqnII',
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
  -- Treat both sides of this a single variable polynomial
  have h9 := congr_arg (mv_polynomial.eval₂ (@polynomial.C F _) singlify) h8,
  rw mv_polynomial.eval₂_add at h9,
  rw mv_polynomial.eval₂_sum at h9,
  simp [mv_polynomial.smul_eq_C_mul] at h9,
  simp [my_multivariable_to_single_variable] at h9,
  simp [←polynomial.smul_eq_C_mul] at h9,
  -- Now we solve the main goal. First, we expand the definition of "satisfying"
  rw satisfying,
  rw ←h9,
  clear h8 h9,

  -- TODO is there a more efficient way to simply say (evaluate f on both sides of this hypothesis)? Yes the congr tactic does this
  have h10 : ((H * t_mv + mv_polynomial.C 1).eval₂ polynomial.C singlify) %ₘ t = (((V a_stmt)^2).eval₂ polynomial.C singlify) %ₘ t,
    rw eqnII,
  -- h10 done
  rw mv_polynomial.eval₂_add at h10,
  rw mv_polynomial.eval₂_mul at h10,

  rw ←mv_polynomial.eval₂_pow,

  rw ←h10,
  rw t_mv,
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
end


end
