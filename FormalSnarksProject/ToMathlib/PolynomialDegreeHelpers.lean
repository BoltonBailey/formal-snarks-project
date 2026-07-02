import Mathlib

/-!

# Degree helpers for the Groth16 completeness proof

The honest ("witness-following") Groth16 prover encodes the QAP polynomials by their coefficients
on the SRS monomials `x^0, …, x^(n_var - 1)` (and the quotient polynomial on
`x^0·t, …, x^(n_var - 2)·t`). These lemmas justify that encoding: a polynomial of degree `< n`
is recovered from its first `n` coefficients, sums of `C _ * _` combinations respect degree
bounds, and the quotient by a monic divisor satisfies the expected degree bound when the
division is exact.

-/

open scoped BigOperators

namespace Polynomial

variable {F : Type*} [Field F]

/-- A polynomial of degree `< n` is the sum of its first `n` monomials, as a `List.finRange`
sum (the shape in which the AGM prover's linear combination of SRS powers appears). -/
lemma list_sum_C_coeff_mul_X_pow (p : Polynomial F) (n : ℕ) (h : p.degree < n) :
    ((List.finRange n).map (fun i : Fin n => C (p.coeff i) * X ^ (i : ℕ))).sum = p := by
  rw [← Fin.sum_univ_def, Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i) n]
  simp_rw [C_mul_X_pow_eq_monomial]
  by_cases hp : p = 0
  · simp [hp]
  · exact (as_sum_range' p n ((natDegree_lt_iff_degree_lt hp).mpr h)).symm

/-- Degree bound for the statement/witness linear combinations `∑ C (f i) * g i` of QAP
polynomials. -/
lemma degree_list_sum_C_mul_lt {ι : Type*} (l : List ι) (f : ι → F) (g : ι → Polynomial F)
    (n : ℕ) (hg : ∀ i, (g i).degree < n) :
    ((l.map fun i => C (f i) * g i).sum).degree < n := by
  induction l with
  | nil => simpa using WithBot.bot_lt_coe n
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact lt_of_le_of_lt (degree_add_le _ _)
      (max_lt (lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _) (hg hd)) ih)

/-- If `q` divides `p` exactly (`p %ₘ q = 0`) and `degree p < c + degree q`, then the quotient
`p /ₘ q` has degree `< c`. -/
lemma degree_divByMonic_lt_of_degree_lt {p q : Polynomial F} (hq : q.Monic)
    (hmod : p %ₘ q = 0) {c : ℕ} (hpq : p.degree < c + q.degree) :
    (p /ₘ q).degree < c := by
  by_cases h0 : p /ₘ q = 0
  · rw [h0, degree_zero]
    exact WithBot.bot_lt_coe c
  · have hp : p = q * (p /ₘ q) := by
      have h := modByMonic_add_div p q
      rw [hmod, zero_add] at h
      exact h.symm
    rw [hp, degree_mul, add_comm (c : WithBot ℕ) q.degree] at hpq
    exact (WithBot.add_lt_add_iff_left (degree_eq_bot.not.mpr hq.ne_zero)).mp hpq

/-- A degree bound `degree u < n` gives `degree u ≤ n - 1` (in `WithBot ℕ`, handling `u = 0`). -/
lemma degree_le_coe_sub_one {u : Polynomial F} {n : ℕ} (hu : u.degree < n) :
    u.degree ≤ ((n - 1 : ℕ) : WithBot ℕ) := by
  by_cases h0 : u = 0
  · simp [h0]
  · rw [degree_eq_natDegree h0] at hu ⊢
    exact_mod_cast Nat.le_pred_of_lt (by exact_mod_cast hu)

/-- Degree bound for the QAP polynomial `u * v - w`, matching the degree budget available for the
quotient-by-`t` encoding: if all of `u`, `v`, `w` have degree `< n` (with `0 < n ≤ m`), then
`u * v - w` has degree `< ↑(n - 1) + ↑m` (the degree bound of `x^(n-2) · t` when `deg t = m`). -/
lemma degree_mul_sub_lt_of_degree_lt {u v w : Polynomial F} {n m : ℕ}
    (hu : u.degree < n) (hv : v.degree < n) (hw : w.degree < n)
    (hn : 0 < n) (hnm : n ≤ m) :
    (u * v - w).degree < ((n - 1 : ℕ) : WithBot ℕ) + (m : WithBot ℕ) := by
  have hcast : ((n - 1 : ℕ) : WithBot ℕ) + (m : WithBot ℕ) = ((n - 1 + m : ℕ) : WithBot ℕ) :=
    (Nat.cast_add _ _).symm
  rw [hcast]
  apply lt_of_le_of_lt (degree_sub_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (degree_mul_le _ _)
    apply lt_of_le_of_lt (add_le_add (degree_le_coe_sub_one hu) (degree_le_coe_sub_one hv))
    exact_mod_cast (by omega : n - 1 + (n - 1) < n - 1 + m)
  · exact lt_of_lt_of_le hw (by exact_mod_cast (by omega : n ≤ n - 1 + m))

end Polynomial
