import data.mv_polynomial.basic
-- import data.finsupp.lattice

open mv_polynomial
namespace mv_polynomial
section

universes u

variables {F : Type u}
variables [field F]

noncomputable theory

parameter {vars : Type}
parameter [decidable_eq vars]


def degree_bound (b : vars →₀ ℕ) (p : mv_polynomial vars F) := (∀ v : vars →₀ ℕ, v ∈ p.support → v ≤ b)

-- Two mv_polynomials are equal iff their coefficients are equal for all terms with variables below the max degree
lemma eq_iff_coeff_eq_below_degree_bound (p q : mv_polynomial vars F) 
  (b : vars →₀ ℕ) 
  (bound_p : p.degree_bound b) 
  (bound_q : q.degree_bound b) 
  : p = q ↔ (∀ (c : vars →₀ ℕ), c ≤ b → p.coeff c = q.coeff c)
:=
begin
  rw mv_polynomial.ext_iff,
  split,
    { intros hm c hc, 
      exact hm c, },
    { intros hc m,
      by_cases m ∈ p.support,
      { exact hc m (bound_p m h), },
      { have hp : coeff m p = 0, exact not_mem_support_iff.mp h,
        by_cases m ∈ q.support,
        { exact hc m (bound_q m h), },
          have hq : coeff m q = 0, exact not_mem_support_iff.mp h,
          rw [hp, hq], }, },
end


-- degree_bound lemmas for X, C, add, mul

lemma degree_bound_C (f : F) : degree_bound 0 (@mv_polynomial.C F _ _ f) :=
begin
  sorry,
end

lemma degree_bound_X (v : vars) : degree_bound (finsupp.single v 1) (@mv_polynomial.X F _ _ v) :=
begin
  sorry,
end

lemma degree_bound_add (p q : mv_polynomial vars F) 
  (bp bq : vars →₀ ℕ) 
  (degree_bound_p : degree_bound bp p)
  (degree_bound_q : degree_bound bq q)
 : degree_bound (bp ⊔ bq) (p + q) :=
begin
  sorry,
end


lemma degree_bound_mul (p q : mv_polynomial vars F) 
  (bp bq : vars →₀ ℕ) 
  (degree_bound_p : degree_bound bp p)
  (degree_bound_q : degree_bound bq q)
 : degree_bound (bp + bq) (p * q) :=
begin
  sorry,
end


end