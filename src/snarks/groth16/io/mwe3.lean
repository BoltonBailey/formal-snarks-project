import data.mv_polynomial.basic
import algebra.polynomial.big_operators

open_locale big_operators classical

section 

open mv_polynomial 

noncomputable theory



universes u v

parameter {F : Type u}
parameter [field F]

namespace mv_polynomial
variables {σ : Type*} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variables {R : Type u} 
variables [comm_semiring R] {p q : mv_polynomial σ R}



@[derive decidable_eq]
inductive vars : Type
| α : vars
| β : vars
| γ : vars
| δ : vars

run_cmd mk_simp_attr `polynomial_nf
run_cmd tactic.add_doc_string `simp_attr.polynomial_nf "Attribute for lemmas that are used in the conversion of mv_polynomial expressions to a normal form"

variables {α : Type u} {β : Type v}

namespace finset
variables {s₁ s₂ : finset α} {a : α} {b : β}  {f g : α → β}


section semiring
variables [non_unital_non_assoc_semiring β]

lemma mul_sum_2 : 
 ∑ x in s₁, b * f x 
  = b * (∑ x in s₁, f x) :=
finset.mul_sum.symm


@[polynomial_nf]
lemma sum_X_mul (f : α -> mv_polynomial σ R) (s : σ) :
  (∑ x in s₁, X s * f x) = X s * (∑ x in s₁, f x) :=
by rw finset.mul_sum


-- set_option pp.notation false
-- set_option pp.implicit true

lemma foo : 
  ∑ (i : fin 3),
    mv_polynomial.X vars.γ
    * ((mv_polynomial.C (i : polynomial F)) : mv_polynomial vars (polynomial F))
  =
  mv_polynomial.X vars.γ
  * ∑ (i : fin 4),
    ((mv_polynomial.C (i : polynomial F)) : mv_polynomial vars (polynomial F))
   :=
begin
  rw sum_X_mul, -- fails
  -- rw mul_sum_2, -- works
end

end semiring

end finset

end mv_polynomial

end