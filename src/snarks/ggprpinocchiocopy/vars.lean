
import data.finsupp.basic

section


/-- An inductive type from which to index the variables of the multi-variable polynomials the proof manages -/
@[derive decidable_eq]
inductive vars : Type
| α : vars
| β_v : vars
| β_w : vars
| γ : vars

lemma finsupp_vars_eq_ext (f g : vars →₀ ℕ) : f = g ↔ 
  f vars.α = g vars.α 
  ∧ f vars.β_v = g vars.β_v
  ∧ f vars.β_w = g vars.β_w
  ∧ f vars.γ = g vars.γ :=
begin
  rw finsupp.ext_iff,
  split,
    {
      intro h,
      split, exact h vars.α,
      split, exact h vars.β_v,
      split, exact h vars.β_w,
      exact h vars.γ,
    },
    {
      intro h,
      intro a,
      induction a,
      finish,
      finish,
      finish,
      finish,
    },
  -- induction,
end

end