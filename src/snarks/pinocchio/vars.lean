
import data.finsupp.basic

section


/-- An inductive type from which to index the variables of the multi-variable polynomials the proof manages -/
@[derive decidable_eq]
inductive vars : Type
| r_v : vars
| r_w : vars
| α_v : vars
| α_w : vars
| α_y : vars
| β : vars
| γ : vars

lemma finsupp_vars_eq_ext (f g : vars →₀ ℕ) : f = g ↔ 
  f vars.r_v = g vars.r_v 
  ∧ f vars.r_w = g vars.r_w
  ∧ f vars.α_v = g vars.α_v
  ∧ f vars.α_w = g vars.α_w
  ∧ f vars.α_y = g vars.α_y
  ∧ f vars.β = g vars.β
  ∧ f vars.γ = g vars.γ :=
begin
  rw finsupp.ext_iff,
  split,
    {
      intro h,
      split, exact h vars.r_v,
      split, exact h vars.r_w,
      split, exact h vars.α_v,
      split, exact h vars.α_w,
      split, exact h vars.α_y,
      split, exact h vars.β,
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
      finish,
      finish,
      finish,
    },
  -- induction,
end

end