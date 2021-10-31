import data.finsupp.basic

section


/-- An inductive type from which to index the variables of the mv_polynomials the proof manages -/
@[derive decidable_eq]
inductive vars : Type
| α : vars
| β : vars

lemma finsupp_vars_eq_ext (f g : vars →₀ ℕ) : f = g ↔ 
  f vars.α = g vars.α ∧ f vars.β = g vars.β :=
begin
  rw finsupp.ext_iff,
  split,
    {
      intro h,
      split, exact h vars.α,
      exact h vars.β,
    },
    {
      intro h,
      intro a,
      induction a,
      finish,
      finish,
    },
  -- induction,
end

end