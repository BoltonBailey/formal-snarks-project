import data.finsupp.basic

section


/-- An inductive type from which to index the variables of the mv_polynomials the proof manages -/
@[derive decidable_eq]
inductive vars : Type
| α : vars
| β : vars
| γ : vars
| δ : vars
-- | x : vars

-- lemma finsupp_vars_eq_ext (f g : vars →₀ ℕ) : f = g ↔ 
--   f vars.α = g vars.α ∧ f vars.β = g vars.β ∧ f vars.γ = g vars.γ ∧ f vars.δ = g vars.δ ∧ f vars.x = g vars.x :=
-- begin
--   rw finsupp.ext_iff,
--   split,
--     {
--       intro h,
--       split, exact h vars.α,
--       split, exact h vars.β,
--       split, exact h vars.γ,
--       split, exact h vars.δ,
--       exact h vars.x,
--     },
--     {
--       intro h,
--       intro a,
--       induction a,
--       finish,
--       finish,
--       finish,
--       finish,
--       finish,
--     },
-- end

lemma finsupp_vars_eq_ext (f g : vars →₀ ℕ) : f = g ↔ 
  f vars.α = g vars.α ∧ f vars.β = g vars.β ∧ f vars.γ = g vars.γ ∧ f vars.δ = g vars.δ :=
begin
  rw finsupp.ext_iff,
  split,
    {
      intro h,
      split, exact h vars.α,
      split, exact h vars.β,
      split, exact h vars.γ,
      exact h vars.δ,
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