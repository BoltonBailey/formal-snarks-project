
import tactic
-- TODO post to zulip complaining that this throws on g but not on f and that the error message "failed" is unhelpful

def f : ℕ → ℕ := (λ n : ℕ , n + 1)

def g (n : ℕ) : ℕ := n + 1

lemma foo : ∀ i : ℕ, f i = g i :=
begin
  -- intro i, -- This causes the rw g to work, since it is no longer under a binder
  rw f,
  rw g,
  -- simp_rw g, -- This also works
end



