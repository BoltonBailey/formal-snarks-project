
import data.nat.basic

section my_section

-- Mario's example
open tactic
meta def mysatz : tactic unit := do
  `[simp only [mul_eq_zero, zero_mul, mul_zero, zero_eq_zero, or_true, true_or]
    at * {fail_if_unchanged := ff}],
  _::_ ← get_goals | skip,
  `[cases ‹_ ∨ _› with found_zero found_zero]; (do
    `[rw found_zero at *; clear found_zero],
    mysatz)

lemma zero_eq_zero : 0 = 0 ↔ true := 
begin
  simp only [eq_self_iff_true],
end

example (a b c d e f : ℕ) (h1 : a = 0 ∨ b = 0) (h2 : d * e = a) : b * d * f * e = 0
:=
begin
  mysatz,

  -- iterate 5 {
  --   focus {
  --   fail_if_success { done },
  --   try {simp only [mul_eq_zero, zero_mul, mul_zero, zero_eq_zero, or_true, true_or] at *}, 
  --   try {clear found_zero}, -- clear "found_zero" if present
  --   done <|> id {cases ‹_ ∨ _› with found_zero found_zero; rw found_zero at *},
  --   }, },




end 

end my_section


