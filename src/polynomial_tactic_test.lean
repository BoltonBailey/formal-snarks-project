import polynomial_tactic
import general_lemmas.single_antidiagonal
import shorten

open_locale big_operators

section
open mv_polynomial

noncomputable theory


universes u


/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]


@[derive decidable_eq]
inductive vars : Type
| x : vars
| y : vars
| z : vars


lemma foo (a b c d e f : F) (h1 : a + b + c + d = 0) (h2 : c + d + e + f = 0) ( h3 : a + b = 0) : e + f = 0 :=
begin
  rw h3 at h1,
  simp at h1,
  rw h1 at h2,
  simp at h2,
  exact h2,
  -- TODO, the mutual simplification tactic should close this in one step, essentially doing the above steps
  -- could it also handle 

end

lemma bar (a b c d e f : F) (h1 : a + b + c + d = 0) (h2 : c + d + e + f = 0) ( h3 : e + f = 0) : a + b = 0 :=
begin
  rw h3 at h2,
  -- obviuosly a grouping issue

end


lemma baz (a b c d e f : F) (h1 : true) (h2 : c + d + e + f = 0) ( h3 : true) : a + b = 0 :=
begin
  cases_type* true,
  -- obviuosly a grouping issue

end