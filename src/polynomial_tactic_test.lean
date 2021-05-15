import polynomial_tactic

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


def my_polynomial : mv_polynomial vars F := (X vars.x + X vars.y + 2 * X vars.z) * (X vars.x + X vars.y + 2 * X vars.z)

example : coeff (finsupp.single vars.z 1 + finsupp.single vars.y 1) my_polynomial = 4 :=
begin
  rw my_polynomial,
  simp only with coeff_simp,
  -- TODO you can probably take queues from what you do in the babysnark file

end

end