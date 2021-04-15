import data.fintype.basic

section


/-- An inductive type from which to index the variables of the 3-variable polynomials the proof manages -/
@[derive decidable_eq]
inductive vars : Type
| s : vars
| α : vars
| β_v : vars
| β_w : vars
| β_y : vars
| γ : vars

end