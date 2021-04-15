

section


/-- An inductive type from which to index the variables of the 3-variable polynomials the proof manages -/
@[derive decidable_eq]
inductive vars : Type
| r_v : vars
| r_w : vars
| s : vars
| α_v : vars
| α_w : vars
| α_y : vars
| β : vars
| γ : vars

end