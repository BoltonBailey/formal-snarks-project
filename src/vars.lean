

section


/-- An inductive type from which to index the variables of the 3-variable polynomials the proof manages -/
@[derive decidable_eq]
inductive vars : Type
| X : vars
| Y : vars
| Z : vars

end