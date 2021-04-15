

section


/-- An inductive type from which to index the variables of the 3-variable polynomials the proof manages -/
@[derive decidable_eq]
inductive vars : Type
| Alpha : vars
| Beta : vars
| Gamma : vars
| Delta : vars
| X : vars

end