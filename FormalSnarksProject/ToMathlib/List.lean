

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.MvPolynomial.Monad
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.List.BigOperators.Basic


lemma List.sum_map_zero {α : Type u_1} {β : Type u_2} [AddCommMonoid β]
    {l : List α} : List.sum (List.map (fun _ => (0 : β)) l) = 0 := by
  induction l with
  | nil => rfl
  | cons h t ih => rw [List.map_cons, List.sum_cons, ih, add_zero]
