

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.MvPolynomial.Monad
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.List.BigOperators.Basic

-- https://github.com/leanprover-community/mathlib4/pull/11112
lemma List.sum_map_zero {α : Type u_1} {β : Type u_2} [AddCommMonoid β]
    {l : List α} : List.sum (List.map (fun _ => (0 : β)) l) = 0 := by
  simp only [map_const', sum_replicate, smul_zero]
