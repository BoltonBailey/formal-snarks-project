module

public import Mathlib.Data.FinEnum

/-!

# `FinEnum.toList` of instances built by `FinEnum.ofList`

The SNARK definitions build `FinEnum` instances for their (possibly parameterized) index types via
`FinEnum.ofList`. The soundness proofs need to expand `FinEnum.toList` of such instances back into
the defining list, which holds propositionally (up to `dedup`) but not definitionally when the list
is parameterized (e.g. by `List.finRange n_var`). These lemmas provide that expansion.

-/

@[expose] public section

namespace FinEnum

variable {α : Type*} [DecidableEq α]

/-- `toList` of an instance built by `ofNodupList` is the defining list. -/
lemma toList_ofNodupList (xs : List α) (h : ∀ x, x ∈ xs) (h' : xs.Nodup) :
    @FinEnum.toList α (FinEnum.ofNodupList xs h h') = xs := by
  show (List.finRange xs.length).map xs.get = xs
  exact List.map_get_finRange xs

/-- `toList` of an instance built by `ofList` is the defining list, deduplicated. -/
lemma toList_ofList (xs : List α) (h : ∀ x, x ∈ xs) :
    @FinEnum.toList α (FinEnum.ofList xs h) = xs.dedup :=
  toList_ofNodupList _ _ _

/-- `toList` of an instance built by `ofList` from a list without duplicates is that list. -/
lemma toList_ofList_of_nodup (xs : List α) (h : ∀ x, x ∈ xs) (h' : xs.Nodup) :
    @FinEnum.toList α (FinEnum.ofList xs h) = xs :=
  (toList_ofList xs h).trans (List.dedup_eq_self.mpr h')

end FinEnum
