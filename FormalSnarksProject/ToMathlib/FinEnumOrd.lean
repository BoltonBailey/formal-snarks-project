/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Data.FinEnum

/-!
# Lawful `Ord` instances from `FinEnum`

`COrdMvPolynomial σ R` requires `[Ord σ] [Std.TransOrd σ] [Std.LawfulEqOrd σ]` on the variable
type. Our SNARK variable types are small enumerations that already carry `FinEnum` instances, so
we obtain a lawful `Ord` by pulling back the comparison on `Fin n` along `FinEnum.equiv`.

These are deliberately *not* global instances: a blanket `[FinEnum σ] → Ord σ` instance would
overlap with existing `Ord` instances (e.g. on `Option σ`, where core's `instOrdOption` must win
so that core's lawfulness instances for `Option` apply). Instead, each variable type declares

```lean
instance : Ord Vars := FinEnum.toOrd
instance : Std.TransOrd Vars := FinEnum.toOrd.transOrd
instance : Std.LawfulEqOrd Vars := FinEnum.toOrd.lawfulEqOrd
```
-/

public section

namespace FinEnum

variable {σ : Type*} [FinEnum σ]

/-- The comparison on `σ` obtained by pulling back the comparison on `Fin n` along
`FinEnum.equiv`. -/
@[instance_reducible] protected def toOrd : Ord σ :=
  ⟨fun a b => compare (equiv a) (equiv b)⟩

private abbrev finCompare : Fin (card σ) → Fin (card σ) → Ordering := compare

theorem toOrd.transOrd : @Std.TransOrd σ FinEnum.toOrd where
  eq_swap {_a _b} := Std.OrientedCmp.eq_swap (cmp := finCompare (σ := σ))
  isLE_trans h₁ h₂ := Std.TransCmp.isLE_trans (cmp := finCompare (σ := σ)) h₁ h₂

theorem toOrd.lawfulEqOrd : @Std.LawfulEqOrd σ FinEnum.toOrd where
  compare_self {a} := Std.ReflCmp.compare_self (cmp := finCompare (σ := σ)) (a := equiv a)
  eq_of_compare h :=
    equiv.injective (Std.LawfulEqCmp.eq_of_compare (cmp := finCompare (σ := σ)) h)

end FinEnum
