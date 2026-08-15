module

public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

-- `Polynomial.modByMonic_eq_zero_iff_quotient_eq_zero` (PR 11116) is now in Mathlib,
-- so it is no longer defined here.

lemma RingHom.list_map_sum {A : Type v} {B : Type w}
    [Semiring A] [Semiring B]
    (φ : A →+* B) {ι : Type u_1} (f : ι → A) (s : List ι) :
    φ (List.sum (s.map fun (x : ι) => f x)) = List.sum (s.map fun (x : ι) => φ (f x)) := by
  induction s with
  | nil =>
    simp
  | cons x xs ih =>
    simp [ih]
