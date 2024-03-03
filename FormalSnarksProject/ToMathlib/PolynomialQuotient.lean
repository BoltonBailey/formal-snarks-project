import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Data.Polynomial.FieldDivision

-- https://github.com/leanprover-community/mathlib4/pull/11116
lemma Polynomial.modByMonic_eq_zero_iff_quotient_eq_zero {R : Type*} [CommRing R] (p q : Polynomial R) (hq : q.Monic) :
    p %ₘ q = 0 ↔ (p : Polynomial R ⧸ Ideal.span {q}) = 0 := by
  rw [Polynomial.dvd_iff_modByMonic_eq_zero hq, Ideal.Quotient.eq_zero_iff_dvd]

-- https://github.com/leanprover-community/mathlib4/pull/11116
@[simp]
lemma Polynomial.quotient_singleton_eq {R : Type*} [CommRing R] (p : Polynomial R) : (Ideal.Quotient.mk (Ideal.span {p})) p = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_dvd]

lemma RingHom.list_map_sum {A : Type v} {B : Type w}
    [Semiring A] [Semiring B]
    (φ : A →+* B) {ι : Type u_1} (f : ι → A) (s : List ι) :
    φ (List.sum (s.map fun (x : ι) => f x)) = List.sum (s.map fun (x : ι) => φ (f x)) := by
  induction s with
  | nil =>
    simp
  | cons x xs ih =>
    simp [ih]
