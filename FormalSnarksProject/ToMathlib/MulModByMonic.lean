
import Mathlib.Data.Polynomial.Div

-- https://github.com/leanprover-community/mathlib4/pull/11113
lemma Polynomial.mul_modByMonic {F : Type} [CommRing F] (t p : Polynomial F) (mt : t.Monic) : (t * p) %ₘ t = 0 := by
  rw [Polynomial.dvd_iff_modByMonic_eq_zero mt]
  exact dvd_mul_right t p
