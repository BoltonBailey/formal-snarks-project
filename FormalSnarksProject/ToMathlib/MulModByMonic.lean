
import Mathlib.Data.Polynomial.Div

lemma Polynomial.mul_modByMonic {F : Type} [Field F] (t p : Polynomial F) (mt : t.Monic) : (t * p) %ₘ t = 0 := by
  rw [Polynomial.dvd_iff_modByMonic_eq_zero]
  apply dvd_mul_right
  exact mt
