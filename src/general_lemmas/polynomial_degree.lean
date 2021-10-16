import data.polynomial.div
import data.polynomial.field_division
import algebra.polynomial.big_operators

open_locale big_operators

section

universes u


parameter {F : Type u}
parameter [field F] 

 -- /-- t is the polynomial divisibility by which is used to verify satisfaction of the SSP -/
-- def t : polynomial R := ∏ i in (finset.fin_range m), (polynomial.X - polynomial.C (r i))
-- TODO this and the following lemmas about this could potentially be spun off 
-- make a `monic_from_roots` function for mathlib

/-- t has degree m -/
lemma nat_degree_product_form (m : ℕ) (f : fin m → F) : 
  polynomial.nat_degree (∏ i in (finset.fin_range m), (polynomial.X - polynomial.C (f i))) = m :=
begin
  -- rw t,
  rw polynomial.nat_degree_prod,
  simp,
  intros i hi,
  exact polynomial.X_sub_C_ne_zero (f i),
end

lemma monic_of_product_form (m : ℕ) (f : fin m → F) : 
  (∏ i in (finset.fin_range m), (polynomial.X - polynomial.C (f i))).monic :=
begin
  apply polynomial.monic_prod_of_monic,
  intros i hi,
  exact polynomial.monic_X_sub_C (f i),
end


end