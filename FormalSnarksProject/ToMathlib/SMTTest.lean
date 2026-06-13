import Mathlib
import Smt

#check Smt.Config

example [Nonempty U] {f : U → U → U} {a b c d : U}
  (h0 : a = b) (h1 : c = d) (h2 : p1 ∧ True) (h3 : (¬ p1) ∨ (p2 ∧ p3))
  (h4 : (¬ p3) ∨ (¬ (f a c = f b d))) : False := by
  smt [h0, h1, h2, h3, h4]

lemma foo [Field F] (a b x y z : F)
    (h1 : a * x = 0) (h2 : a * y + b * x = z) (h4 : b * y = 0) : (b * x - z) * (a * y - z) = 0 := by
  -- smt (showQuery := true) [h1, h2, h4]
  -- smt [h1, h2, h4]
  grobner
  -- linear_combination h1

#print axioms foo
