import Mathlib.Data.Polynomial.Div
import FormalSnarksProject.ToMathlib.List
import Mathlib.Data.MvPolynomial.Equiv

open scoped BigOperators Classical

section Groth16TypeIII

open MvPolynomial Finsupp Option

@[simp]
lemma MvPolynomial.optionEquivRight_X_some (R : Type u) (S₁ : Type v) [CommSemiring R] (x : S₁) :
    (MvPolynomial.optionEquivRight R S₁) (X (some x)) = X x := by
  unfold optionEquivRight AlgEquiv.ofAlgHom
  simp only [AlgEquiv.coe_mk, aeval_X, Option.elim]

@[simp]
lemma MvPolynomial.optionEquivRight_X_none (R : Type u) (S₁ : Type v) [CommSemiring R] :
    (MvPolynomial.optionEquivRight R S₁) (X (none)) = C (Polynomial.X) := by
  unfold optionEquivRight AlgEquiv.ofAlgHom
  simp only [AlgEquiv.coe_mk, aeval_X, Option.elim]

@[simp]
lemma MvPolynomial.optionEquivRight_C (R : Type u) (S₁ : Type v) [CommSemiring R] (r : R) :
    (MvPolynomial.optionEquivRight R S₁) (C r) = C (Polynomial.C r) := by
  unfold optionEquivRight AlgEquiv.ofAlgHom
  simp only [Option.elim, AlgEquiv.coe_mk, aeval_C]
  rfl


/-- A ring hom from polynomials to multivariable polynomials over an option type -/
noncomputable def to_MvPolynomial_Option {F : Type} [Field F] (V : Type) :
    Polynomial F →+* MvPolynomial (Option V) F
  where
    toFun p := Polynomial.eval₂ (MvPolynomial.C) (MvPolynomial.X none) p
    map_one' := by simp
    map_mul' := by simp
    map_zero' := by simp
    map_add' := by simp

lemma to_MvPolynomial_Option_X {F V : Type} [Field F] :
    to_MvPolynomial_Option V (Polynomial.X) = MvPolynomial.X (R := F) none := by
  simp [to_MvPolynomial_Option]

lemma to_MvPolynomial_Option_C {F V : Type} [Field F] (r : F) :
    to_MvPolynomial_Option V (Polynomial.C r) = MvPolynomial.C r := by
  simp [to_MvPolynomial_Option]

@[simp]
theorem MvPolynomial.algHom_eval₂_algebraMap {σ R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] (p : MvPolynomial σ R) (f : A →ₐ[R] B) (a : σ -> A) :
    f (eval₂ (algebraMap R A) a p) = eval₂ (algebraMap R B) (f ∘ a) p := by
  simp only [eval₂, sum_def]
  simp only [f.map_sum, f.map_mul, f.map_pow, eq_intCast, map_intCast, AlgHom.commutes]
  congr
  ext x
  congr
  simp only [Function.comp_apply]
  unfold prod
  rw [f.map_prod]
  congr
  ext x1
  simp

theorem Polynomial.hom_congr_vars {R : Type u} {S : Type v}
    [CommSemiring R] [CommSemiring S]
    {f₁ : Polynomial R →+* S} {f₂ : Polynomial R →+* S}
    (hC : RingHom.comp f₁ Polynomial.C = RingHom.comp f₂ Polynomial.C)
    (hv : f₁ (Polynomial.X) = f₂ (Polynomial.X)) :
    f₁ = f₂ := by
  ext p
  exact congrFun (congrArg FunLike.coe hC) p
  exact hv


lemma optionEquivRight_comp_to_MvPolynomial_Option {F V : Type} [Field F] :
    RingHom.comp (MvPolynomial.optionEquivRight F V).toRingEquiv.toRingHom (to_MvPolynomial_Option (F := F) V) = C := by

  apply Polynomial.hom_congr_vars
  · simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom]
    rw [RingHom.comp_assoc]
    rw [@RingHom.ext_iff]
    intro x
    simp [to_MvPolynomial_Option_C]


  · simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    -- simp?
    rw [to_MvPolynomial_Option_X]
    simp only [MvPolynomial.optionEquivRight_X_none]


-- Point-free, this becomes (MvPolynomial.optionEquivRight F Vars) ∘ to_MvPolynomial_Option = C
lemma optionEquivRight_to_MvPolynomial_Option {F V : Type} [Field F] (p : Polynomial F) :
    (MvPolynomial.optionEquivRight F V) (to_MvPolynomial_Option V p) = C p := by
  rw [<-FunLike.congr_fun optionEquivRight_comp_to_MvPolynomial_Option p]
  simp


lemma MvPolynomial.sum_map_C {σ A R : Type} [CommSemiring R] (l : List A) (f : A → R) :
    (l.map (fun (x : A) => C (σ := σ) (f x))).sum = C ((l.map f).sum) := by
  -- sorry
  induction l with
  | nil => simp
  | cons hd tl ih => simp [ih]



theorem AlgEquiv.list_map_sum {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
    [CommSemiring R] [Semiring A₁] [Semiring A₂] [Algebra R A₁] [Algebra R A₂]
    (e : A₁ ≃ₐ[R] A₂) {ι : Type u_1} (f : ι → A₁) (l : List ι) :
    e (l.map (fun (x : ι) => f x)).sum = (l.map fun (x : ι) => e (f x)).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp [ih]
