module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.FinEnum.Option
public import CompPoly.OrdMultivariate.COrdMvPolynomialEvalLemmas
public import CompPoly.OrdMultivariate.Rename
public import CompPoly.Univariate.ToPoly.Impl
public import CompPoly.Univariate.ToPoly.Equiv
public import CompPoly.Univariate.DivisionCorrectness

public section

open scoped BigOperators

section Groth16TypeIII

open MvPolynomial Finsupp Option


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

theorem Polynomial.hom_congr_vars {R : Type u} {S : Type v}
    [CommSemiring R] [CommSemiring S]
    {f₁ : Polynomial R →+* S} {f₂ : Polynomial R →+* S}
    (hC : RingHom.comp f₁ Polynomial.C = RingHom.comp f₂ Polynomial.C)
    (hv : f₁ (Polynomial.X) = f₂ (Polynomial.X)) :
    f₁ = f₂ := by
  ext p
  · exact congrFun (congrArg DFunLike.coe hC) p
  · exact hv

lemma optionEquivRight_comp_to_MvPolynomial_Option {F V : Type} [Field F] :
    RingHom.comp (MvPolynomial.optionEquivRight F V).toRingEquiv.toRingHom
      (to_MvPolynomial_Option (F := F) V) = C := by
  apply Polynomial.hom_congr_vars
  · simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom]
    rw [RingHom.comp_assoc]
    rw [@RingHom.ext_iff]
    intro x
    simp [to_MvPolynomial_Option_C]
  · simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    rw [to_MvPolynomial_Option_X]
    simp only [MvPolynomial.optionEquivRight_X_none]

-- Point-free, this becomes (MvPolynomial.optionEquivRight F Vars) ∘ to_MvPolynomial_Option = C
lemma optionEquivRight_to_MvPolynomial_Option {F V : Type} [Field F] (p : Polynomial F) :
    (MvPolynomial.optionEquivRight F V) (to_MvPolynomial_Option V p) = C p := by
  rw [<-DFunLike.congr_fun optionEquivRight_comp_to_MvPolynomial_Option p]
  simp

lemma MvPolynomial.sum_map_C {σ A R : Type} [CommSemiring R] (l : List A) (f : A → R) :
    (l.map (fun (x : A) => C (σ := σ) (f x))).sum = C ((l.map f).sum) := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp [ih]

/-- `List.sum_append` restated over `AddMonoid`. The core `List.sum_append` takes
`Std.Associative`/`Std.LawfulLeftIdentity` instance arguments, which `simp` fails to synthesize
while the list's element type is still a metavariable mid-rewrite; this version only needs the
`AddMonoid` instance. -/
theorem List.sum_append_add_monoid {M : Type*} [AddMonoid M] :
    ∀ (l₁ l₂ : List M), (l₁ ++ l₂).sum = l₁.sum + l₂.sum
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp only [List.cons_append, List.sum_cons, List.sum_append_add_monoid l₁ l₂, add_assoc]

theorem AlgEquiv.list_map_sum {R : Type*} {A₁ : Type*} {A₂ : Type*}
    [CommSemiring R] [Semiring A₁] [Semiring A₂] [Algebra R A₁] [Algebra R A₂]
    (e : A₁ ≃ₐ[R] A₂) {ι : Type*} (f : ι → A₁) (l : List ι) :
    e (l.map (fun (x : ι) => f x)).sum = (l.map fun (x : ι) => e (f x)).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih => simp [ih]

/-! ### Computable-polynomial (`COrdMvPolynomial`) version of the `Option` embedding

The SNARK definitions describe SRS elements as `CPoly.COrdMvPolynomial (Option Vars) F`, with the
univariate QAP polynomials given as computable `CompPoly.CPolynomial F`. `to_COrdMvPolynomial_Option`
embeds such a `CPolynomial` into a `COrdMvPolynomial (Option V)`, mapping the variable to the `none`
sample (via `CPolynomial.eval₂`). `cmvOptionEmbedPoly` is the corresponding mathlib-`Polynomial`
embedding, kept only as the bridge TARGET: `fromCOrdMvPolynomial_to_COrdMvPolynomial_Option` records that
the computable embedding agrees with `to_MvPolynomial_Option ∘ toPoly` across `CPoly.COrdMvPolynomial.ordPolyRingEquiv`,
which is how soundness proofs fall back on the existing `optionEquivRight` machinery. -/

open CPoly
open CompPoly

/-- Embedding of mathlib univariate `Polynomial`s into `COrdMvPolynomial` over an option type, sending
`Polynomial.X` to the `none` sample. Used only as the bridge target for `to_COrdMvPolynomial_Option`. -/
noncomputable def cmvOptionEmbedPoly {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (V : Type) [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V] :
    Polynomial F →+* COrdMvPolynomial (Option V) F :=
  Polynomial.eval₂RingHom COrdMvPolynomial.CRingHom (COrdMvPolynomial.X none)

@[simp] lemma cmvOptionEmbedPoly_X {F V : Type} [Field F] [BEq F] [LawfulBEq F] [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V] :
    cmvOptionEmbedPoly V (Polynomial.X) = COrdMvPolynomial.X (R := F) none := by
  simp [cmvOptionEmbedPoly]

@[simp] lemma cmvOptionEmbedPoly_C {F V : Type} [Field F] [BEq F] [LawfulBEq F] [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
    (r : F) :
    cmvOptionEmbedPoly V (Polynomial.C r) = COrdMvPolynomial.C r := by
  simp only [cmvOptionEmbedPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

lemma fromCOrdMvPolynomial_cmvOptionEmbedPoly {F V : Type} [Field F] [BEq F] [LawfulBEq F]
    [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V] (p : Polynomial F) :
    CPoly.COrdMvPolynomial.fromCOrdMvPolynomial (cmvOptionEmbedPoly V p) = to_MvPolynomial_Option V p := by
  have hpr : ∀ x : COrdMvPolynomial (Option V) F,
      (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option V) (R := F)).toRingHom x = CPoly.COrdMvPolynomial.fromCOrdMvPolynomial x :=
    fun _ => rfl
  have key :
      RingHom.comp (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option V) (R := F)).toRingHom
        (cmvOptionEmbedPoly (F := F) V) = to_MvPolynomial_Option V := by
    apply Polynomial.hom_congr_vars
    · ext r
      simp only [RingHom.coe_comp, Function.comp_apply, cmvOptionEmbedPoly_C,
        to_MvPolynomial_Option_C]
      rw [hpr, CPoly.COrdMvPolynomial.fromCOrdMvPolynomial_C]
    · simp only [RingHom.coe_comp, Function.comp_apply, cmvOptionEmbedPoly_X,
        to_MvPolynomial_Option_X]
      rw [hpr, CPoly.COrdMvPolynomial.fromCOrdMvPolynomial_X]
  have hp := DFunLike.congr_fun key p
  simp only [RingHom.coe_comp, Function.comp_apply] at hp
  rw [hpr] at hp
  exact hp

/-- The computable (`CompPoly.CPolynomial`) version of the `Option` embedding: sends a univariate
computable polynomial to a `COrdMvPolynomial (Option V)`, mapping the variable to the `none` sample.
The SNARK definitions describe SRS elements with this. -/
noncomputable def to_COrdMvPolynomial_Option {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (V : Type) [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V] (p : CompPoly.CPolynomial F) : COrdMvPolynomial (Option V) F :=
  CompPoly.CPolynomial.eval₂ COrdMvPolynomial.CRingHom (COrdMvPolynomial.X none) p

lemma to_COrdMvPolynomial_Option_eq_poly {F V : Type} [Field F] [BEq F] [LawfulBEq F] [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
    (p : CompPoly.CPolynomial F) :
    to_COrdMvPolynomial_Option V p = cmvOptionEmbedPoly V p.toPoly := by
  rw [to_COrdMvPolynomial_Option, CompPoly.CPolynomial.eval₂_toPoly, cmvOptionEmbedPoly,
    Polynomial.coe_eval₂RingHom]

/-- The computable embedding agrees with the mathlib embedding `to_MvPolynomial_Option ∘ toPoly`
across `CPoly.COrdMvPolynomial.ordPolyRingEquiv` — the bridge soundness proofs use to fall back on `optionEquivRight`. -/
lemma fromCOrdMvPolynomial_to_COrdMvPolynomial_Option {F V : Type} [Field F] [BEq F] [LawfulBEq F]
    [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V] (p : CompPoly.CPolynomial F) :
    CPoly.COrdMvPolynomial.fromCOrdMvPolynomial (to_COrdMvPolynomial_Option V p) = to_MvPolynomial_Option V p.toPoly := by
  rw [to_COrdMvPolynomial_Option_eq_poly, fromCOrdMvPolynomial_cmvOptionEmbedPoly]

/-! ### `CPolynomial` monic / `modByMonic` helpers for the QAP vanishing polynomial

The soundness/completeness proofs need the computable vanishing polynomial
`t = ∏ (X - C (rᵢ))` to be monic and the basic `(t * p) %ₘ t = 0` fact, neither of which CompPoly
exposes natively for `CPolynomial`. These transport the statements through `toPoly` to the mathlib
`Polynomial` lemmas (`monic_X_sub_C`, `monic_prod_of_monic`, `modByMonic_eq_zero_iff_dvd`). -/

namespace CompPoly.CPolynomial

/-- `toPoly` of a computable linear factor `X - C x` is mathlib's `X - C x`. -/
lemma toPoly_X_sub_C {F : Type} [Field F] [BEq F] [LawfulBEq F] (x : F) :
    (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C x).toPoly = Polynomial.X - Polynomial.C x := by
  rw [toPoly_sub, X_toPoly, C_toPoly]

/-- The computable vanishing polynomial `∏ (X - C (r i))` is monic. -/
lemma monic_prod_X_sub_C {F : Type} [Field F] [BEq F] [LawfulBEq F] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → F) :
    (∏ i ∈ s, (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i))).monic := by
  rw [monic_toPoly_iff, toPoly_prod]
  simp only [toPoly_X_sub_C]
  exact Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (r i))

/-- The forward map of CompPoly's ring equivalence is `toPoly`, stated as an equality of
functions. CompPoly's `ringEquiv_apply` closes this by `rfl`, but that definitional unfolding is
unavailable to importers of the (unexposed) definitions, so the lemma is used explicitly below. -/
lemma coe_ringEquiv {F : Type} [Field F] [BEq F] [LawfulBEq F] :
    ⇑(CompPoly.CPolynomial.ringEquiv (R := F)) = CompPoly.CPolynomial.toPoly :=
  funext CompPoly.CPolynomial.ringEquiv_apply

/-- `toPoly` is injective (it underlies the ring equivalence with mathlib `Polynomial`). -/
lemma toPoly_injective {F : Type} [Field F] [BEq F] [LawfulBEq F] :
    Function.Injective (CompPoly.CPolynomial.toPoly (R := F)) := by
  rw [← coe_ringEquiv]
  exact (CompPoly.CPolynomial.ringEquiv (R := F)).injective

/-- `toPoly` distributes over `List.sum`. -/
lemma toPoly_list_sum {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (l : List (CompPoly.CPolynomial F)) :
    l.sum.toPoly = (l.map CompPoly.CPolynomial.toPoly).sum := by
  simpa only [coe_ringEquiv] using map_list_sum (CompPoly.CPolynomial.ringEquiv (R := F)) l

/-- For monic `t`, `(t * p) %ₘ t = 0` — the computable analogue of `Polynomial.mul_self_modByMonic`. -/
lemma mul_self_modByMonic {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (t p : CompPoly.CPolynomial F) (ht : t.monic) :
    (t * p).modByMonic t = 0 := by
  rw [← toPoly_eq_zero_iff, modByMonic_toPoly_eq_modByMonic _ _ ht, toPoly_mul,
    Polynomial.modByMonic_eq_zero_iff_dvd ((monic_toPoly_iff t).mp ht)]
  exact dvd_mul_right _ _

end CompPoly.CPolynomial

end Groth16TypeIII
