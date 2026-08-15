
module

public import FormalSnarksProject.Models.AGMProofSystemInstantiation
public import FormalSnarksProject.ToMathlib.ForTransformations

@[expose] public section


section

/-!
This file contains functions for manipulating AGMProofSystemInstantiations.
These functions can be used to prove the soundness of the AGM SNARK.

The SRS values are the computable `CPoly.COrdMvPolynomial`; the soundness proofs work with them
directly (they are a `CommRing` with no zero divisors, see `ToMathlib/ForTransformations.lean`),
transporting to mathlib's `MvPolynomial` along `CPoly.COrdMvPolynomial.ordPolyRingEquiv` only where a mathlib-side
fact is needed (`collapseToxicWaste`).
-/

open CPoly CPoly.COrdMvPolynomial

variable {F : Type}

variable [Field F] [BEq F] [LawfulBEq F]

/--
Given a particular toxic waste sample, we can multiply this sample through all SRS elems without affecting the soundness of the SNARK. This assumes that all checks have uniform degree as polynomials over the proof elements, (indeed for bilinear pairings, these polynomials will have degree 2) -/
def changeExponent_G1 (𝓟 : AGMProofSystemInstantiation F) (sample : 𝓟.Sample)
    (d : ℕ) :
    AGMProofSystemInstantiation F where
      Stmt := 𝓟.Stmt
      Sample := 𝓟.Sample
      SRSElements_G1 := 𝓟.SRSElements_G1
      SRSElements_G2 := 𝓟.SRSElements_G2
      SRSElementValue_G1 := fun i => X sample ^ d * 𝓟.SRSElementValue_G1 i
      SRSElementValue_G2 := 𝓟.SRSElementValue_G2
      Proof_G1 := 𝓟.Proof_G1
      Proof_G2 := 𝓟.Proof_G2
      EqualityChecks := 𝓟.EqualityChecks
      Pairings := 𝓟.Pairings
      Pairings_FinEnum := 𝓟.Pairings_FinEnum
      verificationPairingSRS_G1 := 𝓟.verificationPairingSRS_G1
      verificationPairingSRS_G2 := 𝓟.verificationPairingSRS_G2
      verificationPairingProof_G1 := 𝓟.verificationPairingProof_G1
      verificationPairingProof_G2 := 𝓟.verificationPairingProof_G2
      Identified_Proof_Elems := 𝓟.Identified_Proof_Elems

lemma changeExponent_soundness {𝓟 : AGMProofSystemInstantiation F} (sample : 𝓟.Sample) (d : ℕ)
    (hTypeIII : 𝓟.Identified_Proof_Elems = [])
    (Wit : Type)
    (relation : 𝓟.Stmt -> Wit -> Prop) (extractor : 𝓟.Prover -> Wit)
    (h_sound : 𝓟.soundness F Wit relation extractor ) :
    (changeExponent_G1 𝓟 sample d).soundness F Wit relation extractor := by
  intros stmt agm checks_pass
  rcases checks_pass with ⟨poly_checks_pass, _⟩
  apply h_sound
  clear h_sound
  unfold AGMProofSystemInstantiation.verify AGMProofSystemInstantiation.check_poly AGMProofSystemInstantiation.pairing_poly AGMProofSystemInstantiation.proof_element_G1_as_poly AGMProofSystemInstantiation.proof_element_G2_as_poly at *
  constructor
  · intro check_idx
    replace poly_checks_pass := poly_checks_pass check_idx
    unfold changeExponent_G1 at poly_checks_pass
    simp only at poly_checks_pass
    simp only [
      mul_left_comm _ (X sample ^ d),
      mul_assoc (X sample ^ d),
      List.sum_map_mul_left,
      ←mul_add (X sample ^ d)] at poly_checks_pass
    rw [mul_eq_zero] at poly_checks_pass
    cases poly_checks_pass with
    | inl poly_checks_pass =>
      exact absurd poly_checks_pass
        (pow_ne_zero d (CPoly.COrdMvPolynomial.X_ne_zero sample))
    | inr poly_checks_pass =>
      exact poly_checks_pass
  · rw [hTypeIII]
    simp

/--
Adds one SRS element to another and zeros out the added element. This might be useful in the case where in the given SNARK, this pair of SRS elements are always used with the same coefficient, in which case the resulting SNARK is complete. -/
def collapseSRSElement_G1 (𝓟 : AGMProofSystemInstantiation F)
    [DecidableEq 𝓟.SRSElements_G1] (twin1 twin2 : 𝓟.SRSElements_G1) :
    AGMProofSystemInstantiation F where
      Stmt := 𝓟.Stmt
      Sample := 𝓟.Sample
      SRSElements_G1 := 𝓟.SRSElements_G1
      SRSElements_G2 := 𝓟.SRSElements_G2
      SRSElementValue_G1 := fun srs => if srs = twin1
                                        then 𝓟.SRSElementValue_G1 twin1 + 𝓟.SRSElementValue_G1 twin2
                                        else if srs = twin2 then 0 else 𝓟.SRSElementValue_G1 srs
      SRSElementValue_G2 := 𝓟.SRSElementValue_G2
      Proof_G1 := 𝓟.Proof_G1
      Proof_G2 := 𝓟.Proof_G2
      EqualityChecks := 𝓟.EqualityChecks
      Pairings := 𝓟.Pairings
      Pairings_FinEnum := 𝓟.Pairings_FinEnum
      verificationPairingSRS_G1 := 𝓟.verificationPairingSRS_G1
      verificationPairingSRS_G2 := 𝓟.verificationPairingSRS_G2
      verificationPairingProof_G1 := 𝓟.verificationPairingProof_G1
      verificationPairingProof_G2 := 𝓟.verificationPairingProof_G2
      Identified_Proof_Elems := 𝓟.Identified_Proof_Elems

lemma collapseSRSElement_G1_soundness (𝓟 : AGMProofSystemInstantiation F)
    (hTypeIII : 𝓟.Identified_Proof_Elems = [])
    [DecidableEq 𝓟.SRSElements_G1] (twin1 twin2 : 𝓟.SRSElements_G1) (not_same : twin1 ≠ twin2)
    (interchangeable :
      ∀ (idx : 𝓟.Proof_G1)
        (agm : 𝓟.Proof_G1 → 𝓟.SRSElements_G1 → F),
        agm idx twin1 = agm idx twin2)
    (interchangeable' : ∀ (stmt : 𝓟.Stmt) (check_idx : 𝓟.EqualityChecks) (pairing : 𝓟.Pairings check_idx), 𝓟.verificationPairingSRS_G1 stmt check_idx pairing twin1 = 𝓟.verificationPairingSRS_G1 stmt check_idx pairing twin2)
    (Wit : Type)
    (relation : 𝓟.Stmt -> Wit -> Prop) (extractor : 𝓟.Prover -> Wit)
    (h_sound : 𝓟.soundness F Wit relation extractor) :
    (collapseSRSElement_G1 𝓟 twin1 twin2).soundness F Wit relation extractor := by
  -- The `FinEnum` enumeration is a nodup listing of all SRS elements, so every element is
  -- counted exactly once (this replaces the `count = 1` hypotheses of the pre-`FinEnum`
  -- version of this lemma).
  have hcount1 : (FinEnum.toList 𝓟.SRSElements_G1).count twin1 = 1 :=
    List.count_eq_one_of_mem FinEnum.nodup_toList (FinEnum.mem_toList twin1)
  have hcount2 : (FinEnum.toList 𝓟.SRSElements_G1).count twin2 = 1 :=
    List.count_eq_one_of_mem FinEnum.nodup_toList (FinEnum.mem_toList twin2)
  intros stmt agm checks_pass
  -- Re-type the introduced data at the underlying scheme (definitionally equal), so the
  -- goals below are type-correct without unfolding `collapseSRSElement_G1` projections.
  change 𝓟.Stmt at stmt
  change AGMProofSystemInstantiation.Prover F 𝓟 at agm
  rcases checks_pass with ⟨poly_checks_pass, null⟩
  apply h_sound
  clear h_sound null
  unfold AGMProofSystemInstantiation.verify AGMProofSystemInstantiation.check_poly AGMProofSystemInstantiation.pairing_poly AGMProofSystemInstantiation.proof_element_G1_as_poly AGMProofSystemInstantiation.proof_element_G2_as_poly at *
  constructor
  · intro check_idx
    replace poly_checks_pass := poly_checks_pass check_idx
    unfold collapseSRSElement_G1 at poly_checks_pass
    simp only [mul_ite, mul_zero] at poly_checks_pass
    rw [←poly_checks_pass]
    clear poly_checks_pass
    -- Congruence surgery down to the per-pairing G1 inputs. (Explicit `congrArg` steps rather
    -- than `congr`, whose congruence-lemma synthesis `whnf`s the computable-polynomial
    -- expressions and times out.)
    refine congrArg List.sum (List.map_congr_left fun pairing _ => ?_)
    refine congrArg₂ (· * ·) ?_ rfl
    refine congrArg₂ (· + ·) ?_ ?_
    · refine congrArg List.sum (List.map_congr_left fun proof_elem _ => ?_)
      refine congrArg₂ (· * ·) rfl ?_
      replace interchangeable := interchangeable proof_elem agm.1
      simp only [List.sum_map_ite_eq, nsmul_eq_mul, zero_sub, smul_neg]
      simp only [hcount1, Nat.cast_one, interchangeable, not_same, ↓reduceIte, one_mul, hcount2]
      ring
    · simp only [List.sum_map_ite_eq, nsmul_eq_mul, zero_sub, smul_neg]
      simp only [hcount1, Nat.cast_one, not_same, ↓reduceIte, one_mul, hcount2]
      rw [mul_add]
      simp_rw [interchangeable']
      ring
  · rw [hTypeIII]
    simp

/-- Returns a SNARK where one fewer toxic waste element is actually used,
replaced by sample_target ^ d -/
def collapseToxicWaste (𝓟 : AGMProofSystemInstantiation F) (d : ℕ)
    [DecidableEq 𝓟.Sample]
    (sample_removed sample_target : 𝓟.Sample) :
    AGMProofSystemInstantiation F where
      Stmt := 𝓟.Stmt
      Sample := 𝓟.Sample
      SRSElements_G1 := 𝓟.SRSElements_G1
      SRSElements_G2 := 𝓟.SRSElements_G2
      SRSElementValue_G1 := fun elem => COrdMvPolynomial.bind₁
                              ((fun x => (if x = sample_removed then X (R := F) sample_target ^ d else X x)))
                              (𝓟.SRSElementValue_G1 elem)
      SRSElementValue_G2 := fun elem => COrdMvPolynomial.bind₁
                              ((fun x => (if x = sample_removed then X (R := F) sample_target ^ d else X x)))
                              (𝓟.SRSElementValue_G2 elem)
      Proof_G1 := 𝓟.Proof_G1
      Proof_G2 := 𝓟.Proof_G2
      EqualityChecks := 𝓟.EqualityChecks
      Pairings := 𝓟.Pairings
      Pairings_FinEnum := 𝓟.Pairings_FinEnum
      verificationPairingSRS_G1 := 𝓟.verificationPairingSRS_G1
      verificationPairingSRS_G2 := 𝓟.verificationPairingSRS_G2
      verificationPairingProof_G1 := 𝓟.verificationPairingProof_G1
      verificationPairingProof_G2 := 𝓟.verificationPairingProof_G2
      Identified_Proof_Elems := 𝓟.Identified_Proof_Elems

lemma collapseToxicWaste_check_poly (𝓟 : AGMProofSystemInstantiation F) (d : ℕ)
    [DecidableEq 𝓟.Sample]
    (sample_removed sample_target : 𝓟.Sample) :
    ∀ agm stmt check_idx,
      AGMProofSystemInstantiation.check_poly (collapseToxicWaste 𝓟 d sample_removed sample_target) agm stmt check_idx
        =
      COrdMvPolynomial.bind₁
        ((fun x => (if x = sample_removed then X sample_target ^ d else X x)))
        (AGMProofSystemInstantiation.check_poly 𝓟 agm stmt check_idx) := by
  intros agm stmt check_idx
  unfold collapseToxicWaste AGMProofSystemInstantiation.check_poly AGMProofSystemInstantiation.pairing_poly AGMProofSystemInstantiation.proof_element_G1_as_poly AGMProofSystemInstantiation.proof_element_G2_as_poly
  simp only [CPoly.COrdMvPolynomial.bind₁_eq_eval₂Hom, RingHom.list_map_sum, _root_.map_mul,
    _root_.map_add, CPoly.COrdMvPolynomial.eval₂Hom_algebraMap_C]

lemma collapseToxicWaste_soundness (𝓟 : AGMProofSystemInstantiation F) (d : ℕ) (hd : 0 < d)
    [DecidableEq 𝓟.Sample]
    (sample_removed sample_target : 𝓟.Sample)
    (sample_target_neq_removed : sample_target ≠ sample_removed)
    (hdegree : ∀ agm stmt check_idx, COrdMvPolynomial.degreeOf sample_target
      (AGMProofSystemInstantiation.check_poly 𝓟 agm stmt check_idx) < d)
    (hTypeIII : 𝓟.Identified_Proof_Elems = [])
    (Wit : Type)
    (relation : 𝓟.Stmt -> Wit -> Prop) (extractor : 𝓟.Prover -> Wit)
    (h_sound : 𝓟.soundness F Wit relation extractor) :
    (collapseToxicWaste 𝓟 d sample_removed sample_target).soundness F Wit relation extractor := by
  intros stmt agm checks_pass
  rcases checks_pass with ⟨poly_checks_pass, proof_elem_checks_pass⟩
  apply h_sound
  clear h_sound proof_elem_checks_pass
  unfold AGMProofSystemInstantiation.verify
  constructor
  · intro check_idx
    replace poly_checks_pass := poly_checks_pass check_idx
    rw [collapseToxicWaste_check_poly 𝓟 d sample_removed sample_target agm stmt check_idx]
      at poly_checks_pass
    -- Transport the substituted check equation to mathlib's `MvPolynomial` and conclude with
    -- the (mathlib-side) injectivity of the substitution on low-degree polynomials.
    have equivZero : (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := 𝓟.Sample) (R := F)) 0 = 0 := map_zero
    have equivX : ∀ v : 𝓟.Sample,
        (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := 𝓟.Sample) (R := F)) (X v) = MvPolynomial.X v :=
      fun v => CPoly.COrdMvPolynomial.fromCOrdMvPolynomial_X v
    have equivPow : ∀ (q : COrdMvPolynomial 𝓟.Sample F) (n : ℕ),
        (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := 𝓟.Sample) (R := F)) (q ^ n)
          = (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := 𝓟.Sample) (R := F)) q ^ n :=
      fun q n => map_pow _ q n
    replace poly_checks_pass :
        (MvPolynomial.bind₁ (fun x => (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := 𝓟.Sample) (R := F))
            (if x = sample_removed then X sample_target ^ d else X x)))
          ((CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := 𝓟.Sample) (R := F))
            (AGMProofSystemInstantiation.check_poly 𝓟 agm stmt check_idx)) = 0 := by
      rw [← CPoly.COrdMvPolynomial.ordPolyRingEquiv_bind₁, poly_checks_pass]
      exact map_zero
    have hfun : (fun x => (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := 𝓟.Sample) (R := F))
          (if x = sample_removed then X sample_target ^ d else X x))
        = fun x => if x = sample_removed then MvPolynomial.X (R := F) sample_target ^ d
            else MvPolynomial.X x := by
      funext x
      by_cases hx : x = sample_removed
      · rw [if_pos hx, if_pos hx, equivPow, equivX]
      · rw [if_neg hx, if_neg hx, equivX]
    rw [hfun] at poly_checks_pass
    have hzero : (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := 𝓟.Sample) (R := F))
        (AGMProofSystemInstantiation.check_poly 𝓟 agm stmt check_idx) = 0 := by
      apply MvPolynomial.bind₁_ite_pow_eq_zero_of (σ := 𝓟.Sample)
        ((CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := 𝓟.Sample) (R := F))
          (AGMProofSystemInstantiation.check_poly 𝓟 agm stmt check_idx))
        d hd sample_removed sample_target
      · exact sample_target_neq_removed
      · exact poly_checks_pass
      · have h := hdegree agm stmt check_idx
        have hb : COrdMvPolynomial.degreeOf sample_target
              (AGMProofSystemInstantiation.check_poly 𝓟 agm stmt check_idx)
            = MvPolynomial.degreeOf sample_target
              ((CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := 𝓟.Sample) (R := F))
                (AGMProofSystemInstantiation.check_poly 𝓟 agm stmt check_idx)) :=
          congrFun CPoly.COrdMvPolynomial.degreeOf_equiv sample_target
        rw [hb] at h
        exact h
    apply (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := 𝓟.Sample) (R := F)).injective
    rw [hzero, equivZero]
  · rw [hTypeIII]
    simp

end
