
import FormalSnarksProject.Models.AGMProofSystemInstantiation
import FormalSnarksProject.ToMathlib.ForTransformations


section

/-!
This file contains functionf for manipulating AGMProofSystemInstantiations.
These functions can be used to prove the soundness of the AGM SNARK.
-/

universe u

variable {F : Type}

variable [Field F]

/--
Given a particular toxic waste sample, we can multiply this sample through all SRS elems without affecting the soundness of the SNARK. This assumes that all checks have uniform degree as polynomials over the proof elements, (indeed for bilinear pairings, these polynomials will have degree 2) -/
noncomputable def changeExponent_G1 (𝓟 : AGMProofSystemInstantiation F) (sample : 𝓟.Sample)
    (d : ℕ) :
    AGMProofSystemInstantiation F where
      Stmt := 𝓟.Stmt
      Sample := 𝓟.Sample
      SRSElements_G1 := 𝓟.SRSElements_G1
      ListSRSElements_G1 := 𝓟.ListSRSElements_G1
      SRSElements_G2 := 𝓟.SRSElements_G2
      ListSRSElements_G2 := 𝓟.ListSRSElements_G2
      SRSElementValue_G1 := fun i => MvPolynomial.X sample ^ d * 𝓟.SRSElementValue_G1 i
      SRSElementValue_G2 := 𝓟.SRSElementValue_G2
      Proof_G1 := 𝓟.Proof_G1
      ListProof_G1 := 𝓟.ListProof_G1
      Proof_G2 := 𝓟.Proof_G2
      ListProof_G2 := 𝓟.ListProof_G2
      EqualityChecks := 𝓟.EqualityChecks
      Pairings := 𝓟.Pairings
      ListPairings := 𝓟.ListPairings
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
    simp at poly_checks_pass
    simp only [
      mul_comm _ (MvPolynomial.X sample ^ d),
      mul_left_comm _ (MvPolynomial.X sample ^ d),
      mul_assoc (MvPolynomial.X sample ^ d),
      List.sum_map_mul_right, List.sum_map_mul_left,
      ←mul_add (MvPolynomial.X sample ^ d)] at poly_checks_pass
    rw [mul_eq_zero] at poly_checks_pass
    cases poly_checks_pass with
    | inl poly_checks_pass =>
      exfalso
      simp at poly_checks_pass
    | inr poly_checks_pass =>
      exact poly_checks_pass
  · rw [hTypeIII]
    simp

/--
Adds one SRS element to another and zeros out the added element. This might be useful in the case where in the given SNARK, this pair of SRS elements are always used with the same coefficient, in which case the resulting SNARK is complete. -/
noncomputable def collapseSRSElement_G1 (𝓟 : AGMProofSystemInstantiation F)
    [DecidableEq 𝓟.SRSElements_G1] (twin1 twin2 : 𝓟.SRSElements_G1) :
    AGMProofSystemInstantiation F where
      Stmt := 𝓟.Stmt
      Sample := 𝓟.Sample
      SRSElements_G1 := 𝓟.SRSElements_G1
      ListSRSElements_G1 := 𝓟.ListSRSElements_G1
      SRSElements_G2 := 𝓟.SRSElements_G2
      ListSRSElements_G2 := 𝓟.ListSRSElements_G2
      SRSElementValue_G1 := fun srs => if srs = twin1
                                        then 𝓟.SRSElementValue_G1 twin1 + 𝓟.SRSElementValue_G1 twin2
                                        else if srs = twin2 then 0 else 𝓟.SRSElementValue_G1 srs
      SRSElementValue_G2 := 𝓟.SRSElementValue_G2
      Proof_G1 := 𝓟.Proof_G1
      ListProof_G1 := 𝓟.ListProof_G1
      Proof_G2 := 𝓟.Proof_G2
      ListProof_G2 := 𝓟.ListProof_G2
      EqualityChecks := 𝓟.EqualityChecks
      Pairings := 𝓟.Pairings
      ListPairings := 𝓟.ListPairings
      verificationPairingSRS_G1 := 𝓟.verificationPairingSRS_G1
      verificationPairingSRS_G2 := 𝓟.verificationPairingSRS_G2
      verificationPairingProof_G1 := 𝓟.verificationPairingProof_G1
      verificationPairingProof_G2 := 𝓟.verificationPairingProof_G2
      Identified_Proof_Elems := 𝓟.Identified_Proof_Elems

lemma collapseSRSElement_G1_soundness (𝓟 : AGMProofSystemInstantiation F)
    (hTypeIII : 𝓟.Identified_Proof_Elems = [])
    [DecidableEq 𝓟.SRSElements_G1] (twin1 twin2 : 𝓟.SRSElements_G1) (not_same : twin1 ≠ twin2)
    (hcount1 : 𝓟.ListSRSElements_G1.count twin1 = 1)
    (hcount2 : 𝓟.ListSRSElements_G1.count twin2 = 1)
    (interchangeable :
      ∀ (idx : 𝓟.Proof_G1)
        (agm : 𝓟.Proof_G1 → 𝓟.SRSElements_G1 → F),
        agm idx twin1 = agm idx twin2)
    (interchangeable' : ∀ (stmt : 𝓟.Stmt) (check_idx : 𝓟.EqualityChecks) (pairing : 𝓟.Pairings check_idx),  𝓟.verificationPairingSRS_G1 stmt check_idx pairing twin1 = 𝓟.verificationPairingSRS_G1 stmt check_idx pairing twin2 )
    (Wit : Type)
    (relation : 𝓟.Stmt -> Wit -> Prop) (extractor : 𝓟.Prover -> Wit)
    (h_sound : 𝓟.soundness F Wit relation extractor) :
    (collapseSRSElement_G1 𝓟 twin1 twin2).soundness F Wit relation extractor := by
  intros stmt agm checks_pass
  rcases checks_pass with ⟨poly_checks_pass, null⟩
  apply h_sound
  clear h_sound null
  unfold AGMProofSystemInstantiation.verify AGMProofSystemInstantiation.check_poly AGMProofSystemInstantiation.pairing_poly AGMProofSystemInstantiation.proof_element_G1_as_poly AGMProofSystemInstantiation.proof_element_G2_as_poly at *
  constructor
  · intro check_idx
    replace poly_checks_pass := poly_checks_pass check_idx
    unfold collapseSRSElement_G1 at poly_checks_pass
    simp at poly_checks_pass
    rw [←poly_checks_pass]
    clear poly_checks_pass
    congr
    funext pairing
    congr 1
    congr 1
    · congr
      funext proof_elem
      congr 1
      replace interchangeable := interchangeable proof_elem agm.1
      simp [List.sum_map_ite_eq, hcount1, hcount2, not_same, interchangeable]
      ring
    · simp [List.sum_map_ite_eq, hcount1, hcount2, not_same, interchangeable]
      rw [mul_add]
      simp_rw [interchangeable']
      ring
  · rw [hTypeIII]
    simp

/-- Returns a SNARK where one fewer toxic waste element is actually used,
replaced by sample_target ^ d -/
noncomputable def collapseToxicWaste (𝓟 : AGMProofSystemInstantiation F) (d : ℕ)
    [DecidableEq 𝓟.Sample]
    (sample_removed sample_target : 𝓟.Sample) :
    AGMProofSystemInstantiation F where
      Stmt := 𝓟.Stmt
      Sample := 𝓟.Sample
      SRSElements_G1 := 𝓟.SRSElements_G1
      ListSRSElements_G1 := 𝓟.ListSRSElements_G1
      SRSElements_G2 := 𝓟.SRSElements_G2
      ListSRSElements_G2 := 𝓟.ListSRSElements_G2
      SRSElementValue_G1 := fun elem => MvPolynomial.bind₁
                              ((fun x => (if x = sample_removed then MvPolynomial.X (R := F) sample_target ^ d else MvPolynomial.X x)))
                              (𝓟.SRSElementValue_G1 elem)
      SRSElementValue_G2 := fun elem => MvPolynomial.bind₁
                              ((fun x => (if x = sample_removed then MvPolynomial.X (R := F) sample_target ^ d else MvPolynomial.X x)))
                              (𝓟.SRSElementValue_G2 elem)
      Proof_G1 := 𝓟.Proof_G1
      ListProof_G1 := 𝓟.ListProof_G1
      Proof_G2 := 𝓟.Proof_G2
      ListProof_G2 := 𝓟.ListProof_G2
      EqualityChecks := 𝓟.EqualityChecks
      Pairings := 𝓟.Pairings
      ListPairings := 𝓟.ListPairings
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
      MvPolynomial.bind₁
        ((fun x => (if x = sample_removed then MvPolynomial.X sample_target ^ d else MvPolynomial.X x)))
        (AGMProofSystemInstantiation.check_poly 𝓟 agm stmt check_idx) := by
  intros agm stmt check_idx
  unfold collapseToxicWaste AGMProofSystemInstantiation.check_poly AGMProofSystemInstantiation.pairing_poly AGMProofSystemInstantiation.proof_element_G1_as_poly AGMProofSystemInstantiation.proof_element_G2_as_poly
  simp [AlgHom.list_map_sum]

lemma collapseToxicWaste_soundness (𝓟 : AGMProofSystemInstantiation F) (d : ℕ) (hd : 0 < d)
    [DecidableEq 𝓟.Sample]
    (sample_removed sample_target : 𝓟.Sample)
    (sample_target_neq_removed : sample_target ≠ sample_removed)
    (hdegree : ∀ agm stmt check_idx, MvPolynomial.degreeOf sample_target (AGMProofSystemInstantiation.check_poly 𝓟 agm stmt check_idx) < d)
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
    have checked_poly_is_transformed :
        AGMProofSystemInstantiation.check_poly (collapseToxicWaste 𝓟 d sample_removed sample_target) agm stmt check_idx
          =
        MvPolynomial.bind₁
          ((fun x => (if x = sample_removed then MvPolynomial.X (R := F) sample_target ^ d else MvPolynomial.X x)))
          (AGMProofSystemInstantiation.check_poly 𝓟 agm stmt check_idx) := by
      exact collapseToxicWaste_check_poly 𝓟 d sample_removed sample_target agm stmt check_idx
    rw [checked_poly_is_transformed] at poly_checks_pass
    apply MvPolynomial.bind₁_ite_pow_eq_zero_of (σ := 𝓟.Sample) (AGMProofSystemInstantiation.check_poly 𝓟 agm stmt check_idx) d hd sample_removed sample_target
    exact sample_target_neq_removed
    exact poly_checks_pass
    exact hdegree agm stmt check_idx
  · rw [hTypeIII]
    simp

end
