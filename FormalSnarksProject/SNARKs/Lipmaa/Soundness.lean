import FormalSnarksProject.SNARKs.Lipmaa.Defs


open scoped BigOperators

section Lipmaa

open Option AGMProofSystemInstantiation
open CompPoly

namespace Lipmaa

section soundness

-- Remove heartbeat limit for upcoming long-running proof
set_option maxHeartbeats 0 in -- 0 means no limit
lemma soundness
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {u_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {v_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {v_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {w_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {w_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {r : Fin n_wit → F} :
    (AGMProofSystemInstantiation.soundness
      F
      (Lipmaa
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
        (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (r := r))
      (Fin n_wit -> F)
      (fun (stmt : Fin n_stmt → F) (wit : Fin n_wit -> F) =>
        let t : CompPoly.CPolynomial F :=
          ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i));
        (((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit i) * u_wit i) (List.finRange n_wit))))
            *
          ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit i) * v_wit i) (List.finRange n_wit))))
            -
          ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit i) * w_wit i) (List.finRange n_wit))))).modByMonic t = 0
      )
      (fun prover i => prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i))
    ) := by

  unfold AGMProofSystemInstantiation.soundness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly

  -- TODO namespcace AGMProofSystemInstantiation eliminate
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, null⟩
  intro t
  have eqn := eqns ()
  clear eqns null

  -- let C_m := fun i => prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)
  -- let C_h := fun x => prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.x_pow_times_t x)

  suffices
      ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * u_wit i) (List.finRange n_wit))))
      *
      ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * v_wit i) (List.finRange n_wit))))
      =
      ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * w_wit i) (List.finRange n_wit))))
      +
      List.sum (List.map (fun x : Fin (n_var - 1) => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.x_pow_times_t x)) * (CompPoly.CPolynomial.X ^ (x : ℕ) * t)) (List.finRange (n_var - 1))) by

    rw [<-sub_eq_iff_eq_add'] at this
    have h := congr_arg (fun x => x.modByMonic t) this
    simp only at h
    simp
    rw [h]
    clear this h

    simp only [mul_comm _ (t), <-mul_assoc]
    simp only [mul_assoc, List.sum_map_mul_right, List.sum_map_mul_left]

    apply CompPoly.CPolynomial.mul_self_modByMonic
    exact CompPoly.CPolynomial.monic_prod_X_sub_C _ r



  -- Step 1: Obtain the coefficient equations of the MvPolynomials
  --
  -- TODO(FinEnum/CompPoly refactor): the original pipeline rewrote `eqn` via `simp_rw [Lipmaa]`
  -- followed by a list-expansion `simp only [...]`. After the move from explicit `List` fields to
  -- `FinEnum` instances, the SRS enumerations are `FinEnum.toList` of *parameterized* index types,
  -- which do not reduce to the concrete `++`/`finRange` lists definitionally, so the list-expansion
  -- no longer fires. (`Lipmaa` is now `@[reducible]`, which also makes `simp_rw [Lipmaa]` a no-op.)
  -- This was already blocked by the v4.29 `List.sum_append` regression (see git history for the full
  -- pre-bump pipeline); both need resolving together before the coefficient extraction can resume.
  sorry

end soundness

end Lipmaa

end Lipmaa
