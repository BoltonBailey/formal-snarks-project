import FormalSnarksProject.SNARKs.Lipmaa.Defs


open scoped BigOperators Classical

section Lipmaa

open MvPolynomial Option AGMProofSystemInstantiation

namespace Lipmaa

section soundness

lemma Polynomial.mul_self_modByMonic {F : Type} [Field F] (t p : Polynomial F) (mt : t.Monic) : (t * p) %ₘ t = 0 := by
  rw [Polynomial.modByMonic_eq_zero_iff_dvd mt]
  apply dvd_mul_right



-- Remove heartbeat limit for upcoming long-running proof
set_option maxHeartbeats 0 in -- 0 means no limit
lemma soundness
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F)}
    {u_wit : Fin n_wit → (Polynomial F)}
    {v_stmt : Fin n_stmt → (Polynomial F)}
    {v_wit : Fin n_wit → (Polynomial F)}
    {w_stmt : Fin n_stmt → (Polynomial F)}
    {w_wit : Fin n_wit → (Polynomial F)}
    {r : Fin n_wit → F} :
    (AGMProofSystemInstantiation.soundness
      F
      (Lipmaa
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
        (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (r := r))
      (Fin n_wit -> F)
      (fun (stmt : Fin n_stmt → F) (wit : Fin n_wit -> F) =>
        let t : Polynomial F :=
          ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i));
        (((List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * u_wit i) (List.finRange n_wit))))
            *
          ((List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * v_wit i) (List.finRange n_wit))))
            -
          ((List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * w_wit i) (List.finRange n_wit)))))
            %ₘ t = 0
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
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * u_wit i) (List.finRange n_wit))))
      *
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * v_wit i) (List.finRange n_wit))))
      =
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * w_wit i) (List.finRange n_wit))))
      +
      List.sum (List.map (fun x : Fin (n_var - 1) => Polynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * t)) (List.finRange (n_var - 1))) by

    rw [<-sub_eq_iff_eq_add'] at this
    have h := congr_arg (fun x => x %ₘ t) this
    simp only at h
    simp
    rw [h]
    clear this h

    simp only [mul_comm _ (t), <-mul_assoc]
    simp only [mul_assoc, List.sum_map_mul_right, List.sum_map_mul_left]

    apply Polynomial.mul_self_modByMonic
    apply Polynomial.monic_prod_of_monic
    intro i hi
    exact Polynomial.monic_X_sub_C (r i)



  -- Step 1: Obtain the coefficient equations of the MvPolynomials
  simp_rw [Lipmaa] at eqn
  -- All I want is a tactic that will apply the following simplifications to eqn in sequence.
  -- TODO can I write a tactic taking a nested list of simp lemmas?
  -- Can I combine all of these?
  simp only [monomial_zero', List.singleton_append, List.cons_append, List.append_assoc,
    List.map_cons, Sum.elim_inl, Sum.elim_inr, List.map_append, List.map_map, List.sum_cons,
    List.sum_append, List.map_nil, List.sum_nil, add_zero, Sum.elim_lam_const_lam_const, map_one,
    one_mul, map_zero, zero_mul, map_neg, neg_mul, neg_add_rev, zero_add, mul_zero,
    -- Note: everything above is @simp tagged
    Function.comp_def, List.sum_map_zero] at eqn

  -- TODO(v4.29 bump): the remainder of this proof is blocked by a `List.sum_append` regression.
  -- As of toolchain v4.29.0, `List.sum_append` carries a `Std.LawfulLeftIdentity (· + ·) 0` instance
  -- argument that `simp`/`rw` cannot synthesize here (the element type is only known via a metavariable
  -- during instance search), so the `(_ ++ _).sum` terms never split and the downstream
  -- `optionEquivRight` distribution + coefficient extraction stall. The full pipeline is preserved in
  -- git history (pre-bump); restore it once the upstream regression is resolved.
  sorry

end soundness

end Lipmaa

end Lipmaa
