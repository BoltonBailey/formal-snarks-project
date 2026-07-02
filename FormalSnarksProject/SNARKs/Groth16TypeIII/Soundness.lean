
import FormalSnarksProject.SNARKs.Groth16TypeIII.Defs

/-!

# Groth16TypeIII Soundness

This file contains the soundness proof for the Type III version of Groth16 presented in
["Another Look at Extraction and Randomization of Groth's zk-SNARK" by Baghery et al.](https://eprint.iacr.org/2020/811).

There are a couple of ways to check this file.

1. Run `lake build FormalSnarksProject.SNARKs.Groth16TypeIII.Soundness` from the project home directory.
   This will run the soundness proof and print the result to the console.
2. Open the file in VSCode and observe the proof in the InfoView pane.

NOTE: If you try to run `lake build` on this file using polyrith, it fails, even though it works
fine in the editor. This perhaps has to do with polyrith making external calls to Sage Web APIs.

Currently the file contains the call to `linear_combination` that polyrith outputs to avoid this.

-/


open scoped BigOperators

open Option AGMProofSystemInstantiation
open CompPoly

namespace Groth16TypeIII

section soundness


-- Remove heartbeat limit for upcoming long-running proof
set_option maxHeartbeats 0 in -- 0 means no limit
-- The final `linear_combination`/`ring` step recurses deeply on the large polynomial expressions
set_option maxRecDepth 4000 in
lemma is_sound
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {u_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {v_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {v_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {w_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {w_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {r : Fin n_wit → F} :
    (soundness
      F
      (Groth16TypeIII
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


  -- Unfold the soundness definition fully
  unfold soundness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly
  -- Introduce the arguments to the soundness definition
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, null⟩
  intro t
  have eqn := eqns ()
  clear eqns null


  -- Simplify the equation
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
    -- Restate the goal's relation polynomial in the explicit `A * B - C` form (defeq to the
    -- extractor-substituted relation), so it matches `this` syntactically.
    show (((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
        + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * u_wit i) (List.finRange n_wit))))
        * ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
        + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * v_wit i) (List.finRange n_wit))))
        - ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
        + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * w_wit i) (List.finRange n_wit))))).modByMonic t = 0
    rw [this]
    clear this

    simp only [mul_comm _ (t), <-mul_assoc]
    simp only [mul_assoc, List.sum_map_mul_right, List.sum_map_mul_left]

    apply CompPoly.CPolynomial.mul_self_modByMonic
    exact CompPoly.CPolynomial.monic_prod_X_sub_C _ r


  -- Step 1: Obtain the coefficient equations of the mv_polynomials
  --
  -- TODO(FinEnum/CompPoly refactor): the original pipeline rewrote `eqn` via `simp_rw [Groth16TypeIII]`
  -- followed by several list-expansion `simp only [...]` passes. After the move from explicit `List`
  -- fields to `FinEnum` instances, the SRS enumerations are `FinEnum.toList` of *parameterized* index
  -- types, which do not reduce to the concrete `++`/`finRange` lists definitionally, so the
  -- list-expansion no longer fires. (`Groth16TypeIII` is now `@[reducible]`, which also makes
  -- `simp_rw [Groth16TypeIII]` a no-op.) This was already blocked by the v4.29 `List.sum_append`
  -- regression (see git history for the full pre-bump pipeline); both need resolving together before
  -- the `optionEquivRight` distribution + coefficient extraction can resume.
  sorry


end soundness

end Groth16TypeIII
