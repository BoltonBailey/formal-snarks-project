
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


open scoped BigOperators Classical

open MvPolynomial Option AGMProofSystemInstantiation

namespace Groth16TypeIII

section soundness


-- Remove heartbeat limit for upcoming long-running proof
set_option maxHeartbeats 0 in -- 0 means no limit
-- The final `linear_combination`/`ring` step recurses deeply on the large polynomial expressions
set_option maxRecDepth 4000 in
lemma is_sound
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F)}
    {u_wit : Fin n_wit → (Polynomial F)}
    {v_stmt : Fin n_stmt → (Polynomial F)}
    {v_wit : Fin n_wit → (Polynomial F)}
    {w_stmt : Fin n_stmt → (Polynomial F)}
    {w_wit : Fin n_wit → (Polynomial F)}
    {r : Fin n_wit → F} :
    (soundness
      F
      (Groth16TypeIII
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

    apply Polynomial.self_mul_modByMonic
    apply Polynomial.monic_prod_of_monic
    intro i hi
    exact Polynomial.monic_X_sub_C (r i)


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

  -- Step 2: Recursively simplify and case-analyze the equations
  -- dsimp only


  -- Set statements so that the equations are easier to read
  -- Most are optional, but there are a few that are necessary due to a bug in polyrith that causes it not to properly transcribe casts in its output
  -- /-

  -- generalize (List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt))) = sum_u_stmt at *

  -- generalize (List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt))) = sum_v_stmt at *

  -- generalize (List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt))) = sum_w_stmt at *


  -- generalize (Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.α)) = A_1 at *

  -- generalize (Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.β)) = A_2 at *

  -- generalize (Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.δ)) = A_3 at *

  -- generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var))) = sum_A_x at *


  -- generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x)) * u_stmt x) (List.finRange n_stmt))) = sum_A_u_stmt at *

  -- generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x)) * v_stmt x) (List.finRange n_stmt))) = sum_A_v_stmt at *

  -- generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x)) * w_stmt x) (List.finRange n_stmt))) = sum_A_w_stmt at *

  -- generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x)) * u_wit x) (List.finRange n_wit))) = sum_A_u_wit at *

  -- generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x)) * v_wit x) (List.finRange n_wit))) = sum_A_v_wit at *

  -- generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x)) * w_wit x) (List.finRange n_wit))) = sum_A_w_wit at *

  -- generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i)))) (List.finRange (n_var - 1)))) = sum_A_x_t at *

  -- generalize Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.β)) = B_1 at *

  -- generalize Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.γ)) = B_2 at *

  -- generalize Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.δ)) = B_3 at *

  -- generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var)) = sum_B_x at *

  -- generalize Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.α) = C_1 at *

  -- generalize Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.β) = C_2 at *

  -- generalize Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.δ) = C_3 at *

  -- generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x)) * u_wit x) (List.finRange n_wit)) = sum_C_u_wit at *

  -- generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x)) * v_wit x) (List.finRange n_wit)) = sum_C_v_wit at *

  -- generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x)) * w_wit x) (List.finRange n_wit)) = sum_C_w_wit at *

  -- generalize List.sum (List.map (fun x : Fin (n_var - 1) => Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i)))) (List.finRange (n_var - 1))) = sum_C_x_t at *

  -- clear_value sum_A_x sum_A_x_t sum_B_x sum_C_x_t
  -- clear_value sum_u_stmt sum_v_stmt sum_w_stmt A_1 A_2 A_3 sum_A_x sum_A_u_stmt sum_A_v_stmt sum_A_w_stmt sum_A_u_wit sum_A_v_wit sum_A_w_wit sum_A_x_t B_1 B_2 B_3 sum_B_x C_1 C_2 C_3 sum_C_u_wit sum_C_v_wit sum_C_w_wit sum_C_x_t
  -- -/


  -- integral_domain_tactic


  -- skip
  -- -- Generated by polyrith
  -- linear_combination
  --   A_1 * B_3 * h0121 +
  --           (-(1 * sum_B_x * sum_A_x) - 1 * sum_A_x_t * B_3 - 1 * sum_A_w_wit * B_3) * h1122 -
  --         1 * h0022 +
  --       B_1 * sum_A_x * h1022 +
  --     (sum_v_stmt + sum_C_v_wit) * h0122

  -- -- Generated by polyrith
  -- linear_combination
  --   A_1 * B_3 * h0121 + (-(1 * sum_A_x_t * B_3) - 1 * sum_A_w_wit * B_3) * h1122 - 1 * h0022


end soundness

end Groth16TypeIII
