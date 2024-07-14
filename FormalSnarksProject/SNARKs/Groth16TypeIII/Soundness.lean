
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
-- set_option maxHeartbeats 0 -- 0 means no limit

lemma is_sound
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F) }
    {u_wit : Fin n_wit → (Polynomial F) }
    {v_stmt : Fin n_stmt → (Polynomial F) }
    {v_wit : Fin n_wit → (Polynomial F) }
    {w_stmt : Fin n_stmt → (Polynomial F) }
    {w_wit : Fin n_wit → (Polynomial F) }
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
          ∏ i in (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i));
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
  sleep 4000


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
    done


  -- Step 1: Obtain the coefficient equations of the mv_polynomials
  simp_rw [Groth16TypeIII] at eqn


  -- All I want is a tactic that will apply the following simplifications to eqn in sequence.
  -- TODO can I write a tactic taking a nested list of simp lemmas?
  -- Can I combine all of these?


  simp only [
    Function.comp, List.sum_map_zero,
    mul_add, add_mul, List.sum_map_add,
    List.map_append, List.map_map, List.map_cons, List.map_nil,
    -- List.sum_append, List.sum_nil, List.sum_cons
    ] at eqn
  -- done
  simp only [map_one, List.singleton_append, List.cons_append, map_prod, map_sub, List.append_assoc,
    List.sum_cons, List.sum_append, List.sum_map_add, one_mul, map_zero, zero_mul, List.sum_nil,
    add_zero, map_neg, neg_mul, neg_add_rev, List.map_const', List.length_finRange,
    List.sum_replicate, smul_zero, mul_zero, zero_add] at eqn

  -- done

  simp only [
    -- Associativity to obtain a right-leaning tree
    mul_assoc,
    -- Commutativity lemmas to move X (some _) to the left
    mul_left_comm (C _) (X (some _)) _, mul_left_comm (List.sum _) (X (some _)) _,
    mul_comm (C _) (X (some _)), mul_comm (List.sum _) (X (some _)),
    -- Move negations to the bottom
    neg_mul, mul_neg,
    -- Move constant multiplications (which the X (some _) terms should be) out of sums
    List.sum_map_mul_right, List.sum_map_mul_left] at eqn


  -- done

  -- Apply MvPolynomial.optionEquivRight *here*, so that we can treat polynomials in Vars_X as constants
  trace "Converting to MvPolynomial over Polynomials"
  -- replace eqn := congr_arg (MvPolynomial.optionEquivRight F Vars) eqn
  simp only [←(EquivLike.apply_eq_iff_eq (optionEquivRight _ _))] at eqn
  simp only [AlgEquiv.map_add, AlgEquiv.map_zero, AlgEquiv.map_mul, AlgEquiv.map_one,
    AlgEquiv.map_neg, AlgEquiv.list_map_sum, AlgEquiv.map_pow] at eqn
  simp only [optionEquivRight_C, optionEquivRight_X_none, optionEquivRight_X_some, optionEquivRight_to_MvPolynomial_Option] at eqn

  -- Move Cs back out so we can recognize the monomials
  simp only [←C_mul, ←C_pow, ←C_add,
    sum_map_C] at eqn

  simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add, add_mul] at eqn

  -- done

  -- done

  trace "Applying individual coefficients"

  have h0012 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
  have h0021 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
  have h0022 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
  have h0112 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
  have h0121 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
  have h0122 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
  have h0212 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
  have h0221 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
  have h0222 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
  have h1022 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
  have h1112 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
  have h1121 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
  have h1122 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn

  clear eqn

  trace "Distribute coefficient-taking over terms"
  simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122

  trace "Simplifying coefficient expressions"
  simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122

  trace "Determine which coefficients are nonzero"
  simp (config := {decide := true}) only [ite_false, ite_true] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122
  trace "Remove zeros"
  simp only [neg_zero, add_zero, zero_add] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122

  -- done

  -- Step 2: Recursively simplify and case-analyze the equations
  -- dsimp only


  -- Set statements so that the equations are easier to read
  -- Most are optional, but there are a few that are necessary due to a bug in polyrith that causes it not to properly transcribe casts in its output
  -- /-

  generalize (List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt))) = sum_u_stmt at *

  generalize (List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt))) = sum_v_stmt at *

  generalize (List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt))) = sum_w_stmt at *


  generalize (Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.α)) = A_1 at *

  generalize (Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.β)) = A_2 at *

  generalize (Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.δ)) = A_3 at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var))) = sum_A_x at *


  generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x)) * u_stmt x) (List.finRange n_stmt))) = sum_A_u_stmt at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x)) * v_stmt x) (List.finRange n_stmt))) = sum_A_v_stmt at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x)) * w_stmt x) (List.finRange n_stmt))) = sum_A_w_stmt at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x)) * u_wit x) (List.finRange n_wit))) = sum_A_u_wit at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x)) * v_wit x) (List.finRange n_wit))) = sum_A_v_wit at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x)) * w_wit x) (List.finRange n_wit))) = sum_A_w_wit at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i)))) (List.finRange (n_var - 1)))) = sum_A_x_t at *

  generalize Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.β)) = B_1 at *

  generalize Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.γ)) = B_2 at *

  generalize Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.δ)) = B_3 at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var)) = sum_B_x at *

  generalize Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.α) = C_1 at *

  generalize Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.β) = C_2 at *

  generalize Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.δ) = C_3 at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x)) * u_wit x) (List.finRange n_wit)) = sum_C_u_wit at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x)) * v_wit x) (List.finRange n_wit)) = sum_C_v_wit at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x)) * w_wit x) (List.finRange n_wit)) = sum_C_w_wit at *

  generalize List.sum (List.map (fun x : Fin (n_var - 1) => Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i)))) (List.finRange (n_var - 1))) = sum_C_x_t at *

  -- clear_value sum_A_x sum_A_x_t sum_B_x sum_C_x_t
  -- clear_value sum_u_stmt sum_v_stmt sum_w_stmt A_1 A_2 A_3 sum_A_x sum_A_u_stmt sum_A_v_stmt sum_A_w_stmt sum_A_u_wit sum_A_v_wit sum_A_w_wit sum_A_x_t B_1 B_2 B_3 sum_B_x C_1 C_2 C_3 sum_C_u_wit sum_C_v_wit sum_C_w_wit sum_C_x_t
  -- -/


  integral_domain_tactic

  save

  skip
  -- Generated by polyrith
  linear_combination
    A_1 * B_3 * h0121 +
            (-(1 * sum_B_x * sum_A_x) - 1 * sum_A_x_t * B_3 - 1 * sum_A_w_wit * B_3) * h1122 -
          1 * h0022 +
        B_1 * sum_A_x * h1022 +
      (sum_v_stmt + sum_C_v_wit) * h0122

  -- Generated by polyrith
  linear_combination
    A_1 * B_3 * h0121 + (-(1 * sum_A_x_t * B_3) - 1 * sum_A_w_wit * B_3) * h1122 - 1 * h0022


end soundness
