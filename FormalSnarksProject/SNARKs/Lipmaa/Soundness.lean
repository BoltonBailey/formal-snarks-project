import FormalSnarksProject.SNARKs.Lipmaa.Defs


open scoped BigOperators Classical

section Lipmaa

open MvPolynomial Option AGMProofSystemInstantiation

namespace Lipmaa

section soundness

lemma Polynomial.mul_modByMonic {F : Type} [Field F] (t p : Polynomial F) (mt : t.Monic) : (t * p) %ₘ t = 0 := by
  rw [Polynomial.dvd_iff_modByMonic_eq_zero]
  apply dvd_mul_right
  exact mt



-- Remove heartbeat limit for upcoming long-running proof
set_option maxHeartbeats 0 -- 0 means no limit

lemma soundness
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F) }
    {u_wit : Fin n_wit → (Polynomial F) }
    {v_stmt : Fin n_stmt → (Polynomial F) }
    {v_wit : Fin n_wit → (Polynomial F) }
    {w_stmt : Fin n_stmt → (Polynomial F) }
    {w_wit : Fin n_wit → (Polynomial F) }
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

  unfold soundness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly

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

    apply Polynomial.mul_modByMonic
    apply Polynomial.monic_prod_of_monic
    intro i hi
    exact Polynomial.monic_X_sub_C (r i)
    done



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
    Function.comp, List.sum_map_zero] at eqn

  simp only [mul_add, add_mul, List.sum_map_add] at eqn

  -- Move all the X (some _) terms to the left, and out of sums
  simp only [
    -- Associativity to obtain a right-leaning tree
    mul_assoc,
    -- Commutativity lemmas to move X (some _) to the left
    mul_left_comm (C _) (X (some _)) _, mul_left_comm (List.sum _) (X (some _)) _,
    mul_comm (C _) (X (some _)), mul_comm (List.sum _) (X (some _)),
    -- Commutativity lemmas to move X (some _) ^ _ to the left
    mul_left_comm (C _) (X (some _) ^ _) _, mul_left_comm (List.sum _) (X (some _) ^ _) _,
    mul_comm (C _) (X (some _) ^ _), mul_comm (List.sum _) (X (some _) ^ _),
    -- Move negations to the bottom
    neg_mul, mul_neg,
    -- Move constant multiplications (which the X (some _) terms should be) out of sums
    List.sum_map_mul_right, List.sum_map_mul_left] at eqn

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

  simp only [X, C_apply, monomial_mul, monomial_pow, one_mul, mul_one, add_zero, zero_add, mul_add, add_mul] at eqn

  trace "Applying individual coefficients"

  have h0012 := congr_arg (coeff (Finsupp.single Vars.y (75 * 0 + 25 * 0 + 5 * 1 + 1 * 2))) eqn
  have h0021 := congr_arg (coeff (Finsupp.single Vars.y (75 * 0 + 25 * 0 + 5 * 2 + 1 * 1))) eqn
  have h0022 := congr_arg (coeff (Finsupp.single Vars.y (75 * 0 + 25 * 0 + 5 * 2 + 1 * 2))) eqn
  have h0112 := congr_arg (coeff (Finsupp.single Vars.y (75 * 0 + 25 * 1 + 5 * 1 + 1 * 2))) eqn
  have h0121 := congr_arg (coeff (Finsupp.single Vars.y (75 * 0 + 25 * 1 + 5 * 2 + 1 * 1))) eqn
  have h0122 := congr_arg (coeff (Finsupp.single Vars.y (75 * 0 + 25 * 1 + 5 * 2 + 1 * 2))) eqn
  have h0212 := congr_arg (coeff (Finsupp.single Vars.y (75 * 0 + 25 * 2 + 5 * 1 + 1 * 2))) eqn
  have h0221 := congr_arg (coeff (Finsupp.single Vars.y (75 * 0 + 25 * 2 + 5 * 2 + 1 * 1))) eqn
  have h0222 := congr_arg (coeff (Finsupp.single Vars.y (75 * 0 + 25 * 2 + 5 * 2 + 1 * 2))) eqn
  have h1022 := congr_arg (coeff (Finsupp.single Vars.y (75 * 1 + 25 * 0 + 5 * 2 + 1 * 2))) eqn
  have h1112 := congr_arg (coeff (Finsupp.single Vars.y (75 * 1 + 25 * 1 + 5 * 1 + 1 * 2))) eqn
  have h1121 := congr_arg (coeff (Finsupp.single Vars.y (75 * 1 + 25 * 1 + 5 * 2 + 1 * 1))) eqn
  have h1122 := congr_arg (coeff (Finsupp.single Vars.y (75 * 1 + 25 * 1 + 5 * 2 + 1 * 2))) eqn

  -- have h1023 := congr_arg (coeff (Finsupp.single Vars.y (75 * 1 + 25 * 0 + 5 * 2 + 1 * 3))) eqn


  clear eqn

  trace "Distribute coefficient-taking over terms"
  simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122

  -- done

  trace "Simplifying coefficient expressions"
  simp only [Vars.finsupp_eq_ext, Finsupp.smul_single', Finsupp.single_apply, Finsupp.add_apply] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122

  trace "Determine which coefficients are nonzero"
  simp (config := {decide := true}) only [ite_false, ite_true] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122
  trace "Remove zeros"
  simp only [neg_zero, add_zero, zero_add, one_pow, mul_one, one_mul] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122


  -- Step 2: Recursively simplify and case-analyze the equations
  -- dsimp only


  -- Set statements so that the equations are easier to read
  -- /-
  set sum_u_stmt := (List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
  set sum_v_stmt := (List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
  set sum_w_stmt := (List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))

  set A_1 := Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.α)
  set A_2 := Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.β)
  set A_3 := Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.δ)
  set sum_A_x := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ))
          (List.finRange n_var))

  set sum_A_u_stmt := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x)) *
              u_stmt x)
          (List.finRange n_stmt))
  set sum_A_v_stmt := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x)) *
              v_stmt x)
          (List.finRange n_stmt))
  set sum_A_w_stmt := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x)) *
              w_stmt x)
          (List.finRange n_stmt))
  set sum_A_u_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x)) *
              u_wit x)
          (List.finRange n_wit))
  set sum_A_v_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x)) *
              v_wit x)
          (List.finRange n_wit))
  set sum_A_w_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x)) *
              w_wit x)
          (List.finRange n_wit))
  set sum_A_x_t := (List.sum
                  (List.map
                    (fun x =>
                      Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.x_pow_times_t x)) *
                        (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i))))
                    (List.finRange (n_var - 1))))
  set B_1 := Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.β))
  set B_2 := Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.γ))
  set B_3 := Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.δ))

  set sum_B_x := List.sum
                    (List.map
                      (fun x =>
                        Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ))
                      (List.finRange n_var))

  set C_1 := Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.α)
  set C_2 := Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.β)
  set C_3 := Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.δ)
  set sum_C_u_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x)) *
              u_wit x)
          (List.finRange n_wit))
  set sum_C_v_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x)) *
              v_wit x)
          (List.finRange n_wit))
  set sum_C_w_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x)) *
              w_wit x)
          (List.finRange n_wit))
  set sum_C_x_t := List.sum
        (List.map
          (fun x : Fin (n_var - 1) =>
            Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i))))
          (List.finRange (n_var - 1)))

  -- clear_value sum_A_x sum_A_x_t sum_B_x sum_C_x_t
  clear_value sum_u_stmt sum_v_stmt sum_w_stmt A_1 A_2 A_3 sum_A_x sum_A_u_stmt sum_A_v_stmt sum_A_w_stmt sum_A_u_wit sum_A_v_wit sum_A_w_wit sum_A_x_t B_1 B_2 B_3 sum_B_x C_1 C_2 C_3 sum_C_u_wit sum_C_v_wit sum_C_w_wit sum_C_x_t
  -- -/
  -- done

  integral_domain_tactic

  save

  skip
  polyrith

  polyrith

  -- NOTE: If you try to run lake build on this file, polyrith fails, even though it works fine in the editor
  -- This perhaps has to do with polyrith making external calls to Sage Web APIs

end soundness
