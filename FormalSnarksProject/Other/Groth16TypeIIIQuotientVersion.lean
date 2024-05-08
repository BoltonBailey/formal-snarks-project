import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Algebra.Polynomial.Div
-- import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Algebra.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode
import FormalSnarksProject.ToMathlib.PolynomialQuotient

/-!

# Groth16TypeIII

This file contains a second proof of the soundness of the Groth16 SNARK, this time using the idea of casting all polynomialls to the quotient ring `F[X]/(t)` where `t` is the polynomial whose roots are the witness values. This avoids the need to determine the coefficient fo this value.

-/

open scoped BigOperators Classical

section Groth16TypeIII

open MvPolynomial Option AGMProofSystemInstantiation

namespace Groth16TypeIII

inductive Vars : Type where
  | α : Vars
  | β : Vars
  | γ : Vars
  | δ : Vars
deriving Repr, BEq

local notation "Vars_α" => some Vars.α
local notation "Vars_β" => some Vars.β
local notation "Vars_γ" => some Vars.γ
local notation "Vars_δ" => some Vars.δ
local notation "Vars_x" => none

lemma Vars.finsupp_eq_ext (f g : Vars →₀ ℕ) : f = g ↔
    f Vars.α = g Vars.α
    ∧ f Vars.β = g Vars.β
    ∧ f Vars.γ = g Vars.γ
    ∧ f Vars.δ = g Vars.δ := by
  rw [DFunLike.ext_iff]
  constructor
  · intro h
    simp_rw [h]
    simp only [and_self]
  · intro h x
    cases x <;> tauto


inductive Proof_G1_Idx : Type where
  | A : Proof_G1_Idx
  | C : Proof_G1_Idx

-- instance : Fintype Proof_G1_Idx :=
--   ⟨⟨[Proof_G1_Idx.A, Proof_G1_Idx.C], by simp⟩, fun x => by cases x <;> simp⟩

inductive Proof_G2_Idx : Type where
  | B : Proof_G2_Idx

instance : Fintype Proof_G2_Idx :=
  ⟨⟨[Proof_G2_Idx.B], by simp⟩, fun x => by cases x; simp⟩

inductive PairingsIdx : Type where
  | ab : PairingsIdx
  | αβ : PairingsIdx
  | stmtγ : PairingsIdx
  | cδ : PairingsIdx

-- instance : Fintype PairingsIdx :=
--   ⟨⟨[PairingsIdx.ab, PairingsIdx.αβ, PairingsIdx.stmtγ, PairingsIdx.cδ], by simp⟩,
--     fun x => by cases x <;> simp⟩

inductive SRS_Elements_G1_Idx {n_stmt n_wit n_var : ℕ} : Type where
  | α : SRS_Elements_G1_Idx
  | β : SRS_Elements_G1_Idx
  | δ : SRS_Elements_G1_Idx
  | x_pow : Fin n_var → SRS_Elements_G1_Idx
  | x_pow_times_t : Fin (n_var - 1) → SRS_Elements_G1_Idx
  | y : Fin n_stmt → SRS_Elements_G1_Idx
  | q : Fin n_wit → SRS_Elements_G1_Idx

inductive SRS_Elements_G2_Idx {n_stmt n_wit n_var : ℕ} : Type where
  | β : SRS_Elements_G2_Idx
  | γ : SRS_Elements_G2_Idx
  | δ : SRS_Elements_G2_Idx
  | x_pow : Fin n_var → SRS_Elements_G2_Idx

-- TODO Note: May well be best to completely forget about generalizing "straightforward" to the very end.
-- TODO Note: Refactor files - model and a subdirectory for the six files from

/--
A description of the Groth 16 SNARK, as described in
"Another Look at Extraction and Randomization of Groth’s zk-SNARK" by Baghery et al.
In this paper, the authors describe a version of the Groth 16 SNARK which is more amenable to
extraction and randomization, and which is "Type III" - it assumes that the two base groups of the
elliptic curve pairing are distinct.
This is represented as a function which takes in various paramters of a QAP (number of inputs,
outputs, the polynomials etc.) and returns the instantiation of Groth '16 on this instance.

Some comments on the implementation:

n from the paper = n_var
l from the paper = n_stmt
m - l from the paper = n_wit

-/
noncomputable def Groth16TypeIII
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F]
    /- The naturals representing:
      n_stmt - the statement size,
      n_wit - the witness size -/
    {n_stmt n_wit n_var : ℕ}
    /- u_stmt and u_wit are Fin-indexed collections of polynomials from the square span program -/
    {u_stmt : Fin n_stmt → (Polynomial F) }
    {u_wit : Fin n_wit → (Polynomial F) }
    {v_stmt : Fin n_stmt → (Polynomial F) }
    {v_wit : Fin n_wit → (Polynomial F) }
    {w_stmt : Fin n_stmt → (Polynomial F) }
    {w_wit : Fin n_wit → (Polynomial F) }
    /- The polynomial t -/
    {t : Polynomial F} :
    AGMProofSystemInstantiation F :=
  {
    Stmt := Fin n_stmt -> F
    Sample := Option Vars
    SRSElements_G1 := @SRS_Elements_G1_Idx n_stmt n_wit n_var
    ListSRSElements_G1 :=
      [SRS_Elements_G1_Idx.α]
      ++ [SRS_Elements_G1_Idx.β]
      ++ [SRS_Elements_G1_Idx.δ]
      ++ ((List.finRange n_var).map fun i => SRS_Elements_G1_Idx.x_pow i)
      ++ ((List.finRange (n_var - 1)).map fun i => SRS_Elements_G1_Idx.x_pow_times_t i)
      ++ ((List.finRange n_stmt).map fun i => SRS_Elements_G1_Idx.y i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_G1_Idx.q i)
    SRSElements_G2 := @SRS_Elements_G2_Idx n_stmt n_wit n_var
    ListSRSElements_G2 :=
      [SRS_Elements_G2_Idx.β]
      ++ [SRS_Elements_G2_Idx.γ]
      ++ [SRS_Elements_G2_Idx.δ]
      ++ ((List.finRange n_var).map fun i => SRS_Elements_G2_Idx.x_pow i)
    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_G1_Idx.α => X Vars_γ * X Vars_δ * X Vars_α
      | SRS_Elements_G1_Idx.β => X Vars_γ * X Vars_δ * X Vars_β
      | SRS_Elements_G1_Idx.δ => X Vars_γ * X Vars_δ * X Vars_δ
      | SRS_Elements_G1_Idx.x_pow i => X Vars_γ * X Vars_δ * X Vars_x ^ (i : ℕ)
      | SRS_Elements_G1_Idx.x_pow_times_t i => X Vars_γ
                                                  * X Vars_x ^ (i : ℕ)
                                                  * to_MvPolynomial_Option Vars t
      | SRS_Elements_G1_Idx.y i => ((X Vars_β * X Vars_δ) * ( (to_MvPolynomial_Option Vars (u_stmt i))))
                                      +
                                      (X Vars_α * X Vars_δ) * (to_MvPolynomial_Option Vars (v_stmt i))
                                      +
                                      X Vars_δ * (to_MvPolynomial_Option Vars (w_stmt i))
      | SRS_Elements_G1_Idx.q i => (X Vars_β * X Vars_γ) * ( to_MvPolynomial_Option Vars (u_wit i))
                                      +
                                      (X Vars_α * X Vars_γ) * (to_MvPolynomial_Option Vars (v_wit i))
                                      +
                                      X Vars_γ * to_MvPolynomial_Option Vars (w_wit i)
      -- Note that the polynomials here have been multiplied through by γδ
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_G2_Idx.β => X Vars_γ * X Vars_δ * X Vars_β
      | SRS_Elements_G2_Idx.γ => X Vars_γ * X Vars_δ * X Vars_γ
      | SRS_Elements_G2_Idx.δ => X Vars_γ * X Vars_δ * X Vars_δ
      | SRS_Elements_G2_Idx.x_pow i => X Vars_γ * X Vars_δ * X Vars_x ^ (i : ℕ)
    Proof_G1 := Proof_G1_Idx
    ListProof_G1 := [Proof_G1_Idx.A, Proof_G1_Idx.C]
    Proof_G2 := Proof_G2_Idx
    ListProof_G2 := [Proof_G2_Idx.B]
    EqualityChecks := Unit
    Pairings := fun _ => PairingsIdx
    ListPairings := fun _ => [PairingsIdx.ab, PairingsIdx.αβ, PairingsIdx.stmtγ, PairingsIdx.cδ]
    verificationPairingSRS_G1 := fun stmt _ i SRS_idx => match i with
      | PairingsIdx.ab => match SRS_idx with
        | SRS_Elements_G1_Idx.α => 0
        | SRS_Elements_G1_Idx.β => 0
        | SRS_Elements_G1_Idx.δ => 0
        | SRS_Elements_G1_Idx.x_pow _ => 0
        | SRS_Elements_G1_Idx.x_pow_times_t _ => 0
        | SRS_Elements_G1_Idx.y _ => 0
        | SRS_Elements_G1_Idx.q _ => 0
      | PairingsIdx.αβ => match SRS_idx with
        | SRS_Elements_G1_Idx.α => 1
        | SRS_Elements_G1_Idx.β => 0
        | SRS_Elements_G1_Idx.δ => 0
        | SRS_Elements_G1_Idx.x_pow _ => 0
        | SRS_Elements_G1_Idx.x_pow_times_t _ => 0
        | SRS_Elements_G1_Idx.y _ => 0
        | SRS_Elements_G1_Idx.q _ => 0
      | PairingsIdx.stmtγ => match SRS_idx with
        | SRS_Elements_G1_Idx.α => 0
        | SRS_Elements_G1_Idx.β => 0
        | SRS_Elements_G1_Idx.δ => 0
        | SRS_Elements_G1_Idx.x_pow _ => 0
        | SRS_Elements_G1_Idx.x_pow_times_t _ => 0
        | SRS_Elements_G1_Idx.y i => stmt i
        | SRS_Elements_G1_Idx.q _ => 0
      | PairingsIdx.cδ => match SRS_idx with
        | SRS_Elements_G1_Idx.α => 0
        | SRS_Elements_G1_Idx.β => 0
        | SRS_Elements_G1_Idx.δ => 0
        | SRS_Elements_G1_Idx.x_pow _ => 0
        | SRS_Elements_G1_Idx.x_pow_times_t _ => 0
        | SRS_Elements_G1_Idx.y _ => 0
        | SRS_Elements_G1_Idx.q i => 0
    verificationPairingSRS_G2 := fun stmt _ i SRS_idx => match i with
      | PairingsIdx.ab => match SRS_idx with
        | SRS_Elements_G2_Idx.β => 0
        | SRS_Elements_G2_Idx.γ => 0
        | SRS_Elements_G2_Idx.δ => 0
        | SRS_Elements_G2_Idx.x_pow _ => 0
      | PairingsIdx.αβ => match SRS_idx with
        | SRS_Elements_G2_Idx.β => 1
        | SRS_Elements_G2_Idx.γ => 0
        | SRS_Elements_G2_Idx.δ => 0
        | SRS_Elements_G2_Idx.x_pow _ => 0
      | PairingsIdx.stmtγ => match SRS_idx with
        | SRS_Elements_G2_Idx.β => 0
        | SRS_Elements_G2_Idx.γ => 1
        | SRS_Elements_G2_Idx.δ => 0
        | SRS_Elements_G2_Idx.x_pow _ => 0
      | PairingsIdx.cδ => match SRS_idx with
        | SRS_Elements_G2_Idx.β => 0
        | SRS_Elements_G2_Idx.γ => 0
        | SRS_Elements_G2_Idx.δ => 1
        | SRS_Elements_G2_Idx.x_pow _ => 0
    verificationPairingProof_G1 := fun stmt _ i pf => match i with
      | PairingsIdx.ab => match pf with
        | Proof_G1_Idx.A => 1
        | Proof_G1_Idx.C => 0
      | PairingsIdx.αβ => match pf with
        | Proof_G1_Idx.A => 0
        | Proof_G1_Idx.C => 0
      | PairingsIdx.stmtγ => match pf with
        | Proof_G1_Idx.A => 0
        | Proof_G1_Idx.C => 0
      | PairingsIdx.cδ => match pf with
        | Proof_G1_Idx.A => 0
        | Proof_G1_Idx.C => 1
    verificationPairingProof_G2 := fun stmt _ i pf => match i with
      | PairingsIdx.ab => match pf with
        | Proof_G2_Idx.B => -1
      | PairingsIdx.αβ => match pf with
        | Proof_G2_Idx.B => 0
      | PairingsIdx.stmtγ => match pf with
        | Proof_G2_Idx.B => 0
      | PairingsIdx.cδ => match pf with
        | Proof_G2_Idx.B => 0
  }

section soundness

lemma Polynomial.mul_self_modByMonic {F : Type} [Field F] (t p : Polynomial F) (mt : t.Monic) : (t * p) %ₘ t = 0 := by
  rw [Polynomial.dvd_iff_modByMonic_eq_zero]
  apply dvd_mul_right
  exact mt

-- Remove heartbeat limit for upcoming long-running proof
set_option maxHeartbeats 0 -- 0 means no limit

lemma is_sound_quotient_version
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F) }
    {u_wit : Fin n_wit → (Polynomial F) }
    {v_stmt : Fin n_stmt → (Polynomial F) }
    {v_wit : Fin n_wit → (Polynomial F) }
    {w_stmt : Fin n_stmt → (Polynomial F) }
    {w_wit : Fin n_wit → (Polynomial F) }
    {t : Polynomial F} :
    (soundness
      F
      (Groth16TypeIII
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
        (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (t := t))
      (Fin n_wit -> F)
      (fun (stmt : Fin n_stmt → F) (wit : Fin n_wit -> F) =>
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

  have eqn := eqns ()
  clear eqns null

  -- done

  -- -- Simplify the equation
  -- suffices
  --     ((List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
  --     + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * u_wit i) (List.finRange n_wit))))
  --     *
  --     ((List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
  --     + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * v_wit i) (List.finRange n_wit))))
  --     =
  --     ((List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
  --     + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.q i)) * w_wit i) (List.finRange n_wit))))
  --     +
  --     List.sum (List.map (fun x : Fin (n_var - 1) => Polynomial.C (prover.fst Proof_G1_Idx.C (SRS_Elements_G1_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * t)) (List.finRange (n_var - 1))) by

  --   rw [<-sub_eq_iff_eq_add'] at this
  --   have h := congr_arg (fun x => x %ₘ t) this
  --   simp only at h
  --   simp
  --   rw [h]
  --   clear this h

  --   simp only [mul_comm _ (t), <-mul_assoc]
  --   simp only [mul_assoc, List.sum_map_mul_right, List.sum_map_mul_left]

  --   apply Polynomial.mul_self_modByMonic
  --   apply Polynomial.monic_prod_of_monic
  --   intro i hi
  --   exact Polynomial.monic_X_sub_C (r i)
  --   done



  -- Step 1: Obtain the coefficient equations of the mv_polynomials
  simp_rw [Groth16TypeIII] at eqn
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

  simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add, add_mul] at eqn

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


  -- Step 2: Recursively simplify and case-analyze the equations
  -- dsimp only
  replace h0012 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h0012
  replace h0021 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h0021
  replace h0022 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h0022
  replace h0112 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h0112
  replace h0121 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h0121
  replace h0122 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h0122
  replace h0212 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h0212
  replace h0221 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h0221
  replace h0222 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h0222
  replace h1022 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h1022
  replace h1112 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h1112
  replace h1121 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h1121
  replace h1122 := congr_arg ((Ideal.Quotient.mk (Ideal.span {t}))) h1122

  rw [Polynomial.modByMonic_eq_zero_iff_quotient_eq_zero]

  simp? [map_add, map_neg, map_mul, map_zero, RingHom.list_map_sum (Ideal.Quotient.mk (Ideal.span {t}))] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122 ⊢

  -- Set statements so that the equations are easier to read
  -- Most are optional, but there are a few that are necessary due to a bug in polyrith that causes it not to properly transcribe casts in its output
  -- /-
  set sum_u_stmt := (List.sum (List.map (fun i => (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (stmt i)) *  (Ideal.Quotient.mk (Ideal.span {t})) (u_stmt i)) (List.finRange n_stmt)))
  set sum_v_stmt := (List.sum (List.map (fun i => (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (stmt i)) * (Ideal.Quotient.mk (Ideal.span {t})) (v_stmt i)) (List.finRange n_stmt)))
  set sum_w_stmt := (List.sum (List.map (fun i => (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (stmt i)) * (Ideal.Quotient.mk (Ideal.span {t})) (w_stmt i)) (List.finRange n_stmt)))

  set A_1 := (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.α))
  set A_2 := (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.β))
  set A_3 := (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.A SRS_Elements_G1_Idx.δ))
  set sum_A_x := List.sum
        (List.map
          (fun x =>
            (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.x_pow x))) * (Ideal.Quotient.mk (Ideal.span {t})) Polynomial.X ^ (x : ℕ))
          (List.finRange n_var))

  set sum_A_u_stmt := List.sum
        (List.map
          (fun x =>
            (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x))) *
              (Ideal.Quotient.mk (Ideal.span {t})) (u_stmt x))
          (List.finRange n_stmt))
  set sum_A_v_stmt := List.sum
        (List.map
          (fun x =>
            (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x))) *
              (Ideal.Quotient.mk (Ideal.span {t})) (v_stmt x))
          (List.finRange n_stmt))
  set sum_A_w_stmt := List.sum
        (List.map
          (fun x =>
            (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.y x))) *
              (Ideal.Quotient.mk (Ideal.span {t})) (w_stmt x))
          (List.finRange n_stmt))
  set sum_A_u_wit := List.sum
        (List.map
          (fun x =>
            (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x))) *
              (Ideal.Quotient.mk (Ideal.span {t})) (u_wit x))
          (List.finRange n_wit))
  set sum_A_v_wit := List.sum
        (List.map
          (fun x =>
            (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x))) *
              (Ideal.Quotient.mk (Ideal.span {t})) (v_wit x))
          (List.finRange n_wit))
  set sum_A_w_wit := List.sum
        (List.map
          (fun x =>
            (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.q x))) *
              (Ideal.Quotient.mk (Ideal.span {t})) (w_wit x))
          (List.finRange n_wit))
  set sum_A_x_t := (List.sum
                  (List.map
                    (fun x =>
                      (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.A (SRS_Elements_G1_Idx.x_pow_times_t x))) *
                        ((Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.X ^ (x : ℕ)) * (Ideal.Quotient.mk (Ideal.span {t})) t))
                    (List.finRange (n_var - 1))))
  set B_1 := (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.β)))
  set B_2 := (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.γ)))
  set B_3 := (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.δ)))

  set sum_B_x := List.sum
                    (List.map
                      (fun x =>
                        (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.2 Proof_G2_Idx.B (SRS_Elements_G2_Idx.x_pow x))) * (Ideal.Quotient.mk (Ideal.span {t})) Polynomial.X ^ (x : ℕ))
                      (List.finRange n_var))

  set C_1 := Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.α)
  set C_2 := Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.β)
  set C_3 := Polynomial.C (prover.1 Proof_G1_Idx.C SRS_Elements_G1_Idx.δ)
  set sum_C_u_wit := List.sum
        (List.map
          (fun x =>
            (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x))) *
              u_wit x)
          (List.finRange n_wit))
  set sum_C_v_wit := List.sum
        (List.map
          (fun x =>
            (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x))) *
              v_wit x)
          (List.finRange n_wit))
  set sum_C_w_wit := List.sum
        (List.map
          (fun x =>
            (Ideal.Quotient.mk (Ideal.span {t})) (Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.q x))) *
              (Ideal.Quotient.mk (Ideal.span {t})) (w_wit x))
          (List.finRange n_wit))
  set sum_C_x_t := List.sum
        (List.map
          (fun x : Fin (n_var - 1) =>
            Polynomial.C (prover.1 Proof_G1_Idx.C (SRS_Elements_G1_Idx.x_pow_times_t x)) * ((Ideal.Quotient.mk (Ideal.span {t})) Polynomial.X ^ (x : ℕ) * t))
          (List.finRange (n_var - 1)))

  -- clear_value sum_A_x sum_A_x_t sum_B_x sum_C_x_t
  clear_value sum_u_stmt sum_v_stmt sum_w_stmt A_1 A_2 A_3 sum_A_x sum_A_u_stmt sum_A_v_stmt sum_A_w_stmt sum_A_u_wit sum_A_v_wit sum_A_w_wit sum_A_x_t B_1 B_2 B_3 sum_B_x C_1 C_2 C_3 sum_C_u_wit sum_C_v_wit sum_C_w_wit sum_C_x_t
  -- -/

  -- done

  haveI : NoZeroDivisors (Polynomial F ⧸ Ideal.span {t}) := by sorry

  integral_domain_tactic -- fails here due to not deriving NoZeroDivisors



end soundness

end Groth16TypeIII
