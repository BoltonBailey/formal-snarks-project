import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Data.Polynomial.Div
import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Data.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode


open scoped BigOperators Classical

section Groth16TypeIII

open MvPolynomial Option

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
  rw [FunLike.ext_iff]
  constructor
  · intro h
    simp_rw [h]
    simp only [and_self]
  · intro h x
    cases x <;> tauto


inductive Proof_Left_Idx : Type where
  | A : Proof_Left_Idx
  | C : Proof_Left_Idx

-- instance : Fintype Proof_Left_Idx :=
--   ⟨⟨[Proof_Left_Idx.A, Proof_Left_Idx.C], by simp⟩, fun x => by cases x <;> simp⟩

inductive Proof_Right_Idx : Type where
  | B : Proof_Right_Idx

instance : Fintype Proof_Right_Idx :=
  ⟨⟨[Proof_Right_Idx.B], by simp⟩, fun x => by cases x; simp⟩

inductive PairingsIdx : Type where
  | ab : PairingsIdx
  | αβ : PairingsIdx
  | stmtγ : PairingsIdx
  | cδ : PairingsIdx

-- instance : Fintype PairingsIdx :=
--   ⟨⟨[PairingsIdx.ab, PairingsIdx.αβ, PairingsIdx.stmtγ, PairingsIdx.cδ], by simp⟩,
--     fun x => by cases x <;> simp⟩

inductive CRS_Elements_Left_Idx {n_stmt n_wit n_var : ℕ} : Type where
  | α : CRS_Elements_Left_Idx
  | β : CRS_Elements_Left_Idx
  | δ : CRS_Elements_Left_Idx
  | x_pow : Fin n_var → CRS_Elements_Left_Idx
  | x_pow_times_t : Fin (n_var - 1) → CRS_Elements_Left_Idx
  | y : Fin n_stmt → CRS_Elements_Left_Idx
  | q : Fin n_wit → CRS_Elements_Left_Idx

inductive CRS_Elements_Right_Idx {n_stmt n_wit n_var : ℕ} : Type where
  | β : CRS_Elements_Right_Idx
  | γ : CRS_Elements_Right_Idx
  | δ : CRS_Elements_Right_Idx
  | x_pow : Fin n_var → CRS_Elements_Right_Idx

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
    /- The roots of the polynomial t -/
    {r : Fin n_wit → F} :
    AGMProofSystemInstantiation F :=
  let t : Polynomial F :=
    ∏ i in (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i));
  {
    Stmt := Fin n_stmt -> F
    Sample := Option Vars
    CrsElements_Left := @CRS_Elements_Left_Idx n_stmt n_wit n_var
    ListCrsElements_Left :=
      [CRS_Elements_Left_Idx.α]
      ++ [CRS_Elements_Left_Idx.β]
      ++ [CRS_Elements_Left_Idx.δ]
      ++ ((List.finRange n_var).map fun i => CRS_Elements_Left_Idx.x_pow i)
      ++ ((List.finRange (n_var - 1)).map fun i => CRS_Elements_Left_Idx.x_pow_times_t i)
      ++ ((List.finRange n_stmt).map fun i => CRS_Elements_Left_Idx.y i)
      ++ ((List.finRange n_wit).map fun i => CRS_Elements_Left_Idx.q i)
    CrsElements_Right := @CRS_Elements_Right_Idx n_stmt n_wit n_var
    ListCrsElements_Right :=
      [CRS_Elements_Right_Idx.β]
      ++ [CRS_Elements_Right_Idx.γ]
      ++ [CRS_Elements_Right_Idx.δ]
      ++ ((List.finRange n_var).map fun i => CRS_Elements_Right_Idx.x_pow i)
    crsElementValue_Left := fun crs_idx => match crs_idx with
      | CRS_Elements_Left_Idx.α => X Vars_γ * X Vars_δ * X Vars_α
      | CRS_Elements_Left_Idx.β => X Vars_γ * X Vars_δ * X Vars_β
      | CRS_Elements_Left_Idx.δ => X Vars_γ * X Vars_δ * X Vars_δ
      | CRS_Elements_Left_Idx.x_pow i => X Vars_γ * X Vars_δ * X Vars_x ^ (i : ℕ)
      | CRS_Elements_Left_Idx.x_pow_times_t i => X Vars_γ
                                                  * X Vars_x ^ (i : ℕ)
                                                  * to_MvPolynomial_Option Vars t
      | CRS_Elements_Left_Idx.y i => ((X Vars_β * X Vars_δ) * ( (to_MvPolynomial_Option Vars (u_stmt i))))
                                      +
                                      (X Vars_α * X Vars_δ) * (to_MvPolynomial_Option Vars (v_stmt i))
                                      +
                                      X Vars_δ * (to_MvPolynomial_Option Vars (w_stmt i))
      | CRS_Elements_Left_Idx.q i => (X Vars_β * X Vars_γ) * ( to_MvPolynomial_Option Vars (u_wit i))
                                      +
                                      (X Vars_α * X Vars_γ) * (to_MvPolynomial_Option Vars (v_wit i))
                                      +
                                      X Vars_γ * to_MvPolynomial_Option Vars (w_wit i)
      -- Note that the polynomials here have been multiplied through by γδ
    crsElementValue_Right := fun crs_idx => match crs_idx with
      | CRS_Elements_Right_Idx.β => X Vars_γ * X Vars_δ * X Vars_β
      | CRS_Elements_Right_Idx.γ => X Vars_γ * X Vars_δ * X Vars_γ
      | CRS_Elements_Right_Idx.δ => X Vars_γ * X Vars_δ * X Vars_δ
      | CRS_Elements_Right_Idx.x_pow i => X Vars_γ * X Vars_δ * X Vars_x ^ (i : ℕ)
    Proof_Left := Proof_Left_Idx
    ListProof_Left := [Proof_Left_Idx.A, Proof_Left_Idx.C]
    Proof_Right := Proof_Right_Idx
    ListProof_Right := [Proof_Right_Idx.B]
    EqualityChecks := Unit
    Pairings := fun _ => PairingsIdx
    ListPairings := fun _ => [PairingsIdx.ab, PairingsIdx.αβ, PairingsIdx.stmtγ, PairingsIdx.cδ]
    verificationPairingCRSLeft := fun stmt _ i crs_idx => match i with
      | PairingsIdx.ab => match crs_idx with
        | CRS_Elements_Left_Idx.α => 0
        | CRS_Elements_Left_Idx.β => 0
        | CRS_Elements_Left_Idx.δ => 0
        | CRS_Elements_Left_Idx.x_pow _ => 0
        | CRS_Elements_Left_Idx.x_pow_times_t _ => 0
        | CRS_Elements_Left_Idx.y _ => 0
        | CRS_Elements_Left_Idx.q _ => 0
      | PairingsIdx.αβ => match crs_idx with
        | CRS_Elements_Left_Idx.α => 1
        | CRS_Elements_Left_Idx.β => 0
        | CRS_Elements_Left_Idx.δ => 0
        | CRS_Elements_Left_Idx.x_pow _ => 0
        | CRS_Elements_Left_Idx.x_pow_times_t _ => 0
        | CRS_Elements_Left_Idx.y _ => 0
        | CRS_Elements_Left_Idx.q _ => 0
      | PairingsIdx.stmtγ => match crs_idx with
        | CRS_Elements_Left_Idx.α => 0
        | CRS_Elements_Left_Idx.β => 0
        | CRS_Elements_Left_Idx.δ => 0
        | CRS_Elements_Left_Idx.x_pow _ => 0
        | CRS_Elements_Left_Idx.x_pow_times_t _ => 0
        | CRS_Elements_Left_Idx.y i => stmt i
        | CRS_Elements_Left_Idx.q _ => 0
      | PairingsIdx.cδ => match crs_idx with
        | CRS_Elements_Left_Idx.α => 0
        | CRS_Elements_Left_Idx.β => 0
        | CRS_Elements_Left_Idx.δ => 0
        | CRS_Elements_Left_Idx.x_pow _ => 0
        | CRS_Elements_Left_Idx.x_pow_times_t _ => 0
        | CRS_Elements_Left_Idx.y _ => 0
        | CRS_Elements_Left_Idx.q i => 0
    verificationPairingCRSRight := fun stmt _ i crs_idx => match i with
      | PairingsIdx.ab => match crs_idx with
        | CRS_Elements_Right_Idx.β => 0
        | CRS_Elements_Right_Idx.γ => 0
        | CRS_Elements_Right_Idx.δ => 0
        | CRS_Elements_Right_Idx.x_pow _ => 0
      | PairingsIdx.αβ => match crs_idx with
        | CRS_Elements_Right_Idx.β => 1
        | CRS_Elements_Right_Idx.γ => 0
        | CRS_Elements_Right_Idx.δ => 0
        | CRS_Elements_Right_Idx.x_pow _ => 0
      | PairingsIdx.stmtγ => match crs_idx with
        | CRS_Elements_Right_Idx.β => 0
        | CRS_Elements_Right_Idx.γ => 1
        | CRS_Elements_Right_Idx.δ => 0
        | CRS_Elements_Right_Idx.x_pow _ => 0
      | PairingsIdx.cδ => match crs_idx with
        | CRS_Elements_Right_Idx.β => 0
        | CRS_Elements_Right_Idx.γ => 0
        | CRS_Elements_Right_Idx.δ => 1
        | CRS_Elements_Right_Idx.x_pow _ => 0
    verificationPairingProofLeft := fun stmt _ i pf => match i with
      | PairingsIdx.ab => match pf with
        | Proof_Left_Idx.A => 1
        | Proof_Left_Idx.C => 0
      | PairingsIdx.αβ => match pf with
        | Proof_Left_Idx.A => 0
        | Proof_Left_Idx.C => 0
      | PairingsIdx.stmtγ => match pf with
        | Proof_Left_Idx.A => 0
        | Proof_Left_Idx.C => 0
      | PairingsIdx.cδ => match pf with
        | Proof_Left_Idx.A => 0
        | Proof_Left_Idx.C => 1
    verificationPairingProofRight := fun stmt _ i pf => match i with
      | PairingsIdx.ab => match pf with
        | Proof_Right_Idx.B => -1
      | PairingsIdx.αβ => match pf with
        | Proof_Right_Idx.B => 0
      | PairingsIdx.stmtγ => match pf with
        | Proof_Right_Idx.B => 0
      | PairingsIdx.cδ => match pf with
        | Proof_Right_Idx.B => 0
  }

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
      (fun prover i => prover.fst Proof_Left_Idx.C (CRS_Elements_Left_Idx.q i))
    ) := by

  unfold AGMProofSystemInstantiation.soundness AGMProofSystemInstantiation.verify AGMProofSystemInstantiation.proof_element_left_as_poly AGMProofSystemInstantiation.proof_element_right_as_poly
  -- TODO namespcace AGMProofSystemInstantiation eliminate
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, null⟩
  intro t
  have eqn := eqns ()
  clear eqns null

  -- let C_m := fun i => prover.fst Proof_Left_Idx.C (CRS_Elements_Left_Idx.q i)
  -- let C_h := fun x => prover.fst Proof_Left_Idx.C (CRS_Elements_Left_Idx.x_pow_times_t x)

  suffices
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Left_Idx.C (CRS_Elements_Left_Idx.q i)) * u_wit i) (List.finRange n_wit))))
      *
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Left_Idx.C (CRS_Elements_Left_Idx.q i)) * v_wit i) (List.finRange n_wit))))
      =
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Left_Idx.C (CRS_Elements_Left_Idx.q i)) * w_wit i) (List.finRange n_wit))))
      +
      List.sum (List.map (fun x : Fin (n_var - 1) => Polynomial.C (prover.fst Proof_Left_Idx.C (CRS_Elements_Left_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * t)) (List.finRange (n_var - 1))) by

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

  start_proof

## -- Step 1: Obtain the coefficient equations of the mv_polynomials
## simp_rw [Groth16TypeIII] at eqn
  -- All I want is a tactic that will apply the following simplifications to eqn in sequence.
  -- TODO can I write a tactic taking a nested list of simp lemmas?
  -- Can I combine all of these?
## simp only [monomial_zero', List.singleton_append, List.cons_append, List.append_assoc,
    List.map_cons, Sum.elim_inl, Sum.elim_inr, List.map_append, List.map_map, List.sum_cons,
    List.sum_append, List.map_nil, List.sum_nil, add_zero, Sum.elim_lam_const_lam_const, map_one,
    one_mul, map_zero, zero_mul, map_neg, neg_mul, neg_add_rev, zero_add, mul_zero,
    -- Note: everything above is @simp tagged
    Function.comp, List.sum_map_zero] at eqn

## simp only [mul_add, add_mul, List.sum_map_add] at eqn

  -- Move all the X (some _) terms to the left, and out of sums
## simp only [
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
## trace "Converting to MvPolynomial over Polynomials"
  -- replace eqn := congr_arg (MvPolynomial.optionEquivRight F Vars) eqn
## simp only [←(EquivLike.apply_eq_iff_eq (optionEquivRight _ _))] at eqn
## simp only [AlgEquiv.map_add, AlgEquiv.map_zero, AlgEquiv.map_mul, AlgEquiv.map_one,
    AlgEquiv.map_neg, AlgEquiv.list_map_sum, AlgEquiv.map_pow] at eqn
## simp only [optionEquivRight_C, optionEquivRight_X_none, optionEquivRight_X_some, optionEquivRight_to_MvPolynomial_Option] at eqn

  -- Move Cs back out so we can recognize the monomials
## simp only [←C_mul, ←C_pow, ←C_add,
    sum_map_C] at eqn

## simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add, add_mul] at eqn

## trace "Applying individual coefficients"

## have h0012 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
## have h0021 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
## have h0022 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
## have h0112 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
## have h0121 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
## have h0122 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
## have h0212 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
## have h0221 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
## have h0222 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
## have h1022 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
## have h1112 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
## have h1121 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
## have h1122 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn

## clear eqn

## trace "Distribute coefficient-taking over terms"
## simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122

## trace "Simplifying coefficient expressions"
## simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122

## trace "Determine which coefficients are nonzero"
## simp (config := {decide := true}) only [ite_false, ite_true] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122
## trace "Remove zeros"
## simp only [neg_zero, add_zero, zero_add] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122

## save

  -- Step 2: Recursively simplify and case-analyze the equations
  -- dsimp only


  -- Set statements so that the equations are easier to read
  -- Most are optional, but the
  -- /-
  -- set sum_u_stmt := (List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
  -- set sum_v_stmt := (List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
  -- set sum_w_stmt := (List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))

  -- set A_1 := Polynomial.C (prover.1 Proof_Left_Idx.A CRS_Elements_Left_Idx.α)
  -- set A_2 := Polynomial.C (prover.1 Proof_Left_Idx.A CRS_Elements_Left_Idx.β)
  -- set A_3 := Polynomial.C (prover.1 Proof_Left_Idx.A CRS_Elements_Left_Idx.δ)
## set sum_A_x := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_Left_Idx.A (CRS_Elements_Left_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ))
          (List.finRange n_var))

  -- set sum_A_u_stmt := List.sum
  --       (List.map
  --         (fun x =>
  --           Polynomial.C (prover.1 Proof_Left_Idx.A (CRS_Elements_Left_Idx.y x)) *
  --             u_stmt x)
  --         (List.finRange n_stmt))
  -- set sum_A_v_stmt := List.sum
  --       (List.map
  --         (fun x =>
  --           Polynomial.C (prover.1 Proof_Left_Idx.A (CRS_Elements_Left_Idx.y x)) *
  --             v_stmt x)
  --         (List.finRange n_stmt))
  -- set sum_A_w_stmt := List.sum
  --       (List.map
  --         (fun x =>
  --           Polynomial.C (prover.1 Proof_Left_Idx.A (CRS_Elements_Left_Idx.y x)) *
  --             w_stmt x)
  --         (List.finRange n_stmt))
  -- set sum_A_u_wit := List.sum
  --       (List.map
  --         (fun x =>
  --           Polynomial.C (prover.1 Proof_Left_Idx.A (CRS_Elements_Left_Idx.q x)) *
  --             u_wit x)
  --         (List.finRange n_wit))
  -- set sum_A_v_wit := List.sum
  --       (List.map
  --         (fun x =>
  --           Polynomial.C (prover.1 Proof_Left_Idx.A (CRS_Elements_Left_Idx.q x)) *
  --             v_wit x)
  --         (List.finRange n_wit))
  -- set sum_A_w_wit := List.sum
  --       (List.map
  --         (fun x =>
  --           Polynomial.C (prover.1 Proof_Left_Idx.A (CRS_Elements_Left_Idx.q x)) *
  --             w_wit x)
  --         (List.finRange n_wit))
## set sum_A_x_t := (List.sum
                  (List.map
                    (fun x =>
                      Polynomial.C (prover.1 Proof_Left_Idx.A (CRS_Elements_Left_Idx.x_pow_times_t x)) *
                        (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i))))
                    (List.finRange (n_var - 1))))
  -- set B_1 := Polynomial.C (prover.2 Proof_Right_Idx.B (CRS_Elements_Right_Idx.β))
  -- set B_2 := Polynomial.C (prover.2 Proof_Right_Idx.B (CRS_Elements_Right_Idx.γ))
  -- set B_3 := Polynomial.C (prover.2 Proof_Right_Idx.B (CRS_Elements_Right_Idx.δ))

## set sum_B_x := List.sum
                    (List.map
                      (fun x =>
                        Polynomial.C (prover.2 Proof_Right_Idx.B (CRS_Elements_Right_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ))
                      (List.finRange n_var))

  -- set C_1 := Polynomial.C (prover.1 Proof_Left_Idx.C CRS_Elements_Left_Idx.α)
  -- set C_2 := Polynomial.C (prover.1 Proof_Left_Idx.C CRS_Elements_Left_Idx.β)
  -- set C_3 := Polynomial.C (prover.1 Proof_Left_Idx.C CRS_Elements_Left_Idx.δ)
  -- set sum_C_u_wit := List.sum
  --       (List.map
  --         (fun x =>
  --           Polynomial.C (prover.1 Proof_Left_Idx.C (CRS_Elements_Left_Idx.q x)) *
  --             u_wit x)
  --         (List.finRange n_wit))
  -- set sum_C_v_wit := List.sum
  --       (List.map
  --         (fun x =>
  --           Polynomial.C (prover.1 Proof_Left_Idx.C (CRS_Elements_Left_Idx.q x)) *
  --             v_wit x)
  --         (List.finRange n_wit))
  -- set sum_C_w_wit := List.sum
  --       (List.map
  --         (fun x =>
  --           Polynomial.C (prover.1 Proof_Left_Idx.C (CRS_Elements_Left_Idx.q x)) *
  --             w_wit x)
  --         (List.finRange n_wit))
## set sum_C_x_t := List.sum
        (List.map
          (fun x : Fin (n_var - 1) =>
            Polynomial.C (prover.1 Proof_Left_Idx.C (CRS_Elements_Left_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i))))
          (List.finRange (n_var - 1)))

## clear_value sum_A_x sum_A_x_t sum_B_x sum_C_x_t
  -- clear_value sum_u_stmt sum_v_stmt sum_w_stmt A_1 A_2 A_3 sum_A_x sum_A_u_stmt sum_A_v_stmt sum_A_w_stmt sum_A_u_wit sum_A_v_wit sum_A_w_wit sum_A_x_t B_1 B_2 B_3 sum_B_x C_1 C_2 C_3 sum_C_u_wit sum_C_v_wit sum_C_w_wit sum_C_x_t
  -- -/

## integral_domain_tactic

## save

## skip
## polyrith

## polyrith

  -- NOTE: If you try to run lake build on this file, polyrith fails, even though it works fine in the editor
  -- This perhaps has to do with polyrith making external calls to Sage Web APIs

end soundness


-- TODO I'm using lists rather than finsets now, so I think I can get rid of all the finset lemmas

end Groth16TypeIII
