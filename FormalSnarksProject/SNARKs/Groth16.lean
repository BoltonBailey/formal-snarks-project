import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Algebra.Polynomial.Div
-- import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Algebra.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode
-- import FormalSnarksProject.ToMathlib.MulModByMonic

/-!

# Groth16TypeI

This file contains the soundness proof for the Type I version of Groth16 presented in
["On the Size of Pairing-based Non-interactive Arguments"](https://eprint.iacr.org/2016/260.pdf)
by Jens Groth.


-/

open scoped BigOperators Classical

section Groth16TypeI

open MvPolynomial Option AGMProofSystemInstantiation

namespace Groth16TypeI

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


inductive Proof_Idx : Type where
  | A : Proof_Idx
  | B : Proof_Idx
  | C : Proof_Idx

inductive PairingsIdx : Type where
  | ab : PairingsIdx
  | αβ : PairingsIdx
  | stmtγ : PairingsIdx
  | cδ : PairingsIdx

inductive SRS_Elements_Idx {n_stmt n_wit n_var : ℕ} : Type where
  | α : SRS_Elements_Idx
  | β : SRS_Elements_Idx
  | δ : SRS_Elements_Idx
  | γ : SRS_Elements_Idx
  | x_pow : Fin n_var → SRS_Elements_Idx
  | x_pow_times_t : Fin (n_var - 1) → SRS_Elements_Idx
  | y : Fin n_stmt → SRS_Elements_Idx
  | q : Fin n_wit → SRS_Elements_Idx

noncomputable def Groth16TypeI
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
    SRSElements_G1 := @SRS_Elements_Idx n_stmt n_wit n_var
    ListSRSElements_G1 :=
      [SRS_Elements_Idx.α]
      ++ [SRS_Elements_Idx.β]
      ++ [SRS_Elements_Idx.δ]
      ++ ((List.finRange n_var).map fun i => SRS_Elements_Idx.x_pow i)
      ++ ((List.finRange (n_var - 1)).map fun i => SRS_Elements_Idx.x_pow_times_t i)
      ++ ((List.finRange n_stmt).map fun i => SRS_Elements_Idx.y i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.q i)
    SRSElements_G2 := @SRS_Elements_Idx n_stmt n_wit n_var
    ListSRSElements_G2 :=
      [SRS_Elements_Idx.β]
      ++ [SRS_Elements_Idx.γ]
      ++ [SRS_Elements_Idx.δ]
      ++ ((List.finRange n_var).map fun i => SRS_Elements_Idx.x_pow i)
    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.α => X Vars_γ * X Vars_δ * X Vars_α
      | SRS_Elements_Idx.β => X Vars_γ * X Vars_δ * X Vars_β
      | SRS_Elements_Idx.γ => X Vars_γ * X Vars_δ * X Vars_γ
      | SRS_Elements_Idx.δ => X Vars_γ * X Vars_δ * X Vars_δ
      | SRS_Elements_Idx.x_pow i => X Vars_γ * X Vars_δ * X Vars_x ^ (i : ℕ)
      | SRS_Elements_Idx.x_pow_times_t i => X Vars_γ
                                                  * X Vars_x ^ (i : ℕ)
                                                  * to_MvPolynomial_Option Vars t
      | SRS_Elements_Idx.y i => ((X Vars_β * X Vars_δ) * ( (to_MvPolynomial_Option Vars (u_stmt i))))
                                      +
                                      (X Vars_α * X Vars_δ) * (to_MvPolynomial_Option Vars (v_stmt i))
                                      +
                                      X Vars_δ * (to_MvPolynomial_Option Vars (w_stmt i))
      | SRS_Elements_Idx.q i => (X Vars_β * X Vars_γ) * ( to_MvPolynomial_Option Vars (u_wit i))
                                      +
                                      (X Vars_α * X Vars_γ) * (to_MvPolynomial_Option Vars (v_wit i))
                                      +
                                      X Vars_γ * to_MvPolynomial_Option Vars (w_wit i)
      -- Note that the polynomials here have been multiplied through by γδ
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.α => X Vars_γ * X Vars_δ * X Vars_α
      | SRS_Elements_Idx.β => X Vars_γ * X Vars_δ * X Vars_β
      | SRS_Elements_Idx.γ => X Vars_γ * X Vars_δ * X Vars_γ
      | SRS_Elements_Idx.δ => X Vars_γ * X Vars_δ * X Vars_δ
      | SRS_Elements_Idx.x_pow i => X Vars_γ * X Vars_δ * X Vars_x ^ (i : ℕ)
      | SRS_Elements_Idx.x_pow_times_t i => X Vars_γ
                                                  * X Vars_x ^ (i : ℕ)
                                                  * to_MvPolynomial_Option Vars t
      | SRS_Elements_Idx.y i => ((X Vars_β * X Vars_δ) * ( (to_MvPolynomial_Option Vars (u_stmt i))))
                                      +
                                      (X Vars_α * X Vars_δ) * (to_MvPolynomial_Option Vars (v_stmt i))
                                      +
                                      X Vars_δ * (to_MvPolynomial_Option Vars (w_stmt i))
      | SRS_Elements_Idx.q i => (X Vars_β * X Vars_γ) * ( to_MvPolynomial_Option Vars (u_wit i))
                                      +
                                      (X Vars_α * X Vars_γ) * (to_MvPolynomial_Option Vars (v_wit i))
                                      +
                                      X Vars_γ * to_MvPolynomial_Option Vars (w_wit i)
      -- Note that the polynomials here have been multiplied through by γδ
    Proof_G1 := Proof_Idx
    ListProof_G1 := [Proof_Idx.A, Proof_Idx.B, Proof_Idx.C]
    Proof_G2 := Proof_Idx
    ListProof_G2 := [Proof_Idx.A, Proof_Idx.B, Proof_Idx.C]
    EqualityChecks := Unit
    Pairings := fun _ => PairingsIdx
    ListPairings := fun _ => [PairingsIdx.ab, PairingsIdx.αβ, PairingsIdx.stmtγ, PairingsIdx.cδ]
    verificationPairingSRS_G1 := fun stmt _ i SRS_idx => match i with
      | PairingsIdx.ab => match SRS_idx with
        | SRS_Elements_Idx.α => 0
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | SRS_Elements_Idx.x_pow_times_t _ => 0
        | SRS_Elements_Idx.y _ => 0
        | SRS_Elements_Idx.q _ => 0
      | PairingsIdx.αβ => match SRS_idx with
        | SRS_Elements_Idx.α => 1
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | SRS_Elements_Idx.x_pow_times_t _ => 0
        | SRS_Elements_Idx.y _ => 0
        | SRS_Elements_Idx.q _ => 0
      | PairingsIdx.stmtγ => match SRS_idx with
        | SRS_Elements_Idx.α => 0
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | SRS_Elements_Idx.x_pow_times_t _ => 0
        | SRS_Elements_Idx.y i => stmt i
        | SRS_Elements_Idx.q _ => 0
      | PairingsIdx.cδ => match SRS_idx with
        | SRS_Elements_Idx.α => 0
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | SRS_Elements_Idx.x_pow_times_t _ => 0
        | SRS_Elements_Idx.y _ => 0
        | SRS_Elements_Idx.q i => 0
    verificationPairingSRS_G2 := fun stmt _ i SRS_idx => match i with
      | PairingsIdx.ab => match SRS_idx with
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | _ => 0
      | PairingsIdx.αβ => match SRS_idx with
        | SRS_Elements_Idx.β => 1
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | _ => 0
      | PairingsIdx.stmtγ => match SRS_idx with
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 1
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | _ => 0
      | PairingsIdx.cδ => match SRS_idx with
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 1
        | SRS_Elements_Idx.x_pow _ => 0
        | _ => 0
    verificationPairingProof_G1 := fun stmt _ i pf => match i with
      | PairingsIdx.ab => match pf with
        | Proof_Idx.A => 1
        | Proof_Idx.B => 0
        | Proof_Idx.C => 0
      | PairingsIdx.αβ => match pf with
        | Proof_Idx.A => 0
        | Proof_Idx.B => 0
        | Proof_Idx.C => 0
      | PairingsIdx.stmtγ => match pf with
        | Proof_Idx.A => 0
        | Proof_Idx.B => 0
        | Proof_Idx.C => 0
      | PairingsIdx.cδ => match pf with
        | Proof_Idx.A => 0
        | Proof_Idx.B => 0
        | Proof_Idx.C => 1
    verificationPairingProof_G2 := fun stmt _ i pf => match i with
      | PairingsIdx.ab => match pf with
        | Proof_Idx.A => 0
        | Proof_Idx.B => -1
        | Proof_Idx.C => 0
      | PairingsIdx.αβ => match pf with
        | Proof_Idx.A => 0
        | Proof_Idx.B => 0
        | Proof_Idx.C => 0
      | PairingsIdx.stmtγ => match pf with
        | Proof_Idx.A => 0
        | Proof_Idx.B => 0
        | Proof_Idx.C => 0
      | PairingsIdx.cδ => match pf with
        | Proof_Idx.A => 0
        | Proof_Idx.B => 0
        | Proof_Idx.C => 0
    Identified_Proof_Elems := [(Proof_Idx.A, Proof_Idx.A), (Proof_Idx.B, Proof_Idx.B), (Proof_Idx.C, Proof_Idx.C)]
  }

lemma identified_proof_elems_def
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F) }
    {u_wit : Fin n_wit → (Polynomial F) }
    {v_stmt : Fin n_stmt → (Polynomial F) }
    {v_wit : Fin n_wit → (Polynomial F) }
    {w_stmt : Fin n_stmt → (Polynomial F) }
    {w_wit : Fin n_wit → (Polynomial F) }
    {r : Fin n_wit → F} :
    (Groth16TypeI
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
        (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (r := r)).Identified_Proof_Elems = [(Proof_Idx.A, Proof_Idx.A), (Proof_Idx.B, Proof_Idx.B), (Proof_Idx.C, Proof_Idx.C)] := rfl

section soundness

-- Remove heartbeat limit for upcoming long-running proof
set_option maxHeartbeats 0 -- 0 means no limit

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
      (Groth16TypeI
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
      (fun prover i => prover.fst Proof_Idx.C (SRS_Elements_Idx.q i))
    ) := by
  -- Unfold the soundness definition fully
  unfold soundness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly
  -- Introduce the arguments to the soundness definition
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, typeI_identification⟩
  intro t
  have eqn := eqns ()
  clear eqns

  -- Unpack the typeI idenitifcation facts
  simp only [identified_proof_elems_def, Bool.not_eq_true, List.mem_cons, List.mem_singleton,
    forall_eq_or_imp, forall_eq] at typeI_identification
  simp only [List.find?_nil, List.not_mem_nil, IsEmpty.forall_iff, Prod.forall, implies_true,
    and_true] at typeI_identification
  rcases typeI_identification with ⟨eqnA, eqnB, eqnC⟩

  -- Simplify the equation
  suffices
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Idx.C (SRS_Elements_Idx.q i)) * u_wit i) (List.finRange n_wit))))
      *
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Idx.C (SRS_Elements_Idx.q i)) * v_wit i) (List.finRange n_wit))))
      =
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Idx.C (SRS_Elements_Idx.q i)) * w_wit i) (List.finRange n_wit))))
      +
      List.sum (List.map (fun x : Fin (n_var - 1) => Polynomial.C (prover.fst Proof_Idx.C (SRS_Elements_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * t)) (List.finRange (n_var - 1))) by

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
    done



  -- Step 1: Obtain the coefficient equations of the mv_polynomials
  simp_rw [Groth16TypeI] at eqn eqnA eqnB eqnC

  simp only [monomial_zero', List.singleton_append, List.cons_append, List.append_assoc,
    List.map_cons, Sum.elim_inl, Sum.elim_inr, List.map_append, List.map_map, List.sum_cons,
    List.sum_append, List.map_nil, List.sum_nil, add_zero, Sum.elim_lam_const_lam_const, map_one,
    one_mul, map_zero, zero_mul, map_neg, neg_mul, neg_add_rev, zero_add, mul_zero,
    -- Note: everything above is @simp tagged
    Function.comp, List.sum_map_zero] at eqn eqnA eqnB eqnC

  simp only [mul_add, add_mul, List.sum_map_add] at eqn eqnA eqnB eqnC

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
    List.sum_map_mul_right, List.sum_map_mul_left] at eqn eqnA eqnB eqnC

  -- Apply MvPolynomial.optionEquivRight *here*, so that we can treat polynomials in Vars_X as constants
  trace "Converting to MvPolynomial over Polynomials"
  simp only [←(EquivLike.apply_eq_iff_eq (optionEquivRight _ _))] at eqn eqnA eqnB eqnC
  simp only [AlgEquiv.map_add, AlgEquiv.map_zero, AlgEquiv.map_mul, AlgEquiv.map_one,
    AlgEquiv.map_neg, AlgEquiv.list_map_sum, AlgEquiv.map_pow] at eqn eqnA eqnB eqnC
  simp only [optionEquivRight_C, optionEquivRight_X_none, optionEquivRight_X_some, optionEquivRight_to_MvPolynomial_Option] at eqn eqnA eqnB eqnC

  -- Move Cs back out so we can recognize the monomials
  simp only [←C_mul, ←C_pow, ←C_add,
    sum_map_C] at eqn eqnA eqnB eqnC

  simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add, add_mul] at eqn eqnA eqnB eqnC

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

  have hA1011 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 1)) eqnA
  have hA0111 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 1)) eqnA
  have hA0012 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqnA
  have hA0011 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 1)) eqnA
  have hA0010 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 0)) eqnA
  have hA0101 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 0 + Finsupp.single Vars.δ 1)) eqnA
  have hA1001 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 0 + Finsupp.single Vars.δ 1)) eqnA
  have hA0001 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 0 + Finsupp.single Vars.δ 1)) eqnA
  have hA0110 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 0)) eqnA
  have hA1010 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 0)) eqnA
  have hA0021 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqnA

  have hB1011 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 1)) eqnB
  have hB0111 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 1)) eqnB
  have hB0012 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqnB
  have hB0011 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 1)) eqnB
  have hB0010 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 0)) eqnB
  have hB0101 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 0 + Finsupp.single Vars.δ 1)) eqnB
  have hB1001 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 0 + Finsupp.single Vars.δ 1)) eqnB
  have hB0001 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 0 + Finsupp.single Vars.δ 1)) eqnB
  have hB0110 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 0)) eqnB
  have hB1010 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 0)) eqnB
  have hB0021 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqnB

  have hC1011 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 1)) eqnC
  have hC0111 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 1)) eqnC
  have hC0012 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqnC
  have hC0011 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 1)) eqnC
  have hC0010 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 0)) eqnC
  have hC0101 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 0 + Finsupp.single Vars.δ 1)) eqnC
  have hC1001 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 0 + Finsupp.single Vars.δ 1)) eqnC
  have hC0001 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 0 + Finsupp.single Vars.δ 1)) eqnC
  have hC0110 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 0)) eqnC
  have hC1010 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 0)) eqnC
  have hC0021 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqnC

  clear eqn eqnA eqnB eqnC

  trace "Distribute coefficient-taking over terms"
  simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122 hA1011 hA0111 hA0012 hA0011 hA0010 hA0101 hA1001 hA0001 hA0110 hA1010 hA0021 hB1011 hB0111 hB0012 hB0011 hB0010 hB0101 hB1001 hB0001 hB0110 hB1010 hB0021 hC1011 hC0111 hC0012 hC0011 hC0010 hC0101 hC1001 hC0001 hC0110 hC1010 hC0021

  trace "Simplifying coefficient expressions"
  simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122 hA1011 hA0111 hA0012 hA0011 hA0010 hA0101 hA1001 hA0001 hA0110 hA1010 hA0021 hB1011 hB0111 hB0012 hB0011 hB0010 hB0101 hB1001 hB0001 hB0110 hB1010 hB0021 hC1011 hC0111 hC0012 hC0011 hC0010 hC0101 hC1001 hC0001 hC0110 hC1010 hC0021

  trace "Determine which coefficients are nonzero"
  simp (config := {decide := true}) only [ite_false, ite_true] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122 hA1011 hA0111 hA0012 hA0011 hA0010 hA0101 hA1001 hA0001 hA0110 hA1010 hA0021 hB1011 hB0111 hB0012 hB0011 hB0010 hB0101 hB1001 hB0001 hB0110 hB1010 hB0021 hC1011 hC0111 hC0012 hC0011 hC0010 hC0101 hC1001 hC0001 hC0110 hC1010 hC0021
  trace "Remove zeros"
  simp only [neg_zero, add_zero, zero_add] at h0012 h0021 h0022 h0112 h0121 h0122 h0212 h0221 h0222 h1022 h1112 h1121 h1122 hA1011 hA0111 hA0012 hA0011 hA0010 hA0101 hA1001 hA0001 hA0110 hA1010 hA0021 hB1011 hB0111 hB0012 hB0011 hB0010 hB0101 hB1001 hB0001 hB0110 hB1010 hB0021 hC1011 hC0111 hC0012 hC0011 hC0010 hC0101 hC1001 hC0001 hC0110 hC1010 hC0021

  save

  -- Step 2: Recursively simplify and case-analyze the equations
  -- dsimp only


  -- Set statements so that the equations are easier to read
  -- Most are optional, but there are a few that are necessary due to a bug in polyrith that causes it not to properly transcribe casts in its output
  -- /-
  set sum_u_stmt := (List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
  set sum_v_stmt := (List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
  set sum_w_stmt := (List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))

  set A_1 := Polynomial.C (prover.1 Proof_Idx.A SRS_Elements_Idx.α)
  set A_2 := Polynomial.C (prover.1 Proof_Idx.A SRS_Elements_Idx.β)
  set A_3 := Polynomial.C (prover.1 Proof_Idx.A SRS_Elements_Idx.δ)
  set sum_A_x := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_Idx.A (SRS_Elements_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ))
          (List.finRange n_var))

  set sum_A_u_stmt := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_Idx.A (SRS_Elements_Idx.y x)) *
              u_stmt x)
          (List.finRange n_stmt))
  set sum_A_v_stmt := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_Idx.A (SRS_Elements_Idx.y x)) *
              v_stmt x)
          (List.finRange n_stmt))
  set sum_A_w_stmt := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_Idx.A (SRS_Elements_Idx.y x)) *
              w_stmt x)
          (List.finRange n_stmt))
  set sum_A_u_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_Idx.A (SRS_Elements_Idx.q x)) *
              u_wit x)
          (List.finRange n_wit))
  set sum_A_v_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_Idx.A (SRS_Elements_Idx.q x)) *
              v_wit x)
          (List.finRange n_wit))
  set sum_A_w_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_Idx.A (SRS_Elements_Idx.q x)) *
              w_wit x)
          (List.finRange n_wit))
  set sum_A_x_t := (List.sum
                  (List.map
                    (fun x =>
                      Polynomial.C (prover.1 Proof_Idx.A (SRS_Elements_Idx.x_pow_times_t x)) *
                        (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i))))
                    (List.finRange (n_var - 1))))
  set B_1 := Polynomial.C (prover.2 Proof_Idx.B (SRS_Elements_Idx.β))
  set B_2 := Polynomial.C (prover.2 Proof_Idx.B (SRS_Elements_Idx.γ))
  set B_3 := Polynomial.C (prover.2 Proof_Idx.B (SRS_Elements_Idx.δ))

  set sum_B_x := List.sum
                    (List.map
                      (fun x =>
                        Polynomial.C (prover.2 Proof_Idx.B (SRS_Elements_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ))
                      (List.finRange n_var))

  set C_1 := Polynomial.C (prover.1 Proof_Idx.C SRS_Elements_Idx.α)
  set C_2 := Polynomial.C (prover.1 Proof_Idx.C SRS_Elements_Idx.β)
  set C_3 := Polynomial.C (prover.1 Proof_Idx.C SRS_Elements_Idx.δ)
  set sum_C_u_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_Idx.C (SRS_Elements_Idx.q x)) *
              u_wit x)
          (List.finRange n_wit))
  set sum_C_v_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_Idx.C (SRS_Elements_Idx.q x)) *
              v_wit x)
          (List.finRange n_wit))
  set sum_C_w_wit := List.sum
        (List.map
          (fun x =>
            Polynomial.C (prover.1 Proof_Idx.C (SRS_Elements_Idx.q x)) *
              w_wit x)
          (List.finRange n_wit))
  set sum_C_x_t := List.sum
        (List.map
          (fun x : Fin (n_var - 1) =>
            Polynomial.C (prover.1 Proof_Idx.C (SRS_Elements_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i))))
          (List.finRange (n_var - 1)))

  -- clear_value sum_A_x sum_A_x_t sum_B_x sum_C_x_t
  -- clear_value sum_u_stmt sum_v_stmt sum_w_stmt A_1 A_2 A_3 sum_A_x sum_A_u_stmt sum_A_v_stmt sum_A_w_stmt sum_A_u_wit sum_A_v_wit sum_A_w_wit sum_A_x_t B_1 B_2 B_3 sum_B_x C_1 C_2 C_3 sum_C_u_wit sum_C_v_wit sum_C_w_wit sum_C_x_t
  -- -/


  integral_domain_tactic <;> polyrith
  -- Output not checked
  sorry



end soundness

end Groth16TypeI
