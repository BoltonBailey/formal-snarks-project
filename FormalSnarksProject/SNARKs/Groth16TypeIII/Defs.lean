
import Mathlib

import FormalSnarksProject.Models.AGMProofSystemInstantiation
import FormalSnarksProject.ToMathlib.OptionEquivRight
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode

/-!

# Groth16TypeIII

This file contains the definition for the Type III version of Groth16 presented in
["Another Look at Extraction and Randomization of Groth's zk-SNARK" by Baghery et al.](https://eprint.iacr.org/2020/811).

-/

open scoped BigOperators

section Groth16TypeIII

open Option AGMProofSystemInstantiation
open CPoly CPoly.CMvPolynomial
open CompPoly

namespace Groth16TypeIII

inductive Vars : Type where
  | α : Vars
  | β : Vars
  | γ : Vars
  | δ : Vars
deriving Repr, BEq, DecidableEq

instance : FinEnum Vars := .ofList [.α, .β, .γ, .δ] (fun x => by cases x <;> simp)

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
deriving DecidableEq

instance : FinEnum Proof_G1_Idx := .ofList [.A, .C] (fun x => by cases x <;> simp)

inductive Proof_G2_Idx : Type where
  | B : Proof_G2_Idx
deriving DecidableEq

instance : FinEnum Proof_G2_Idx := .ofList [.B] (fun x => by cases x <;> simp)

inductive PairingsIdx : Type where
  | ab : PairingsIdx
  | αβ : PairingsIdx
  | stmtγ : PairingsIdx
  | cδ : PairingsIdx
deriving DecidableEq

instance : FinEnum PairingsIdx :=
  .ofList [.ab, .αβ, .stmtγ, .cδ] (fun x => by cases x <;> simp)

inductive SRS_Elements_G1_Idx {n_stmt n_wit n_var : ℕ} : Type where
  | α : SRS_Elements_G1_Idx
  | β : SRS_Elements_G1_Idx
  | δ : SRS_Elements_G1_Idx
  | x_pow : Fin n_var → SRS_Elements_G1_Idx
  | x_pow_times_t : Fin (n_var - 1) → SRS_Elements_G1_Idx
  | y : Fin n_stmt → SRS_Elements_G1_Idx
  | q : Fin n_wit → SRS_Elements_G1_Idx
deriving DecidableEq

instance {n_stmt n_wit n_var : ℕ} :
    FinEnum (@SRS_Elements_G1_Idx n_stmt n_wit n_var) := .ofList
  ([.α, .β, .δ]
    ++ (List.finRange n_var).map .x_pow
    ++ (List.finRange (n_var - 1)).map .x_pow_times_t
    ++ (List.finRange n_stmt).map .y
    ++ (List.finRange n_wit).map .q)
  (fun x => by cases x <;> simp)

inductive SRS_Elements_G2_Idx {n_stmt n_wit n_var : ℕ} : Type where
  | β : SRS_Elements_G2_Idx
  | γ : SRS_Elements_G2_Idx
  | δ : SRS_Elements_G2_Idx
  | x_pow : Fin n_var → SRS_Elements_G2_Idx
deriving DecidableEq

instance {n_stmt n_wit n_var : ℕ} :
    FinEnum (@SRS_Elements_G2_Idx n_stmt n_wit n_var) := .ofList
  ([.β, .γ, .δ] ++ (List.finRange n_var).map .x_pow)
  (fun x => by cases x <;> simp)

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
@[reducible] noncomputable def Groth16TypeIII
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    /- The naturals representing:
      n_stmt - the statement size,
      n_wit - the witness size -/
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (CompPoly.CPolynomial F) }
    {u_wit : Fin n_wit → (CompPoly.CPolynomial F) }
    {v_stmt : Fin n_stmt → (CompPoly.CPolynomial F) }
    {v_wit : Fin n_wit → (CompPoly.CPolynomial F) }
    {w_stmt : Fin n_stmt → (CompPoly.CPolynomial F) }
    {w_wit : Fin n_wit → (CompPoly.CPolynomial F) }
    /- The roots of the polynomial t -/
    {r : Fin n_wit → F} :
    AGMProofSystemInstantiation F :=
  let t : CompPoly.CPolynomial F :=
    ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i));
  {
    Stmt := Fin n_stmt -> F
    Sample := Option Vars
    SRSElements_G1 := @SRS_Elements_G1_Idx n_stmt n_wit n_var
    SRSElements_G2 := @SRS_Elements_G2_Idx n_stmt n_wit n_var
    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_G1_Idx.α => X Vars_γ * X Vars_δ * X Vars_α
      | SRS_Elements_G1_Idx.β => X Vars_γ * X Vars_δ * X Vars_β
      | SRS_Elements_G1_Idx.δ => X Vars_γ * X Vars_δ * X Vars_δ
      | SRS_Elements_G1_Idx.x_pow i => X Vars_γ * X Vars_δ * X Vars_x ^ (i : ℕ)
      | SRS_Elements_G1_Idx.x_pow_times_t i => X Vars_γ
                                                  * X Vars_x ^ (i : ℕ)
                                                  * to_CMvPolynomial_Option Vars t
      | SRS_Elements_G1_Idx.y i => ((X Vars_β * X Vars_δ) * ( (to_CMvPolynomial_Option Vars (u_stmt i))))
                                      +
                                      (X Vars_α * X Vars_δ) * (to_CMvPolynomial_Option Vars (v_stmt i))
                                      +
                                      X Vars_δ * (to_CMvPolynomial_Option Vars (w_stmt i))
      | SRS_Elements_G1_Idx.q i => (X Vars_β * X Vars_γ) * ( to_CMvPolynomial_Option Vars (u_wit i))
                                      +
                                      (X Vars_α * X Vars_γ) * (to_CMvPolynomial_Option Vars (v_wit i))
                                      +
                                      X Vars_γ * to_CMvPolynomial_Option Vars (w_wit i)
      -- Note that the polynomials here have been multiplied through by γδ
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_G2_Idx.β => X Vars_γ * X Vars_δ * X Vars_β
      | SRS_Elements_G2_Idx.γ => X Vars_γ * X Vars_δ * X Vars_γ
      | SRS_Elements_G2_Idx.δ => X Vars_γ * X Vars_δ * X Vars_δ
      | SRS_Elements_G2_Idx.x_pow i => X Vars_γ * X Vars_δ * X Vars_x ^ (i : ℕ)
    Proof_G1 := Proof_G1_Idx
    Proof_G2 := Proof_G2_Idx
    EqualityChecks := Unit
    Pairings := fun _ => PairingsIdx
    Pairings_FinEnum := fun _ => inferInstance
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
        | SRS_Elements_G1_Idx.q _ => 0
    verificationPairingSRS_G2 := fun _stmt _ i SRS_idx => match i with
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
    verificationPairingProof_G1 := fun _stmt _ i pf => match i with
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
    verificationPairingProof_G2 := fun _stmt _ i pf => match i with
      | PairingsIdx.ab => match pf with
        | Proof_G2_Idx.B => -1
      | PairingsIdx.αβ => match pf with
        | Proof_G2_Idx.B => 0
      | PairingsIdx.stmtγ => match pf with
        | Proof_G2_Idx.B => 0
      | PairingsIdx.cδ => match pf with
        | Proof_G2_Idx.B => 0
  }

end Groth16TypeIII

end Groth16TypeIII
