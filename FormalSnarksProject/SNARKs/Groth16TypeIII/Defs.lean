import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Data.Polynomial.Div
import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Data.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode
import FormalSnarksProject.ToMathlib.MulModByMonic

/-!

# Groth16TypeIII

This file contains the definition for the Type III version of Groth16 presented in
["Another Look at Extraction and Randomization of Groth's zk-SNARK" by Baghery et al.](https://eprint.iacr.org/2020/811).

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
  rw [FunLike.ext_iff]
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

end Groth16TypeIII
