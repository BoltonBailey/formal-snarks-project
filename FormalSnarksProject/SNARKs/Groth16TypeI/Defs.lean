import FormalSnarksProject.Models.AGMProofSystemInstantiation
import FormalSnarksProject.ToMathlib.OptionEquivRight
import FormalSnarksProject.ToMathlib.FinEnumToList
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode

/-!

# Groth16TypeI

This file contains the soundness proof for the Type I version of Groth16 presented in
["On the Size of Pairing-based Non-interactive Arguments"](https://eprint.iacr.org/2016/260.pdf)
by Jens Groth.

In the Type I (symmetric pairing) setting all three proof elements `A`, `B`, `C` can be given on
either side of the pairing; the verifier requires the two copies of each to agree (the
`Identified_Proof_Elems` field). The verification equation itself uses `A` and `C` from the first
group and `B` from the second, so it coincides with the Type III equation and the soundness
argument goes through without using the identifications at all.

-/

open scoped BigOperators

section Groth16TypeI

open MvPolynomial Option AGMProofSystemInstantiation
open CompPoly

namespace Groth16TypeI

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


inductive Proof_Idx : Type where
  | A : Proof_Idx
  | B : Proof_Idx
  | C : Proof_Idx
deriving DecidableEq

instance : FinEnum Proof_Idx := .ofList [.A, .B, .C] (fun x => by cases x <;> simp)

@[simp] lemma toList_Proof_Idx : FinEnum.toList Proof_Idx = [.A, .B, .C] := by rfl

inductive PairingsIdx : Type where
  | ab : PairingsIdx
  | αβ : PairingsIdx
  | stmtγ : PairingsIdx
  | cδ : PairingsIdx
deriving DecidableEq

instance : FinEnum PairingsIdx :=
  .ofList [.ab, .αβ, .stmtγ, .cδ] (fun x => by cases x <;> simp)

@[simp] lemma toList_PairingsIdx : FinEnum.toList PairingsIdx = [.ab, .αβ, .stmtγ, .cδ] := by rfl

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

@[simp] lemma toList_SRS_Elements_G1_Idx {n_stmt n_wit n_var : ℕ} :
    FinEnum.toList (@SRS_Elements_G1_Idx n_stmt n_wit n_var) =
      [.α, .β, .δ]
        ++ (List.finRange n_var).map .x_pow
        ++ (List.finRange (n_var - 1)).map .x_pow_times_t
        ++ (List.finRange n_stmt).map .y
        ++ (List.finRange n_wit).map .q :=
  FinEnum.toList_ofList_of_nodup _ _ (by
    have hx : Function.Injective (@SRS_Elements_G1_Idx.x_pow n_stmt n_wit n_var) :=
      fun a b h => by injection h
    have hxt : Function.Injective (@SRS_Elements_G1_Idx.x_pow_times_t n_stmt n_wit n_var) :=
      fun a b h => by injection h
    have hy : Function.Injective (@SRS_Elements_G1_Idx.y n_stmt n_wit n_var) :=
      fun a b h => by injection h
    have hq : Function.Injective (@SRS_Elements_G1_Idx.q n_stmt n_wit n_var) :=
      fun a b h => by injection h
    have h1 : (List.map SRS_Elements_G1_Idx.x_pow (List.finRange n_var)).Nodup :=
      (List.nodup_finRange _).map hx
    have h2 : ((List.finRange (n_var - 1)).map SRS_Elements_G1_Idx.x_pow_times_t).Nodup :=
      (List.nodup_finRange _).map hxt
    have h3 : ((List.finRange n_stmt).map SRS_Elements_G1_Idx.y).Nodup :=
      (List.nodup_finRange _).map hy
    have h4 : ((List.finRange n_wit).map SRS_Elements_G1_Idx.q).Nodup :=
      (List.nodup_finRange _).map hq
    simp only [List.nodup_append, List.disjoint_left, List.nodup_cons, List.mem_cons,
      List.mem_append, List.mem_map, List.not_mem_nil, List.nodup_nil]
    aesop)

@[simp] lemma toList_SRS_Elements_G2_Idx {n_stmt n_wit n_var : ℕ} :
    FinEnum.toList (@SRS_Elements_G2_Idx n_stmt n_wit n_var) =
      [.β, .γ, .δ] ++ (List.finRange n_var).map .x_pow :=
  FinEnum.toList_ofList_of_nodup _ _ (by
    have hx : Function.Injective (@SRS_Elements_G2_Idx.x_pow n_stmt n_wit n_var) :=
      fun a b h => by injection h
    simp [(List.nodup_finRange _).map hx])

/--
A description of the Groth 16 SNARK in the Type I (symmetric pairing) setting, as presented in
["On the Size of Pairing-based Non-interactive Arguments"](https://eprint.iacr.org/2016/260.pdf).
The SRS elements of both groups and the verification equation are as in the Type III version;
additionally each proof element may be given on either side of the pairing, and the verifier
checks that the two copies agree.

Note that the SRS polynomials here have been multiplied through by γδ.
-/
@[reducible] noncomputable def Groth16TypeI
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
      | SRS_Elements_G1_Idx.α => CPoly.CMvPolynomial.X Vars_γ * CPoly.CMvPolynomial.X Vars_δ * CPoly.CMvPolynomial.X Vars_α
      | SRS_Elements_G1_Idx.β => CPoly.CMvPolynomial.X Vars_γ * CPoly.CMvPolynomial.X Vars_δ * CPoly.CMvPolynomial.X Vars_β
      | SRS_Elements_G1_Idx.δ => CPoly.CMvPolynomial.X Vars_γ * CPoly.CMvPolynomial.X Vars_δ * CPoly.CMvPolynomial.X Vars_δ
      | SRS_Elements_G1_Idx.x_pow i => CPoly.CMvPolynomial.X Vars_γ * CPoly.CMvPolynomial.X Vars_δ * CPoly.CMvPolynomial.X Vars_x ^ (i : ℕ)
      | SRS_Elements_G1_Idx.x_pow_times_t i => CPoly.CMvPolynomial.X Vars_γ
                                                  * CPoly.CMvPolynomial.X Vars_x ^ (i : ℕ)
                                                  * to_CMvPolynomial_Option Vars t
      | SRS_Elements_G1_Idx.y i => ((CPoly.CMvPolynomial.X Vars_β * CPoly.CMvPolynomial.X Vars_δ) * ( (to_CMvPolynomial_Option Vars (u_stmt i))))
                                      +
                                      (CPoly.CMvPolynomial.X Vars_α * CPoly.CMvPolynomial.X Vars_δ) * (to_CMvPolynomial_Option Vars (v_stmt i))
                                      +
                                      CPoly.CMvPolynomial.X Vars_δ * (to_CMvPolynomial_Option Vars (w_stmt i))
      | SRS_Elements_G1_Idx.q i => (CPoly.CMvPolynomial.X Vars_β * CPoly.CMvPolynomial.X Vars_γ) * ( to_CMvPolynomial_Option Vars (u_wit i))
                                      +
                                      (CPoly.CMvPolynomial.X Vars_α * CPoly.CMvPolynomial.X Vars_γ) * (to_CMvPolynomial_Option Vars (v_wit i))
                                      +
                                      CPoly.CMvPolynomial.X Vars_γ * to_CMvPolynomial_Option Vars (w_wit i)
      -- Note that the polynomials here have been multiplied through by γδ
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_G2_Idx.β => CPoly.CMvPolynomial.X Vars_γ * CPoly.CMvPolynomial.X Vars_δ * CPoly.CMvPolynomial.X Vars_β
      | SRS_Elements_G2_Idx.γ => CPoly.CMvPolynomial.X Vars_γ * CPoly.CMvPolynomial.X Vars_δ * CPoly.CMvPolynomial.X Vars_γ
      | SRS_Elements_G2_Idx.δ => CPoly.CMvPolynomial.X Vars_γ * CPoly.CMvPolynomial.X Vars_δ * CPoly.CMvPolynomial.X Vars_δ
      | SRS_Elements_G2_Idx.x_pow i => CPoly.CMvPolynomial.X Vars_γ * CPoly.CMvPolynomial.X Vars_δ * CPoly.CMvPolynomial.X Vars_x ^ (i : ℕ)
    Proof_G1 := Proof_Idx
    Proof_G2 := Proof_Idx
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
    verificationPairingProof_G2 := fun _stmt _ i pf => match i with
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

end Groth16TypeI

end Groth16TypeI
