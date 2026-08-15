/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import FormalSnarksProject.Models.AGMProofSystemInstantiation
public import Mathlib.Algebra.Polynomial.Div
-- import FormalSnarksProject.ToMathlib.List
public import FormalSnarksProject.ToMathlib.OptionEquivRight
public import FormalSnarksProject.ToMathlib.FinEnumToList
public import Mathlib.Algebra.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode
public import FormalSnarksProject.ToMathlib.FinEnumOrd

/-!
# The Lipmaa SNARK

Definition of the Lipmaa SNARK construction as an `AGMProofSystemInstantiation`.
-/

public section


open scoped BigOperators

section Lipmaa

open Option AGMProofSystemInstantiation
open CPoly CPoly.COrdMvPolynomial
open CompPoly

namespace Lipmaa

inductive Vars : Type where
  | y : Vars
deriving Repr, BEq, DecidableEq

instance : FinEnum Vars := .ofList [.y] (fun x => by cases x <;> simp)

instance : Ord Vars := FinEnum.toOrd
instance : Std.TransOrd Vars := FinEnum.toOrd.transOrd
instance : Std.LawfulEqOrd Vars := FinEnum.toOrd.lawfulEqOrd

local notation "Vars_y" => some Vars.y
local notation "Vars_x" => none



lemma Vars.finsupp_eq_ext (f g : Vars →₀ ℕ) : f = g ↔
    f Vars.y = g Vars.y := by
  rw [DFunLike.ext_iff]
  constructor
  · intro h
    simp_rw [h]
  · intro h x
    cases x; tauto


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

/-! ### `FinEnum.toList` expansions

The soundness proof expands the sums over SRS/proof/pairing indices into sums over the concrete
defining lists. For the parameterized SRS index types this holds only propositionally (via
`FinEnum.toList_ofList_of_nodup`), since `List.dedup` does not reduce on `List.finRange` of a
variable length. -/

@[simp] lemma toList_Proof_G1_Idx : FinEnum.toList Proof_G1_Idx = [.A, .C] := by rfl

@[simp] lemma toList_Proof_G2_Idx : FinEnum.toList Proof_G2_Idx = [.B] := by rfl

@[simp] lemma toList_PairingsIdx : FinEnum.toList PairingsIdx = [.ab, .αβ, .stmtγ, .cδ] := by rfl

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

-- TODO Note: May well be best to completely forget about generalizing "straightforward" to the very end.
-- TODO Note: Refactor files - model and a subdirectory for the six files from

/--
TODO
-/
@[expose, reducible] noncomputable def Lipmaa
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    /- The naturals representing:
      n_stmt - the statement size,
      n_wit - the witness size -/
    {n_stmt n_wit n_var : ℕ}
    /- u_stmt and u_wit are Fin-indexed collections of polynomials from the square span program -/
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
      | SRS_Elements_G1_Idx.α => (X Vars_y ^ 5) * (X Vars_y ^ 1) * (X Vars_y ^ 75)
      | SRS_Elements_G1_Idx.β => (X Vars_y ^ 5) * (X Vars_y ^ 1) * (X Vars_y ^ 25)
      | SRS_Elements_G1_Idx.δ => (X Vars_y ^ 5) * (X Vars_y ^ 1) * (X Vars_y ^ 1)
      | SRS_Elements_G1_Idx.x_pow i => (X Vars_y ^ 5) * (X Vars_y ^ 1) * X Vars_x ^ (i : ℕ)
      | SRS_Elements_G1_Idx.x_pow_times_t i => (X Vars_y ^ 5)
                                                  * X Vars_x ^ (i : ℕ)
                                                  * to_COrdMvPolynomial_Option Vars t
      | SRS_Elements_G1_Idx.y i => (((X Vars_y ^ 25) * (X Vars_y ^ 1)) * ( (to_COrdMvPolynomial_Option Vars (u_stmt i))))
                                      +
                                      ((X Vars_y ^ 75) * (X Vars_y ^ 1)) * (to_COrdMvPolynomial_Option Vars (v_stmt i))
                                      +
                                      (X Vars_y ^ 1) * (to_COrdMvPolynomial_Option Vars (w_stmt i))
      | SRS_Elements_G1_Idx.q i => ((X Vars_y ^ 25) * (X Vars_y ^ 5)) * ( to_COrdMvPolynomial_Option Vars (u_wit i))
                                      +
                                      ((X Vars_y ^ 75) * (X Vars_y ^ 5)) * (to_COrdMvPolynomial_Option Vars (v_wit i))
                                      +
                                      (X Vars_y ^ 5) * to_COrdMvPolynomial_Option Vars (w_wit i)
      -- Note that the polynomials here have been multiplied through by γδ
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_G2_Idx.β => (X Vars_y ^ 5) * (X Vars_y ^ 1) * (X Vars_y ^ 25)
      | SRS_Elements_G2_Idx.γ => (X Vars_y ^ 5) * (X Vars_y ^ 1) * (X Vars_y ^ 5)
      | SRS_Elements_G2_Idx.δ => (X Vars_y ^ 5) * (X Vars_y ^ 1) * (X Vars_y ^ 1)
      | SRS_Elements_G2_Idx.x_pow i => (X Vars_y ^ 5) * (X Vars_y ^ 1) * X Vars_x ^ (i : ℕ)
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



end Lipmaa

end Lipmaa
