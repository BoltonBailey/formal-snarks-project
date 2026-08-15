/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import FormalSnarksProject.Models.AGMProofSystemInstantiationTypeI
public import FormalSnarksProject.ToMathlib.OptionEquivRight
public import FormalSnarksProject.ToMathlib.FinEnumToList
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode
public import FormalSnarksProject.ToMathlib.FinEnumOrd

/-!

# Groth16TypeI

This file contains the definition of the Type I (symmetric pairing) version of Groth16, as
presented in
["On the Size of Pairing-based Non-interactive Arguments"](https://eprint.iacr.org/2016/260.pdf)
by Jens Groth.

In the Type I setting there is a single source group, so there is a single SRS containing all
the elements that the Type III version splits between G1 and G2, and every SRS element (and
every proof element) can be used on either side of any pairing. This is modeled by
`AGMProofSystemInstantiationTypeI`, which has a single collection of SRS elements and a single
copy of each proof element (no `Identified_Proof_Elems` are needed).

The verification equation is the usual Groth16 one, with `A` and `C` used on the left of their
pairings and `B` on the right. The prover is nevertheless strictly more powerful than in the
Type III setting, since each proof element may involve *all* SRS elements; the soundness
analysis in `Soundness.lean` accounts for this (in particular `A` and `B` may swap roles).

Note that the SRS polynomials here have been multiplied through by γδ.

-/

public section

open scoped BigOperators

section Groth16TypeI

open MvPolynomial Option AGMProofSystemInstantiationTypeI
open CompPoly

namespace Groth16TypeI

inductive Vars : Type where
  | α : Vars
  | β : Vars
  | γ : Vars
  | δ : Vars
deriving Repr, BEq, DecidableEq

instance : FinEnum Vars := .ofList [.α, .β, .γ, .δ] (fun x => by cases x <;> simp)

instance : Ord Vars := FinEnum.toOrd
instance : Std.TransOrd Vars := FinEnum.toOrd.transOrd
instance : Std.LawfulEqOrd Vars := FinEnum.toOrd.lawfulEqOrd

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

/-- The index type for the SRS. In the symmetric setting there is a single SRS containing the
union of the elements of the two Type III SRSs: the toxic-waste elements α, β, γ, δ, the powers
of x, the powers of x times the vanishing polynomial t, and the statement (y) and witness (q)
QAP combinations. -/
inductive SRS_Elements_Idx {n_stmt n_wit n_var : ℕ} : Type where
  | α : SRS_Elements_Idx
  | β : SRS_Elements_Idx
  | γ : SRS_Elements_Idx
  | δ : SRS_Elements_Idx
  | x_pow : Fin n_var → SRS_Elements_Idx
  | x_pow_times_t : Fin (n_var - 1) → SRS_Elements_Idx
  | y : Fin n_stmt → SRS_Elements_Idx
  | q : Fin n_wit → SRS_Elements_Idx
deriving DecidableEq

instance {n_stmt n_wit n_var : ℕ} :
    FinEnum (@SRS_Elements_Idx n_stmt n_wit n_var) := .ofList
  ([.α, .β, .γ, .δ]
    ++ (List.finRange n_var).map .x_pow
    ++ (List.finRange (n_var - 1)).map .x_pow_times_t
    ++ (List.finRange n_stmt).map .y
    ++ (List.finRange n_wit).map .q)
  (fun x => by cases x <;> simp)

@[simp] lemma toList_SRS_Elements_Idx {n_stmt n_wit n_var : ℕ} :
    FinEnum.toList (@SRS_Elements_Idx n_stmt n_wit n_var) =
      [.α, .β, .γ, .δ]
        ++ (List.finRange n_var).map .x_pow
        ++ (List.finRange (n_var - 1)).map .x_pow_times_t
        ++ (List.finRange n_stmt).map .y
        ++ (List.finRange n_wit).map .q :=
  FinEnum.toList_ofList_of_nodup _ _ (by
    have hx : Function.Injective (@SRS_Elements_Idx.x_pow n_stmt n_wit n_var) :=
      fun a b h => by injection h
    have hxt : Function.Injective (@SRS_Elements_Idx.x_pow_times_t n_stmt n_wit n_var) :=
      fun a b h => by injection h
    have hy : Function.Injective (@SRS_Elements_Idx.y n_stmt n_wit n_var) :=
      fun a b h => by injection h
    have hq : Function.Injective (@SRS_Elements_Idx.q n_stmt n_wit n_var) :=
      fun a b h => by injection h
    have h1 : (List.map SRS_Elements_Idx.x_pow (List.finRange n_var)).Nodup :=
      (List.nodup_finRange _).map hx
    have h2 : ((List.finRange (n_var - 1)).map SRS_Elements_Idx.x_pow_times_t).Nodup :=
      (List.nodup_finRange _).map hxt
    have h3 : ((List.finRange n_stmt).map SRS_Elements_Idx.y).Nodup :=
      (List.nodup_finRange _).map hy
    have h4 : ((List.finRange n_wit).map SRS_Elements_Idx.q).Nodup :=
      (List.nodup_finRange _).map hq
    simp only [List.nodup_append, List.disjoint_left, List.nodup_cons, List.mem_cons,
      List.mem_append, List.mem_map, List.not_mem_nil, List.nodup_nil]
    aesop)

/--
A description of the Groth 16 SNARK in the Type I (symmetric pairing) setting, as presented in
["On the Size of Pairing-based Non-interactive Arguments"](https://eprint.iacr.org/2016/260.pdf).
There is a single SRS containing the union of the elements of the two Type III SRSs, and every
SRS element can appear in every proof element and on either side of every pairing.

Note that the SRS polynomials here have been multiplied through by γδ.
-/
@[expose, reducible] noncomputable def Groth16TypeI
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
    AGMProofSystemInstantiationTypeI F :=
  let t : CompPoly.CPolynomial F :=
    ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i));
  {
    Stmt := Fin n_stmt -> F
    Sample := Option Vars
    SRSElements := @SRS_Elements_Idx n_stmt n_wit n_var
    SRSElementValue := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.α => CPoly.COrdMvPolynomial.X Vars_γ * CPoly.COrdMvPolynomial.X Vars_δ * CPoly.COrdMvPolynomial.X Vars_α
      | SRS_Elements_Idx.β => CPoly.COrdMvPolynomial.X Vars_γ * CPoly.COrdMvPolynomial.X Vars_δ * CPoly.COrdMvPolynomial.X Vars_β
      | SRS_Elements_Idx.γ => CPoly.COrdMvPolynomial.X Vars_γ * CPoly.COrdMvPolynomial.X Vars_δ * CPoly.COrdMvPolynomial.X Vars_γ
      | SRS_Elements_Idx.δ => CPoly.COrdMvPolynomial.X Vars_γ * CPoly.COrdMvPolynomial.X Vars_δ * CPoly.COrdMvPolynomial.X Vars_δ
      | SRS_Elements_Idx.x_pow i => CPoly.COrdMvPolynomial.X Vars_γ * CPoly.COrdMvPolynomial.X Vars_δ * CPoly.COrdMvPolynomial.X Vars_x ^ (i : ℕ)
      | SRS_Elements_Idx.x_pow_times_t i => CPoly.COrdMvPolynomial.X Vars_γ
                                                  * CPoly.COrdMvPolynomial.X Vars_x ^ (i : ℕ)
                                                  * to_COrdMvPolynomial_Option Vars t
      | SRS_Elements_Idx.y i => ((CPoly.COrdMvPolynomial.X Vars_β * CPoly.COrdMvPolynomial.X Vars_δ) * ( (to_COrdMvPolynomial_Option Vars (u_stmt i))))
                                      +
                                      (CPoly.COrdMvPolynomial.X Vars_α * CPoly.COrdMvPolynomial.X Vars_δ) * (to_COrdMvPolynomial_Option Vars (v_stmt i))
                                      +
                                      CPoly.COrdMvPolynomial.X Vars_δ * (to_COrdMvPolynomial_Option Vars (w_stmt i))
      | SRS_Elements_Idx.q i => (CPoly.COrdMvPolynomial.X Vars_β * CPoly.COrdMvPolynomial.X Vars_γ) * ( to_COrdMvPolynomial_Option Vars (u_wit i))
                                      +
                                      (CPoly.COrdMvPolynomial.X Vars_α * CPoly.COrdMvPolynomial.X Vars_γ) * (to_COrdMvPolynomial_Option Vars (v_wit i))
                                      +
                                      CPoly.COrdMvPolynomial.X Vars_γ * to_COrdMvPolynomial_Option Vars (w_wit i)
      -- Note that the polynomials here have been multiplied through by γδ
    Proof := Proof_Idx
    EqualityChecks := Unit
    Pairings := fun _ => PairingsIdx
    Pairings_FinEnum := fun _ => inferInstance
    verificationPairingSRSLeft := fun stmt _ i SRS_idx => match i with
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
        | SRS_Elements_Idx.q _ => 0
    verificationPairingSRSRight := fun _stmt _ i SRS_idx => match i with
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
        | SRS_Elements_Idx.α => 0
        | SRS_Elements_Idx.β => 1
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | SRS_Elements_Idx.x_pow_times_t _ => 0
        | SRS_Elements_Idx.y _ => 0
        | SRS_Elements_Idx.q _ => 0
      | PairingsIdx.stmtγ => match SRS_idx with
        | SRS_Elements_Idx.α => 0
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 1
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | SRS_Elements_Idx.x_pow_times_t _ => 0
        | SRS_Elements_Idx.y _ => 0
        | SRS_Elements_Idx.q _ => 0
      | PairingsIdx.cδ => match SRS_idx with
        | SRS_Elements_Idx.α => 0
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 1
        | SRS_Elements_Idx.x_pow _ => 0
        | SRS_Elements_Idx.x_pow_times_t _ => 0
        | SRS_Elements_Idx.y _ => 0
        | SRS_Elements_Idx.q _ => 0
    verificationPairingProofLeft := fun _stmt _ i pf => match i with
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
    verificationPairingProofRight := fun _stmt _ i pf => match i with
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
  }

end Groth16TypeI

end Groth16TypeI
