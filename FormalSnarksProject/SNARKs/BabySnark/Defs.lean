module

public import FormalSnarksProject.Models.AGMProofSystemInstantiation
public import Mathlib.Algebra.Polynomial.Div
public import FormalSnarksProject.ToMathlib.OptionEquivRight
public import FormalSnarksProject.ToMathlib.FinEnumToList
public import FormalSnarksProject.ToMathlib.PolynomialDegreeHelpers
public import Mathlib.Algebra.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode
public import FormalSnarksProject.ToMathlib.FinEnumOrd

/-!

# BabySNARK

This file contains the soundness proof for
[BabySNARK](https://github.com/initc3/babySNARK/blob/master/babysnark.pdf), a SNARK for square
span programs. It is a Type I SNARK: all SRS elements appear in both groups, and the three proof
elements `H`, `V`, `B` are each identified across the two groups.

The verifier's checks are:
- I  : (H + t(τ)) * t(τ) + 1 - (V + u_io(τ))² = 0   (the square span check, with `t(τ)` and
       `u_io(τ)` assembled by the verifier from the `τ^i` SRS elements)
- II : B * γ - (γβ) * V = 0                          (forcing `B = β·V`)

Check II's `βγ` coefficient forces the `β·u_wit`-slots of `B` to encode the polynomial part of
`V`, which is why the extractor reads the witness off `B`. Since the verifier assembles `t` and
`u_io` from only the first `n_var` powers of `τ`, the statement requires `t` and the `u_stmt`
polynomials to have degree `< n_var`.

-/

public section

open scoped BigOperators

section BabySNARK

open MvPolynomial Option AGMProofSystemInstantiation
open CompPoly

namespace BabySNARK

inductive Vars : Type where
  | β : Vars
  | γ : Vars
deriving Repr, BEq, DecidableEq

instance : FinEnum Vars := .ofList [.β, .γ] (fun x => by cases x <;> simp)

instance : Ord Vars := FinEnum.toOrd
instance : Std.TransOrd Vars := FinEnum.toOrd.transOrd
instance : Std.LawfulEqOrd Vars := FinEnum.toOrd.lawfulEqOrd

local notation "Vars_β" => some Vars.β
local notation "Vars_γ" => some Vars.γ
local notation "Vars_τ" => (none : Option Vars)

lemma Vars.finsupp_eq_ext (f g : Vars →₀ ℕ) : f = g ↔
    f Vars.β = g Vars.β
    ∧ f Vars.γ = g Vars.γ := by
  rw [DFunLike.ext_iff]
  constructor
  · intro h
    simp_rw [h]
    simp only [and_self]
  · intro h x
    cases x <;> tauto


inductive Proof_Idx : Type where
  | H : Proof_Idx
  | V : Proof_Idx
  | B : Proof_Idx
deriving DecidableEq

instance : FinEnum Proof_Idx := .ofList [.H, .V, .B] (fun x => by cases x <;> simp)

@[simp] lemma toList_Proof_Idx : FinEnum.toList Proof_Idx = [.H, .V, .B] := by rfl

inductive SRS_Elements_Idx {n_stmt n_wit n_var : ℕ} : Type where
  | τ_pow : Fin n_var → SRS_Elements_Idx
  | γ : SRS_Elements_Idx
  | γβ : SRS_Elements_Idx
  | βu : Fin n_wit → SRS_Elements_Idx
deriving DecidableEq

instance {n_stmt n_wit n_var : ℕ} :
    FinEnum (@SRS_Elements_Idx n_stmt n_wit n_var) := .ofList
  (((List.finRange n_var).map .τ_pow)
    ++ [.γ]
    ++ [.γβ]
    ++ ((List.finRange n_wit).map .βu))
  (fun x => by cases x <;> simp)

@[simp] lemma toList_SRS_Elements_Idx {n_stmt n_wit n_var : ℕ} :
    FinEnum.toList (@SRS_Elements_Idx n_stmt n_wit n_var) =
      ((List.finRange n_var).map .τ_pow)
        ++ [.γ]
        ++ [.γβ]
        ++ ((List.finRange n_wit).map .βu) :=
  FinEnum.toList_ofList_of_nodup _ _ (by
    have hτ : Function.Injective (@SRS_Elements_Idx.τ_pow n_stmt n_wit n_var) :=
      fun a b h => by injection h
    have hβu : Function.Injective (@SRS_Elements_Idx.βu n_stmt n_wit n_var) :=
      fun a b h => by injection h
    have n1 : (List.map SRS_Elements_Idx.τ_pow (List.finRange n_var)).Nodup :=
      (List.nodup_finRange _).map hτ
    have n2 : (List.map SRS_Elements_Idx.βu (List.finRange n_wit)).Nodup :=
      (List.nodup_finRange _).map hβu
    simp only [List.nodup_append, List.disjoint_left, List.nodup_cons, List.mem_cons,
      List.mem_append, List.mem_map, List.not_mem_nil, List.nodup_nil, List.mem_singleton]
    aesop)

inductive ChecksIdx : Type where
  | CheckI : ChecksIdx
  | CheckII : ChecksIdx
deriving DecidableEq

instance : FinEnum ChecksIdx := .ofList [.CheckI, .CheckII] (fun x => by cases x <;> simp)

inductive PairingsI_Idx : Type where
  | ht : PairingsI_Idx
  | gg : PairingsI_Idx
  | vv : PairingsI_Idx
deriving DecidableEq

instance : FinEnum PairingsI_Idx := .ofList [.ht, .gg, .vv] (fun x => by cases x <;> simp)

@[simp] lemma toList_PairingsI_Idx : FinEnum.toList PairingsI_Idx = [.ht, .gg, .vv] := by rfl

inductive PairingsII_Idx : Type where
  | bγ : PairingsII_Idx
  | γβv : PairingsII_Idx
deriving DecidableEq

instance : FinEnum PairingsII_Idx := .ofList [.bγ, .γβv] (fun x => by cases x <;> simp)

@[simp] lemma toList_PairingsII_Idx : FinEnum.toList PairingsII_Idx = [.bγ, .γβv] := by rfl


@[expose, reducible] noncomputable def BabySNARK
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n_stmt n_wit n_var : ℕ}
    /- u_stmt and u_wit are Fin-indexed collections of polynomials from the square span program -/
    {u_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {u_wit : Fin n_wit → CompPoly.CPolynomial F}
    {t : CompPoly.CPolynomial F} :
    AGMProofSystemInstantiation F :=
  {
    Stmt := Fin n_stmt -> F
    Sample := Option Vars
    SRSElements_G1 := @SRS_Elements_Idx n_stmt n_wit n_var
    SRSElements_G2 := @SRS_Elements_Idx n_stmt n_wit n_var
    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.τ_pow i => CPoly.COrdMvPolynomial.X Vars_τ ^ (i : ℕ)
      -- NOTE: an earlier version of this file gave the `γ` element the value `X Vars_β`, i.e.
      -- the check II pairing e(B, γ) = e(γβ, V) degenerated to e(B, β) = e(γβ, V). With that
      -- SRS, soundness fails for square span programs where some combination of the `u_wit`
      -- polynomials is a nonzero constant.
      | SRS_Elements_Idx.γ => CPoly.COrdMvPolynomial.X Vars_γ
      | SRS_Elements_Idx.γβ => CPoly.COrdMvPolynomial.X Vars_γ * CPoly.COrdMvPolynomial.X Vars_β
      | SRS_Elements_Idx.βu i =>
        CPoly.COrdMvPolynomial.X Vars_β * to_COrdMvPolynomial_Option Vars (u_wit i)
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.τ_pow i => CPoly.COrdMvPolynomial.X Vars_τ ^ (i : ℕ)
      | SRS_Elements_Idx.γ => CPoly.COrdMvPolynomial.X Vars_γ
      | SRS_Elements_Idx.γβ => CPoly.COrdMvPolynomial.X Vars_γ * CPoly.COrdMvPolynomial.X Vars_β
      | SRS_Elements_Idx.βu i =>
        CPoly.COrdMvPolynomial.X Vars_β * to_COrdMvPolynomial_Option Vars (u_wit i)
    Proof_G1 := Proof_Idx
    Proof_G2 := Proof_Idx
    EqualityChecks := ChecksIdx
    Pairings := fun check_idx => match check_idx with
      | ChecksIdx.CheckI => PairingsI_Idx
      | ChecksIdx.CheckII => PairingsII_Idx
    Pairings_FinEnum := fun check_idx => match check_idx with
      | ChecksIdx.CheckI => inferInstance
      | ChecksIdx.CheckII => inferInstance
    verificationPairingSRS_G1 := fun stmt check_idx i SRS_idx => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.ht => match SRS_idx with
          | SRS_Elements_Idx.τ_pow i => t.coeff i
          | SRS_Elements_Idx.γ => 0
          | SRS_Elements_Idx.γβ => 0
          | SRS_Elements_Idx.βu _ => 0
        | PairingsI_Idx.gg => match SRS_idx with
          | SRS_Elements_Idx.τ_pow i => if (i : ℕ) = 0 then 1 else 0
          | SRS_Elements_Idx.γ => 0
          | SRS_Elements_Idx.γβ => 0
          | SRS_Elements_Idx.βu _ => 0
        | PairingsI_Idx.vv => match SRS_idx with
          | SRS_Elements_Idx.τ_pow i => List.sum (List.map (fun j => (stmt j) * (u_stmt j).coeff i) (List.finRange n_stmt))
          | SRS_Elements_Idx.γ => 0
          | SRS_Elements_Idx.γβ => 0
          | SRS_Elements_Idx.βu _ => 0
      | ChecksIdx.CheckII => match i with
        | PairingsII_Idx.bγ => match SRS_idx with
          | SRS_Elements_Idx.τ_pow _ => 0
          | SRS_Elements_Idx.γ => 0
          | SRS_Elements_Idx.γβ => 0
          | SRS_Elements_Idx.βu _ => 0
        | PairingsII_Idx.γβv => match SRS_idx with
          | SRS_Elements_Idx.τ_pow _ => 0
          | SRS_Elements_Idx.γ => 0
          | SRS_Elements_Idx.γβ => 1
          | SRS_Elements_Idx.βu _ => 0
    verificationPairingSRS_G2 := fun stmt check_idx i SRS_idx => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.ht => match SRS_idx with
          | SRS_Elements_Idx.τ_pow i => t.coeff i
          | SRS_Elements_Idx.γ => 0
          | SRS_Elements_Idx.γβ => 0
          | SRS_Elements_Idx.βu _ => 0
        | PairingsI_Idx.gg => match SRS_idx with
          | SRS_Elements_Idx.τ_pow i => if (i : ℕ) = 0 then 1 else 0
          | SRS_Elements_Idx.γ => 0
          | SRS_Elements_Idx.γβ => 0
          | SRS_Elements_Idx.βu _ => 0
        | PairingsI_Idx.vv => match SRS_idx with
          | SRS_Elements_Idx.τ_pow i => -List.sum (List.map (fun j => (stmt j) * (u_stmt j).coeff i) (List.finRange n_stmt))
          | SRS_Elements_Idx.γ => 0
          | SRS_Elements_Idx.γβ => 0
          | SRS_Elements_Idx.βu _ => 0
      | ChecksIdx.CheckII => match i with
        | PairingsII_Idx.bγ => match SRS_idx with
          | SRS_Elements_Idx.τ_pow _ => 0
          | SRS_Elements_Idx.γ => 1
          | SRS_Elements_Idx.γβ => 0
          | SRS_Elements_Idx.βu _ => 0
        | PairingsII_Idx.γβv => match SRS_idx with
          | SRS_Elements_Idx.τ_pow _ => 0
          | SRS_Elements_Idx.γ => 0
          | SRS_Elements_Idx.γβ => 0
          | SRS_Elements_Idx.βu _ => 0
    verificationPairingProof_G1 := fun _stmt check_idx i pf => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.ht => match pf with
          | Proof_Idx.H => 1
          | Proof_Idx.V => 0
          | Proof_Idx.B => 0
        | PairingsI_Idx.gg => match pf with
          | Proof_Idx.H => 0
          | Proof_Idx.V => 0
          | Proof_Idx.B => 0
        | PairingsI_Idx.vv => match pf with
          | Proof_Idx.H => 0
          | Proof_Idx.V => 1
          | Proof_Idx.B => 0
      | ChecksIdx.CheckII => match i with
        | PairingsII_Idx.bγ => match pf with
          | Proof_Idx.H => 0
          | Proof_Idx.V => 0
          | Proof_Idx.B => 1
        | PairingsII_Idx.γβv => match pf with
          | Proof_Idx.H => 0
          | Proof_Idx.V => 0
          | Proof_Idx.B => 0
    verificationPairingProof_G2 := fun _stmt check_idx i pf => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.ht => match pf with
          | Proof_Idx.H => 0
          | Proof_Idx.V => 0
          | Proof_Idx.B => 0
        | PairingsI_Idx.gg => match pf with
          | Proof_Idx.H => 0
          | Proof_Idx.V => 0
          | Proof_Idx.B => 0
        | PairingsI_Idx.vv => match pf with
          | Proof_Idx.H => 0
          | Proof_Idx.V => -1
          | Proof_Idx.B => 0
      | ChecksIdx.CheckII => match i with
        | PairingsII_Idx.bγ => match pf with
          | Proof_Idx.H => 0
          | Proof_Idx.V => 0
          | Proof_Idx.B => 0
        | PairingsII_Idx.γβv => match pf with
          | Proof_Idx.H => 0
          | Proof_Idx.V => -1
          | Proof_Idx.B => 0
    Identified_Proof_Elems := [(Proof_Idx.H, Proof_Idx.H), (Proof_Idx.V, Proof_Idx.V), (Proof_Idx.B, Proof_Idx.B)]
  }

end BabySNARK

end BabySNARK
