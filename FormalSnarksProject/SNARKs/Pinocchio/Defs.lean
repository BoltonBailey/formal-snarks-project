import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Algebra.Polynomial.Div
import FormalSnarksProject.ToMathlib.OptionEquivRight
import FormalSnarksProject.ToMathlib.FinEnumToList
import Mathlib.Algebra.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode
import FormalSnarksProject.ToMathlib.FinEnumOrd

/-!

# Pinocchio

This file contains the definition and soundness proof of the Pinocchio SNARK
(["Pinocchio: Nearly Practical Verifiable Computation" by Parno, Howell, Gentry, Raykova](https://eprint.iacr.org/2013/279)).

Pinocchio is a Type I SNARK: proof elements can in principle be supplied on either side of the
pairing. `W_mid` is the one proof element used on both sides; the model's
`Identified_Proof_Elems` field records that the verifier requires the two copies to agree
(in the group-based scheme they are literally the same group element).

-/

open scoped BigOperators

section Pinocchio

open MvPolynomial Option AGMProofSystemInstantiation
open CompPoly

namespace Pinocchio

inductive Vars : Type where
  | r_v : Vars
  | r_w : Vars
  | α_v : Vars
  | α_w : Vars
  | α_y : Vars
  | β : Vars
  | γ : Vars
deriving Repr, BEq, DecidableEq

instance : FinEnum Vars :=
  .ofList [.r_v, .r_w, .α_v, .α_w, .α_y, .β, .γ] (fun x => by cases x <;> simp)

instance : Ord Vars := FinEnum.toOrd
instance : Std.TransOrd Vars := FinEnum.toOrd.transOrd
instance : Std.LawfulEqOrd Vars := FinEnum.toOrd.lawfulEqOrd

local notation "poly_r_v" => CPoly.COrdMvPolynomial.X (some Vars.r_v)
local notation "poly_r_w" => CPoly.COrdMvPolynomial.X (some Vars.r_w)
local notation "poly_α_v" => CPoly.COrdMvPolynomial.X (some Vars.α_v)
local notation "poly_α_w" => CPoly.COrdMvPolynomial.X (some Vars.α_w)
local notation "poly_α_y" => CPoly.COrdMvPolynomial.X (some Vars.α_y)
local notation "poly_β" => CPoly.COrdMvPolynomial.X (some Vars.β)
local notation "poly_γ" => CPoly.COrdMvPolynomial.X (some Vars.γ)
local notation "poly_s" => CPoly.COrdMvPolynomial.X (none : Option Vars)

lemma Vars.finsupp_eq_ext (f g : Vars →₀ ℕ) : f = g ↔
    f Vars.r_v = g Vars.r_v
    ∧ f Vars.r_w = g Vars.r_w
    ∧ f Vars.α_v = g Vars.α_v
    ∧ f Vars.α_w = g Vars.α_w
    ∧ f Vars.α_y = g Vars.α_y
    ∧ f Vars.β = g Vars.β
    ∧ f Vars.γ = g Vars.γ := by
  rw [DFunLike.ext_iff]
  constructor
  · intro h
    simp_rw [h]
    simp only [and_self]
  · intro h x
    cases x <;> tauto

-- Pinocchio is a Type I SNARK, so in theory any proof element can be given on the left.
-- The W_mid is the only proof element used on both sides.
-- The `Identified_Proof_Elems` field guarantees that the W_mid is the same on both sides.
inductive Proof_G1_Idx : Type where
  | V_mid : Proof_G1_Idx
  | V_mid' : Proof_G1_Idx
  | W_mid : Proof_G1_Idx
  | W_mid' : Proof_G1_Idx
  | Y_mid : Proof_G1_Idx
  | Y_mid' : Proof_G1_Idx
  | Z : Proof_G1_Idx
deriving DecidableEq

instance : FinEnum Proof_G1_Idx :=
  .ofList [.V_mid, .V_mid', .W_mid, .W_mid', .Y_mid, .Y_mid', .Z] (fun x => by cases x <;> simp)

@[simp] lemma toList_Proof_G1_Idx :
    FinEnum.toList Proof_G1_Idx = [.V_mid, .V_mid', .W_mid, .W_mid', .Y_mid, .Y_mid', .Z] := by rfl

inductive Proof_G2_Idx : Type where
  | W_mid : Proof_G2_Idx
  | H : Proof_G2_Idx
deriving DecidableEq

instance : FinEnum Proof_G2_Idx := .ofList [.W_mid, .H] (fun x => by cases x <;> simp)

@[simp] lemma toList_Proof_G2_Idx : FinEnum.toList Proof_G2_Idx = [.W_mid, .H] := by rfl

inductive ChecksIdx : Type where
  | CheckI : ChecksIdx
  | CheckII : ChecksIdx
  | CheckIII : ChecksIdx
  | CheckIV : ChecksIdx
  | CheckV : ChecksIdx
deriving DecidableEq

instance : FinEnum ChecksIdx :=
  .ofList [.CheckI, .CheckII, .CheckIII, .CheckIV, .CheckV] (fun x => by cases x <;> simp)

inductive PairingsI_Idx : Type where
  | lhs : PairingsI_Idx
  | rhs1 : PairingsI_Idx
  | rhs2 : PairingsI_Idx
deriving DecidableEq

instance : FinEnum PairingsI_Idx := .ofList [.lhs, .rhs1, .rhs2] (fun x => by cases x <;> simp)

@[simp] lemma toList_PairingsI_Idx : FinEnum.toList PairingsI_Idx = [.lhs, .rhs1, .rhs2] := by rfl

inductive PairingsII_Idx : Type where
  | lhs : PairingsII_Idx
  | rhs : PairingsII_Idx
deriving DecidableEq

instance : FinEnum PairingsII_Idx := .ofList [.lhs, .rhs] (fun x => by cases x <;> simp)

@[simp] lemma toList_PairingsII_Idx : FinEnum.toList PairingsII_Idx = [.lhs, .rhs] := by rfl

inductive PairingsIII_Idx : Type where
  | lhs : PairingsIII_Idx
  | rhs : PairingsIII_Idx
deriving DecidableEq

instance : FinEnum PairingsIII_Idx := .ofList [.lhs, .rhs] (fun x => by cases x <;> simp)

@[simp] lemma toList_PairingsIII_Idx : FinEnum.toList PairingsIII_Idx = [.lhs, .rhs] := by rfl

inductive PairingsIV_Idx : Type where
  | lhs : PairingsIV_Idx
  | rhs : PairingsIV_Idx
deriving DecidableEq

instance : FinEnum PairingsIV_Idx := .ofList [.lhs, .rhs] (fun x => by cases x <;> simp)

@[simp] lemma toList_PairingsIV_Idx : FinEnum.toList PairingsIV_Idx = [.lhs, .rhs] := by rfl

inductive PairingsV_Idx : Type where
  | lhs : PairingsV_Idx
  | rhs : PairingsV_Idx
deriving DecidableEq

instance : FinEnum PairingsV_Idx := .ofList [.lhs, .rhs] (fun x => by cases x <;> simp)

@[simp] lemma toList_PairingsV_Idx : FinEnum.toList PairingsV_Idx = [.lhs, .rhs] := by rfl

inductive SRS_Elements_Idx {n_stmt n_wit d : ℕ} : Type where
  -- Evaluation key
  | EK_v : Fin n_wit -> SRS_Elements_Idx
  | EK_w : Fin n_wit -> SRS_Elements_Idx
  | EK_y : Fin n_wit -> SRS_Elements_Idx
  | EK_α_v : Fin n_wit -> SRS_Elements_Idx
  | EK_α_w : Fin n_wit -> SRS_Elements_Idx
  | EK_α_y : Fin n_wit -> SRS_Elements_Idx
  | EK_s_pow : Fin d -> SRS_Elements_Idx
  | EK_β_v_w_y : Fin n_wit -> SRS_Elements_Idx
  -- Verification key
  | VK_1 : SRS_Elements_Idx
  | VK_α_v : SRS_Elements_Idx
  | VK_α_w : SRS_Elements_Idx
  | VK_α_y : SRS_Elements_Idx
  | VK_γ : SRS_Elements_Idx
  | VK_βγ : SRS_Elements_Idx
  | VK_t : SRS_Elements_Idx
  | VK_v_0 : SRS_Elements_Idx
  | VK_w_0 : SRS_Elements_Idx
  | VK_y_0 : SRS_Elements_Idx
  | VK_v_stmt : Fin n_stmt -> SRS_Elements_Idx
  | VK_w_stmt : Fin n_stmt -> SRS_Elements_Idx
  | VK_y_stmt : Fin n_stmt -> SRS_Elements_Idx
deriving DecidableEq

instance {n_stmt n_wit d : ℕ} :
    FinEnum (@SRS_Elements_Idx n_stmt n_wit d) := .ofList
  (((List.finRange n_wit).map .EK_v)
    ++ ((List.finRange n_wit).map .EK_w)
    ++ ((List.finRange n_wit).map .EK_y)
    ++ ((List.finRange n_wit).map .EK_α_v)
    ++ ((List.finRange n_wit).map .EK_α_w)
    ++ ((List.finRange n_wit).map .EK_α_y)
    ++ ((List.finRange d).map .EK_s_pow)
    ++ ((List.finRange n_wit).map .EK_β_v_w_y)
    ++ [.VK_1, .VK_α_v, .VK_α_w, .VK_α_y, .VK_γ, .VK_βγ, .VK_t, .VK_v_0, .VK_w_0, .VK_y_0]
    ++ ((List.finRange n_stmt).map .VK_v_stmt)
    ++ ((List.finRange n_stmt).map .VK_w_stmt)
    ++ ((List.finRange n_stmt).map .VK_y_stmt))
  (fun x => by cases x <;> simp)

-- The nodup proof for the 13-chunk SRS enumeration is a large `aesop` case analysis
set_option maxHeartbeats 3200000 in
@[simp] lemma toList_SRS_Elements_Idx {n_stmt n_wit d : ℕ} :
    FinEnum.toList (@SRS_Elements_Idx n_stmt n_wit d) =
      ((List.finRange n_wit).map .EK_v)
        ++ ((List.finRange n_wit).map .EK_w)
        ++ ((List.finRange n_wit).map .EK_y)
        ++ ((List.finRange n_wit).map .EK_α_v)
        ++ ((List.finRange n_wit).map .EK_α_w)
        ++ ((List.finRange n_wit).map .EK_α_y)
        ++ ((List.finRange d).map .EK_s_pow)
        ++ ((List.finRange n_wit).map .EK_β_v_w_y)
        ++ [.VK_1, .VK_α_v, .VK_α_w, .VK_α_y, .VK_γ, .VK_βγ, .VK_t, .VK_v_0, .VK_w_0, .VK_y_0]
        ++ ((List.finRange n_stmt).map .VK_v_stmt)
        ++ ((List.finRange n_stmt).map .VK_w_stmt)
        ++ ((List.finRange n_stmt).map .VK_y_stmt) :=
  FinEnum.toList_ofList_of_nodup _ _ (by
    have h_EK_v : Function.Injective (@SRS_Elements_Idx.EK_v n_stmt n_wit d) :=
      fun a b h => by injection h
    have h_EK_w : Function.Injective (@SRS_Elements_Idx.EK_w n_stmt n_wit d) :=
      fun a b h => by injection h
    have h_EK_y : Function.Injective (@SRS_Elements_Idx.EK_y n_stmt n_wit d) :=
      fun a b h => by injection h
    have h_EK_α_v : Function.Injective (@SRS_Elements_Idx.EK_α_v n_stmt n_wit d) :=
      fun a b h => by injection h
    have h_EK_α_w : Function.Injective (@SRS_Elements_Idx.EK_α_w n_stmt n_wit d) :=
      fun a b h => by injection h
    have h_EK_α_y : Function.Injective (@SRS_Elements_Idx.EK_α_y n_stmt n_wit d) :=
      fun a b h => by injection h
    have h_EK_s_pow : Function.Injective (@SRS_Elements_Idx.EK_s_pow n_stmt n_wit d) :=
      fun a b h => by injection h
    have h_EK_β_v_w_y : Function.Injective (@SRS_Elements_Idx.EK_β_v_w_y n_stmt n_wit d) :=
      fun a b h => by injection h
    have h_VK_v_stmt : Function.Injective (@SRS_Elements_Idx.VK_v_stmt n_stmt n_wit d) :=
      fun a b h => by injection h
    have h_VK_w_stmt : Function.Injective (@SRS_Elements_Idx.VK_w_stmt n_stmt n_wit d) :=
      fun a b h => by injection h
    have h_VK_y_stmt : Function.Injective (@SRS_Elements_Idx.VK_y_stmt n_stmt n_wit d) :=
      fun a b h => by injection h
    have n1 : (List.map SRS_Elements_Idx.EK_v (List.finRange n_wit)).Nodup :=
      (List.nodup_finRange _).map h_EK_v
    have n2 : (List.map SRS_Elements_Idx.EK_w (List.finRange n_wit)).Nodup :=
      (List.nodup_finRange _).map h_EK_w
    have n3 : (List.map SRS_Elements_Idx.EK_y (List.finRange n_wit)).Nodup :=
      (List.nodup_finRange _).map h_EK_y
    have n4 : (List.map SRS_Elements_Idx.EK_α_v (List.finRange n_wit)).Nodup :=
      (List.nodup_finRange _).map h_EK_α_v
    have n5 : (List.map SRS_Elements_Idx.EK_α_w (List.finRange n_wit)).Nodup :=
      (List.nodup_finRange _).map h_EK_α_w
    have n6 : (List.map SRS_Elements_Idx.EK_α_y (List.finRange n_wit)).Nodup :=
      (List.nodup_finRange _).map h_EK_α_y
    have n7 : (List.map SRS_Elements_Idx.EK_s_pow (List.finRange d)).Nodup :=
      (List.nodup_finRange _).map h_EK_s_pow
    have n8 : (List.map SRS_Elements_Idx.EK_β_v_w_y (List.finRange n_wit)).Nodup :=
      (List.nodup_finRange _).map h_EK_β_v_w_y
    have n9 : (List.map SRS_Elements_Idx.VK_v_stmt (List.finRange n_stmt)).Nodup :=
      (List.nodup_finRange _).map h_VK_v_stmt
    have n10 : (List.map SRS_Elements_Idx.VK_w_stmt (List.finRange n_stmt)).Nodup :=
      (List.nodup_finRange _).map h_VK_w_stmt
    have n11 : (List.map SRS_Elements_Idx.VK_y_stmt (List.finRange n_stmt)).Nodup :=
      (List.nodup_finRange _).map h_VK_y_stmt
    simp only [List.nodup_append, List.disjoint_left, List.nodup_cons, List.mem_cons,
      List.mem_append, List.mem_map, List.not_mem_nil, List.nodup_nil]
    aesop)

/--
A description of the Pinocchio SNARK.

The toxic-waste samples are `r_v, r_w, α_v, α_w, α_y, β, γ` (with `r_y = r_v * r_w` implicit)
plus the evaluation point `s` (the `none` sample).
-/
@[reducible] noncomputable def Pinocchio
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    /- The naturals representing:
      m - m from paper - The QAP size
      n_in - n from paper - the number of inputs
      n_out - n' from paper - the number of outputs
      n_mid - (m - N) from paper - the number of internal gates
      d - the degree of h -/
    {n_stmt n_wit d : ℕ}
    /- fin-indexed collections of polynomials from the quadratic arithmetic program -/
    {v_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {w_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {y_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {v_wit : Fin n_wit → CompPoly.CPolynomial F}
    {w_wit : Fin n_wit → CompPoly.CPolynomial F}
    {y_wit : Fin n_wit → CompPoly.CPolynomial F}
    {v_0 : CompPoly.CPolynomial F}
    {w_0 : CompPoly.CPolynomial F}
    {y_0 : CompPoly.CPolynomial F}
    /- t is the polynomial divisibility by which is used to verify satisfaction of the QAP -/
    {t : CompPoly.CPolynomial F} :
    AGMProofSystemInstantiation F :=
  { Stmt := Fin n_stmt → F
    Sample := Option Vars
    SRSElements_G1 := @SRS_Elements_Idx n_stmt n_wit d
    -- Note that Pinocchio is a Type I SNARK - all SRS elements appear in both groups
    SRSElements_G2 := @SRS_Elements_Idx n_stmt n_wit d
    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.EK_v i => poly_r_v * to_COrdMvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_w i => poly_r_w * to_COrdMvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_y i => poly_r_v * poly_r_w * to_COrdMvPolynomial_Option Vars (y_wit i)
      | SRS_Elements_Idx.EK_α_v i => poly_r_v * poly_α_v * to_COrdMvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_α_w i => poly_r_w * poly_α_w * to_COrdMvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_α_y i => poly_r_v * poly_r_w * poly_α_y * to_COrdMvPolynomial_Option Vars (y_wit i)
      | SRS_Elements_Idx.EK_s_pow i => poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_β_v_w_y i => poly_β * (poly_r_v * to_COrdMvPolynomial_Option Vars (v_wit i) + poly_r_w * to_COrdMvPolynomial_Option Vars (w_wit i) + poly_r_v * poly_r_w * to_COrdMvPolynomial_Option Vars (y_wit i))
      | SRS_Elements_Idx.VK_1 => 1
      | SRS_Elements_Idx.VK_α_v => poly_α_v
      | SRS_Elements_Idx.VK_α_w => poly_α_w
      | SRS_Elements_Idx.VK_α_y => poly_α_y
      | SRS_Elements_Idx.VK_γ => poly_γ
      | SRS_Elements_Idx.VK_βγ => poly_β * poly_γ
      | SRS_Elements_Idx.VK_t => poly_r_v * poly_r_w * to_COrdMvPolynomial_Option Vars t
      | SRS_Elements_Idx.VK_v_0 => poly_r_v * to_COrdMvPolynomial_Option Vars v_0
      | SRS_Elements_Idx.VK_w_0 => poly_r_w * to_COrdMvPolynomial_Option Vars w_0
      | SRS_Elements_Idx.VK_y_0 => poly_r_v * poly_r_w * to_COrdMvPolynomial_Option Vars y_0
      | SRS_Elements_Idx.VK_v_stmt i => poly_r_v * to_COrdMvPolynomial_Option Vars (v_stmt i)
      | SRS_Elements_Idx.VK_w_stmt i => poly_r_w * to_COrdMvPolynomial_Option Vars (w_stmt i)
      | SRS_Elements_Idx.VK_y_stmt i => poly_r_v * poly_r_w * to_COrdMvPolynomial_Option Vars (y_stmt i)
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.EK_v i => poly_r_v * to_COrdMvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_w i => poly_r_w * to_COrdMvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_y i => poly_r_v * poly_r_w * to_COrdMvPolynomial_Option Vars (y_wit i)
      | SRS_Elements_Idx.EK_α_v i => poly_r_v * poly_α_v * to_COrdMvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_α_w i => poly_r_w * poly_α_w * to_COrdMvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_α_y i => poly_r_v * poly_r_w * poly_α_y * to_COrdMvPolynomial_Option Vars (y_wit i)
      | SRS_Elements_Idx.EK_s_pow i => poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_β_v_w_y i => poly_β * (poly_r_v * to_COrdMvPolynomial_Option Vars (v_wit i) + poly_r_w * to_COrdMvPolynomial_Option Vars (w_wit i) + poly_r_v * poly_r_w * to_COrdMvPolynomial_Option Vars (y_wit i))
      | SRS_Elements_Idx.VK_1 => 1
      | SRS_Elements_Idx.VK_α_v => poly_α_v
      | SRS_Elements_Idx.VK_α_w => poly_α_w
      | SRS_Elements_Idx.VK_α_y => poly_α_y
      | SRS_Elements_Idx.VK_γ => poly_γ
      | SRS_Elements_Idx.VK_βγ => poly_β * poly_γ
      | SRS_Elements_Idx.VK_t => poly_r_v * poly_r_w * to_COrdMvPolynomial_Option Vars t
      | SRS_Elements_Idx.VK_v_0 => poly_r_v * to_COrdMvPolynomial_Option Vars v_0
      | SRS_Elements_Idx.VK_w_0 => poly_r_w * to_COrdMvPolynomial_Option Vars w_0
      | SRS_Elements_Idx.VK_y_0 => poly_r_v * poly_r_w * to_COrdMvPolynomial_Option Vars y_0
      | SRS_Elements_Idx.VK_v_stmt i => poly_r_v * to_COrdMvPolynomial_Option Vars (v_stmt i)
      | SRS_Elements_Idx.VK_w_stmt i => poly_r_w * to_COrdMvPolynomial_Option Vars (w_stmt i)
      | SRS_Elements_Idx.VK_y_stmt i => poly_r_v * poly_r_w * to_COrdMvPolynomial_Option Vars (y_stmt i)
    Proof_G1 := Proof_G1_Idx
    Proof_G2 := Proof_G2_Idx
    EqualityChecks := ChecksIdx
    Pairings := fun check_idx => match check_idx with
      | ChecksIdx.CheckI => PairingsI_Idx
      | ChecksIdx.CheckII => PairingsII_Idx
      | ChecksIdx.CheckIII => PairingsIII_Idx
      | ChecksIdx.CheckIV => PairingsIV_Idx
      | ChecksIdx.CheckV => PairingsV_Idx
    Pairings_FinEnum := fun check_idx => match check_idx with
      | ChecksIdx.CheckI => inferInstance
      | ChecksIdx.CheckII => inferInstance
      | ChecksIdx.CheckIII => inferInstance
      | ChecksIdx.CheckIV => inferInstance
      | ChecksIdx.CheckV => inferInstance
    verificationPairingSRS_G1 := fun stmt check_idx i SRS_idx => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_v_0 => 1
          | SRS_Elements_Idx.VK_v_stmt k => stmt k
          | _ => 0
        | PairingsI_Idx.rhs1 => match SRS_idx with
          | SRS_Elements_Idx.VK_t => 1
          | _ => 0
        | PairingsI_Idx.rhs2 => match SRS_idx with
          | SRS_Elements_Idx.VK_y_0 => 1
          | SRS_Elements_Idx.VK_y_stmt k => stmt k
          | _ => 0
      | ChecksIdx.CheckII => match i with
        | PairingsII_Idx.lhs => match SRS_idx with
          | _ => 0
        | PairingsII_Idx.rhs => match SRS_idx with
          | _ => 0
      | ChecksIdx.CheckIII => match i with
        | PairingsIII_Idx.lhs => match SRS_idx with
          | _ => 0
        | PairingsIII_Idx.rhs => match SRS_idx with
          | _ => 0
      | ChecksIdx.CheckIV => match i with
        | PairingsIV_Idx.lhs => match SRS_idx with
          | _ => 0
        | PairingsIV_Idx.rhs => match SRS_idx with
          | _ => 0
      | ChecksIdx.CheckV => match i with
        | PairingsV_Idx.lhs => match SRS_idx with
          | _ => 0
        | PairingsV_Idx.rhs => match SRS_idx with
          | _ => 0
    verificationPairingSRS_G2 := fun stmt check_idx i SRS_idx => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_w_0 => 1
          | SRS_Elements_Idx.VK_w_stmt k => stmt k
          | _ => 0
        | PairingsI_Idx.rhs1 => 0
        | PairingsI_Idx.rhs2 => match SRS_idx with
          | SRS_Elements_Idx.VK_1 => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
      | ChecksIdx.CheckII => match i with
        | PairingsII_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_1 => 1
          | _ => 0
        | PairingsII_Idx.rhs => match SRS_idx with
          | SRS_Elements_Idx.VK_α_v => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
      | ChecksIdx.CheckIII => match i with
        | PairingsIII_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_1 => 1
          | _ => 0
        | PairingsIII_Idx.rhs => match SRS_idx with
          | SRS_Elements_Idx.VK_α_w => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
      | ChecksIdx.CheckIV => match i with
        | PairingsIV_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_1 => 1
          | _ => 0
        | PairingsIV_Idx.rhs => match SRS_idx with
          | SRS_Elements_Idx.VK_α_y => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
      | ChecksIdx.CheckV => match i with
        | PairingsV_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_γ => 1
          | _ => 0
        | PairingsV_Idx.rhs => match SRS_idx with
          | SRS_Elements_Idx.VK_βγ => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
    verificationPairingProof_G1 := fun _stmt check_idx i pf_idx => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.lhs => match pf_idx with
          | Proof_G1_Idx.V_mid => 1
          | _ => 0
        | PairingsI_Idx.rhs1 => match pf_idx with
          | _ => 0
        | PairingsI_Idx.rhs2 => match pf_idx with
          | Proof_G1_Idx.Y_mid => 1
          | _ => 0
      | ChecksIdx.CheckII => match i with
        | PairingsII_Idx.lhs => match pf_idx with
          | Proof_G1_Idx.V_mid' => 1
          | _ => 0
        | PairingsII_Idx.rhs => match pf_idx with
          | Proof_G1_Idx.V_mid => 1
          | _ => 0
      | ChecksIdx.CheckIII => match i with
        | PairingsIII_Idx.lhs => match pf_idx with
          | Proof_G1_Idx.W_mid' => 1
          | _ => 0
        | PairingsIII_Idx.rhs => match pf_idx with
          | Proof_G1_Idx.W_mid => 1
          | _ => 0
      | ChecksIdx.CheckIV => match i with
        | PairingsIV_Idx.lhs => match pf_idx with
          | Proof_G1_Idx.Y_mid' => 1
          | _ => 0
        | PairingsIV_Idx.rhs => match pf_idx with
          | Proof_G1_Idx.Y_mid => 1
          | _ => 0
      | ChecksIdx.CheckV => match i with
        | PairingsV_Idx.lhs => match pf_idx with
          | Proof_G1_Idx.Z => 1
          | _ => 0
        | PairingsV_Idx.rhs => match pf_idx with
          | Proof_G1_Idx.V_mid => 1
          | Proof_G1_Idx.W_mid => 1
          | Proof_G1_Idx.Y_mid => 1
          | _ => 0
    verificationPairingProof_G2 := fun _stmt check_idx i pf_idx => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.lhs => match pf_idx with
          | Proof_G2_Idx.W_mid => 1
          | _ => 0
        | PairingsI_Idx.rhs1 => match pf_idx with
          | Proof_G2_Idx.H => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
        | PairingsI_Idx.rhs2 => match pf_idx with
          | _ => 0
      | ChecksIdx.CheckII => 0
      | ChecksIdx.CheckIII => 0
      | ChecksIdx.CheckIV => 0
      | ChecksIdx.CheckV => 0
    Identified_Proof_Elems := [(Proof_G1_Idx.W_mid, Proof_G2_Idx.W_mid)]
  }


end Pinocchio

end Pinocchio
