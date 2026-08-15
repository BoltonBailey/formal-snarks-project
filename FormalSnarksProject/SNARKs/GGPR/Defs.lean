import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Algebra.Polynomial.Div
import FormalSnarksProject.ToMathlib.OptionEquivRight
import FormalSnarksProject.ToMathlib.FinEnumToList
import Mathlib.Algebra.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode
import FormalSnarksProject.ToMathlib.FinEnumOrd

/-!

# GGPR

This file contains the definition and soundness proof of the GGPR SNARK
(["Quadratic Span Programs and Succinct NIZKs without PCPs" by Gennaro, Gentry, Parno, Raykova](https://eprint.iacr.org/2012/215)).

The verifier's checks are:
- I  : (v_0(s) + v_in(s) + V_mid) * (w_0(s) + W) - t * H = 0
- II : V_mid' - α * V_mid = 0
- III: W' - α * W = 0
- IV : H' - α * H = 0
- V  : Y * γ - V_mid * (β_v γ) - (β_w γ) * W = 0

Check V pins the witness: the coefficient of `β_v γ` says that the `EK_β_v`-slots of `Y` encode
the polynomial `V_mid`, and the coefficient of `β_w γ` similarly encodes `W`. The extractor
therefore reads the witness off `Y` (an earlier draft mistakenly read it off `H`, whose β-slots
are unconstrained by check I and only forced to a vanishing combination by check IV — with that
extractor the statement is false).

-/

open scoped BigOperators

section GGPR

open MvPolynomial Option AGMProofSystemInstantiation
open CompPoly

namespace GGPR

inductive Vars : Type where
  | α : Vars
  | β_v : Vars
  | β_w : Vars
  | β_y : Vars
  | γ : Vars
deriving Repr, BEq, DecidableEq

instance : FinEnum Vars :=
  .ofList [.α, .β_v, .β_w, .β_y, .γ] (fun x => by cases x <;> simp)

instance : Ord Vars := FinEnum.toOrd
instance : Std.TransOrd Vars := FinEnum.toOrd.transOrd
instance : Std.LawfulEqOrd Vars := FinEnum.toOrd.lawfulEqOrd

local notation "poly_α" => CPoly.COrdMvPolynomial.X (some Vars.α)
local notation "poly_β_v" => CPoly.COrdMvPolynomial.X (some Vars.β_v)
local notation "poly_β_w" => CPoly.COrdMvPolynomial.X (some Vars.β_w)
local notation "poly_β_y" => CPoly.COrdMvPolynomial.X (some Vars.β_y)
local notation "poly_γ" => CPoly.COrdMvPolynomial.X (some Vars.γ)
local notation "poly_s" => CPoly.COrdMvPolynomial.X (none : Option Vars)

lemma Vars.finsupp_eq_ext (f g : Vars →₀ ℕ) : f = g ↔
    f Vars.α = g Vars.α
    ∧ f Vars.β_v = g Vars.β_v
    ∧ f Vars.β_w = g Vars.β_w
    ∧ f Vars.β_y = g Vars.β_y
    ∧ f Vars.γ = g Vars.γ := by
  rw [DFunLike.ext_iff]
  constructor
  · intro h
    simp_rw [h]
    simp only [and_self]
  · intro h x
    cases x <;> tauto

inductive Proof_G1_Idx : Type where
  | V_mid : Proof_G1_Idx
  | V_mid' : Proof_G1_Idx
  | W' : Proof_G1_Idx
  | Y : Proof_G1_Idx
  | H' : Proof_G1_Idx
deriving DecidableEq

instance : FinEnum Proof_G1_Idx :=
  .ofList [.V_mid, .V_mid', .W', .Y, .H'] (fun x => by cases x <;> simp)

@[simp] lemma toList_Proof_G1_Idx :
    FinEnum.toList Proof_G1_Idx = [.V_mid, .V_mid', .W', .Y, .H'] := by rfl

inductive Proof_G2_Idx : Type where
  | W : Proof_G2_Idx
  | H : Proof_G2_Idx
deriving DecidableEq

instance : FinEnum Proof_G2_Idx := .ofList [.W, .H] (fun x => by cases x <;> simp)

@[simp] lemma toList_Proof_G2_Idx : FinEnum.toList Proof_G2_Idx = [.W, .H] := by rfl

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
  | rhs : PairingsI_Idx
deriving DecidableEq

instance : FinEnum PairingsI_Idx := .ofList [.lhs, .rhs] (fun x => by cases x <;> simp)

@[simp] lemma toList_PairingsI_Idx : FinEnum.toList PairingsI_Idx = [.lhs, .rhs] := by rfl

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
  | rhs1 : PairingsV_Idx
  | rhs2 : PairingsV_Idx
deriving DecidableEq

instance : FinEnum PairingsV_Idx := .ofList [.lhs, .rhs1, .rhs2] (fun x => by cases x <;> simp)

@[simp] lemma toList_PairingsV_Idx : FinEnum.toList PairingsV_Idx = [.lhs, .rhs1, .rhs2] := by rfl

inductive SRS_Elements_Idx {n_stmt n_wit m d : ℕ} : Type where
  -- Function universal
  | EK_s_pow : Fin d -> SRS_Elements_Idx
  | EK_α_s_pow : Fin d -> SRS_Elements_Idx
  -- Evaluation key
  | EK_v : Fin n_wit -> SRS_Elements_Idx
  | EK_w : Fin m -> SRS_Elements_Idx
  | EK_α_v : Fin n_wit -> SRS_Elements_Idx
  | EK_α_w : Fin m -> SRS_Elements_Idx
  | EK_β_v : Fin n_wit -> SRS_Elements_Idx
  | EK_β_w : Fin m -> SRS_Elements_Idx
  -- Verification key
  | VK_1 : SRS_Elements_Idx
  | VK_α : SRS_Elements_Idx
  | VK_γ : SRS_Elements_Idx
  | VK_βv_γ : SRS_Elements_Idx
  | VK_βw_γ : SRS_Elements_Idx
  | VK_v_0 : SRS_Elements_Idx
  | VK_w_0 : SRS_Elements_Idx
  | VK_t : SRS_Elements_Idx
  | VK_v_stmt : Fin n_stmt -> SRS_Elements_Idx
deriving DecidableEq

instance {n_stmt n_wit m d : ℕ} :
    FinEnum (@SRS_Elements_Idx n_stmt n_wit m d) := .ofList
  (((List.finRange d).map .EK_s_pow)
    ++ ((List.finRange d).map .EK_α_s_pow)
    ++ ((List.finRange n_wit).map .EK_v)
    ++ ((List.finRange m).map .EK_w)
    ++ ((List.finRange n_wit).map .EK_α_v)
    ++ ((List.finRange m).map .EK_α_w)
    ++ ((List.finRange n_wit).map .EK_β_v)
    ++ ((List.finRange m).map .EK_β_w)
    ++ [.VK_1, .VK_α, .VK_γ, .VK_βv_γ, .VK_βw_γ, .VK_v_0, .VK_w_0, .VK_t]
    ++ ((List.finRange n_stmt).map .VK_v_stmt))
  (fun x => by cases x <;> simp)

-- The nodup proof for the 10-chunk SRS enumeration is a large `aesop` case analysis
set_option maxHeartbeats 3200000 in
@[simp] lemma toList_SRS_Elements_Idx {n_stmt n_wit m d : ℕ} :
    FinEnum.toList (@SRS_Elements_Idx n_stmt n_wit m d) =
      ((List.finRange d).map .EK_s_pow)
        ++ ((List.finRange d).map .EK_α_s_pow)
        ++ ((List.finRange n_wit).map .EK_v)
        ++ ((List.finRange m).map .EK_w)
        ++ ((List.finRange n_wit).map .EK_α_v)
        ++ ((List.finRange m).map .EK_α_w)
        ++ ((List.finRange n_wit).map .EK_β_v)
        ++ ((List.finRange m).map .EK_β_w)
        ++ [.VK_1, .VK_α, .VK_γ, .VK_βv_γ, .VK_βw_γ, .VK_v_0, .VK_w_0, .VK_t]
        ++ ((List.finRange n_stmt).map .VK_v_stmt) :=
  FinEnum.toList_ofList_of_nodup _ _ (by
    have h1 : Function.Injective (@SRS_Elements_Idx.EK_s_pow n_stmt n_wit m d) :=
      fun a b h => by injection h
    have h2 : Function.Injective (@SRS_Elements_Idx.EK_α_s_pow n_stmt n_wit m d) :=
      fun a b h => by injection h
    have h3 : Function.Injective (@SRS_Elements_Idx.EK_v n_stmt n_wit m d) :=
      fun a b h => by injection h
    have h4 : Function.Injective (@SRS_Elements_Idx.EK_w n_stmt n_wit m d) :=
      fun a b h => by injection h
    have h5 : Function.Injective (@SRS_Elements_Idx.EK_α_v n_stmt n_wit m d) :=
      fun a b h => by injection h
    have h6 : Function.Injective (@SRS_Elements_Idx.EK_α_w n_stmt n_wit m d) :=
      fun a b h => by injection h
    have h7 : Function.Injective (@SRS_Elements_Idx.EK_β_v n_stmt n_wit m d) :=
      fun a b h => by injection h
    have h8 : Function.Injective (@SRS_Elements_Idx.EK_β_w n_stmt n_wit m d) :=
      fun a b h => by injection h
    have h9 : Function.Injective (@SRS_Elements_Idx.VK_v_stmt n_stmt n_wit m d) :=
      fun a b h => by injection h
    have n1 : (List.map SRS_Elements_Idx.EK_s_pow (List.finRange d)).Nodup :=
      (List.nodup_finRange _).map h1
    have n2 : (List.map SRS_Elements_Idx.EK_α_s_pow (List.finRange d)).Nodup :=
      (List.nodup_finRange _).map h2
    have n3 : (List.map SRS_Elements_Idx.EK_v (List.finRange n_wit)).Nodup :=
      (List.nodup_finRange _).map h3
    have n4 : (List.map SRS_Elements_Idx.EK_w (List.finRange m)).Nodup :=
      (List.nodup_finRange _).map h4
    have n5 : (List.map SRS_Elements_Idx.EK_α_v (List.finRange n_wit)).Nodup :=
      (List.nodup_finRange _).map h5
    have n6 : (List.map SRS_Elements_Idx.EK_α_w (List.finRange m)).Nodup :=
      (List.nodup_finRange _).map h6
    have n7 : (List.map SRS_Elements_Idx.EK_β_v (List.finRange n_wit)).Nodup :=
      (List.nodup_finRange _).map h7
    have n8 : (List.map SRS_Elements_Idx.EK_β_w (List.finRange m)).Nodup :=
      (List.nodup_finRange _).map h8
    have n9 : (List.map SRS_Elements_Idx.VK_v_stmt (List.finRange n_stmt)).Nodup :=
      (List.nodup_finRange _).map h9
    simp only [List.nodup_append, List.disjoint_left, List.nodup_cons, List.mem_cons,
      List.mem_append, List.mem_map, List.not_mem_nil, List.nodup_nil]
    aesop)

/--
A description of the GGPR SNARK. GGPR is a Type I SNARK: all SRS elements appear in both
groups of the pairing.
-/
@[reducible] noncomputable def GGPR
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    /- The naturals representing:
      m - m from paper - The QAP size
      n_in - n from paper - the number of inputs
      n_out - n' from paper - the number of outputs
      n_mid - (m - N) from paper - the number of internal gates
      d - the degree of h -/
    {n_stmt n_wit m d : ℕ}
    /- fin-indexed collections of polynomials from the quadratic arithmetic program -/
    {v_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {v_wit : Fin n_wit → CompPoly.CPolynomial F}
    {w_wit : Fin m → CompPoly.CPolynomial F}
    {v_0 : CompPoly.CPolynomial F}
    {w_0 : CompPoly.CPolynomial F}
    /- The roots of the polynomial t -/
    {r : Fin (n_wit) → F} :
    AGMProofSystemInstantiation F :=
  /- t is the polynomial divisibility by which is used to verify satisfaction of the QAP -/
  let t : CompPoly.CPolynomial F :=
    ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i));
  { Stmt := Fin n_stmt → F
    Sample := Option Vars
    SRSElements_G1 := @SRS_Elements_Idx n_stmt n_wit m d
    -- Note that GGPR is a Type I SNARK - all SRS elements appear in both groups of the pairing
    SRSElements_G2 := @SRS_Elements_Idx n_stmt n_wit m d
    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.EK_s_pow i => poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_α_s_pow i => poly_α * poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_v i => to_COrdMvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_w i => to_COrdMvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_α_v i => poly_α * to_COrdMvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_α_w i => poly_α * to_COrdMvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_β_v i => poly_β_v * to_COrdMvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_β_w i => poly_β_w * to_COrdMvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.VK_1 => 1
      | SRS_Elements_Idx.VK_α => poly_α
      | SRS_Elements_Idx.VK_γ => poly_γ
      | SRS_Elements_Idx.VK_βv_γ => poly_β_v * poly_γ
      | SRS_Elements_Idx.VK_βw_γ => poly_β_w * poly_γ
      | SRS_Elements_Idx.VK_v_0 => to_COrdMvPolynomial_Option Vars v_0
      | SRS_Elements_Idx.VK_w_0 => to_COrdMvPolynomial_Option Vars w_0
      | SRS_Elements_Idx.VK_t => to_COrdMvPolynomial_Option Vars t
      | SRS_Elements_Idx.VK_v_stmt i => to_COrdMvPolynomial_Option Vars (v_stmt i)
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.EK_s_pow i => poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_α_s_pow i => poly_α * poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_v i => to_COrdMvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_w i => to_COrdMvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_α_v i => poly_α * to_COrdMvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_α_w i => poly_α * to_COrdMvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_β_v i => poly_β_v * to_COrdMvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_β_w i => poly_β_w * to_COrdMvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.VK_1 => 1
      | SRS_Elements_Idx.VK_α => poly_α
      | SRS_Elements_Idx.VK_γ => poly_γ
      | SRS_Elements_Idx.VK_βv_γ => poly_β_v * poly_γ
      | SRS_Elements_Idx.VK_βw_γ => poly_β_w * poly_γ
      | SRS_Elements_Idx.VK_v_0 => to_COrdMvPolynomial_Option Vars v_0
      | SRS_Elements_Idx.VK_w_0 => to_COrdMvPolynomial_Option Vars w_0
      | SRS_Elements_Idx.VK_t => to_COrdMvPolynomial_Option Vars t
      | SRS_Elements_Idx.VK_v_stmt i => to_COrdMvPolynomial_Option Vars (v_stmt i)
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
    -- For convenience we keep all proof elements on the same side of the pairing
    -- I : (v_0(s) + v_in(s) + V_mid(s)) * (w_0(s) + W) - t * H = 0
    -- II : V_mid' * 1 - V_mid * α = 0
    -- III : W' * 1 - α * W = 0
    -- IV : H' * 1 -  α * H = 0
    -- V : Y * 1 - V_mid * (βv γ) - (β_w γ) * W = 0
    verificationPairingSRS_G1 := fun stmt check_idx i SRS_idx => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_v_0 => 1
          | SRS_Elements_Idx.VK_v_stmt k => stmt k
          | _ => 0
        | PairingsI_Idx.rhs => match SRS_idx with
          | SRS_Elements_Idx.VK_t => 1
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
          | SRS_Elements_Idx.VK_α => 1
          | _ => 0
      | ChecksIdx.CheckIV => match i with
        | PairingsIV_Idx.lhs => match SRS_idx with
          | _ => 0
        | PairingsIV_Idx.rhs => match SRS_idx with
          | SRS_Elements_Idx.VK_α => 1
          | _ => 0
      | ChecksIdx.CheckV => match i with
        | PairingsV_Idx.lhs => match SRS_idx with
          | _ => 0
        | PairingsV_Idx.rhs1 => match SRS_idx with
          | _ => 0
        | PairingsV_Idx.rhs2 => match SRS_idx with
          | SRS_Elements_Idx.VK_βw_γ => 1
          | _ => 0
    verificationPairingSRS_G2 := fun _stmt check_idx i SRS_idx => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_w_0 => 1
          | _ => 0
        | PairingsI_Idx.rhs => 0
      | ChecksIdx.CheckII => match i with
        | PairingsII_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_1 => 1
          | _ => 0
        | PairingsII_Idx.rhs => match SRS_idx with
          | SRS_Elements_Idx.VK_α => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
      | ChecksIdx.CheckIII => match i with
        | PairingsIII_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_1 => 1
          | _ => 0
        | PairingsIII_Idx.rhs => match SRS_idx with
          | _ => 0
      | ChecksIdx.CheckIV => match i with
        | PairingsIV_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_1 => 1
          | _ => 0
        | PairingsIV_Idx.rhs => match SRS_idx with
          | _ => 0
      | ChecksIdx.CheckV => match i with
        | PairingsV_Idx.lhs => match SRS_idx with
          | SRS_Elements_Idx.VK_γ => 1
          | _ => 0
        | PairingsV_Idx.rhs1 => match SRS_idx with
          | SRS_Elements_Idx.VK_βv_γ => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
        | PairingsV_Idx.rhs2 => match SRS_idx with
          | _ => 0
    verificationPairingProof_G1 := fun _stmt check_idx i pf_idx => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.lhs => match pf_idx with
          | Proof_G1_Idx.V_mid => 1
          | _ => 0
        | PairingsI_Idx.rhs => match pf_idx with
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
          | Proof_G1_Idx.W' => 1
          | _ => 0
        | PairingsIII_Idx.rhs => match pf_idx with
          | _ => 0
      | ChecksIdx.CheckIV => match i with
        | PairingsIV_Idx.lhs => match pf_idx with
          | Proof_G1_Idx.H' => 1
          | _ => 0
        | PairingsIV_Idx.rhs => match pf_idx with
          | _ => 0
      | ChecksIdx.CheckV => match i with
        | PairingsV_Idx.lhs => match pf_idx with
          | Proof_G1_Idx.Y => 1
          | _ => 0
        | PairingsV_Idx.rhs1 => match pf_idx with
          | Proof_G1_Idx.V_mid => 1
          | _ => 0
        | PairingsV_Idx.rhs2 => match pf_idx with
          | _ => 0
    verificationPairingProof_G2 := fun _stmt check_idx i pf_idx => match check_idx with
      | ChecksIdx.CheckI => match i with
        | PairingsI_Idx.lhs => match pf_idx with
          | Proof_G2_Idx.W => 1
          | _ => 0
        | PairingsI_Idx.rhs => match pf_idx with
          | Proof_G2_Idx.H => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
      | ChecksIdx.CheckII => 0
      | ChecksIdx.CheckIII => match i with
        | PairingsIII_Idx.lhs => match pf_idx with
          | _ => 0
        | PairingsIII_Idx.rhs => match pf_idx with
          | Proof_G2_Idx.W => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
      | ChecksIdx.CheckIV => match i with
        | PairingsIV_Idx.lhs => match pf_idx with
          | _ => 0
        | PairingsIV_Idx.rhs => match pf_idx with
          | Proof_G2_Idx.H => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
      | ChecksIdx.CheckV => match i with
        | PairingsV_Idx.lhs => match pf_idx with
          | _ => 0
        | PairingsV_Idx.rhs1 => match pf_idx with
          | _ => 0
        | PairingsV_Idx.rhs2 => match pf_idx with
          | Proof_G2_Idx.W => -1 -- Negate the rhs Right elements to show they are moved to the left
          | _ => 0
    Identified_Proof_Elems := []
  }


end GGPR

end GGPR
