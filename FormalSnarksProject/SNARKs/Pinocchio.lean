import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Data.Polynomial.Div
import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Data.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.ToMathlib.MulModByMonic

open scoped BigOperators Classical

section Pinocchio

open MvPolynomial Option AGMProofSystemInstantiation

namespace Pinocchio

inductive Vars : Type where
  | r_v : Vars
  | r_w : Vars
  | α_v : Vars
  | α_w : Vars
  | α_y : Vars
  | β : Vars
  | γ : Vars
deriving Repr, BEq

local notation "poly_r_v" => X (some Vars.r_v)
local notation "poly_r_w" => X (some Vars.r_w)
local notation "poly_α_v" => X (some Vars.α_v)
local notation "poly_α_w" => X (some Vars.α_w)
local notation "poly_α_y" => X (some Vars.α_y)
local notation "poly_β" => X (some Vars.β)
local notation "poly_γ" => X (some Vars.γ)
local notation "poly_s" => X (none)

lemma Vars.finsupp_eq_ext (f g : Vars →₀ ℕ) : f = g ↔
    f Vars.r_v = g Vars.r_v
    ∧ f Vars.r_w = g Vars.r_w
    ∧ f Vars.α_v = g Vars.α_v
    ∧ f Vars.α_w = g Vars.α_w
    ∧ f Vars.α_y = g Vars.α_y
    ∧ f Vars.β = g Vars.β
    ∧ f Vars.γ = g Vars.γ := by
  rw [FunLike.ext_iff]
  constructor
  · intro h
    simp_rw [h]
    simp only [and_self]
  · intro h x
    cases x <;> tauto

-- Pinnochi is a Type I SNARK, so in theorey any proof element can be given on the left.
-- The W_mid is the only proof element used on both sides.
-- We later introduce an artificial equation to guarantee that the W_mid is the same on both sides.
inductive Proof_G1_Idx : Type where
  | V_mid : Proof_G1_Idx
  | V_mid' : Proof_G1_Idx
  | W_mid : Proof_G1_Idx
  | W_mid' : Proof_G1_Idx
  | Y_mid : Proof_G1_Idx
  | Y_mid' : Proof_G1_Idx
  | Z : Proof_G1_Idx

inductive Proof_G2_Idx : Type where
  | W_mid : Proof_G2_Idx
  | H : Proof_G2_Idx

inductive ChecksIdx : Type where
  | CheckI : ChecksIdx
  | CheckII : ChecksIdx
  | CheckIII : ChecksIdx
  | CheckIV : ChecksIdx
  | CheckV : ChecksIdx

inductive PairingsI_Idx : Type where
  | lhs : PairingsI_Idx
  | rhs1 : PairingsI_Idx
  | rhs2 : PairingsI_Idx

inductive PairingsII_Idx : Type where
  | lhs : PairingsII_Idx
  | rhs : PairingsII_Idx

inductive PairingsIII_Idx : Type where
  | lhs : PairingsIII_Idx
  | rhs : PairingsIII_Idx

inductive PairingsIV_Idx : Type where
  | lhs : PairingsIV_Idx
  | rhs : PairingsIV_Idx

inductive PairingsV_Idx : Type where
  | lhs : PairingsV_Idx
  | rhs : PairingsV_Idx


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

set_option maxHeartbeats 0 -- Disable heartbeats to prevent timeouts

noncomputable def Pinocchio
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F]
    /- The naturals representing:
      m - m from paper - The QAP size
      n_in - n from paper - the number of inputs
      n_out - n' from paper - the number of outputs
      n_mid - (m - N) from paper - the number of internal gates
      d - the degree of h -/
    {n_stmt n_wit d : ℕ}
    -- -- N from paper
    -- {n_stmt : ℕ := n_in + n_out}
    -- -- Alternative names
    -- def n_wit := n_mid
    -- def m := n_stmt + n_wit
    /- fin-indexed collections of polynomials from the quadratic arithmetic program -/
    {v_stmt : Fin n_stmt → Polynomial F }
    {w_stmt : Fin n_stmt → Polynomial F }
    {y_stmt : Fin n_stmt → Polynomial F }
    {v_wit : Fin n_wit → Polynomial F }
    {w_wit : Fin n_wit → Polynomial F }
    {y_wit : Fin n_wit → Polynomial F }
    {v_0 : Polynomial F }
    {w_0 : Polynomial F }
    {y_0 : Polynomial F }
    /- t is the polynomial divisibility by which is used to verify satisfaction of the QAP -/
    {t : Polynomial F}
    -- t can also be expressed as follows, but this structure is not important for soundness
    -- {r : Fin (n_wit) → F}
    -- let t : Polynomial F := ∏ i : Fin n_wit in Fingeneralize.univ, (Polynomial.X - Polynomial.C (r i)
    :
    AGMProofSystemInstantiation F :=
  { Stmt := Fin n_stmt → F
    Sample := Option Vars
    SRSElements_G1 := @SRS_Elements_Idx n_stmt n_wit d
    ListSRSElements_G1 :=
      ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_v i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_w i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_y i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_α_v i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_α_w i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_α_y i)
      ++ ((List.finRange d).map fun i => SRS_Elements_Idx.EK_s_pow i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_β_v_w_y i)
      ++ [SRS_Elements_Idx.VK_1, SRS_Elements_Idx.VK_α_v, SRS_Elements_Idx.VK_α_w, SRS_Elements_Idx.VK_α_y, SRS_Elements_Idx.VK_γ, SRS_Elements_Idx.VK_βγ, SRS_Elements_Idx.VK_t, SRS_Elements_Idx.VK_v_0, SRS_Elements_Idx.VK_w_0, SRS_Elements_Idx.VK_y_0]
      ++ ((List.finRange n_stmt).map fun i => SRS_Elements_Idx.VK_v_stmt i)
      ++ ((List.finRange n_stmt).map fun i => SRS_Elements_Idx.VK_w_stmt i)
      ++ ((List.finRange n_stmt).map fun i => SRS_Elements_Idx.VK_y_stmt i)
    -- Note that Pinochio is a Type I SNARK - all SRS elements appear in both groups of the pairing
    SRSElements_G2 := @SRS_Elements_Idx n_stmt n_wit d
    ListSRSElements_G2 :=
      ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_v i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_w i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_y i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_α_v i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_α_w i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_α_y i)
      ++ ((List.finRange d).map fun i => SRS_Elements_Idx.EK_s_pow i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_β_v_w_y i)
      ++ [SRS_Elements_Idx.VK_1, SRS_Elements_Idx.VK_α_v, SRS_Elements_Idx.VK_α_w, SRS_Elements_Idx.VK_α_y, SRS_Elements_Idx.VK_γ, SRS_Elements_Idx.VK_βγ, SRS_Elements_Idx.VK_t, SRS_Elements_Idx.VK_v_0, SRS_Elements_Idx.VK_w_0, SRS_Elements_Idx.VK_y_0]
      ++ ((List.finRange n_stmt).map fun i => SRS_Elements_Idx.VK_v_stmt i)
      ++ ((List.finRange n_stmt).map fun i => SRS_Elements_Idx.VK_w_stmt i)
      ++ ((List.finRange n_stmt).map fun i => SRS_Elements_Idx.VK_y_stmt i)

    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.EK_v i => poly_r_v * to_MvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_w i => poly_r_w * to_MvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_y i => poly_r_v * poly_r_w * to_MvPolynomial_Option Vars (y_wit i)
      | SRS_Elements_Idx.EK_α_v i => poly_r_v * poly_α_v * to_MvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_α_w i => poly_r_w * poly_α_w * to_MvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_α_y i => poly_r_v * poly_r_w * poly_α_y * to_MvPolynomial_Option Vars (y_wit i)
      | SRS_Elements_Idx.EK_s_pow i => poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_β_v_w_y i => poly_β * (poly_r_v * to_MvPolynomial_Option Vars (v_wit i) + poly_r_w * to_MvPolynomial_Option Vars (w_wit i) + poly_r_v * poly_r_w * to_MvPolynomial_Option Vars (y_wit i))
      | SRS_Elements_Idx.VK_1 => 1
      | SRS_Elements_Idx.VK_α_v => poly_α_v
      | SRS_Elements_Idx.VK_α_w => poly_α_w
      | SRS_Elements_Idx.VK_α_y => poly_α_y
      | SRS_Elements_Idx.VK_γ => poly_γ
      | SRS_Elements_Idx.VK_βγ => poly_β * poly_γ
      | SRS_Elements_Idx.VK_t => poly_r_v * poly_r_w * to_MvPolynomial_Option Vars t
      | SRS_Elements_Idx.VK_v_0 => poly_r_v * to_MvPolynomial_Option Vars v_0
      | SRS_Elements_Idx.VK_w_0 => poly_r_w * to_MvPolynomial_Option Vars w_0
      | SRS_Elements_Idx.VK_y_0 => poly_r_v * poly_r_w * to_MvPolynomial_Option Vars y_0
      | SRS_Elements_Idx.VK_v_stmt i => poly_r_v * to_MvPolynomial_Option Vars (v_stmt i)
      | SRS_Elements_Idx.VK_w_stmt i => poly_r_w * to_MvPolynomial_Option Vars (w_stmt i)
      | SRS_Elements_Idx.VK_y_stmt i => poly_r_v * poly_r_w * to_MvPolynomial_Option Vars (y_stmt i)


    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.EK_v i => poly_r_v * to_MvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_w i => poly_r_w * to_MvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_y i => poly_r_v * poly_r_w * to_MvPolynomial_Option Vars (y_wit i)
      | SRS_Elements_Idx.EK_α_v i => poly_r_v * poly_α_v * to_MvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_α_w i => poly_r_w * poly_α_w * to_MvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_α_y i => poly_r_v * poly_r_w * poly_α_y * to_MvPolynomial_Option Vars (y_wit i)
      | SRS_Elements_Idx.EK_s_pow i => poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_β_v_w_y i => poly_β * (poly_r_v * to_MvPolynomial_Option Vars (v_wit i) + poly_r_w * to_MvPolynomial_Option Vars (w_wit i) + poly_r_v * poly_r_w * to_MvPolynomial_Option Vars (y_wit i))
      | SRS_Elements_Idx.VK_1 => 1
      | SRS_Elements_Idx.VK_α_v => poly_α_v
      | SRS_Elements_Idx.VK_α_w => poly_α_w
      | SRS_Elements_Idx.VK_α_y => poly_α_y
      | SRS_Elements_Idx.VK_γ => poly_γ
      | SRS_Elements_Idx.VK_βγ => poly_β * poly_γ
      | SRS_Elements_Idx.VK_t => poly_r_v * poly_r_w * to_MvPolynomial_Option Vars t
      | SRS_Elements_Idx.VK_v_0 => poly_r_v * to_MvPolynomial_Option Vars v_0
      | SRS_Elements_Idx.VK_w_0 => poly_r_w * to_MvPolynomial_Option Vars w_0
      | SRS_Elements_Idx.VK_y_0 => poly_r_v * poly_r_w * to_MvPolynomial_Option Vars y_0
      | SRS_Elements_Idx.VK_v_stmt i => poly_r_v * to_MvPolynomial_Option Vars (v_stmt i)
      | SRS_Elements_Idx.VK_w_stmt i => poly_r_w * to_MvPolynomial_Option Vars (w_stmt i)
      | SRS_Elements_Idx.VK_y_stmt i => poly_r_v * poly_r_w * to_MvPolynomial_Option Vars (y_stmt i)

    Proof_G1 := Proof_G1_Idx
    ListProof_G1 := [Proof_G1_Idx.V_mid, Proof_G1_Idx.V_mid', Proof_G1_Idx.W_mid, Proof_G1_Idx.W_mid', Proof_G1_Idx.Y_mid, Proof_G1_Idx.Y_mid', Proof_G1_Idx.Z]
    Proof_G2 := Proof_G2_Idx
    ListProof_G2 := [Proof_G2_Idx.W_mid, Proof_G2_Idx.H]
    EqualityChecks := ChecksIdx
    Pairings := fun check_idx => match check_idx with
      | ChecksIdx.CheckI => PairingsI_Idx
      | ChecksIdx.CheckII => PairingsII_Idx
      | ChecksIdx.CheckIII => PairingsIII_Idx
      | ChecksIdx.CheckIV => PairingsIV_Idx
      | ChecksIdx.CheckV => PairingsV_Idx
    ListPairings := fun check_idx => match check_idx with
      | ChecksIdx.CheckI => [PairingsI_Idx.lhs, PairingsI_Idx.rhs1, PairingsI_Idx.rhs2]
      | ChecksIdx.CheckII => [PairingsII_Idx.lhs, PairingsII_Idx.rhs]
      | ChecksIdx.CheckIII => [PairingsIII_Idx.lhs, PairingsIII_Idx.rhs]
      | ChecksIdx.CheckIV => [PairingsIV_Idx.lhs, PairingsIV_Idx.rhs]
      | ChecksIdx.CheckV => [PairingsV_Idx.lhs, PairingsV_Idx.rhs]
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
    verificationPairingProof_G1 := fun stmt check_idx i pf_idx => match check_idx with
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
    verificationPairingProof_G2 := fun stmt check_idx i pf_idx => match check_idx with
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


lemma soundness
    {F : Type} [Field F]
    {n_stmt n_wit d : ℕ}
    {v_stmt : Fin n_stmt → Polynomial F }
    {w_stmt : Fin n_stmt → Polynomial F }
    {y_stmt : Fin n_stmt → Polynomial F }
    {v_wit : Fin n_wit → Polynomial F }
    {w_wit : Fin n_wit → Polynomial F }
    {y_wit : Fin n_wit → Polynomial F }
    {v_0 : Polynomial F }
    {w_0 : Polynomial F }
    {y_0 : Polynomial F }
    /- t is the polynomial divisibility by which is used to verify satisfaction of the QAP -/
    {t : Polynomial F}
    (tMonic : t.Monic)
    -- t can also be expressed as follows, but this structure is not important for soundness
    -- {r : Fin (n_wit) → F}
    -- let t : Polynomial F := ∏ i : Fin n_wit in Fingeneralize.univ, (Polynomial.X - Polynomial.C (r i)
    :
    (AGMProofSystemInstantiation.soundness
      F
      (@Pinocchio F _ n_stmt n_wit d
        v_stmt w_stmt y_stmt
        v_wit w_wit y_wit
        v_0 w_0 y_0
        t)
      (Fin n_wit → F)
      (fun (stmt : Fin n_stmt → F) (wit : Fin n_wit -> F) =>
        (-- Definition 2 from Pinocchio
          (v_0
            + (List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * v_wit i) (List.finRange n_wit)))
          )
        *
          (w_0
            + (List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * w_wit i) (List.finRange n_wit)))
          )
        -
          (y_0
            + (List.sum (List.map (fun i => Polynomial.C (stmt i) * y_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * y_wit i) (List.finRange n_wit)))
          )
        )
          %ₘ t = 0)
        ( fun prover i => prover.fst Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y i) )
    ) := by
  unfold soundness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly
  -- TODO namespcace AGMProofSystemInstantiation eliminate
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, eqnVI⟩
  -- If t is provided via a let binding it should be introduced here by intro t
  have eqnI := eqns ChecksIdx.CheckI
  have eqnII := eqns ChecksIdx.CheckII
  have eqnIII := eqns ChecksIdx.CheckIII
  have eqnIV := eqns ChecksIdx.CheckIV
  have eqnV := eqns ChecksIdx.CheckV
  clear eqns eqnVI

  -- Simplify the equation
  suffices
      (
          (v_0
            + (List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y i)) * v_wit i) (List.finRange n_wit)))
          )
        *
          (w_0
            + (List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y i)) * w_wit i) (List.finRange n_wit)))
          )
        -
          (y_0
            + (List.sum (List.map (fun i => Polynomial.C (stmt i) * y_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y i)) * y_wit i) (List.finRange n_wit)))
          )
      )
      =
      (List.sum (List.map (fun x : Fin d => Polynomial.C (prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.EK_s_pow x)) * (Polynomial.X ^ (x : ℕ))) (List.finRange (d)))) * t by

    -- rw [<-sub_eq_iff_eq_add'] at this
    have h := congr_arg (fun x => x %ₘ t) this
    simp only at h
    simp
    rw [h]
    clear this h

    simp only [mul_comm _ (t), <-mul_assoc]
    -- simp only [mul_assoc, List.sum_map_mul_right, List.sum_map_mul_left]

    apply Polynomial.mul_modByMonic t _ tMonic
    done

  -- done


  simp_rw [Pinocchio] at eqnI eqnII eqnIII eqnIV eqnV

  -- All I want is a tactic that will apply the following simplifications to eqn in sequence.
  -- TODO can I write a tactic taking a nested list of simp lemmas?
  -- Can I combine all of these?
  simp only [monomial_zero', List.singleton_append, List.cons_append, List.append_assoc,
    List.map_cons, Sum.elim_inl, Sum.elim_inr, List.map_append, List.map_map, List.sum_cons,
    List.sum_append, List.map_nil, List.sum_nil, add_zero, Sum.elim_lam_const_lam_const, map_one,
    one_mul, map_zero, zero_mul, map_neg, neg_mul, neg_add_rev, zero_add, mul_zero,
    -- Note: everything above is @simp tagged
    Function.comp, List.sum_map_zero] at eqnI eqnII eqnIII eqnIV eqnV

  simp only [mul_add, add_mul, List.sum_map_add] at eqnI eqnII eqnIII eqnIV eqnV

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
    List.sum_map_mul_right, List.sum_map_mul_left] at eqnI eqnII eqnIII eqnIV eqnV

  -- Apply MvPolynomial.optionEquivRight *here*, so that we can treat polynomials in Vars_X as constants
  trace "Converting to MvPolynomial over Polynomials"
  -- replace eqn := congr_arg (MvPolynomial.optionEquivRight F Vars) eqn
  simp only [←(EquivLike.apply_eq_iff_eq (optionEquivRight _ _))] at eqnI eqnII eqnIII eqnIV eqnV
  simp only [AlgEquiv.map_add, AlgEquiv.map_zero, AlgEquiv.map_mul, AlgEquiv.map_one,
    AlgEquiv.map_neg, AlgEquiv.list_map_sum, AlgEquiv.map_pow] at eqnI eqnII eqnIII eqnIV eqnV
  simp only [optionEquivRight_C, optionEquivRight_X_none, optionEquivRight_X_some, optionEquivRight_to_MvPolynomial_Option] at eqnI eqnII eqnIII eqnIV eqnV

  -- Move Cs back out so we can recognize the monomials
  simp only [←C_mul, ←C_pow, ←C_add,
    sum_map_C] at eqnI eqnII eqnIII eqnIV eqnV

  simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add, add_mul] at eqnI eqnII eqnIII eqnIV eqnV

  -- done

  trace "Applying individual coefficients"

  have h1eqnI    := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1)) eqnI
  have h11eqnII  := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnII
  have h19eqnII  := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.γ 1)) eqnII
  have h21eqnII  := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.r_w 1 + Finsupp.single Vars.β 1)) eqnII
  have h22eqnII  := congr_arg (coeff (Finsupp.single Vars.α_v 2)) eqnII
  have h32eqnII  := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.α_w 1)) eqnII
  have h38eqnII  := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1 + Finsupp.single Vars.β 1)) eqnII
  have h52eqnII  := congr_arg (coeff (Finsupp.single Vars.α_v 2 + Finsupp.single Vars.r_v 1)) eqnII
  have h54eqnII  := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.α_y 1)) eqnII
  have h71eqnII  := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.r_w 1)) eqnII
  have h74eqnII  := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.r_v 1 + Finsupp.single Vars.β 1)) eqnII
  have h93eqnII  := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1)) eqnII
  have h94eqnII := congr_arg (coeff (Finsupp.single Vars.α_w 1 + Finsupp.single Vars.r_w 1 + Finsupp.single Vars.α_v 1)) eqnII
  have h101eqnII := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1 + Finsupp.single Vars.α_y 1)) eqnII
  have h27eqnIII := congr_arg (coeff (Finsupp.single Vars.α_w 1 + Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1)) eqnIII
  have h32eqnIII := congr_arg (coeff (Finsupp.single Vars.α_w 1 + Finsupp.single Vars.α_v 1)) eqnIII
  have h33eqnIII := congr_arg (coeff (Finsupp.single Vars.α_w 1 + Finsupp.single Vars.r_w 1)) eqnIII
  have h34eqnIII := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.α_w 1 + Finsupp.single Vars.β 1)) eqnIII
  have h35eqnIII := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1 + Finsupp.single Vars.α_w 1 + Finsupp.single Vars.α_y 1)) eqnIII
  have h53eqnIII := congr_arg (coeff (Finsupp.single Vars.α_w 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnIII
  have h61eqnIII := congr_arg (coeff (Finsupp.single Vars.α_w 1 + Finsupp.single Vars.γ 1)) eqnIII
  have h75eqnIII := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1 + Finsupp.single Vars.α_w 1 + Finsupp.single Vars.β 1)) eqnIII
  have h81eqnIII := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.α_w 1)) eqnIII
  have h88eqnIII := congr_arg (coeff (Finsupp.single Vars.r_w 1 + Finsupp.single Vars.α_w 1 + Finsupp.single Vars.β 1)) eqnIII
  have h89eqnIII := congr_arg (coeff (Finsupp.single Vars.α_w 1 + Finsupp.single Vars.α_y 1)) eqnIII
  have h96eqnIII := congr_arg (coeff (Finsupp.single Vars.α_w 2)) eqnIII
  have h97eqnIII := congr_arg (coeff (Finsupp.single Vars.α_w 2 + Finsupp.single Vars.r_w 1)) eqnIII
  have h98eqnIII := congr_arg (coeff (Finsupp.single Vars.α_w 1 + Finsupp.single Vars.α_v 1 + Finsupp.single Vars.r_v 1)) eqnIII
  have h2eqnIV := congr_arg (coeff (Finsupp.single Vars.r_w 1 + Finsupp.single Vars.α_y 1 + Finsupp.single Vars.β 1)) eqnIV
  have h4eqnIV := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.α_v 1 + Finsupp.single Vars.α_y 1)) eqnIV
  have h23eqnIV := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1 + Finsupp.single Vars.α_y 2)) eqnIV
  have h25eqnIV := congr_arg (coeff (Finsupp.single Vars.r_w 1 + Finsupp.single Vars.α_w 1 + Finsupp.single Vars.α_y 1)) eqnIV
  have h30eqnIV := congr_arg (coeff (Finsupp.single Vars.α_y 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnIV
  have h37eqnIV := congr_arg (coeff (Finsupp.single Vars.α_y 1 + Finsupp.single Vars.γ 1)) eqnIV
  have h54eqnIV := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.α_y 1)) eqnIV
  have h55eqnIV := congr_arg (coeff (Finsupp.single Vars.r_w 1 + Finsupp.single Vars.α_y 1)) eqnIV
  have h56eqnIV := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1 + Finsupp.single Vars.α_y 1 + Finsupp.single Vars.β 1)) eqnIV
  have h57eqnIV := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.α_y 1 + Finsupp.single Vars.β 1)) eqnIV
  have h59eqnIV := congr_arg (coeff (Finsupp.single Vars.α_y 2)) eqnIV
  have h89eqnIV := congr_arg (coeff (Finsupp.single Vars.α_w 1 + Finsupp.single Vars.α_y 1)) eqnIV
  have h102eqnIV := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.α_y 1)) eqnIV
  have h2eqnV := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnV
  have h3eqnV := congr_arg (coeff (Finsupp.single Vars.r_w 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnV
  have h4eqnV := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnV


  clear eqnI
  clear eqnII
  clear eqnIII
  clear eqnIV
  clear eqnV

  trace "Distribute coefficient-taking over terms"
  simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h1eqnI h11eqnII h19eqnII h21eqnII h22eqnII h32eqnII h38eqnII h52eqnII h54eqnII h71eqnII h74eqnII h93eqnII h94eqnII h101eqnII h27eqnIII h32eqnIII h33eqnIII h34eqnIII h35eqnIII h53eqnIII h61eqnIII h75eqnIII h81eqnIII h88eqnIII h89eqnIII h96eqnIII h97eqnIII h98eqnIII h2eqnIV h4eqnIV h23eqnIV h25eqnIV h30eqnIV h37eqnIV h54eqnIV h55eqnIV h56eqnIV h57eqnIV h59eqnIV h89eqnIV h102eqnIV h2eqnV h3eqnV h4eqnV

  trace "Simplifying coefficient expressions"
  simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply] at h1eqnI h11eqnII h19eqnII h21eqnII h22eqnII h32eqnII h38eqnII h52eqnII h54eqnII h71eqnII h74eqnII h93eqnII h94eqnII h101eqnII h27eqnIII h32eqnIII h33eqnIII h34eqnIII h35eqnIII h53eqnIII h61eqnIII h75eqnIII h81eqnIII h88eqnIII h89eqnIII h96eqnIII h97eqnIII h98eqnIII h2eqnIV h4eqnIV h23eqnIV h25eqnIV h30eqnIV h37eqnIV h54eqnIV h55eqnIV h56eqnIV h57eqnIV h59eqnIV h89eqnIV h102eqnIV h2eqnV h3eqnV h4eqnV

  trace "Determine which coefficients are nonzero"
  simp (config := {decide := true}) only [ite_false, ite_true] at h1eqnI h11eqnII h19eqnII h21eqnII h22eqnII h32eqnII h38eqnII h52eqnII h54eqnII h71eqnII h74eqnII h93eqnII h94eqnII h101eqnII h27eqnIII h32eqnIII h33eqnIII h34eqnIII h35eqnIII h53eqnIII h61eqnIII h75eqnIII h81eqnIII h88eqnIII h89eqnIII h96eqnIII h97eqnIII h98eqnIII h2eqnIV h4eqnIV h23eqnIV h25eqnIV h30eqnIV h37eqnIV h54eqnIV h55eqnIV h56eqnIV h57eqnIV h59eqnIV h89eqnIV h102eqnIV h2eqnV h3eqnV h4eqnV
  trace "Remove zeros"
  simp only [neg_zero, add_zero, zero_add, neg_eq_zero] at h1eqnI h11eqnII h19eqnII h21eqnII h22eqnII h32eqnII h38eqnII h52eqnII h54eqnII h71eqnII h74eqnII h93eqnII h94eqnII h101eqnII h27eqnIII h32eqnIII h33eqnIII h34eqnIII h35eqnIII h53eqnIII h61eqnIII h75eqnIII h81eqnIII h88eqnIII h89eqnIII h96eqnIII h97eqnIII h98eqnIII h2eqnIV h4eqnIV h23eqnIV h25eqnIV h30eqnIV h37eqnIV h54eqnIV h55eqnIV h56eqnIV h57eqnIV h59eqnIV h89eqnIV h102eqnIV h2eqnV h3eqnV h4eqnV

  -- done
  simp? [*, -map_eq_zero, -Polynomial.C_eq_zero] at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_w x)) * w_wit x) (List.finRange n_wit)) = sum_V_mid_w_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_v x)) * v_wit x) (List.finRange n_wit)) = sum_V_mid_v_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.EK_v x)) * v_wit x) (List.finRange n_wit)) = sum_W_mid_v_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.EK_w x)) * w_wit x) (List.finRange n_wit)) = sum_W_mid_w_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_s_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange d)) = sum_V_mid_s_pow at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.EK_s_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange d)) = sum_W_mid_s_pow at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.H (SRS_Elements_Idx.EK_s_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange d)) = sum_H_s_pow at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_w x)) * w_wit x) (List.finRange n_wit)) = sum_Y_mid_w_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_v x)) * v_wit x) (List.finRange n_wit)) = sum_Y_mid_v_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_s_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange d)) = sum_Y_mid_s_pow at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_β_v_w_y x)) * v_wit x) (List.finRange n_wit)) = sum_V_mid_EK_β_v_w_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_α_v x)) * v_wit x) (List.finRange n_wit)) = sum_V_mid_EK_α_v at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_y x)) * y_wit x) (List.finRange n_wit)) = sum_V_mid_EK_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.VK_y_stmt x)) * y_stmt x) (List.finRange n_stmt)) = sum_V_mid_VK_y_stmt at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_α_w x)) * w_wit x) (List.finRange n_wit)) = sum_V_mid_EK_α_w at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_α_y x)) * y_wit x) (List.finRange n_wit)) = sum_V_mid_EK_α_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.EK_y x)) * y_wit x) (List.finRange n_wit)) = sum_W_mid_EK_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.VK_y_stmt x)) * y_stmt x) (List.finRange n_stmt)) = sum_W_mid_VK_y_stmt at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid' (SRS_Elements_Idx.EK_α_w x)) * w_wit x) (List.finRange n_wit)) = sum_W_mid'_EK_α_w at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_w x)) * w_wit x) (List.finRange n_wit)) = sum_W_mid_EK_w at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.VK_w_stmt x)) * w_stmt x) (List.finRange n_stmt)) = sum_W_mid_VK_w_stmt at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_β_v_w_y x)) * w_wit x) (List.finRange n_wit)) = sum_W_mid_EK_β_v_w_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_α_y x)) * y_wit x) (List.finRange n_wit)) = sum_W_mid_EK_α_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_v x)) * v_wit x) (List.finRange n_wit)) = sum_W_mid_EK_v at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.VK_v_stmt x)) * v_stmt x) (List.finRange n_stmt)) = sum_W_mid_VK_v_stmt at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_α_w x)) * w_wit x) (List.finRange n_wit)) = sum_W_mid_EK_α_w at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_α_v x)) * v_wit x) (List.finRange n_wit)) = sum_W_mid_EK_α_v at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_β_v_w_y x)) * v_wit x) (List.finRange n_wit)) = sum_Y_mid_EK_β_v_w_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_α_v x)) * v_wit x) (List.finRange n_wit)) = sum_Y_mid_EK_α_v at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_α_y x)) * y_wit x) (List.finRange n_wit)) = sum_Y_mid_EK_α_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_α_w x)) * w_wit x) (List.finRange n_wit)) = sum_Y_mid_EK_α_w at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_w x)) * w_wit x) (List.finRange n_wit)) = sum_Y_mid_EK_w at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.VK_w_stmt x)) * w_stmt x) (List.finRange n_stmt)) = sum_Y_mid_VK_w_stmt at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_v x)) * v_wit x) (List.finRange n_wit)) = sum_Y_mid_EK_v at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.VK_v_stmt x)) * v_stmt x) (List.finRange n_stmt)) = sum_Y_mid_VK_v_stmt at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y x)) * v_wit x) (List.finRange n_wit)) = sum_Z_EK_β_v_w_y_v_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y x)) * w_wit x) (List.finRange n_wit)) = sum_Z_EK_β_v_w_y_w_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y x)) * y_wit x) (List.finRange n_wit)) = sum_Z_EK_β_v_w_y_y_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_β_v_w_y x)) * w_wit x) (List.finRange n_wit)) = sum_V_mid_EK_β_v_w_y_w_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_β_v_w_y x)) * y_wit x) (List.finRange n_wit)) = sum_V_mid_EK_β_v_w_y_y_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_y x)) * y_wit x) (List.finRange n_wit)) = sum_W_mid_EK_y_y_wit at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_y x)) * y_wit x) (List.finRange n_wit)) = sum_Y_mid_EK_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.VK_y_stmt x)) * y_stmt x) (List.finRange n_stmt)) = sum_Y_mid_VK_y_stmt at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.VK_v_stmt x)) * v_stmt x) (List.finRange n_stmt)) = sum_V_mid_VK_v_stmt at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.VK_w_stmt x)) * w_stmt x) (List.finRange n_stmt)) = sum_V_mid_VK_w_stmt at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.VK_y_stmt x)) * y_stmt x) (List.finRange n_stmt)) = sum_G1_W_mid_VK_y_stmt at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_β_v_w_y x)) * v_wit x) (List.finRange n_wit)) = sum_W_mid_EK_β_v_w_y_v_wit at *
  generalize  List.sum
    (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_β_v_w_y x)) * y_wit x)
      (List.finRange n_wit)) = sum_W_mid_EK_β_v_w_y_y_wit at *
  generalize  List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_β_v_w_y x)) * w_wit x)
      (List.finRange n_wit))  = sum_Y_mid_EK_β_v_w_y_w_wit at *
  generalize  List.sum
    (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_β_v_w_y x)) * y_wit x)
      (List.finRange n_wit)) = sum_Y_mid_EK_β_v_w_y_y_wit at *

  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_t) = V_mid_VK_t at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_y_0) = V_mid_VK_y_0 at *
  generalize Polynomial.C (prover.2 Proof_G2_Idx.W_mid SRS_Elements_Idx.VK_t) = G2_W_mid_VK_t at *
  generalize Polynomial.C (prover.2 Proof_G2_Idx.W_mid SRS_Elements_Idx.VK_y_0) = G2_W_mid_VK_y_0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_w_0) = W_mid_VK_w_0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_v_0) = W_mid_VK_v_0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_w_0) = Y_mid_VK_w_0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_v_0) = Y_mid_VK_v_0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_t) = Y_mid_VK_t at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_y_0) = Y_mid_VK_y_0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_v_0) = V_mid_VK_v_0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_βγ) = V_mid_VK_βγ at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_γ) = V_mid_VK_γ at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_α_v) = V_mid_VK_α_v at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_α_w) = V_mid_VK_α_w at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_α_y) = V_mid_VK_α_y at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_t) = G1_W_mid_VK_t at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_y_0) = G1_W_mid_VK_y_0 at *

  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_α_v) = W_mid_VK_α_v at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_βγ) = W_mid_VK_βγ at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_γ) = W_mid_VK_γ at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_α_y) = W_mid_VK_α_y at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_α_w) = W_mid_VK_α_w at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_βγ) = Y_mid_VK_βγ at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_γ) = Y_mid_VK_γ at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_α_v) = Y_mid_VK_α_v at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_α_y) = Y_mid_VK_α_y at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_α_w) = Y_mid_VK_α_w at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_w_0) * w_0 = V_mid_VK_w_0 at *


  generalize List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)) = sum_stmt_v_stmt at *
  generalize List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)) = sum_stmt_w_stmt at *
  generalize List.sum (List.map (fun i => Polynomial.C (stmt i) * y_stmt i) (List.finRange n_stmt)) = sum_stmt_y_stmt at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.VK_v_stmt x)) * v_stmt x) (List.finRange n_stmt)) = sum_W_mid_VK_v_stmt at *
  generalize Polynomial.C (prover.2 Proof_G2_Idx.W_mid SRS_Elements_Idx.VK_1) = W_mid_VK_1 at *

  clear  h11eqnII h19eqnII h22eqnII h32eqnII h54eqnII h32eqnIII h53eqnIII h61eqnIII h89eqnIII h96eqnIII h30eqnIV h37eqnIV h54eqnIV h59eqnIV h89eqnIV h74eqnII h52eqnII h94eqnII h101eqnII h88eqnIII h35eqnIII h97eqnIII h98eqnIII h57eqnIV h4eqnIV h23eqnIV h25eqnIV h21eqnII h38eqnII h34eqnIII h75eqnIII h2eqnIV h56eqnIV


  clear tMonic

  simp [this, -map_eq_zero, -Polynomial.C_eq_zero] at *
  -- polyrith -- error: not in ideal
  integral_domain_tactic <;> sorry
  -- TODO there must be some kind of bug in the representation

  done
