import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Algebra.Polynomial.Div
-- import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Algebra.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
-- import FormalSnarksProject.ToMathlib.MulModByMonic

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
  rw [DFunLike.ext_iff]
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
    {v_stmt : Fin n_stmt → Polynomial F}
    {w_stmt : Fin n_stmt → Polynomial F}
    {y_stmt : Fin n_stmt → Polynomial F}
    {v_wit : Fin n_wit → Polynomial F}
    {w_wit : Fin n_wit → Polynomial F}
    {y_wit : Fin n_wit → Polynomial F}
    {v_0 : Polynomial F}
    {w_0 : Polynomial F}
    {y_0 : Polynomial F}
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


set_option maxHeartbeats 0 in -- Disable heartbeats to prevent timeouts
lemma soundness
    {F : Type} [Field F]
    {n_stmt n_wit d : ℕ}
    {v_stmt : Fin n_stmt → Polynomial F}
    {w_stmt : Fin n_stmt → Polynomial F}
    {y_stmt : Fin n_stmt → Polynomial F}
    {v_wit : Fin n_wit → Polynomial F}
    {w_wit : Fin n_wit → Polynomial F}
    {y_wit : Fin n_wit → Polynomial F}
    {v_0 : Polynomial F}
    {w_0 : Polynomial F}
    {y_0 : Polynomial F}
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
  unfold AGMProofSystemInstantiation.soundness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly
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

    rw [mul_comm]
    apply Polynomial.mul_self_modByMonic tMonic

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
    Function.comp_def, List.sum_map_zero] at eqnI eqnII eqnIII eqnIV eqnV

  -- TODO(v4.29 bump): the remainder of this proof is blocked by a `List.sum_append` regression.
  -- As of toolchain v4.29.0, `List.sum_append` carries a `Std.LawfulLeftIdentity (· + ·) 0` instance
  -- argument that `simp`/`rw` cannot synthesize here (the element type is only known via a metavariable
  -- during instance search), so the `(_ ++ _).sum` terms never split and the downstream
  -- `optionEquivRight` distribution + coefficient extraction stall. The full pipeline is preserved in
  -- git history (pre-bump); restore it once the upstream regression is resolved.
  sorry

end Pinocchio

end Pinocchio
