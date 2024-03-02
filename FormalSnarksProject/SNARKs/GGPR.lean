import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Data.Polynomial.Div
import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Data.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode


open scoped BigOperators Classical

section GGPR

open MvPolynomial Option

namespace GGPR

inductive Vars : Type where
  | α : Vars
  | β_v : Vars
  | β_w : Vars
  | β_y : Vars
  | γ : Vars
deriving Repr, BEq

local notation "poly_α" => X (some Vars.α)
local notation "poly_β_v" => X (some Vars.β_v)
local notation "poly_β_w" => X (some Vars.β_w)
local notation "poly_β_y" => X (some Vars.β_y)
local notation "poly_γ" => X (some Vars.γ)
local notation "poly_s" => X (none)

lemma Vars.finsupp_eq_ext (f g : Vars →₀ ℕ) : f = g ↔
    f Vars.α = g Vars.α
    ∧ f Vars.β_v = g Vars.β_v
    ∧ f Vars.β_w = g Vars.β_w
    ∧ f Vars.β_y = g Vars.β_y
    ∧ f Vars.γ = g Vars.γ := by
  rw [FunLike.ext_iff]
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

inductive Proof_G2_Idx : Type where
  | W : Proof_G2_Idx
  | H : Proof_G2_Idx

inductive ChecksIdx : Type where
  | CheckI : ChecksIdx
  | CheckII : ChecksIdx
  | CheckIII : ChecksIdx
  | CheckIV : ChecksIdx
  | CheckV : ChecksIdx

inductive PairingsI_Idx : Type where
  | lhs : PairingsI_Idx
  | rhs : PairingsI_Idx

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
  | rhs1 : PairingsV_Idx
  | rhs2 : PairingsV_Idx


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

set_option maxHeartbeats 0 -- Disable heartbeats to prevent timeouts

noncomputable def GGPR
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F]
    /- The naturals representing:
      m - m from paper - The QAP size
      n_in - n from paper - the number of inputs
      n_out - n' from paper - the number of outputs
      n_mid - (m - N) from paper - the number of internal gates
      d - the degree of h -/
    {n_stmt n_wit m d : ℕ}
    -- -- N from paper
    -- {n_stmt : ℕ := n_in + n_out}
    -- -- Alternative names
    -- def n_wit := n_mid
    -- def m := n_stmt + n_wit
    /- fin-indexed collections of polynomials from the quadratic arithmetic program -/
    {v_stmt : Fin n_stmt → Polynomial F }
    {v_wit : Fin n_wit → Polynomial F }
    {w_wit : Fin m → Polynomial F }
    {v_0 : Polynomial F }
    {w_0 : Polynomial F }
    /- The roots of the polynomial t -/
    {r : Fin (n_wit) → F} :
    AGMProofSystemInstantiation F :=

  /- t is the polynomial divisibility by which is used to verify satisfaction of the QAP -/
  let t : Polynomial F := ∏ i : Fin n_wit in Finset.univ, (Polynomial.X - Polynomial.C (r i));
  { Stmt := Fin n_stmt → F
    Sample := Option Vars
    SRSElements_G1 := @SRS_Elements_Idx n_stmt n_wit m d
    ListSRSElements_G1 :=
      ((List.finRange d).map fun i => SRS_Elements_Idx.EK_s_pow i)
      ++ ((List.finRange d).map fun i => SRS_Elements_Idx.EK_α_s_pow i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_v i)
      ++ ((List.finRange m).map fun i => SRS_Elements_Idx.EK_w i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_α_v i)
      ++ ((List.finRange m).map fun i => SRS_Elements_Idx.EK_α_w i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_β_v i)
      ++ ((List.finRange m).map fun i => SRS_Elements_Idx.EK_β_w i)
      ++ [SRS_Elements_Idx.VK_1, SRS_Elements_Idx.VK_α, SRS_Elements_Idx.VK_γ, SRS_Elements_Idx.VK_βv_γ, SRS_Elements_Idx.VK_βw_γ, SRS_Elements_Idx.VK_v_0, SRS_Elements_Idx.VK_w_0, SRS_Elements_Idx.VK_t]
      ++ ((List.finRange n_stmt).map fun i => SRS_Elements_Idx.VK_v_stmt i)
    -- Note that GGPR is a Type I SNARK - all SRS elements appear in both groups of the pairing
    SRSElements_G2 := @SRS_Elements_Idx n_stmt n_wit m d
    ListSRSElements_G2 :=
      ((List.finRange d).map fun i => SRS_Elements_Idx.EK_s_pow i)
      ++ ((List.finRange d).map fun i => SRS_Elements_Idx.EK_α_s_pow i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_v i)
      ++ ((List.finRange m).map fun i => SRS_Elements_Idx.EK_w i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_α_v i)
      ++ ((List.finRange m).map fun i => SRS_Elements_Idx.EK_α_w i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.EK_β_v i)
      ++ ((List.finRange m).map fun i => SRS_Elements_Idx.EK_β_w i)
      ++ [SRS_Elements_Idx.VK_1, SRS_Elements_Idx.VK_α, SRS_Elements_Idx.VK_γ, SRS_Elements_Idx.VK_βv_γ, SRS_Elements_Idx.VK_βw_γ, SRS_Elements_Idx.VK_v_0, SRS_Elements_Idx.VK_w_0, SRS_Elements_Idx.VK_t]
      ++ ((List.finRange n_stmt).map fun i => SRS_Elements_Idx.VK_v_stmt i)

    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.EK_s_pow i => poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_α_s_pow i => poly_α * poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_v i => to_MvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_w i => to_MvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_α_v i => poly_α * to_MvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_α_w i => poly_α * to_MvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_β_v i => poly_β_v * to_MvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_β_w i => poly_β_w * to_MvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.VK_1 => 1
      | SRS_Elements_Idx.VK_α => poly_α
      | SRS_Elements_Idx.VK_γ => poly_γ
      | SRS_Elements_Idx.VK_βv_γ => poly_β_v * poly_γ
      | SRS_Elements_Idx.VK_βw_γ => poly_β_w * poly_γ
      | SRS_Elements_Idx.VK_v_0 => to_MvPolynomial_Option Vars v_0
      | SRS_Elements_Idx.VK_w_0 => to_MvPolynomial_Option Vars w_0
      | SRS_Elements_Idx.VK_t => to_MvPolynomial_Option Vars t
      | SRS_Elements_Idx.VK_v_stmt i => to_MvPolynomial_Option Vars (v_stmt i)

    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.EK_s_pow i => poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_α_s_pow i => poly_α * poly_s ^ (i : ℕ)
      | SRS_Elements_Idx.EK_v i => to_MvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_w i => to_MvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_α_v i => poly_α * to_MvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_α_w i => poly_α * to_MvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.EK_β_v i => poly_β_v * to_MvPolynomial_Option Vars (v_wit i)
      | SRS_Elements_Idx.EK_β_w i => poly_β_w * to_MvPolynomial_Option Vars (w_wit i)
      | SRS_Elements_Idx.VK_1 => 1
      | SRS_Elements_Idx.VK_α => poly_α
      | SRS_Elements_Idx.VK_γ => poly_γ
      | SRS_Elements_Idx.VK_βv_γ => poly_β_v * poly_γ
      | SRS_Elements_Idx.VK_βw_γ => poly_β_w * poly_γ
      | SRS_Elements_Idx.VK_v_0 => to_MvPolynomial_Option Vars v_0
      | SRS_Elements_Idx.VK_w_0 => to_MvPolynomial_Option Vars w_0
      | SRS_Elements_Idx.VK_t => to_MvPolynomial_Option Vars t
      | SRS_Elements_Idx.VK_v_stmt i => to_MvPolynomial_Option Vars (v_stmt i)

    Proof_G1 := Proof_G1_Idx
    ListProof_G1 := [Proof_G1_Idx.V_mid, Proof_G1_Idx.V_mid', Proof_G1_Idx.W', Proof_G1_Idx.Y, Proof_G1_Idx.H']
    Proof_G2 := Proof_G2_Idx
    ListProof_G2 := [Proof_G2_Idx.W, Proof_G2_Idx.H]
    EqualityChecks := ChecksIdx
    Pairings := fun check_idx => match check_idx with
      | ChecksIdx.CheckI => PairingsI_Idx
      | ChecksIdx.CheckII => PairingsII_Idx
      | ChecksIdx.CheckIII => PairingsIII_Idx
      | ChecksIdx.CheckIV => PairingsIV_Idx
      | ChecksIdx.CheckV => PairingsV_Idx
    ListPairings := fun check_idx => match check_idx with
      | ChecksIdx.CheckI => [PairingsI_Idx.lhs, PairingsI_Idx.rhs]
      | ChecksIdx.CheckII => [PairingsII_Idx.lhs, PairingsII_Idx.rhs]
      | ChecksIdx.CheckIII => [PairingsIII_Idx.lhs, PairingsIII_Idx.rhs]
      | ChecksIdx.CheckIV => [PairingsIV_Idx.lhs, PairingsIV_Idx.rhs]
      | ChecksIdx.CheckV => [PairingsV_Idx.lhs, PairingsV_Idx.rhs1, PairingsV_Idx.rhs2]
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
    -- I : (v_0(s) + v_in(s) + V_mid(s)) * (w_0(s) + W) - t * H = 0
    -- II : V_mid' * 1 - V_mid * α = 0
    -- III : W' * 1 - α * W = 0
    -- IV : H' * 1 -  α * H = 0
    -- V : Y * 1 - V_mid * (βv γ) - (β_w γ) * W = 0
    verificationPairingSRS_G2 := fun stmt check_idx i SRS_idx => match check_idx with
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
    -- I : (v_0(s) + v_in(s) + V_mid(s)) * (w_0(s) + W) - t * H = 0
    -- II : V_mid' * 1 - V_mid * α = 0
    -- III : W' * 1 - α * W = 0
    -- IV : H' * 1 -  α * H = 0
    -- V : Y * 1 - V_mid * (βv γ) - (β_w γ) * W = 0
    verificationPairingProof_G1 := fun stmt check_idx i pf_idx => match check_idx with
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
    -- I : (v_0(s) + v_in(s) + V_mid(s)) * (w_0(s) + W) - t * H = 0
    -- II : V_mid' * 1 - V_mid * α = 0
    -- III : W' * 1 - α * W = 0
    -- IV : H' * 1 -  α * H = 0
    -- V : Y * 1 - V_mid * (βv γ) - (β_w γ) * W = 0
    verificationPairingProof_G2 := fun stmt check_idx i pf_idx => match check_idx with
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


lemma soundness
    {F : Type} [Field F]
    {n_stmt n_wit m d : ℕ}
    {v_stmt : Fin n_stmt → Polynomial F }
    {v_wit : Fin n_wit → Polynomial F }
    {w_wit : Fin m → Polynomial F }
    {v_0 : Polynomial F }
    {w_0 : Polynomial F }
    {r : Fin (n_wit) → F} :
    (AGMProofSystemInstantiation.soundness
      F
      (@GGPR F _ n_stmt n_wit m d
        v_stmt
        v_wit w_wit
        v_0 w_0
        r)
      ((Fin n_wit → F) × (Fin m → F))
      (fun (stmt : Fin n_stmt → F) (wit : (Fin n_wit -> F) × (Fin m → F)) =>
        let t : Polynomial F := ∏ i : Fin n_wit in Finset.univ, (Polynomial.X - Polynomial.C (r i));
        (-- Definition 2 from GGPR
          (v_0
            + (List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit.fst i) * v_wit i) (List.finRange n_wit)))
          )
        *
          (w_0
            + (List.sum (List.map (fun i => Polynomial.C (wit.snd i) * w_wit i) (List.finRange m)))
          )
        )
          %ₘ t = 0)
        ( fun prover =>
           ⟨fun i => prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.EK_β_v i ) ,
            fun i => prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.EK_β_w i ) ⟩ )
    ) := by
  unfold AGMProofSystemInstantiation.soundness AGMProofSystemInstantiation.verify AGMProofSystemInstantiation.proof_element_G1_as_poly AGMProofSystemInstantiation.proof_element_G2_as_poly
  -- TODO namespcace AGMProofSystemInstantiation eliminate
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, null⟩
  intro t
  have eqnI := eqns ChecksIdx.CheckI
  have eqnII := eqns ChecksIdx.CheckII
  have eqnIII := eqns ChecksIdx.CheckIII
  have eqnIV := eqns ChecksIdx.CheckIV
  have eqnV := eqns ChecksIdx.CheckV
  clear eqns null

  simp_rw [GGPR] at eqnI eqnII eqnIII eqnIV eqnV

  start_proof


  -- All I want is a tactic that will apply the following simplifications to eqn in sequence.
  -- TODO can I write a tactic taking a nested list of simp lemmas?
  -- Can I combine all of these?
## simp only [monomial_zero', List.singleton_append, List.cons_append, List.append_assoc,
    List.map_cons, Sum.elim_inl, Sum.elim_inr, List.map_append, List.map_map, List.sum_cons,
    List.sum_append, List.map_nil, List.sum_nil, add_zero, Sum.elim_lam_const_lam_const, map_one,
    one_mul, map_zero, zero_mul, map_neg, neg_mul, neg_add_rev, zero_add, mul_zero,
    -- Note: everything above is @simp tagged
    Function.comp, List.sum_map_zero] at eqnI eqnII eqnIII eqnIV eqnV

## simp only [mul_add, add_mul, List.sum_map_add] at eqnI eqnII eqnIII eqnIV eqnV

  -- Move all the X (some _) terms to the left, and out of sums
## simp only [
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
## trace "Converting to MvPolynomial over Polynomials"
  -- replace eqn := congr_arg (MvPolynomial.optionEquivRight F Vars) eqn
## simp only [←(EquivLike.apply_eq_iff_eq (optionEquivRight _ _))] at eqnI eqnII eqnIII eqnIV eqnV
## simp only [AlgEquiv.map_add, AlgEquiv.map_zero, AlgEquiv.map_mul, AlgEquiv.map_one,
    AlgEquiv.map_neg, AlgEquiv.list_map_sum, AlgEquiv.map_pow] at eqnI eqnII eqnIII eqnIV eqnV
## simp only [optionEquivRight_C, optionEquivRight_X_none, optionEquivRight_X_some, optionEquivRight_to_MvPolynomial_Option] at eqnI eqnII eqnIII eqnIV eqnV

  -- Move Cs back out so we can recognize the monomials
## simp only [←C_mul, ←C_pow, ←C_add, sum_map_C] at eqnI eqnII eqnIII eqnIV eqnV

## simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add, add_mul] at eqnI eqnII eqnIII eqnIV eqnV

## trace "Applying individual coefficients"

## have h11eqnII := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β_v 1 + Finsupp.single Vars.γ 1)) eqnII
## have h12eqnII := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β_w 1 + Finsupp.single Vars.γ 1)) eqnII
## have h19eqnII := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.γ 1)) eqnII
## have h21eqnII := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β_v 1)) eqnII
## have h22eqnII := congr_arg (coeff (Finsupp.single Vars.α 2)) eqnII
## have h71eqnII := congr_arg (coeff (Finsupp.single Vars.α 1)) eqnII
## have h74eqnII := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β_w 1)) eqnII

## have h11eqnIII := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β_v 1 + Finsupp.single Vars.γ 1)) eqnIII
## have h12eqnIII := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β_w 1 + Finsupp.single Vars.γ 1)) eqnIII
## have h19eqnIII := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.γ 1)) eqnIII
## have h21eqnIII := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β_v 1)) eqnIII
## have h22eqnIII := congr_arg (coeff (Finsupp.single Vars.α 2)) eqnIII
## have h71eqnIII := congr_arg (coeff (Finsupp.single Vars.α 1)) eqnIII
## have h74eqnIII := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β_w 1)) eqnIII

## have h2eqnV := congr_arg (coeff (Finsupp.single Vars.β_v 1 + Finsupp.single Vars.γ 1)) eqnV
## have h3eqnV := congr_arg (coeff (Finsupp.single Vars.β_w 1 + Finsupp.single Vars.γ 1)) eqnV

## have h1eqnI := congr_arg (coeff 0) eqnI

## clear eqnI
## clear eqnII
## clear eqnIII
## clear eqnIV
## clear eqnV

## trace "Distribute coefficient-taking over terms"
## simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h11eqnII h12eqnII h19eqnII h21eqnII h22eqnII h71eqnII h74eqnII h11eqnIII h12eqnIII h19eqnIII h21eqnIII h22eqnIII h71eqnIII h74eqnIII h2eqnV h3eqnV h1eqnI

## trace "Simplifying coefficient expressions"
## simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply] at h11eqnII h12eqnII h19eqnII h21eqnII h22eqnII h71eqnII h74eqnII h11eqnIII h12eqnIII h19eqnIII h21eqnIII h22eqnIII h71eqnIII h74eqnIII h2eqnV h3eqnV h1eqnI

## trace "Determine which coefficients are nonzero"
## simp (config := {decide := true}) only [ite_false, ite_true] at h11eqnII h12eqnII h19eqnII h21eqnII h22eqnII h71eqnII h74eqnII h11eqnIII h12eqnIII h19eqnIII h21eqnIII h22eqnIII h71eqnIII h74eqnIII h2eqnV h3eqnV h1eqnI
## trace "Remove zeros"
## simp only [neg_zero, add_zero, zero_add] at h11eqnII h12eqnII h19eqnII h21eqnII h22eqnII h71eqnII h74eqnII h11eqnIII h12eqnIII h19eqnIII h21eqnIII h22eqnIII h71eqnIII h74eqnIII h2eqnV h3eqnV h1eqnI

## skip

## integral_domain_tactic

## done

  sorry
  -- TODO unfinished
