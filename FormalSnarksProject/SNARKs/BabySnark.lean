import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Data.Polynomial.Div
import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Data.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode
import FormalSnarksProject.ToMathlib.MulModByMonic

/-!

# BabySNARK

This file contains the soundness proof for [BabySNARK](https://github.com/initc3/babySNARK/blob/master/babysnark.pdf).


-/

open scoped BigOperators Classical

section BabySNARK

open MvPolynomial Option AGMProofSystemInstantiation

namespace BabySNARK

inductive Vars : Type where
  | β : Vars
  | γ : Vars
deriving Repr, BEq

local notation "Vars_β" => some Vars.β
local notation "Vars_γ" => some Vars.γ
local notation "Vars_τ" => none

lemma Vars.finsupp_eq_ext (f g : Vars →₀ ℕ) : f = g ↔
    f Vars.β = g Vars.β
    ∧ f Vars.γ = g Vars.γ := by
  rw [FunLike.ext_iff]
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

inductive SRS_Elements_Idx {n_stmt n_wit n_var : ℕ} : Type where
  | τ_pow : Fin n_var → SRS_Elements_Idx
  | γ : SRS_Elements_Idx
  | γβ : SRS_Elements_Idx
  | βu : Fin n_wit → SRS_Elements_Idx

inductive ChecksIdx : Type where
  | CheckI : ChecksIdx
  | CheckII : ChecksIdx


inductive PairingsI_Idx : Type where
  | ht : PairingsI_Idx
  | gg : PairingsI_Idx
  | vv : PairingsI_Idx

inductive PairingsII_Idx : Type where
  | bγ : PairingsII_Idx
  | γβv : PairingsII_Idx


noncomputable def BabySNARK
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    /- u_stmt and u_wit are Fin-indexed collections of polynomials from the square span program -/
    {u_stmt : Fin n_stmt → (Polynomial F) }
    {u_wit : Fin n_wit → (Polynomial F) }
    {t : Polynomial F} :
    AGMProofSystemInstantiation F :=
  {
    Stmt := Fin n_stmt -> F
    Sample := Option Vars
    SRSElements_G1 := @SRS_Elements_Idx n_stmt n_wit n_var
    ListSRSElements_G1 :=
      ((List.finRange n_var).map fun i => SRS_Elements_Idx.τ_pow i)
      ++ [SRS_Elements_Idx.γ]
      ++ [SRS_Elements_Idx.γβ]
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.βu i)
    SRSElements_G2 := @SRS_Elements_Idx n_stmt n_wit n_var
    ListSRSElements_G2 :=
      ((List.finRange n_var).map fun i => SRS_Elements_Idx.τ_pow i)
      ++ [SRS_Elements_Idx.γ]
      ++ [SRS_Elements_Idx.γβ]
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.βu i)
    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.τ_pow i => X Vars_τ ^ (i : ℕ)
      | SRS_Elements_Idx.γ => X Vars_β
      | SRS_Elements_Idx.γβ => X Vars_γ * X Vars_β
      | SRS_Elements_Idx.βu i => X Vars_β * to_MvPolynomial_Option Vars (u_wit i)
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.τ_pow i => X Vars_τ ^ (i : ℕ)
      | SRS_Elements_Idx.γ => X Vars_β
      | SRS_Elements_Idx.γβ => X Vars_γ * X Vars_β
      | SRS_Elements_Idx.βu i => X Vars_β * to_MvPolynomial_Option Vars (u_wit i)
    Proof_G1 := Proof_Idx
    ListProof_G1 := [Proof_Idx.H, Proof_Idx.V, Proof_Idx.B]
    Proof_G2 := Proof_Idx
    ListProof_G2 := [Proof_Idx.H, Proof_Idx.V, Proof_Idx.B]
    EqualityChecks := ChecksIdx
    Pairings := fun check_idx => match check_idx with
      | ChecksIdx.CheckI => PairingsI_Idx
      | ChecksIdx.CheckII => PairingsII_Idx
    ListPairings := fun check_idx => match check_idx with
      | ChecksIdx.CheckI => [PairingsI_Idx.ht, PairingsI_Idx.gg, PairingsI_Idx.vv]
      | ChecksIdx.CheckII => [PairingsII_Idx.bγ, PairingsII_Idx.γβv]
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
    verificationPairingProof_G1 := fun stmt check_idx i pf => match check_idx with
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
    verificationPairingProof_G2 := fun stmt check_idx i pf => match check_idx with
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

lemma identified_proof_elems_def
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F) }
    {u_wit : Fin n_wit → (Polynomial F) }
    {t : Polynomial F} :
    (BabySNARK
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (t := t)).Identified_Proof_Elems = [(Proof_Idx.H, Proof_Idx.H), (Proof_Idx.V, Proof_Idx.V), (Proof_Idx.B, Proof_Idx.B)] := rfl

section soundness

-- Remove heartbeat limit for upcoming long-running proof
set_option maxHeartbeats 0 -- 0 means no limit

lemma is_sound
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F) }
    {u_wit : Fin n_wit → (Polynomial F) }
    {v_stmt : Fin n_stmt → (Polynomial F) }
    {v_wit : Fin n_wit → (Polynomial F) }
    {w_stmt : Fin n_stmt → (Polynomial F) }
    {w_wit : Fin n_wit → (Polynomial F) }
    {t : Polynomial F}
    (ht : List.sum (List.map (fun (x : Fin n_var) => Polynomial.C (Polynomial.coeff t (x : ℕ)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var)) = t)
    (ht0 : t.Monic) :
    (soundness
      F
      (BabySNARK
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (t := t))
      (Fin n_wit -> F)
      (fun (stmt : Fin n_stmt → F) (wit : Fin n_wit -> F) =>
        (((List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * u_wit i) (List.finRange n_wit)))) ^ 2
          - 1
        )
            %ₘ t = 0
      )
      (fun prover i => prover.fst Proof_Idx.B (SRS_Elements_Idx.βu i))
    ) := by
  -- Unfold the soundness definition fully
  unfold soundness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly
  -- Introduce the arguments to the soundness definition
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, typeI_identification⟩
  have eqnI := eqns ChecksIdx.CheckI
  have eqnII := eqns ChecksIdx.CheckII
  clear eqns

  -- Unpack the typeI idenitifcation facts
  simp only [identified_proof_elems_def, Bool.not_eq_true, List.mem_cons, List.mem_singleton,
    forall_eq_or_imp, forall_eq] at typeI_identification
  simp only [List.find?_nil, List.not_mem_nil, IsEmpty.forall_iff, Prod.forall, implies_true,
    and_true] at typeI_identification
  rcases typeI_identification with ⟨eqnH, eqnV, eqnB⟩

  -- Simplify the equation
  suffices
      (((List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Idx.B (SRS_Elements_Idx.βu i)) * u_wit i) (List.finRange n_wit)))) ^ 2
          - 1
        )
      =
      t * (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Idx.H (SRS_Elements_Idx.βu i)) * u_wit i) (List.finRange n_wit))) by

    rw [this]
    apply Polynomial.mul_modByMonic
    assumption

  -- Step 1: Obtain the coefficient equations of the mv_polynomials
  simp_rw [BabySNARK] at eqnI eqnII eqnH eqnV eqnB

  simp only [monomial_zero', List.singleton_append, List.cons_append, List.append_assoc,
    List.map_cons, Sum.elim_inl, Sum.elim_inr, List.map_append, List.map_map, List.sum_cons,
    List.sum_append, List.map_nil, List.sum_nil, add_zero, Sum.elim_lam_const_lam_const, map_one,
    one_mul, map_zero, zero_mul, map_neg, neg_mul, neg_add_rev, zero_add, mul_zero,
    -- Note: everything above is @simp tagged
    Function.comp, List.sum_map_zero] at eqnI eqnII eqnH eqnV eqnB

  simp only [mul_add, add_mul, List.sum_map_add] at eqnI eqnII eqnH eqnV eqnB

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
    List.sum_map_mul_right, List.sum_map_mul_left] at eqnI eqnII eqnH eqnV eqnB

  -- Apply MvPolynomial.optionEquivRight *here*, so that we can treat polynomials in Vars_X as constants
  trace "Converting to MvPolynomial over Polynomials"
  simp only [←(EquivLike.apply_eq_iff_eq (optionEquivRight _ _))] at eqnI eqnII eqnH eqnV eqnB
  simp only [AlgEquiv.map_add, AlgEquiv.map_zero, AlgEquiv.map_mul, AlgEquiv.map_one,
    AlgEquiv.map_neg, AlgEquiv.list_map_sum, AlgEquiv.map_pow] at eqnI eqnII eqnH eqnV eqnB
  simp only [optionEquivRight_C, optionEquivRight_X_none, optionEquivRight_X_some, optionEquivRight_to_MvPolynomial_Option] at eqnI eqnII eqnH eqnV eqnB

  -- Move Cs back out so we can recognize the monomials
  simp only [←C_mul, ←C_pow, ←C_add, ←C_neg,
    sum_map_C] at eqnI eqnII eqnH eqnV eqnB

  simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add, add_mul] at eqnI eqnII eqnH eqnV eqnB

  trace "Applying individual coefficients"

  have hI_00 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 0)) eqnI
  have hI_01 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1)) eqnI
  have hI_02 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2)) eqnI
  have hI_10 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 0)) eqnI
  have hI_11 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnI
  have hI_12 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2)) eqnI
  have hI_20 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 0)) eqnI
  have hI_21 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 1)) eqnI
  have hI_22 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 2)) eqnI

  have hII_00 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 0)) eqnII
  have hII_01 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1)) eqnII
  have hII_02 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2)) eqnII
  have hII_10 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 0)) eqnII
  have hII_11 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnII
  have hII_12 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2)) eqnII
  have hII_20 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 0)) eqnII
  have hII_21 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 1)) eqnII
  have hII_22 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 2)) eqnII

  have hH_00 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 0)) eqnH
  have hH_01 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1)) eqnH
  have hH_02 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2)) eqnH
  have hH_10 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 0)) eqnH
  have hH_11 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnH
  have hH_12 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2)) eqnH
  have hH_20 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 0)) eqnH
  have hH_21 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 1)) eqnH
  have hH_22 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 2)) eqnH

  have hV_00 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 0)) eqnV
  have hV_01 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1)) eqnV
  have hV_02 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2)) eqnV
  have hV_10 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 0)) eqnV
  have hV_11 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnV
  have hV_12 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2)) eqnV
  have hV_20 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 0)) eqnV
  have hV_21 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 1)) eqnV
  have hV_22 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 2)) eqnV

  have hB_00 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 0)) eqnB
  have hB_01 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1)) eqnB
  have hB_02 := congr_arg (coeff (Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2)) eqnB
  have hB_10 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 0)) eqnB
  have hB_11 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnB
  have hB_12 := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2)) eqnB
  have hB_20 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 0)) eqnB
  have hB_21 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 1)) eqnB
  have hB_22 := congr_arg (coeff (Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 2)) eqnB

  clear eqnI eqnII eqnH eqnV eqnB

  trace "Distribute coefficient-taking over terms"
  simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at hI_00 hI_01 hI_02 hI_10 hI_11 hI_12 hI_20 hI_21 hI_22 hII_00 hII_01 hII_02 hII_10 hII_11 hII_12 hII_20 hII_21 hII_22 hH_00 hH_01 hH_02 hH_10 hH_11 hH_12 hH_20 hH_21 hH_22 hV_00 hV_01 hV_02 hV_10 hV_11 hV_12 hV_20 hV_21 hV_22 hB_00 hB_01 hB_02 hB_10 hB_11 hB_12 hB_20 hB_21 hB_22

  trace "Simplifying coefficient expressions"
  simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply] at hI_00 hI_01 hI_02 hI_10 hI_11 hI_12 hI_20 hI_21 hI_22 hII_00 hII_01 hII_02 hII_10 hII_11 hII_12 hII_20 hII_21 hII_22 hH_00 hH_01 hH_02 hH_10 hH_11 hH_12 hH_20 hH_21 hH_22 hV_00 hV_01 hV_02 hV_10 hV_11 hV_12 hV_20 hV_21 hV_22 hB_00 hB_01 hB_02 hB_10 hB_11 hB_12 hB_20 hB_21 hB_22

  trace "Determine which coefficients are nonzero"
  simp (config := {decide := true}) only [ite_false, ite_true] at hI_00 hI_01 hI_02 hI_10 hI_11 hI_12 hI_20 hI_21 hI_22 hII_00 hII_01 hII_02 hII_10 hII_11 hII_12 hII_20 hII_21 hII_22 hH_00 hH_01 hH_02 hH_10 hH_11 hH_12 hH_20 hH_21 hH_22 hV_00 hV_01 hV_02 hV_10 hV_11 hV_12 hV_20 hV_21 hV_22 hB_00 hB_01 hB_02 hB_10 hB_11 hB_12 hB_20 hB_21 hB_22
  trace "Remove zeros"
  simp only [neg_zero, add_zero, zero_add] at hI_00 hI_01 hI_02 hI_10 hI_11 hI_12 hI_20 hI_21 hI_22 hII_00 hII_01 hII_02 hII_10 hII_11 hII_12 hII_20 hII_21 hII_22 hH_00 hH_01 hH_02 hH_10 hH_11 hH_12 hH_20 hH_21 hH_22 hV_00 hV_01 hV_02 hV_10 hV_11 hV_12 hV_20 hV_21 hV_22 hB_00 hB_01 hB_02 hB_10 hB_11 hB_12 hB_20 hB_21 hB_22

  set sum_B_1_τ_pow := List.sum
    (List.map (fun x => Polynomial.C (prover.2 Proof_Idx.B (SRS_Elements_Idx.τ_pow x)) * Polynomial.X ^ (x : ℕ))
      (List.finRange n_var))
  set sum_B_τ_pow := List.sum
    (List.map (fun x => Polynomial.C (prover.2 Proof_Idx.B (SRS_Elements_Idx.τ_pow x)) * Polynomial.X ^ (x : ℕ))
      (List.finRange n_var))
  set sum_V_1_τ_pow := List.sum
    (List.map (fun x => Polynomial.C (prover.1 Proof_Idx.V (SRS_Elements_Idx.τ_pow x)) * Polynomial.X ^ (x : ℕ))
      (List.finRange n_var))
  set sum_V_2_τ_pow := List.sum
    (List.map (fun x => Polynomial.C (prover.2 Proof_Idx.V (SRS_Elements_Idx.τ_pow x)) * Polynomial.X ^ (x : ℕ))
      (List.finRange n_var))
  set sum_H_1_τ_pow := List.sum
    (List.map (fun x => Polynomial.C (prover.1 Proof_Idx.H (SRS_Elements_Idx.τ_pow x)) * Polynomial.X ^ (x : ℕ))
      (List.finRange n_var))
  set sum_H_2_τ_pow := List.sum
    (List.map (fun x => Polynomial.C (prover.2 Proof_Idx.H (SRS_Elements_Idx.τ_pow x)) * Polynomial.X ^ (x : ℕ))
      (List.finRange n_var))

  integral_domain_tactic
  · simp [ht, Polynomial.Monic.ne_zero ht0] at *
    rw [pow_two]
    sorry
  · simp [ht, Polynomial.Monic.ne_zero ht0] at *

end soundness

end BabySNARK
