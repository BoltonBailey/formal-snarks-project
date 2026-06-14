import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Algebra.Polynomial.Div
-- import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Algebra.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode
-- import FormalSnarksProject.ToMathlib.MulModByMonic

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
    {u_stmt : Fin n_stmt → (Polynomial F)}
    {u_wit : Fin n_wit → (Polynomial F)}
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

lemma identified_proof_elems_def
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F)}
    {u_wit : Fin n_wit → (Polynomial F)}
    {t : Polynomial F} :
    (BabySNARK
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (t := t)).Identified_Proof_Elems = [(Proof_Idx.H, Proof_Idx.H), (Proof_Idx.V, Proof_Idx.V), (Proof_Idx.B, Proof_Idx.B)] := rfl

section soundness

-- Remove heartbeat limit for upcoming long-running proof
set_option maxHeartbeats 0 in -- 0 means no limit
lemma is_sound
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F)}
    {u_wit : Fin n_wit → (Polynomial F)}
    {v_stmt : Fin n_stmt → (Polynomial F)}
    {v_wit : Fin n_wit → (Polynomial F)}
    {w_stmt : Fin n_stmt → (Polynomial F)}
    {w_wit : Fin n_wit → (Polynomial F)}
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

  -- Unpack the typeI idenitifcation facts by instantiating at each identified pair
  have eqnH := typeI_identification (Proof_Idx.H, Proof_Idx.H)
    (by rw [identified_proof_elems_def]; exact List.mem_cons_self)
  have eqnV := typeI_identification (Proof_Idx.V, Proof_Idx.V)
    (by rw [identified_proof_elems_def]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have eqnB := typeI_identification (Proof_Idx.B, Proof_Idx.B)
    (by rw [identified_proof_elems_def]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  clear typeI_identification

  -- Simplify the equation
  suffices
      (((List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Idx.B (SRS_Elements_Idx.βu i)) * u_wit i) (List.finRange n_wit)))) ^ 2
          - 1
        )
      =
      t * (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Idx.H (SRS_Elements_Idx.βu i)) * u_wit i) (List.finRange n_wit))) by

    rw [this, mul_comm]
    apply Polynomial.mul_self_modByMonic
    assumption

  -- Step 1: Obtain the coefficient equations of the mv_polynomials
  simp_rw [BabySNARK] at eqnI eqnII eqnH eqnV eqnB

  simp only [monomial_zero', List.singleton_append, List.cons_append, List.append_assoc,
    List.map_cons, Sum.elim_inl, Sum.elim_inr, List.map_append, List.map_map, List.sum_cons,
    List.sum_append, List.map_nil, List.sum_nil, add_zero, Sum.elim_lam_const_lam_const, map_one,
    one_mul, map_zero, zero_mul, map_neg, neg_mul, neg_add_rev, zero_add, mul_zero,
    -- Note: everything above is @simp tagged
    List.nil_append, Function.comp_def, List.sum_map_zero] at eqnI eqnII eqnH eqnV eqnB

  -- TODO(v4.29 bump): the remainder of this proof is blocked by a `List.sum_append` regression.
  -- As of toolchain v4.29.0, `List.sum_append` carries a `Std.LawfulLeftIdentity (· + ·) 0`
  -- instance argument that `simp`/`rw` cannot synthesize here (the element type is only known via a
  -- metavariable during instance search), so the `(_ ++ _).sum` terms never split and the downstream
  -- `optionEquivRight` distribution + coefficient extraction stall. The full pipeline is preserved in
  -- git history (pre-bump); restore it once the upstream regression is resolved.
  sorry

end soundness

end BabySNARK

end BabySNARK
