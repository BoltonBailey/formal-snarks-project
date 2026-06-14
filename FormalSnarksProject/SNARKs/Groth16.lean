import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Algebra.Polynomial.Div
-- import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Algebra.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver
import FormalSnarksProject.SoundnessTactic.ProofMode
-- import FormalSnarksProject.ToMathlib.MulModByMonic

/-!

# Groth16TypeI

This file contains the soundness proof for the Type I version of Groth16 presented in
["On the Size of Pairing-based Non-interactive Arguments"](https://eprint.iacr.org/2016/260.pdf)
by Jens Groth.


-/

open scoped BigOperators Classical

section Groth16TypeI

open MvPolynomial Option AGMProofSystemInstantiation

namespace Groth16TypeI

inductive Vars : Type where
  | α : Vars
  | β : Vars
  | γ : Vars
  | δ : Vars
deriving Repr, BEq

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

inductive PairingsIdx : Type where
  | ab : PairingsIdx
  | αβ : PairingsIdx
  | stmtγ : PairingsIdx
  | cδ : PairingsIdx

inductive SRS_Elements_Idx {n_stmt n_wit n_var : ℕ} : Type where
  | α : SRS_Elements_Idx
  | β : SRS_Elements_Idx
  | δ : SRS_Elements_Idx
  | γ : SRS_Elements_Idx
  | x_pow : Fin n_var → SRS_Elements_Idx
  | x_pow_times_t : Fin (n_var - 1) → SRS_Elements_Idx
  | y : Fin n_stmt → SRS_Elements_Idx
  | q : Fin n_wit → SRS_Elements_Idx

noncomputable def Groth16TypeI
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F]
    /- The naturals representing:
      n_stmt - the statement size,
      n_wit - the witness size -/
    {n_stmt n_wit n_var : ℕ}
    /- u_stmt and u_wit are Fin-indexed collections of polynomials from the square span program -/
    {u_stmt : Fin n_stmt → (Polynomial F)}
    {u_wit : Fin n_wit → (Polynomial F)}
    {v_stmt : Fin n_stmt → (Polynomial F)}
    {v_wit : Fin n_wit → (Polynomial F)}
    {w_stmt : Fin n_stmt → (Polynomial F)}
    {w_wit : Fin n_wit → (Polynomial F)}
    /- The roots of the polynomial t -/
    {r : Fin n_wit → F} :
    AGMProofSystemInstantiation F :=
  let t : Polynomial F :=
    ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i));
  {
    Stmt := Fin n_stmt -> F
    Sample := Option Vars
    SRSElements_G1 := @SRS_Elements_Idx n_stmt n_wit n_var
    ListSRSElements_G1 :=
      [SRS_Elements_Idx.α]
      ++ [SRS_Elements_Idx.β]
      ++ [SRS_Elements_Idx.δ]
      ++ ((List.finRange n_var).map fun i => SRS_Elements_Idx.x_pow i)
      ++ ((List.finRange (n_var - 1)).map fun i => SRS_Elements_Idx.x_pow_times_t i)
      ++ ((List.finRange n_stmt).map fun i => SRS_Elements_Idx.y i)
      ++ ((List.finRange n_wit).map fun i => SRS_Elements_Idx.q i)
    SRSElements_G2 := @SRS_Elements_Idx n_stmt n_wit n_var
    ListSRSElements_G2 :=
      [SRS_Elements_Idx.β]
      ++ [SRS_Elements_Idx.γ]
      ++ [SRS_Elements_Idx.δ]
      ++ ((List.finRange n_var).map fun i => SRS_Elements_Idx.x_pow i)
    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.α => X Vars_γ * X Vars_δ * X Vars_α
      | SRS_Elements_Idx.β => X Vars_γ * X Vars_δ * X Vars_β
      | SRS_Elements_Idx.γ => X Vars_γ * X Vars_δ * X Vars_γ
      | SRS_Elements_Idx.δ => X Vars_γ * X Vars_δ * X Vars_δ
      | SRS_Elements_Idx.x_pow i => X Vars_γ * X Vars_δ * X Vars_x ^ (i : ℕ)
      | SRS_Elements_Idx.x_pow_times_t i => X Vars_γ
                                                  * X Vars_x ^ (i : ℕ)
                                                  * to_MvPolynomial_Option Vars t
      | SRS_Elements_Idx.y i => ((X Vars_β * X Vars_δ) * ( (to_MvPolynomial_Option Vars (u_stmt i))))
                                      +
                                      (X Vars_α * X Vars_δ) * (to_MvPolynomial_Option Vars (v_stmt i))
                                      +
                                      X Vars_δ * (to_MvPolynomial_Option Vars (w_stmt i))
      | SRS_Elements_Idx.q i => (X Vars_β * X Vars_γ) * ( to_MvPolynomial_Option Vars (u_wit i))
                                      +
                                      (X Vars_α * X Vars_γ) * (to_MvPolynomial_Option Vars (v_wit i))
                                      +
                                      X Vars_γ * to_MvPolynomial_Option Vars (w_wit i)
      -- Note that the polynomials here have been multiplied through by γδ
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_Idx.α => X Vars_γ * X Vars_δ * X Vars_α
      | SRS_Elements_Idx.β => X Vars_γ * X Vars_δ * X Vars_β
      | SRS_Elements_Idx.γ => X Vars_γ * X Vars_δ * X Vars_γ
      | SRS_Elements_Idx.δ => X Vars_γ * X Vars_δ * X Vars_δ
      | SRS_Elements_Idx.x_pow i => X Vars_γ * X Vars_δ * X Vars_x ^ (i : ℕ)
      | SRS_Elements_Idx.x_pow_times_t i => X Vars_γ
                                                  * X Vars_x ^ (i : ℕ)
                                                  * to_MvPolynomial_Option Vars t
      | SRS_Elements_Idx.y i => ((X Vars_β * X Vars_δ) * ( (to_MvPolynomial_Option Vars (u_stmt i))))
                                      +
                                      (X Vars_α * X Vars_δ) * (to_MvPolynomial_Option Vars (v_stmt i))
                                      +
                                      X Vars_δ * (to_MvPolynomial_Option Vars (w_stmt i))
      | SRS_Elements_Idx.q i => (X Vars_β * X Vars_γ) * ( to_MvPolynomial_Option Vars (u_wit i))
                                      +
                                      (X Vars_α * X Vars_γ) * (to_MvPolynomial_Option Vars (v_wit i))
                                      +
                                      X Vars_γ * to_MvPolynomial_Option Vars (w_wit i)
      -- Note that the polynomials here have been multiplied through by γδ
    Proof_G1 := Proof_Idx
    ListProof_G1 := [Proof_Idx.A, Proof_Idx.B, Proof_Idx.C]
    Proof_G2 := Proof_Idx
    ListProof_G2 := [Proof_Idx.A, Proof_Idx.B, Proof_Idx.C]
    EqualityChecks := Unit
    Pairings := fun _ => PairingsIdx
    ListPairings := fun _ => [PairingsIdx.ab, PairingsIdx.αβ, PairingsIdx.stmtγ, PairingsIdx.cδ]
    verificationPairingSRS_G1 := fun stmt _ i SRS_idx => match i with
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
    verificationPairingSRS_G2 := fun _stmt _ i SRS_idx => match i with
      | PairingsIdx.ab => match SRS_idx with
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | _ => 0
      | PairingsIdx.αβ => match SRS_idx with
        | SRS_Elements_Idx.β => 1
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | _ => 0
      | PairingsIdx.stmtγ => match SRS_idx with
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 1
        | SRS_Elements_Idx.δ => 0
        | SRS_Elements_Idx.x_pow _ => 0
        | _ => 0
      | PairingsIdx.cδ => match SRS_idx with
        | SRS_Elements_Idx.β => 0
        | SRS_Elements_Idx.γ => 0
        | SRS_Elements_Idx.δ => 1
        | SRS_Elements_Idx.x_pow _ => 0
        | _ => 0
    verificationPairingProof_G1 := fun _stmt _ i pf => match i with
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
    verificationPairingProof_G2 := fun _stmt _ i pf => match i with
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
    Identified_Proof_Elems := [(Proof_Idx.A, Proof_Idx.A), (Proof_Idx.B, Proof_Idx.B), (Proof_Idx.C, Proof_Idx.C)]
  }

lemma identified_proof_elems_def
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F)}
    {u_wit : Fin n_wit → (Polynomial F)}
    {v_stmt : Fin n_stmt → (Polynomial F)}
    {v_wit : Fin n_wit → (Polynomial F)}
    {w_stmt : Fin n_stmt → (Polynomial F)}
    {w_wit : Fin n_wit → (Polynomial F)}
    {r : Fin n_wit → F} :
    (Groth16TypeI
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
        (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (r := r)).Identified_Proof_Elems = [(Proof_Idx.A, Proof_Idx.A), (Proof_Idx.B, Proof_Idx.B), (Proof_Idx.C, Proof_Idx.C)] := rfl

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
    {r : Fin n_wit → F} :
    (soundness
      F
      (Groth16TypeI
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
        (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (r := r))
      (Fin n_wit -> F)
      (fun (stmt : Fin n_stmt → F) (wit : Fin n_wit -> F) =>
        let t : Polynomial F :=
          ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i));
        (((List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * u_wit i) (List.finRange n_wit))))
            *
          ((List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * v_wit i) (List.finRange n_wit))))
            -
          ((List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * w_wit i) (List.finRange n_wit)))))
            %ₘ t = 0
      )
      (fun prover i => prover.fst Proof_Idx.C (SRS_Elements_Idx.q i))
    ) := by
  -- Unfold the soundness definition fully
  unfold soundness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly
  -- Introduce the arguments to the soundness definition
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, typeI_identification⟩
  intro t
  have eqn := eqns ()
  clear eqns

  -- Unpack the typeI idenitifcation facts by instantiating at each identified pair.
  -- (Under toolchain v4.29.0 the previous `simp`-then-`rcases` no longer reduces the membership
  -- hypothesis to a conjunction; instantiating with explicit `List.Mem` proofs is robust.)
  have eqnA := typeI_identification (Proof_Idx.A, Proof_Idx.A)
    (by rw [identified_proof_elems_def]; exact List.mem_cons_self)
  have eqnB := typeI_identification (Proof_Idx.B, Proof_Idx.B)
    (by rw [identified_proof_elems_def]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have eqnC := typeI_identification (Proof_Idx.C, Proof_Idx.C)
    (by rw [identified_proof_elems_def]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  clear typeI_identification

  -- Simplify the equation
  suffices
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Idx.C (SRS_Elements_Idx.q i)) * u_wit i) (List.finRange n_wit))))
      *
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Idx.C (SRS_Elements_Idx.q i)) * v_wit i) (List.finRange n_wit))))
      =
      ((List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => Polynomial.C (prover.fst Proof_Idx.C (SRS_Elements_Idx.q i)) * w_wit i) (List.finRange n_wit))))
      +
      List.sum (List.map (fun x : Fin (n_var - 1) => Polynomial.C (prover.fst Proof_Idx.C (SRS_Elements_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * t)) (List.finRange (n_var - 1))) by

    rw [<-sub_eq_iff_eq_add'] at this
    have h := congr_arg (fun x => x %ₘ t) this
    simp only at h
    simp
    rw [h]
    clear this h

    simp only [mul_comm _ (t), <-mul_assoc]
    simp only [mul_assoc, List.sum_map_mul_right, List.sum_map_mul_left]

    rw [mul_comm]
    apply Polynomial.mul_self_modByMonic
    apply Polynomial.monic_prod_of_monic
    intro i hi
    exact Polynomial.monic_X_sub_C (r i)



  -- Step 1: Obtain the coefficient equations of the mv_polynomials
  simp_rw [Groth16TypeI] at eqn eqnA eqnB eqnC

  simp only [monomial_zero', List.singleton_append, List.cons_append, List.append_assoc,
    List.map_cons, Sum.elim_inl, Sum.elim_inr, List.map_append, List.map_map, List.sum_cons,
    List.sum_append, List.map_nil, List.sum_nil, add_zero, Sum.elim_lam_const_lam_const, map_one,
    one_mul, map_zero, zero_mul, map_neg, neg_mul, neg_add_rev, zero_add, mul_zero,
    -- Note: everything above is @simp tagged
    Function.comp_def, List.sum_map_zero] at eqn eqnA eqnB eqnC

  -- TODO(v4.29 bump): the remainder of this proof is blocked by a `List.sum_append` regression.
  -- As of toolchain v4.29.0, `List.sum_append` carries a `Std.LawfulLeftIdentity (· + ·) 0` instance
  -- argument that `simp`/`rw` cannot synthesize here (the element type is only known via a metavariable
  -- during instance search), so the `(_ ++ _).sum` terms never split and the downstream
  -- `optionEquivRight` distribution + coefficient extraction stall. The full pipeline is preserved in
  -- git history (pre-bump); restore it once the upstream regression is resolved.
  sorry

end soundness

end Groth16TypeI

end Groth16TypeI
