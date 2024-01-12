import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Data.Polynomial.Div
import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Data.MvPolynomial.Equiv
import FormalSnarksProject.SoundnessTactic.SoundnessProver

open scoped BigOperators Classical

section ToySnark

open MvPolynomial Option List

namespace ToySnark

inductive Vars : Type where
  | α : Vars
  | β : Vars
deriving Repr, BEq

inductive StmtEntries : Type where
  | C : StmtEntries
  | D : StmtEntries
  | E : StmtEntries
deriving Repr, BEq

inductive WitEntries : Type where
  | A : WitEntries
  | B : WitEntries
  | I : WitEntries
deriving Repr, BEq

local notation "Vars_α" => some Vars.α
local notation "Vars_β" => some Vars.β
local notation "Vars_x" => none

lemma Vars.finsupp_eq_ext (f g : Vars →₀ ℕ) : f = g ↔
    f Vars.α = g Vars.α
    ∧ f Vars.β = g Vars.β := by
  rw [FunLike.ext_iff]
  constructor
  · intro h
    simp_rw [h]
    simp only [and_self]
  · intro h x
    cases x <;> tauto


-- One left proof
inductive Proof_Left_Idx : Type where
  | Pf : Proof_Left_Idx

instance : Fintype Proof_Left_Idx :=
  ⟨⟨[Proof_Left_Idx.Pf], by simp⟩, fun x => by cases x <;> simp⟩

-- No right proof
def Proof_Right_Idx : Type := Empty

instance : Fintype Proof_Right_Idx := inferInstanceAs (Fintype Empty)

inductive PairingsIdx : Type where
  | lhs : PairingsIdx
  | rhs : PairingsIdx

instance : Fintype PairingsIdx :=
  ⟨⟨[PairingsIdx.lhs, PairingsIdx.rhs], by simp⟩,
    fun x => by cases x <;> simp⟩



/--
A description of a Toy SNARK
-/
noncomputable def ToySnark
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F] :
    AGMProofSystemInstantiation F :=
  {
    Stmt := StmtEntries -> F
    Sample := Option Vars
    CrsElements_Left := Unit ⊕ Unit ⊕ Unit -- Representing α, β, αβ
    ListCrsElements_Left :=
      [.inl ()] ++ [.inr (.inl ())] ++ [.inr (.inr ())]
    CrsElements_Right := Unit ⊕ Unit ⊕ Unit -- Representing α, β, 1
    ListCrsElements_Right :=
      [.inl ()] ++ [.inr (.inl ())] ++ [.inr (.inr ())]
    crsElementValue_Left :=
      Sum.elim (fun _ => MvPolynomial.X Vars_α) <|
      Sum.elim (fun _ => MvPolynomial.X Vars_β) <|
               (fun _ => MvPolynomial.X Vars_α * MvPolynomial.X Vars_β)
    crsElementValue_Right :=
      Sum.elim (fun _ => MvPolynomial.X Vars_α) <|
      Sum.elim (fun _ => MvPolynomial.X Vars_β) <|
               (fun _ => 1)
    Proof_Left := Proof_Left_Idx
    ListProof_Left := [Proof_Left_Idx.Pf]
    Proof_Right := Proof_Right_Idx
    ListProof_Right := []
    EqualityChecks := Unit
    Pairings := fun _ => PairingsIdx
    ListPairings := fun _ => [PairingsIdx.lhs, PairingsIdx.rhs]
    verificationPairingCRSLeft := fun stmt _ i => match i with
      | PairingsIdx.lhs =>
          Sum.elim (fun _ => 0) <|
          Sum.elim (fun _ => 0) <|
                   (fun _ => 0)
      | PairingsIdx.rhs =>
          Sum.elim (fun _ => 0) <|
          Sum.elim (fun _ => 0) <|
                   (fun _ => stmt StmtEntries.E)
    verificationPairingCRSRight := fun stmt _ i => match i with
      | PairingsIdx.lhs =>
          Sum.elim (fun _ => stmt StmtEntries.C) <|
          Sum.elim (fun _ => stmt StmtEntries.D) <|
                   (fun _ => 0)
      | PairingsIdx.rhs =>
          Sum.elim (fun _ => 0) <|
          Sum.elim (fun _ => 0) <|
                   (fun _ => -1) -- the 1s component of the right group of the right pairing is -1 to convey that it is on the rhs of the equation
    verificationPairingProofLeft := fun stmt _ i pf => match i with
      | PairingsIdx.lhs => match pf with
        | Proof_Left_Idx.Pf => 1 -- The left group side of the left-hand pairing is the proof
      | PairingsIdx.rhs => match pf with
        | Proof_Left_Idx.Pf => 0 -- The left group side of the right pairing has no proof
    verificationPairingProofRight := fun stmt _ i pf => 0
  }


section soundness



-- Remove time-out
set_option maxHeartbeats 0 -- 0 means no limit

lemma soundness
    {F : Type} [Field F] :
    (AGMProofSystemInstantiation.soundness
      F
      (ToySnark
        (F := F))
      (WitEntries -> F)
      (fun (stmt : StmtEntries → F) (wit : WitEntries -> F) =>
        wit WitEntries.A * stmt StmtEntries.D = stmt StmtEntries.E -- - wit WitEntries.I
        ∨
        wit WitEntries.B * stmt StmtEntries.C = stmt StmtEntries.E -- - wit WitEntries.I
      )
      (fun prover i => prover.fst Proof_Left_Idx.Pf (if i = WitEntries.A then Sum.inl () else Sum.inr (.inl ())))

    ) := by
  unfold AGMProofSystemInstantiation.soundness AGMProofSystemInstantiation.verify
  intros stmt prover eqns
  have eqn := eqns ()
  clear eqns

  -- Step 1: Obtain the coefficient equations of the mv_polynomials
  simp_rw [ToySnark] at eqn
  simp only [monomial_zero', List.singleton_append, List.cons_append, List.append_assoc,
    List.map_cons, Sum.elim_inl, Sum.elim_inr, List.map_append, List.map_map, List.sum_cons,
    List.sum_append, List.map_nil, List.sum_nil, add_zero, Sum.elim_lam_const_lam_const, map_one,
    one_mul, map_zero, zero_mul, map_neg, neg_mul, neg_add_rev, zero_add, mul_zero,
    -- Note: everything above is @simp tagged
    Function.comp, List.sum_map_zero] at eqn

  simp only [mul_add, add_mul, List.sum_map_add] at eqn

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
    List.sum_map_mul_right, List.sum_map_mul_left] at eqn


  -- I apply MvPolynomial.optionEquivRight *here*,
  -- so that we can treat polynomials in Vars_X as constants
  trace "Converting to MvPolynomial over Polynomials"
  replace eqn := congr_arg (MvPolynomial.optionEquivRight F Vars) eqn
  simp only [AlgEquiv.map_add, AlgEquiv.map_zero, AlgEquiv.map_mul, AlgEquiv.map_one,
    AlgEquiv.map_neg, AlgEquiv.list_map_sum, AlgEquiv.map_pow] at eqn
  simp only [MvPolynomial.optionEquivRight_C, MvPolynomial.optionEquivRight_X_none, MvPolynomial.optionEquivRight_X_some, optionEquivRight_to_MvPolynomial_Option] at eqn
  -- Move Cs back out so we can recognize the monomials
  -- simp only [←MvPolynomial.C_mul, ←MvPolynomial.C_pow, ←MvPolynomial.C_add,
  --   MvPolynomial.sum_map_C] at eqn

  simp only [MvPolynomial.X, C_apply, MvPolynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add, add_mul] at eqn

  trace "Applying individual coefficients"


  have h20 := congr_arg (coeff (Finsupp.single Vars.α 2 + Finsupp.single Vars.β 0)) eqn
  have h11 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1)) eqn
  have h02 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 2)) eqn

  clear eqn

  trace "Distribute coefficient-taking over terms"
  simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h20 h11 h02

  trace "Simplifying coefficient expressions"
  simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply] at h20 h11 h02

  simp [ite_true, ite_self, add_zero, ite_false, and_self, zero_add,
    one_ne_zero, and_false, false_and, add_eq_zero, mul_eq_zero,
    add_right_eq_self, zero_ne_one, and_true, true_and, neg_zero] at h20 h11 h02 ⊢


  -- Completely remove references to Polynomial
  simp only [add_neg_eq_zero, Polynomial.C_inj, ←Polynomial.C_add, ←Polynomial.C_mul] at h20 h11 h02

  integral_domain_tactic



end soundness


-- TODO I'm using lists rather than finsets now, so I think I can get rid of all the finset lemmas

end ToySnark
