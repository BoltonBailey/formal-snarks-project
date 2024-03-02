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
  | x : StmtEntries
  | y : StmtEntries
  | z : StmtEntries
deriving Repr, BEq

inductive WitEntries : Type where
  | A : WitEntries
  | B : WitEntries
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
inductive Proof_G1_Idx : Type where
  | Pf : Proof_G1_Idx

instance : Fintype Proof_G1_Idx :=
  ⟨⟨[Proof_G1_Idx.Pf], by simp⟩, fun x => by cases x <;> simp⟩

-- No right proof
def Proof_G2_Idx : Type := Empty

instance : Fintype Proof_G2_Idx := inferInstanceAs (Fintype Empty)

inductive PairingsIdx : Type where
  | lhs : PairingsIdx
  | rhs : PairingsIdx

instance : Fintype PairingsIdx :=
  ⟨⟨[PairingsIdx.lhs, PairingsIdx.rhs], by simp⟩,
    fun x => by cases x <;> simp⟩

inductive SRS_Elements_G1_Idx : Type where
  | α : SRS_Elements_G1_Idx
  | β : SRS_Elements_G1_Idx

inductive SRS_Elements_G2_Idx : Type where
  | α : SRS_Elements_G2_Idx
  | β : SRS_Elements_G2_Idx


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
    SRSElements_G1 := SRS_Elements_G1_Idx
    ListSRSElements_G1 :=
      [.α, .β]
    SRSElements_G2 := SRS_Elements_G2_Idx
    ListSRSElements_G2 :=
      [.α, .β]
    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_G1_Idx.α => MvPolynomial.X Vars_α
      | SRS_Elements_G1_Idx.β => MvPolynomial.X Vars_β
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_G2_Idx.α => MvPolynomial.X Vars_α
      | SRS_Elements_G2_Idx.β => MvPolynomial.X Vars_β
    Proof_G1 := Proof_G1_Idx
    ListProof_G1 := [Proof_G1_Idx.Pf]
    Proof_G2 := Proof_G2_Idx
    ListProof_G2 := []
    EqualityChecks := Unit
    Pairings := fun _ => PairingsIdx
    ListPairings := fun _ => [PairingsIdx.lhs, PairingsIdx.rhs]
    verificationPairingSRS_G1 := fun stmt _ i SRS_idx => match i with
      | PairingsIdx.lhs => 0
      | PairingsIdx.rhs => match SRS_idx with
        | SRS_Elements_G1_Idx.α => stmt StmtEntries.z
        | SRS_Elements_G1_Idx.β => 0
    verificationPairingSRS_G2 := fun stmt _ i SRS_idx => match i with
      | PairingsIdx.lhs => match SRS_idx with
        | SRS_Elements_G2_Idx.α => stmt StmtEntries.x
        | SRS_Elements_G2_Idx.β => stmt StmtEntries.y
      | PairingsIdx.rhs => match SRS_idx with
        | SRS_Elements_G2_Idx.α => 0
        | SRS_Elements_G2_Idx.β => -1
    verificationPairingProof_G1 := fun stmt _ i pf => match i with
      | PairingsIdx.lhs => match pf with
        | Proof_G1_Idx.Pf => 1
      | PairingsIdx.rhs => match pf with
        | Proof_G1_Idx.Pf => 0
    verificationPairingProof_G2 := fun stmt _ i pf => 0
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
        wit WitEntries.A * stmt StmtEntries.y = stmt StmtEntries.z -- - wit WitEntries.I
        ∨
        wit WitEntries.B * stmt StmtEntries.x = stmt StmtEntries.z -- - wit WitEntries.I
      )
      (fun prover i => prover.fst Proof_G1_Idx.Pf (if i = WitEntries.A then .α else .β))

    ) := by
  unfold AGMProofSystemInstantiation.soundness AGMProofSystemInstantiation.verify AGMProofSystemInstantiation.proof_element_G1_as_poly AGMProofSystemInstantiation.proof_element_G2_as_poly
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, null⟩
  have eqn := eqns ()
  clear eqns null

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
