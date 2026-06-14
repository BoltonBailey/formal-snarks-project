import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib.Algebra.Polynomial.Div
-- import FormalSnarksProject.ToMathlib.List
import FormalSnarksProject.ToMathlib.OptionEquivRight
import Mathlib.Algebra.MvPolynomial.Equiv
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
  rw [DFunLike.ext_iff]
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
  ⟨⟨[Proof_G1_Idx.Pf], by simp⟩, fun x => by cases x; simp⟩

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
    verificationPairingProof_G1 := fun _stmt _ i pf => match i with
      | PairingsIdx.lhs => match pf with
        | Proof_G1_Idx.Pf => 1
      | PairingsIdx.rhs => match pf with
        | Proof_G1_Idx.Pf => 0
    verificationPairingProof_G2 := fun _ _ _ _ => 0
  }


section soundness



-- Remove time-out
set_option maxHeartbeats 0 in -- 0 means no limit
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
  unfold AGMProofSystemInstantiation.soundness AGMProofSystemInstantiation.verify AGMProofSystemInstantiation.check_poly AGMProofSystemInstantiation.pairing_poly AGMProofSystemInstantiation.proof_element_G1_as_poly AGMProofSystemInstantiation.proof_element_G2_as_poly
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
    Function.comp_def, List.sum_map_zero] at eqn

  -- TODO(v4.29 bump): the remainder of this proof is blocked by a `List.sum_append` regression.
  -- As of toolchain v4.29.0, `List.sum_append` carries a `Std.LawfulLeftIdentity (· + ·) 0` instance
  -- argument that `simp`/`rw` cannot synthesize here (the element type is only known via a metavariable
  -- during instance search), so the `(_ ++ _).sum` terms never split and the downstream
  -- `optionEquivRight` distribution + coefficient extraction stall. The full pipeline is preserved in
  -- git history (pre-bump); restore it once the upstream regression is resolved.
  sorry

end soundness


-- TODO I'm using lists rather than finsets now, so I think I can get rid of all the finset lemmas

end ToySnark

end ToySnark
