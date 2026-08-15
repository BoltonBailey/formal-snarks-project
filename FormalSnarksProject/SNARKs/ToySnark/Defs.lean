module

public import FormalSnarksProject.Models.AGMProofSystemInstantiation
public import Mathlib.Algebra.Polynomial.Div
-- import FormalSnarksProject.ToMathlib.List
public import FormalSnarksProject.ToMathlib.OptionEquivRight
public import Mathlib.Algebra.MvPolynomial.Equiv
public import FormalSnarksProject.SoundnessTactic.SoundnessProver
public import FormalSnarksProject.ToMathlib.FinEnumOrd

@[expose] public section

open scoped BigOperators

section ToySnark

open MvPolynomial Option List
open CPoly

namespace ToySnark

inductive Vars : Type where
  | α : Vars
  | β : Vars
deriving Repr, BEq, DecidableEq

instance : FinEnum Vars := .ofList [.α, .β] (fun x => by cases x <;> simp)

instance : Ord Vars := FinEnum.toOrd
instance : Std.TransOrd Vars := FinEnum.toOrd.transOrd
instance : Std.LawfulEqOrd Vars := FinEnum.toOrd.lawfulEqOrd

inductive StmtEntries : Type where
  | x : StmtEntries
  | y : StmtEntries
  | z : StmtEntries
deriving Repr, BEq

inductive WitEntries : Type where
  | A : WitEntries
  | B : WitEntries
deriving Repr, BEq, DecidableEq

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
deriving DecidableEq

instance : FinEnum Proof_G1_Idx := .ofList [.Pf] (fun x => by cases x <;> simp)
@[simp] lemma toList_Proof_G1_Idx : FinEnum.toList Proof_G1_Idx = [.Pf] := by rfl

-- No right proof
def Proof_G2_Idx : Type := Empty

instance : FinEnum Proof_G2_Idx := inferInstanceAs (FinEnum Empty)
@[simp] lemma toList_Proof_G2_Idx : FinEnum.toList Proof_G2_Idx = [] := by rfl

inductive PairingsIdx : Type where
  | lhs : PairingsIdx
  | rhs : PairingsIdx
deriving DecidableEq

instance : FinEnum PairingsIdx := .ofList [.lhs, .rhs] (fun x => by cases x <;> simp)
@[simp] lemma toList_PairingsIdx : FinEnum.toList PairingsIdx = [.lhs, .rhs] := by rfl

inductive SRS_Elements_G1_Idx : Type where
  | α : SRS_Elements_G1_Idx
  | β : SRS_Elements_G1_Idx
deriving DecidableEq

instance : FinEnum SRS_Elements_G1_Idx := .ofList [.α, .β] (fun x => by cases x <;> simp)
@[simp] lemma toList_SRS_Elements_G1_Idx : FinEnum.toList SRS_Elements_G1_Idx = [.α, .β] := by rfl

inductive SRS_Elements_G2_Idx : Type where
  | α : SRS_Elements_G2_Idx
  | β : SRS_Elements_G2_Idx
deriving DecidableEq

instance : FinEnum SRS_Elements_G2_Idx := .ofList [.α, .β] (fun x => by cases x <;> simp)
@[simp] lemma toList_SRS_Elements_G2_Idx : FinEnum.toList SRS_Elements_G2_Idx = [.α, .β] := by rfl


/--
A description of a Toy SNARK
-/
@[reducible] noncomputable def ToySnark
    /- The finite field parameter of our SNARK -/
    {F : Type} [Field F] [BEq F] [LawfulBEq F] :
    AGMProofSystemInstantiation F :=
  {
    Stmt := StmtEntries -> F
    Sample := Option Vars
    SRSElements_G1 := SRS_Elements_G1_Idx
    SRSElements_G2 := SRS_Elements_G2_Idx
    SRSElementValue_G1 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_G1_Idx.α => CPoly.COrdMvPolynomial.X Vars_α
      | SRS_Elements_G1_Idx.β => CPoly.COrdMvPolynomial.X Vars_β
    SRSElementValue_G2 := fun SRS_idx => match SRS_idx with
      | SRS_Elements_G2_Idx.α => CPoly.COrdMvPolynomial.X Vars_α
      | SRS_Elements_G2_Idx.β => CPoly.COrdMvPolynomial.X Vars_β
    Proof_G1 := Proof_G1_Idx
    Proof_G2 := Proof_G2_Idx
    EqualityChecks := Unit
    Pairings := fun _ => PairingsIdx
    Pairings_FinEnum := fun _ => inferInstance
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


end ToySnark

end ToySnark
