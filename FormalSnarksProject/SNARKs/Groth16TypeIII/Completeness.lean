import FormalSnarksProject.SNARKs.Groth16TypeIII.Defs

/-!

# Groth16TypeIII Completeness

This file contains a draft of the completeness proof for the Type III version of Groth16 presented in
["Another Look at Extraction and Randomization of Groth's zk-SNARK" by Baghery et al.](https://eprint.iacr.org/2020/811).

-/

open scoped BigOperators Classical

open MvPolynomial Option AGMProofSystemInstantiation

namespace Groth16TypeIII

section completeness

noncomputable def u_sum {F : Type} [Field F] {n_stmt n_wit : ℕ}
    (u_stmt : Fin n_stmt → (Polynomial F))
    (u_wit : Fin n_wit → (Polynomial F))
    (stmt : Fin n_stmt -> F)
    (wit : Fin n_wit -> F)
    : Polynomial F :=
  List.sum (List.map (fun j => Polynomial.C (stmt j) * (u_stmt j)) (List.finRange n_stmt))
  + List.sum (List.map (fun j => Polynomial.C (wit j) * (u_wit j)) (List.finRange n_wit))

noncomputable def v_sum {F : Type} [Field F] {n_stmt n_wit : ℕ}
    (v_stmt : Fin n_stmt → (Polynomial F))
    (v_wit : Fin n_wit → (Polynomial F))
    (stmt : Fin n_stmt -> F)
    (wit : Fin n_wit -> F)
    : Polynomial F :=
  List.sum (List.map (fun j => Polynomial.C (stmt j) * (v_stmt j)) (List.finRange n_stmt))
  + List.sum (List.map (fun j => Polynomial.C (wit j) * (v_wit j)) (List.finRange n_wit))

noncomputable def w_sum {F : Type} [Field F] {n_stmt n_wit : ℕ}
    (w_stmt : Fin n_stmt → (Polynomial F))
    (w_wit : Fin n_wit → (Polynomial F))
    (stmt : Fin n_stmt -> F)
    (wit : Fin n_wit -> F)
    : Polynomial F :=
  List.sum (List.map (fun j => Polynomial.C (stmt j) * (w_stmt j)) (List.finRange n_stmt))
  + List.sum (List.map (fun j => Polynomial.C (wit j) * (w_wit j)) (List.finRange n_wit))

noncomputable def wit_prover (F : Type) [Field F]
    (n_stmt n_wit n_var : ℕ)
    (u_stmt : Fin n_stmt → (Polynomial F)) (u_wit : Fin n_wit → (Polynomial F))
    (v_stmt : Fin n_stmt → (Polynomial F)) (v_wit : Fin n_wit → (Polynomial F))
    (w_stmt : Fin n_stmt → (Polynomial F)) (w_wit : Fin n_wit → (Polynomial F))
    (r : Fin n_wit → F)
    (stmt : Fin n_stmt -> F)
    (wit : Fin n_wit -> F) :
    (Groth16TypeIII
      (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
      (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
      (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (r := r)).Prover where
        fst pf_elem srs_elem := match pf_elem with
          | Proof_G1_Idx.A => match srs_elem with
            | SRS_Elements_G1_Idx.α => 1
            | SRS_Elements_G1_Idx.β => 0
            | SRS_Elements_G1_Idx.δ => 0
            | SRS_Elements_G1_Idx.x_pow i => (u_sum u_stmt u_wit stmt wit).coeff i
            | SRS_Elements_G1_Idx.x_pow_times_t _ => 0
            | SRS_Elements_G1_Idx.y i => 0
            | SRS_Elements_G1_Idx.q i => 0
          | Proof_G1_Idx.C =>
            match srs_elem with
            | SRS_Elements_G1_Idx.α => 0
            | SRS_Elements_G1_Idx.β => 0
            | SRS_Elements_G1_Idx.δ => 0
            | SRS_Elements_G1_Idx.x_pow _ => 0
            | SRS_Elements_G1_Idx.x_pow_times_t i =>
              let t : Polynomial F := ∏ i in (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i));
              (((u_sum u_stmt u_wit stmt wit) * (v_sum v_stmt v_wit stmt wit) - (w_sum w_stmt w_wit stmt wit)) /ₘ t).coeff i
            | SRS_Elements_G1_Idx.y i => 0
            | SRS_Elements_G1_Idx.q i => wit i
        snd pf_elem srs_elem := match pf_elem with
          | Proof_G2_Idx.B => match srs_elem with
            | SRS_Elements_G2_Idx.β => 1
            | SRS_Elements_G2_Idx.γ => 0
            | SRS_Elements_G2_Idx.δ => 0
            | SRS_Elements_G2_Idx.x_pow i => (v_sum v_stmt v_wit stmt wit).coeff i


def is_complete
    {F : Type} [Field F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (Polynomial F) }
    {u_wit : Fin n_wit → (Polynomial F) }
    {v_stmt : Fin n_stmt → (Polynomial F) }
    {v_wit : Fin n_wit → (Polynomial F) }
    {w_stmt : Fin n_stmt → (Polynomial F) }
    {w_wit : Fin n_wit → (Polynomial F) }
    {r : Fin n_wit → F} :
    (completeness
      F
      (Groth16TypeIII
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
        (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (r := r))
      (Fin n_wit -> F)
      (fun (stmt : Fin n_stmt → F) (wit : Fin n_wit -> F) =>
        let t : Polynomial F :=
          ∏ i in (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i));
        (((List.sum (List.map (fun i => Polynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * u_wit i) (List.finRange n_wit))))
            *
          ((List.sum (List.map (fun i => Polynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * v_wit i) (List.finRange n_wit))))
            -
          ((List.sum (List.map (fun i => Polynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => Polynomial.C (wit i) * w_wit i) (List.finRange n_wit))))
            %ₘ t = 0
        )
      )
      (
        wit_prover
          (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
          (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
          (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (r := r)
      )
    ) := by
  unfold completeness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly
  intros stmt wit relation

  constructor
  · intro check_idx
    sorry
  · sorry

end completeness
