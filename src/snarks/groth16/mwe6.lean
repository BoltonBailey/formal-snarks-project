
/-
Author: Bolton Bailey
-/
import snarks.groth16.declarations
import ...attributes
import ...integral_domain_tactic

/-!
# Knowledge Soundness

This file proves the knowledge-soundness property of the 
[Groth16](https://eprint.iacr.org/2016/260.pdf) system.

Specifically, we prove this property for the NILP system 
described in section 3.1 of that paper.

Furthermore, we carry out the reduction to non-laurent polynomials by multiplying through the CRS with γδ.

-/

open_locale big_operators classical


section groth16

open mv_polynomial groth16 vars

noncomputable theory



universes u


/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]

/-- The naturals representing:
  n_stmt - the statement size, 
  n_wit - the witness size -/ 
parameters {n_stmt n_wit n_var : ℕ}

def l : ℕ := n_stmt

def m : ℕ := n_wit


-- NOTE: In the paper, n_stmt is l and n_wit is n-l. Here, n is defined from these values.

/-- u_stmt and u_wit are fin-indexed collections of polynomials from the square span program -/
parameter {u_stmt : fin n_stmt → (polynomial F) }
parameter {u_wit : fin n_wit → (polynomial F) }
parameter {v_stmt : fin n_stmt → (polynomial F) }
parameter {v_wit : fin n_wit → (polynomial F) }
parameter {w_stmt : fin n_stmt → (polynomial F) }
parameter {w_wit : fin n_wit → (polynomial F) }


/-- The roots of the polynomial t -/
parameter {r : fin m → F} 
/-- t is the polynomial divisibility by which is used to verify satisfaction of the SSP -/
def t : polynomial F := ∏ i in (finset.fin_range m), (polynomial.X - polynomial.C (r i))
-- TODO this and the following lemmas about this could potentially be spun off 
-- make a `monic_from_roots` function for mathlib

/-- t has degree m -/
lemma nat_degree_t : t.nat_degree = m
:=
begin
  -- rw polynomial.nat_degree,
  rw t,
  rw polynomial.nat_degree_prod,
  simp,
  intros i hi,
  exact polynomial.X_sub_C_ne_zero (r i),
end

lemma monic_t : t.monic
:=
begin
  rw t,
  apply polynomial.monic_prod_of_monic,
  intros i hi,
  exact polynomial.monic_X_sub_C (r i),
end

lemma degree_t_pos : 0 < m → 0 < t.degree 
:=
begin
  intro hm,
  suffices h : t.degree = some m,
    rw h,
    apply with_bot.some_lt_some.2,
    exact hm,

  have h := nat_degree_t,
  rw polynomial.nat_degree at h,

  induction h1 : t.degree,

  rw h1 at h,
  rw option.get_or_else at h,
  rw h at hm,
  have h2 := has_lt.lt.false hm,
  exfalso,
  exact h2,

  rw h1 at h,
  rw option.get_or_else at h,
  rw h,
end



-- Single variable form of V_wit
def V_wit_sv (a_wit : fin n_wit → F) : polynomial F 
:= ∑ i in finset.fin_range n_wit, a_wit i • u_wit i

/-- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def V_stmt_sv (a_stmt : fin n_stmt → F) : polynomial F 
:= ∑ i in (finset.fin_range n_stmt), a_stmt i • u_stmt i

/-- Checks whether a statement witness pair satisfies the SSP -/
def satisfying (a_stmt : fin n_stmt → F ) (a_wit : fin n_wit → F) := 
((∑ i in (finset.fin_range n_stmt), a_stmt i • u_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • u_wit i))
  * 
(∑ i in (finset.fin_range n_stmt), a_stmt i • v_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • v_wit i))
  -
(∑ i in (finset.fin_range n_stmt), a_stmt i • w_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • w_wit i)))
   %ₘ t = 0



/- Multivariable polynomial definititons and ultilities -/


-- /-- Helper for converting mv_polynomial to single -/
-- @[simp]
-- def singlify : vars -> polynomial F
-- | vars.x := polynomial.X 
-- | vars.α := 1
-- | vars.β := 1
-- | vars.γ := 1
-- | vars.δ := 1



lemma 
h0112 (A_β foo c d : F)
  (h : A_β = 0 ∨ foo = 0) (hs : c = 0 ∨ d = 0) : false
:=
begin
  repeat {integral_domain_tactic_one_iter},

end

