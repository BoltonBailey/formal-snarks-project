/-
Author: Bolton Bailey
-/
import data.mv_polynomial.basic
import data.polynomial.div
import data.polynomial.field_division
import algebra.polynomial.big_operators
-- import .general_lemmas.polynomial_mv_sv_cast
-- import .general_lemmas.mv_divisability
-- import .general_lemmas.single_antidiagonal
-- import .general_lemmas.polynomial_smul_eq_C_mul
import .vars

/-!
# Knowledge Soundness

This file proves the knowledge-soundness property of the 
[Groth16](https://eprint.iacr.org/2016/260.pdf) system.

Specifically, we prove this property for the NILP system 
described in section 3.1 of that paper.

Furthermore, we carry out the reduction to non-laurent polynomials by multiplying through the CRS with γδ.

We choose r,s to be 0, todo, allow other values

-/

open_locale big_operators


section

open mv_polynomial

noncomputable theory


universes u


/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]

/-- The naturals representing:
  n_stmt - the statement size, 
  n_wit - the witness size -/ 
parameters {n_stmt n_wit n : ℕ}

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
(∑ i in (finset.fin_range n_stmt), a_stmt i • u_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • u_wit i))
  * 
(∑ i in (finset.fin_range n_stmt), a_stmt i • v_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • v_wit i))
  -
(∑ i in (finset.fin_range n_stmt), a_stmt i • w_stmt i
  + (∑ i in (finset.fin_range n_wit), a_wit i • w_wit i))
   %ₘ t = 0



/- Multivariable polynomial definititons and ultilities -/


/-- Helper for converting mv_polynomial to single -/
@[simp]
def singlify : vars -> polynomial F
| vars.x := polynomial.X 
| vars.α := 1
| vars.β := 1
| vars.γ := 1
| vars.δ := 1



/-- Multivariable version of t -/
def t_mv : mv_polynomial vars F := t.eval₂ mv_polynomial.C (X vars.x)

/-- V_stmt as a multivariable polynomial of vars.X -/
def V_stmt_mv (a_stmt : fin n_stmt → F) : mv_polynomial vars F 
:= (V_stmt_sv a_stmt).eval₂ mv_polynomial.C (X vars.x)



run_cmd mk_simp_attr `crs
run_cmd tactic.add_doc_string `simp_attr.crs "Attribute for defintions of CRS elements"


/-- The crs elements as multivariate polynomials of the toxic waste samples -/
@[crs]
def crs_α  : mv_polynomial vars F := X vars.α * X vars.γ * X vars.δ
@[crs]
def crs_β : mv_polynomial vars F := X vars.β * X vars.γ * X vars.δ
@[crs]
def crs_γ : mv_polynomial vars F := X vars.γ * X vars.γ * X vars.δ
@[crs]
def crs_δ : mv_polynomial vars F := X vars.δ * X vars.γ * X vars.δ
@[crs]
def crs_powers_of_x (i : fin m) : (mv_polynomial vars F) := (X vars.x)^(i : ℕ) * X vars.γ * X vars.δ
-- I define prodcuts of these crs elements without the division, then later claim identities. Is this right?
@[crs]
def crs_l (i : fin n_stmt) : (mv_polynomial vars F) := 
((X vars.β * X vars.δ) * (u_stmt i).eval₂ mv_polynomial.C (X vars.x)
+
(X vars.α * X vars.δ) * (v_stmt i).eval₂ mv_polynomial.C (X vars.x)
+
X vars.δ * (w_stmt i).eval₂ mv_polynomial.C (X vars.x))
@[crs]
def crs_m (i : fin n_wit) : (mv_polynomial vars F) := 
((X vars.β * X vars.γ) * (u_wit i).eval₂ mv_polynomial.C (X vars.x)
+
(X vars.α * X vars.γ) * (v_wit i).eval₂ mv_polynomial.C (X vars.x)
+
X vars.γ * (w_wit i).eval₂ mv_polynomial.C (X vars.x))
@[crs]
def crs_n (i : fin n) : (mv_polynomial vars F) := 
X vars.γ * (X vars.x)^(i : ℕ) * t.eval₂ mv_polynomial.C (X vars.x)


-- parameter crs_1 (i : fin n_stmt) : (mv_polynomial vars F) 
-- parameter crs_2 (i : fin n_wit) : (mv_polynomial vars F) 
-- parameter crs_t (i : fin m) : (mv_polynomial vars F)

/-- The coefficients of the CRS elements in the algebraic adversary's representation -/
parameters {a a' a'' a''' b b' b'' b''' c c' c'' c''' : F}
parameters {a1 b1 c1 : fin n_stmt → F}
parameters {a2 b2 c2 : fin n_wit → F}
parameters {a3 b3 c3 : fin n → F}


/-- Polynomial forms of the adversary's proof representation -/
def A  : mv_polynomial vars F := 
  a • crs_α
  +
  a' • crs_β
  + 
  a'' • crs_γ
  +
  a''' • crs_δ
  +
  ∑ i in (finset.fin_range n_stmt), (a1 i) • (crs_l i)
  +
  ∑ i in (finset.fin_range n_wit), (a2 i) • (crs_m i)
  +
  ∑ i in (finset.fin_range n), (a3 i) • (crs_n i)

def B : mv_polynomial vars F := 
  a • crs_α
  +
  a' • crs_β
  + 
  a'' • crs_γ
  +
  a''' • crs_δ
  +
  ∑ i in (finset.fin_range n_stmt), (a1 i) • (crs_l i)
  +
  ∑ i in (finset.fin_range n_wit), (a2 i) • (crs_m i)
  +
  ∑ i in (finset.fin_range n), (a3 i) • (crs_n i)

def C : mv_polynomial vars F := 
  a • crs_α
  +
  a' • crs_β
  + 
  a'' • crs_γ
  +
  a''' • crs_δ
  +
  ∑ i in (finset.fin_range n_stmt), (a1 i) • (crs_l i)
  +
  ∑ i in (finset.fin_range n_wit), (a2 i) • (crs_m i)
  +
  ∑ i in (finset.fin_range n), (a3 i) • (crs_n i)





/-- Show that if the adversary polynomials obey the equations, 
then the coefficients give a satisfying witness. 
TODO is b2 right here? Perhaps it should be replaced by some other function of the a2 b2 c2 or other coefficients -/
theorem case_1 (a_stmt : fin n_stmt → F ) : 
  (0 < m)
  -- -> ∀ i, crs_1_γ i = crs_1 i * crs_γ
  -- -> ∀ i, crs_2_δ i = crs_2 i * crs_δ
  -- -> ∀ i, crs_t_δ i = crs_t i * crs_δ
  -> A * B = crs_α * crs_β + (∑ i in finset.fin_range n_stmt, a_stmt i • crs_l i ) * crs_γ + C * crs_δ
  -> (satisfying a_stmt c2) -- This shows that (a`+1, . . . , am) = (C`+1, . . . , Cm) is a witness for the statement (a1, . . . , a`)
:=
begin
  intros hm eqn,
  rw [A, B, C] at eqn,
  simp only with crs at eqn,
end



end
