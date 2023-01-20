/-
Author: <Redacted for anonymized submission>
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

This file formalizes the knowledge-soundness property of the first protocol described in the Pinocchio paper.

NOTE The implementation here is incomplete, since there seem to be a few problems with the definition that I could not resolve. In particular

How do we check that the proof value of β_v v(s) + β_w w(s) + β_y y(s) is correct using "three pairings" Are we ment to use β_y γ for example?

Why is v_io(s) added to v(s) in the final divisibility requirement - this seems wrong.

-/

open_locale big_operators

section

noncomputable theory


universes u


/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]

/-- The naturals representing:
  m - m from paper - The QAP size 
  n_in - n from paper - the number of inputs 
  n_out - n' from paper - the number of outputs
  n_mid - (m - N) from paper - the number of internal gates
  d - the degree of h -/ 
parameters {n_in n_out n_mid d : ℕ}

-- N from paper
def n_stmt := n_in + n_out

-- Alternative name
def n_wit := n_mid

def m := n_stmt + n_wit


/-- fin-indexed collections of polynomials from the quadratic arithmetic program -/
parameter {v_stmt : fin n_stmt → polynomial F }
parameter {w_stmt : fin n_stmt → polynomial F }
parameter {y_stmt : fin n_stmt → polynomial F }
parameter {v_wit : fin n_wit → polynomial F }
parameter {w_wit : fin n_wit → polynomial F }
parameter {y_wit : fin n_wit → polynomial F }
parameter {v_0 : polynomial F }
parameter {w_0 : polynomial F }
parameter {y_0 : polynomial F }

/-- The roots of the polynomial t -/
parameter {r : fin m → F} 
/-- t is the polynomial divisibility by which is used to verify satisfaction of the QAP -/
def t : polynomial F := ∏ i in (finset.fin_range m), (polynomial.X - polynomial.C (r i))

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



-- -- Single variable form of V_wit
-- def V_wit_sv (a_wit : fin n_wit → F) : polynomial F 
-- := ∑ i in finset.fin_range n_wit, a_wit i • u_wit i

-- /-- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
-- def V_stmt_sv (a_stmt : fin n_stmt → F) : polynomial F 
-- := ∑ i in (finset.fin_range n_stmt), a_stmt i • u_stmt i

/-- Definition 2 from Pinocchio -/
def satisfying (c_stmt : fin n_stmt → F) (c_wit : fin n_wit → F) := 
(
  (v_0 
    + (∑ i in (finset.fin_range n_stmt), c_stmt i • v_stmt i) 
    + ∑ i in (finset.fin_range n_wit), c_wit i • v_wit i)
 * 
  (w_0 
    + (∑ i in (finset.fin_range n_stmt), c_stmt i • w_stmt i) 
    + (∑ i in (finset.fin_range n_wit), c_wit i • w_wit i))
 -
  (y_0 
    + (∑ i in (finset.fin_range n_stmt), c_stmt i • y_stmt i) 
    + (∑ i in (finset.fin_range n_wit), c_wit i • y_wit i)))
   %ₘ t = 0



/- Multivariable polynomial definititons and ultilities -/


/-- Helper for converting mv_polynomial to single -/
-- @[simp]
-- def singlify : vars -> polynomial F
-- | vars.X := polynomial.X 
-- | vars.Alpha := 1
-- | vars.Beta := 1
-- | vars.Gamma := 1
-- | vars.Delta := 1

-- /-- Helpers for representing vars as polynomials -/
def s_poly : mv_polynomial vars F := mv_polynomial.X vars.s
def α_poly : mv_polynomial vars F := mv_polynomial.X vars.α
def β_v_poly : mv_polynomial vars F := mv_polynomial.X vars.β_v
def β_w_poly : mv_polynomial vars F := mv_polynomial.X vars.β_w
def β_y_poly : mv_polynomial vars F := mv_polynomial.X vars.β_y
def γ_poly : mv_polynomial vars F := mv_polynomial.X vars.γ

def poly (v : vars) : mv_polynomial vars F := mv_polynomial.X v

-- /-- Multivariable version of t -/
-- def t_mv : mv_polynomial vars F := t.eval₂ mv_polynomial.C X_poly

-- /-- V_stmt as a multivariable polynomial of vars.X -/
-- def V_stmt_mv (a_stmt : fin n_stmt → F) : mv_polynomial vars F 
-- := (V_stmt_sv a_stmt).eval₂ mv_polynomial.C X_poly


/-- The crs elements as multivariate polynomials of the toxic waste samples: Evaluation key elements -/
def crs_v_wit_k_of_s (k : fin n_wit) : mv_polynomial vars F := (v_wit k).eval₂ mv_polynomial.C s_poly
def crs_v_stmt_k_of_s (k : fin n_stmt) : mv_polynomial vars F := (v_stmt k).eval₂ mv_polynomial.C s_poly -- Part of ver key
def crs_w_wit_k_of_s (k : fin n_wit) : mv_polynomial vars F := (w_wit k).eval₂ mv_polynomial.C s_poly
def crs_w_stmt_k_of_s (k : fin n_stmt) : mv_polynomial vars F := (w_stmt k).eval₂ mv_polynomial.C s_poly
def crs_y_wit_k_of_s (k : fin n_wit) : mv_polynomial vars F := (y_wit k).eval₂ mv_polynomial.C s_poly
def crs_y_stmt_k_of_s (k : fin n_stmt) : mv_polynomial vars F := (y_stmt k).eval₂ mv_polynomial.C s_poly

def crs_α_v_wit_k_of_s (k : fin n_wit) : mv_polynomial vars F := α_poly * (v_wit k).eval₂ mv_polynomial.C s_poly
def crs_α_w_wit_k_of_s (k : fin n_wit) : mv_polynomial vars F := α_poly * (w_wit k).eval₂ mv_polynomial.C s_poly
def crs_α_w_stmt_k_of_s (k : fin n_stmt) : mv_polynomial vars F := α_poly * (w_stmt k).eval₂ mv_polynomial.C s_poly
def crs_α_y_wit_k_of_s (k : fin n_wit) : mv_polynomial vars F := α_poly * (y_wit k).eval₂ mv_polynomial.C s_poly
def crs_α_y_stmt_k_of_s (k : fin n_stmt) : mv_polynomial vars F := α_poly * (y_stmt k).eval₂ mv_polynomial.C s_poly

def crs_β_v_wit_k_of_s (k : fin n_wit) : mv_polynomial vars F := β_v_poly * (v_wit k).eval₂ mv_polynomial.C s_poly
def crs_β_w_wit_k_of_s (k : fin n_wit) : mv_polynomial vars F := β_w_poly * (w_wit k).eval₂ mv_polynomial.C s_poly
def crs_β_w_stmt_k_of_s (k : fin n_stmt) : mv_polynomial vars F := β_w_poly * (w_stmt k).eval₂ mv_polynomial.C s_poly
def crs_β_y_wit_k_of_s (k : fin n_wit) : mv_polynomial vars F := β_y_poly * (y_wit k).eval₂ mv_polynomial.C s_poly
def crs_β_y_stmt_k_of_s (k : fin n_stmt) : mv_polynomial vars F := β_y_poly * (y_stmt k).eval₂ mv_polynomial.C s_poly

def crs_powers_of_s (i : fin d) : (mv_polynomial vars F) := s_poly^(i : ℕ)
def crs_α_powers_of_s (i : fin d) : (mv_polynomial vars F) := α_poly * s_poly^(i : ℕ)
-- TODO this is getting out of hand. Maybe we generalize around this bloat?

/-- The crs elements as multivariate polynomials of the toxic waste samples: Verification key elements -/

def crs_α : mv_polynomial vars F := α_poly
def crs_γ : mv_polynomial vars F := γ_poly
def crs_β_v_γ : mv_polynomial vars F := β_v_poly * γ_poly
def crs_β_w_γ : mv_polynomial vars F := β_w_poly * γ_poly
def crs_β_y_γ : mv_polynomial vars F := β_y_poly * γ_poly
def crs_t : mv_polynomial vars F := 
  (t).eval₂ mv_polynomial.C s_poly
def crs_v_0 : mv_polynomial vars F := 
  (v_0).eval₂ mv_polynomial.C s_poly
def crs_w_0 : mv_polynomial vars F := 
  (w_0).eval₂ mv_polynomial.C s_poly
def crs_y_0 : mv_polynomial vars F := 
  (y_0).eval₂ mv_polynomial.C s_poly

/-- The coefficients of the CRS elements in the algebraic adversary's representation -/
parameters {v_wit_comp_crs_v_wit_k_of_s : fin n_wit →  F}
parameters {v_wit_comp_crs_v_stmt_k_of_s : fin n_stmt →  F}
parameters {v_wit_comp_crs_w_wit_k_of_s : fin n_wit →  F}
parameters {v_wit_comp_crs_w_stmt_k_of_s : fin n_stmt →  F}
parameters {v_wit_comp_crs_y_wit_k_of_s : fin n_wit →  F}
parameters {v_wit_comp_crs_y_stmt_k_of_s : fin n_stmt →  F}

parameters {v_wit_comp_crs_α_v_wit_k_of_s : fin n_wit →  F}
-- parameters {v_wit_comp_crs_α_v_stmt_k_of_s : fin n_stmt →  F}
parameters {v_wit_comp_crs_α_w_wit_k_of_s : fin n_wit →  F}
parameters {v_wit_comp_crs_α_w_stmt_k_of_s : fin n_stmt →  F}
parameters {v_wit_comp_crs_α_y_wit_k_of_s : fin n_wit →  F}
parameters {v_wit_comp_crs_α_y_stmt_k_of_s : fin n_stmt →  F}

parameters {v_wit_comp_crs_β_v_wit_k_of_s : fin n_wit →  F}
-- parameters {v_wit_comp_crs_β_v_stmt_k_of_s : fin n_stmt →  F}
parameters {v_wit_comp_crs_β_w_wit_k_of_s : fin n_wit →  F}
parameters {v_wit_comp_crs_β_w_stmt_k_of_s : fin n_stmt →  F}
parameters {v_wit_comp_crs_β_y_wit_k_of_s : fin n_wit →  F}
parameters {v_wit_comp_crs_β_y_stmt_k_of_s : fin n_stmt →  F}

parameters {v_wit_comp_crs_powers_of_s : fin n_wit →  F}
parameters {v_wit_comp_crs_α_powers_of_s : fin n_stmt →  F}

parameters {v_wit_comp_crs_α : F}
parameters {v_wit_comp_crs_γ : F}
parameters {v_wit_comp_crs_β_v_γ : F}
parameters {v_wit_comp_crs_β_w_γ : F}
parameters {v_wit_comp_crs_β_y_γ : F}
parameters {v_wit_comp_crs_t : F}
parameters {v_wit_comp_crs_v_0 : F}
parameters {v_wit_comp_crs_w_0 : F}
parameters {v_wit_comp_crs_y_0 : F}


/-- Polynomial forms of the adversary's proof representation -/
def proof_v_wit : mv_polynomial vars F := 
  ∑ i in (finset.fin_range n_wit), (v_wit_comp_crs_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (v_wit_comp_crs_v_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (v_wit_comp_crs_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (v_wit_comp_crs_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (v_wit_comp_crs_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (v_wit_comp_crs_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (v_wit_comp_crs_α_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (v_wit_comp_crs_α_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (v_wit_comp_crs_α_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (v_wit_comp_crs_α_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (v_wit_comp_crs_α_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (v_wit_comp_crs_β_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (v_wit_comp_crs_β_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (v_wit_comp_crs_β_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (v_wit_comp_crs_β_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (v_wit_comp_crs_β_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  ∑ i in (finset.fin_range n_wit), (v_wit_comp_crs_powers_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (v_wit_comp_crs_α_powers_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  v_wit_comp_crs_α • crs_α
  +   
  v_wit_comp_crs_γ • crs_γ
  +   
  v_wit_comp_crs_β_v_γ • crs_β_v_γ
  +   
  v_wit_comp_crs_β_w_γ • crs_β_w_γ
  +   
  v_wit_comp_crs_β_y_γ • crs_β_y_γ
  +   
  v_wit_comp_crs_t • crs_t
  +   
  v_wit_comp_crs_v_0 • crs_v_0
  +   
  v_wit_comp_crs_w_0 • crs_w_0
  +   
  v_wit_comp_crs_y_0 • crs_y_0

parameters {w_comp_crs_v_wit_k_of_s : fin n_wit →  F}
parameters {w_comp_crs_v_stmt_k_of_s : fin n_stmt →  F}
parameters {w_comp_crs_w_wit_k_of_s : fin n_wit →  F}
parameters {w_comp_crs_w_stmt_k_of_s : fin n_stmt →  F}
parameters {w_comp_crs_y_wit_k_of_s : fin n_wit →  F}
parameters {w_comp_crs_y_stmt_k_of_s : fin n_stmt →  F}

parameters {w_comp_crs_α_v_wit_k_of_s : fin n_wit →  F}
-- parameters {w_comp_crs_α_v_stmt_k_of_s : fin n_stmt →  F}
parameters {w_comp_crs_α_w_wit_k_of_s : fin n_wit →  F}
parameters {w_comp_crs_α_w_stmt_k_of_s : fin n_stmt →  F}
parameters {w_comp_crs_α_y_wit_k_of_s : fin n_wit →  F}
parameters {w_comp_crs_α_y_stmt_k_of_s : fin n_stmt →  F}

parameters {w_comp_crs_β_v_wit_k_of_s : fin n_wit →  F}
-- parameters {w_comp_crs_β_v_stmt_k_of_s : fin n_stmt →  F}
parameters {w_comp_crs_β_w_wit_k_of_s : fin n_wit →  F}
parameters {w_comp_crs_β_w_stmt_k_of_s : fin n_stmt →  F}
parameters {w_comp_crs_β_y_wit_k_of_s : fin n_wit →  F}
parameters {w_comp_crs_β_y_stmt_k_of_s : fin n_stmt →  F}

parameters {w_comp_crs_powers_of_s : fin n_wit →  F}
parameters {w_comp_crs_α_powers_of_s : fin n_stmt →  F}

parameters {w_comp_crs_α : F}
parameters {w_comp_crs_γ : F}
parameters {w_comp_crs_β_v_γ : F}
parameters {w_comp_crs_β_w_γ : F}
parameters {w_comp_crs_β_y_γ : F}
parameters {w_comp_crs_t : F}
parameters {w_comp_crs_v_0 : F}
parameters {w_comp_crs_w_0 : F}
parameters {w_comp_crs_y_0 : F}


/-- Polynomial forms of the adversary's proof representation -/
def proof_w : mv_polynomial vars F := 
  ∑ i in (finset.fin_range n_wit), (w_comp_crs_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (w_comp_crs_v_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (w_comp_crs_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (w_comp_crs_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (w_comp_crs_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (w_comp_crs_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (w_comp_crs_α_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (w_comp_crs_α_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (w_comp_crs_α_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (w_comp_crs_α_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (w_comp_crs_α_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (w_comp_crs_β_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (w_comp_crs_β_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (w_comp_crs_β_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (w_comp_crs_β_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (w_comp_crs_β_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  ∑ i in (finset.fin_range n_wit), (w_comp_crs_powers_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (w_comp_crs_α_powers_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  w_comp_crs_α • crs_α
  +   
  w_comp_crs_γ • crs_γ
  +   
  w_comp_crs_β_v_γ • crs_β_v_γ
  +   
  w_comp_crs_β_w_γ • crs_β_w_γ
  +   
  w_comp_crs_β_y_γ • crs_β_y_γ
  +   
  w_comp_crs_t • crs_t
  +   
  w_comp_crs_v_0 • crs_v_0
  +   
  w_comp_crs_w_0 • crs_w_0
  +   
  w_comp_crs_y_0 • crs_y_0

parameters {y_comp_crs_v_wit_k_of_s : fin n_wit →  F}
parameters {y_comp_crs_v_stmt_k_of_s : fin n_stmt →  F}
parameters {y_comp_crs_w_wit_k_of_s : fin n_wit →  F}
parameters {y_comp_crs_w_stmt_k_of_s : fin n_stmt →  F}
parameters {y_comp_crs_y_wit_k_of_s : fin n_wit →  F}
parameters {y_comp_crs_y_stmt_k_of_s : fin n_stmt →  F}

parameters {y_comp_crs_α_v_wit_k_of_s : fin n_wit →  F}
-- parameters {y_comp_crs_α_v_stmt_k_of_s : fin n_stmt →  F}
parameters {y_comp_crs_α_w_wit_k_of_s : fin n_wit →  F}
parameters {y_comp_crs_α_w_stmt_k_of_s : fin n_stmt →  F}
parameters {y_comp_crs_α_y_wit_k_of_s : fin n_wit →  F}
parameters {y_comp_crs_α_y_stmt_k_of_s : fin n_stmt →  F}

parameters {y_comp_crs_β_v_wit_k_of_s : fin n_wit →  F}
-- parameters {y_comp_crs_β_v_stmt_k_of_s : fin n_stmt →  F}
parameters {y_comp_crs_β_w_wit_k_of_s : fin n_wit →  F}
parameters {y_comp_crs_β_w_stmt_k_of_s : fin n_stmt →  F}
parameters {y_comp_crs_β_y_wit_k_of_s : fin n_wit →  F}
parameters {y_comp_crs_β_y_stmt_k_of_s : fin n_stmt →  F}

parameters {y_comp_crs_powers_of_s : fin n_wit →  F}
parameters {y_comp_crs_α_powers_of_s : fin n_stmt →  F}

parameters {y_comp_crs_α : F}
parameters {y_comp_crs_γ : F}
parameters {y_comp_crs_β_v_γ : F}
parameters {y_comp_crs_β_w_γ : F}
parameters {y_comp_crs_β_y_γ : F}
parameters {y_comp_crs_t : F}
parameters {y_comp_crs_v_0 : F}
parameters {y_comp_crs_w_0 : F}
parameters {y_comp_crs_y_0 : F}


/-- Polynomial forms of the adversary's proof representation -/
def proof_y : mv_polynomial vars F := 
  ∑ i in (finset.fin_range n_wit), (y_comp_crs_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (y_comp_crs_v_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (y_comp_crs_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (y_comp_crs_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (y_comp_crs_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (y_comp_crs_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (y_comp_crs_α_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (y_comp_crs_α_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (y_comp_crs_α_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (y_comp_crs_α_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (y_comp_crs_α_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (y_comp_crs_β_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (y_comp_crs_β_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (y_comp_crs_β_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (y_comp_crs_β_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (y_comp_crs_β_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  ∑ i in (finset.fin_range n_wit), (y_comp_crs_powers_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (y_comp_crs_α_powers_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  y_comp_crs_α • crs_α
  +   
  y_comp_crs_γ • crs_γ
  +   
  y_comp_crs_β_v_γ • crs_β_v_γ
  +   
  y_comp_crs_β_w_γ • crs_β_w_γ
  +   
  y_comp_crs_β_y_γ • crs_β_y_γ
  +   
  y_comp_crs_t • crs_t
  +   
  y_comp_crs_v_0 • crs_v_0
  +   
  y_comp_crs_w_0 • crs_w_0
  +   
  y_comp_crs_y_0 • crs_y_0

parameters {h_comp_crs_v_wit_k_of_s : fin n_wit →  F}
parameters {h_comp_crs_v_stmt_k_of_s : fin n_stmt →  F}
parameters {h_comp_crs_w_wit_k_of_s : fin n_wit →  F}
parameters {h_comp_crs_w_stmt_k_of_s : fin n_stmt →  F}
parameters {h_comp_crs_y_wit_k_of_s : fin n_wit →  F}
parameters {h_comp_crs_y_stmt_k_of_s : fin n_stmt →  F}

parameters {h_comp_crs_α_v_wit_k_of_s : fin n_wit →  F}
-- parameters {h_comp_crs_α_v_stmt_k_of_s : fin n_stmt →  F}
parameters {h_comp_crs_α_w_wit_k_of_s : fin n_wit →  F}
parameters {h_comp_crs_α_w_stmt_k_of_s : fin n_stmt →  F}
parameters {h_comp_crs_α_y_wit_k_of_s : fin n_wit →  F}
parameters {h_comp_crs_α_y_stmt_k_of_s : fin n_stmt →  F}

parameters {h_comp_crs_β_v_wit_k_of_s : fin n_wit →  F}
-- parameters {h_comp_crs_β_v_stmt_k_of_s : fin n_stmt →  F}
parameters {h_comp_crs_β_w_wit_k_of_s : fin n_wit →  F}
parameters {h_comp_crs_β_w_stmt_k_of_s : fin n_stmt →  F}
parameters {h_comp_crs_β_y_wit_k_of_s : fin n_wit →  F}
parameters {h_comp_crs_β_y_stmt_k_of_s : fin n_stmt →  F}

parameters {h_comp_crs_powers_of_s : fin n_wit →  F}
parameters {h_comp_crs_α_powers_of_s : fin n_stmt →  F}

parameters {h_comp_crs_α : F}
parameters {h_comp_crs_γ : F}
parameters {h_comp_crs_β_v_γ : F}
parameters {h_comp_crs_β_w_γ : F}
parameters {h_comp_crs_β_y_γ : F}
parameters {h_comp_crs_t : F}
parameters {h_comp_crs_v_0 : F}
parameters {h_comp_crs_w_0 : F}
parameters {h_comp_crs_y_0 : F}


/-- Polynomial forms of the adversary's proof representation -/
def proof_h : mv_polynomial vars F := 
  ∑ i in (finset.fin_range n_wit), (h_comp_crs_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (h_comp_crs_v_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (h_comp_crs_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (h_comp_crs_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (h_comp_crs_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (h_comp_crs_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (h_comp_crs_α_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (h_comp_crs_α_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (h_comp_crs_α_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (h_comp_crs_α_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (h_comp_crs_α_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (h_comp_crs_β_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (h_comp_crs_β_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (h_comp_crs_β_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (h_comp_crs_β_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (h_comp_crs_β_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  ∑ i in (finset.fin_range n_wit), (h_comp_crs_powers_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (h_comp_crs_α_powers_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  h_comp_crs_α • crs_α
  +   
  h_comp_crs_γ • crs_γ
  +   
  h_comp_crs_β_v_γ • crs_β_v_γ
  +   
  h_comp_crs_β_w_γ • crs_β_w_γ
  +   
  h_comp_crs_β_y_γ • crs_β_y_γ
  +   
  h_comp_crs_t • crs_t
  +   
  h_comp_crs_v_0 • crs_v_0
  +   
  h_comp_crs_w_0 • crs_w_0
  +   
  h_comp_crs_y_0 • crs_y_0

parameters {α_v_wit_comp_crs_v_wit_k_of_s : fin n_wit →  F}
parameters {α_v_wit_comp_crs_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_v_wit_comp_crs_w_wit_k_of_s : fin n_wit →  F}
parameters {α_v_wit_comp_crs_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_v_wit_comp_crs_y_wit_k_of_s : fin n_wit →  F}
parameters {α_v_wit_comp_crs_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_v_wit_comp_crs_α_v_wit_k_of_s : fin n_wit →  F}
-- parameters {α_v_wit_comp_crs_α_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_v_wit_comp_crs_α_w_wit_k_of_s : fin n_wit →  F}
parameters {α_v_wit_comp_crs_α_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_v_wit_comp_crs_α_y_wit_k_of_s : fin n_wit →  F}
parameters {α_v_wit_comp_crs_α_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_v_wit_comp_crs_β_v_wit_k_of_s : fin n_wit →  F}
-- parameters {α_v_wit_comp_crs_β_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_v_wit_comp_crs_β_w_wit_k_of_s : fin n_wit →  F}
parameters {α_v_wit_comp_crs_β_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_v_wit_comp_crs_β_y_wit_k_of_s : fin n_wit →  F}
parameters {α_v_wit_comp_crs_β_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_v_wit_comp_crs_powers_of_s : fin n_wit →  F}
parameters {α_v_wit_comp_crs_α_powers_of_s : fin n_stmt →  F}

parameters {α_v_wit_comp_crs_α : F}
parameters {α_v_wit_comp_crs_γ : F}
parameters {α_v_wit_comp_crs_β_v_γ : F}
parameters {α_v_wit_comp_crs_β_w_γ : F}
parameters {α_v_wit_comp_crs_β_y_γ : F}
parameters {α_v_wit_comp_crs_t : F}
parameters {α_v_wit_comp_crs_v_0 : F}
parameters {α_v_wit_comp_crs_w_0 : F}
parameters {α_v_wit_comp_crs_y_0 : F}


/-- Polynomial forms of the adversary's proof representation -/
def proof_α_v_wit : mv_polynomial vars F := 
  ∑ i in (finset.fin_range n_wit), (α_v_wit_comp_crs_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_v_wit_comp_crs_v_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_v_wit_comp_crs_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_v_wit_comp_crs_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_v_wit_comp_crs_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_v_wit_comp_crs_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_v_wit_comp_crs_α_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_v_wit_comp_crs_α_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_v_wit_comp_crs_α_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_v_wit_comp_crs_α_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_v_wit_comp_crs_α_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_v_wit_comp_crs_β_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_v_wit_comp_crs_β_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_v_wit_comp_crs_β_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_v_wit_comp_crs_β_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_v_wit_comp_crs_β_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  ∑ i in (finset.fin_range n_wit), (α_v_wit_comp_crs_powers_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_v_wit_comp_crs_α_powers_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  α_v_wit_comp_crs_α • crs_α
  +   
  α_v_wit_comp_crs_γ • crs_γ
  +   
  α_v_wit_comp_crs_β_v_γ • crs_β_v_γ
  +   
  α_v_wit_comp_crs_β_w_γ • crs_β_w_γ
  +   
  α_v_wit_comp_crs_β_y_γ • crs_β_y_γ
  +   
  α_v_wit_comp_crs_t • crs_t
  +   
  α_v_wit_comp_crs_v_0 • crs_v_0
  +   
  α_v_wit_comp_crs_w_0 • crs_w_0
  +   
  α_v_wit_comp_crs_y_0 • crs_y_0

parameters {α_w_comp_crs_v_wit_k_of_s : fin n_wit →  F}
parameters {α_w_comp_crs_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_w_comp_crs_w_wit_k_of_s : fin n_wit →  F}
parameters {α_w_comp_crs_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_w_comp_crs_y_wit_k_of_s : fin n_wit →  F}
parameters {α_w_comp_crs_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_w_comp_crs_α_v_wit_k_of_s : fin n_wit →  F}
-- parameters {α_w_comp_crs_α_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_w_comp_crs_α_w_wit_k_of_s : fin n_wit →  F}
parameters {α_w_comp_crs_α_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_w_comp_crs_α_y_wit_k_of_s : fin n_wit →  F}
parameters {α_w_comp_crs_α_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_w_comp_crs_β_v_wit_k_of_s : fin n_wit →  F}
-- parameters {α_w_comp_crs_β_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_w_comp_crs_β_w_wit_k_of_s : fin n_wit →  F}
parameters {α_w_comp_crs_β_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_w_comp_crs_β_y_wit_k_of_s : fin n_wit →  F}
parameters {α_w_comp_crs_β_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_w_comp_crs_powers_of_s : fin n_wit →  F}
parameters {α_w_comp_crs_α_powers_of_s : fin n_stmt →  F}

parameters {α_w_comp_crs_α : F}
parameters {α_w_comp_crs_γ : F}
parameters {α_w_comp_crs_β_v_γ : F}
parameters {α_w_comp_crs_β_w_γ : F}
parameters {α_w_comp_crs_β_y_γ : F}
parameters {α_w_comp_crs_t : F}
parameters {α_w_comp_crs_v_0 : F}
parameters {α_w_comp_crs_w_0 : F}
parameters {α_w_comp_crs_y_0 : F}


/-- Polynomial forms of the adversary's proof representation -/
def proof_α_w : mv_polynomial vars F := 
  ∑ i in (finset.fin_range n_wit), (α_w_comp_crs_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_w_comp_crs_v_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_w_comp_crs_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_w_comp_crs_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_w_comp_crs_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_w_comp_crs_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_w_comp_crs_α_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_w_comp_crs_α_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_w_comp_crs_α_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_w_comp_crs_α_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_w_comp_crs_α_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_w_comp_crs_β_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_w_comp_crs_β_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_w_comp_crs_β_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_w_comp_crs_β_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_w_comp_crs_β_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  ∑ i in (finset.fin_range n_wit), (α_w_comp_crs_powers_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_w_comp_crs_α_powers_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  α_w_comp_crs_α • crs_α
  +   
  α_w_comp_crs_γ • crs_γ
  +   
  α_w_comp_crs_β_v_γ • crs_β_v_γ
  +   
  α_w_comp_crs_β_w_γ • crs_β_w_γ
  +   
  α_w_comp_crs_β_y_γ • crs_β_y_γ
  +   
  α_w_comp_crs_t • crs_t
  +   
  α_w_comp_crs_v_0 • crs_v_0
  +   
  α_w_comp_crs_w_0 • crs_w_0
  +   
  α_w_comp_crs_y_0 • crs_y_0


parameters {α_y_comp_crs_v_wit_k_of_s : fin n_wit →  F}
parameters {α_y_comp_crs_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_y_comp_crs_w_wit_k_of_s : fin n_wit →  F}
parameters {α_y_comp_crs_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_y_comp_crs_y_wit_k_of_s : fin n_wit →  F}
parameters {α_y_comp_crs_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_y_comp_crs_α_v_wit_k_of_s : fin n_wit →  F}
-- parameters {α_y_comp_crs_α_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_y_comp_crs_α_w_wit_k_of_s : fin n_wit →  F}
parameters {α_y_comp_crs_α_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_y_comp_crs_α_y_wit_k_of_s : fin n_wit →  F}
parameters {α_y_comp_crs_α_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_y_comp_crs_β_v_wit_k_of_s : fin n_wit →  F}
-- parameters {α_y_comp_crs_β_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_y_comp_crs_β_w_wit_k_of_s : fin n_wit →  F}
parameters {α_y_comp_crs_β_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_y_comp_crs_β_y_wit_k_of_s : fin n_wit →  F}
parameters {α_y_comp_crs_β_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_y_comp_crs_powers_of_s : fin n_wit →  F}
parameters {α_y_comp_crs_α_powers_of_s : fin n_stmt →  F}

parameters {α_y_comp_crs_α : F}
parameters {α_y_comp_crs_γ : F}
parameters {α_y_comp_crs_β_v_γ : F}
parameters {α_y_comp_crs_β_w_γ : F}
parameters {α_y_comp_crs_β_y_γ : F}
parameters {α_y_comp_crs_t : F}
parameters {α_y_comp_crs_v_0 : F}
parameters {α_y_comp_crs_w_0 : F}
parameters {α_y_comp_crs_y_0 : F}


/-- Polynomial forms of the adversary's proof representation -/
def proof_α_y : mv_polynomial vars F := 
  ∑ i in (finset.fin_range n_wit), (α_y_comp_crs_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_y_comp_crs_v_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_y_comp_crs_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_y_comp_crs_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_y_comp_crs_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_y_comp_crs_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_y_comp_crs_α_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_y_comp_crs_α_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_y_comp_crs_α_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_y_comp_crs_α_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_y_comp_crs_α_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_y_comp_crs_β_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_y_comp_crs_β_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_y_comp_crs_β_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_y_comp_crs_β_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_y_comp_crs_β_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  ∑ i in (finset.fin_range n_wit), (α_y_comp_crs_powers_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_y_comp_crs_α_powers_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  α_y_comp_crs_α • crs_α
  +   
  α_y_comp_crs_γ • crs_γ
  +   
  α_y_comp_crs_β_v_γ • crs_β_v_γ
  +   
  α_y_comp_crs_β_w_γ • crs_β_w_γ
  +   
  α_y_comp_crs_β_y_γ • crs_β_y_γ
  +   
  α_y_comp_crs_t • crs_t
  +   
  α_y_comp_crs_v_0 • crs_v_0
  +   
  α_y_comp_crs_w_0 • crs_w_0
  +   
  α_y_comp_crs_y_0 • crs_y_0

parameters {α_h_comp_crs_v_wit_k_of_s : fin n_wit →  F}
parameters {α_h_comp_crs_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_h_comp_crs_w_wit_k_of_s : fin n_wit →  F}
parameters {α_h_comp_crs_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_h_comp_crs_y_wit_k_of_s : fin n_wit →  F}
parameters {α_h_comp_crs_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_h_comp_crs_α_v_wit_k_of_s : fin n_wit →  F}
-- parameters {α_h_comp_crs_α_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_h_comp_crs_α_w_wit_k_of_s : fin n_wit →  F}
parameters {α_h_comp_crs_α_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_h_comp_crs_α_y_wit_k_of_s : fin n_wit →  F}
parameters {α_h_comp_crs_α_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_h_comp_crs_β_v_wit_k_of_s : fin n_wit →  F}
-- parameters {α_h_comp_crs_β_v_stmt_k_of_s : fin n_stmt →  F}
parameters {α_h_comp_crs_β_w_wit_k_of_s : fin n_wit →  F}
parameters {α_h_comp_crs_β_w_stmt_k_of_s : fin n_stmt →  F}
parameters {α_h_comp_crs_β_y_wit_k_of_s : fin n_wit →  F}
parameters {α_h_comp_crs_β_y_stmt_k_of_s : fin n_stmt →  F}

parameters {α_h_comp_crs_powers_of_s : fin n_wit →  F}
parameters {α_h_comp_crs_α_powers_of_s : fin n_stmt →  F}

parameters {α_h_comp_crs_α : F}
parameters {α_h_comp_crs_γ : F}
parameters {α_h_comp_crs_β_v_γ : F}
parameters {α_h_comp_crs_β_w_γ : F}
parameters {α_h_comp_crs_β_y_γ : F}
parameters {α_h_comp_crs_t : F}
parameters {α_h_comp_crs_v_0 : F}
parameters {α_h_comp_crs_w_0 : F}
parameters {α_h_comp_crs_y_0 : F}


/-- Polynomial forms of the adversary's proof representation -/
def proof_α_h : mv_polynomial vars F := 
  ∑ i in (finset.fin_range n_wit), (α_h_comp_crs_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_h_comp_crs_v_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_h_comp_crs_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_h_comp_crs_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_h_comp_crs_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_h_comp_crs_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_h_comp_crs_α_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_h_comp_crs_α_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_h_comp_crs_α_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_h_comp_crs_α_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_h_comp_crs_α_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_h_comp_crs_β_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_h_comp_crs_β_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_h_comp_crs_β_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (α_h_comp_crs_β_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_h_comp_crs_β_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  ∑ i in (finset.fin_range n_wit), (α_h_comp_crs_powers_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (α_h_comp_crs_α_powers_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  α_h_comp_crs_α • crs_α
  +   
  α_h_comp_crs_γ • crs_γ
  +   
  α_h_comp_crs_β_v_γ • crs_β_v_γ
  +   
  α_h_comp_crs_β_w_γ • crs_β_w_γ
  +   
  α_h_comp_crs_β_y_γ • crs_β_y_γ
  +   
  α_h_comp_crs_t • crs_t
  +   
  α_h_comp_crs_v_0 • crs_v_0
  +   
  α_h_comp_crs_w_0 • crs_w_0
  +   
  α_h_comp_crs_y_0 • crs_y_0

parameters {β_comp_crs_v_wit_k_of_s : fin n_wit →  F}
parameters {β_comp_crs_v_stmt_k_of_s : fin n_stmt →  F}
parameters {β_comp_crs_w_wit_k_of_s : fin n_wit →  F}
parameters {β_comp_crs_w_stmt_k_of_s : fin n_stmt →  F}
parameters {β_comp_crs_y_wit_k_of_s : fin n_wit →  F}
parameters {β_comp_crs_y_stmt_k_of_s : fin n_stmt →  F}

parameters {β_comp_crs_α_v_wit_k_of_s : fin n_wit →  F}
-- parameters {β_comp_crs_α_v_stmt_k_of_s : fin n_stmt →  F}
parameters {β_comp_crs_α_w_wit_k_of_s : fin n_wit →  F}
parameters {β_comp_crs_α_w_stmt_k_of_s : fin n_stmt →  F}
parameters {β_comp_crs_α_y_wit_k_of_s : fin n_wit →  F}
parameters {β_comp_crs_α_y_stmt_k_of_s : fin n_stmt →  F}

parameters {β_comp_crs_β_v_wit_k_of_s : fin n_wit →  F}
-- parameters {β_comp_crs_β_v_stmt_k_of_s : fin n_stmt →  F}
parameters {β_comp_crs_β_w_wit_k_of_s : fin n_wit →  F}
parameters {β_comp_crs_β_w_stmt_k_of_s : fin n_stmt →  F}
parameters {β_comp_crs_β_y_wit_k_of_s : fin n_wit →  F}
parameters {β_comp_crs_β_y_stmt_k_of_s : fin n_stmt →  F}

parameters {β_comp_crs_powers_of_s : fin n_wit →  F}
parameters {β_comp_crs_α_powers_of_s : fin n_stmt →  F}

parameters {β_comp_crs_α : F}
parameters {β_comp_crs_γ : F}
parameters {β_comp_crs_β_v_γ : F}
parameters {β_comp_crs_β_w_γ : F}
parameters {β_comp_crs_β_y_γ : F}
parameters {β_comp_crs_t : F}
parameters {β_comp_crs_v_0 : F}
parameters {β_comp_crs_w_0 : F}
parameters {β_comp_crs_y_0 : F}


/-- Polynomial forms of the adversary's proof representation -/
def proof_β : mv_polynomial vars F := 
  ∑ i in (finset.fin_range n_wit), (β_comp_crs_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (β_comp_crs_v_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (β_comp_crs_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (β_comp_crs_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (β_comp_crs_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (β_comp_crs_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (β_comp_crs_α_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (β_comp_crs_α_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (β_comp_crs_α_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (β_comp_crs_α_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (β_comp_crs_α_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (β_comp_crs_β_v_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (β_comp_crs_β_y_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (β_comp_crs_β_y_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  + 
  ∑ i in (finset.fin_range n_wit), (β_comp_crs_β_w_wit_k_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (β_comp_crs_β_w_stmt_k_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  ∑ i in (finset.fin_range n_wit), (β_comp_crs_powers_of_s i) • (crs_v_wit_k_of_s i)
  +
  ∑ i in (finset.fin_range n_stmt), (β_comp_crs_α_powers_of_s i) • (crs_v_stmt_k_of_s i)
  +   
  β_comp_crs_α • crs_α
  +   
  β_comp_crs_γ • crs_γ
  +   
  β_comp_crs_β_v_γ • crs_β_v_γ
  +   
  β_comp_crs_β_w_γ • crs_β_w_γ
  +   
  β_comp_crs_β_y_γ • crs_β_y_γ
  +   
  β_comp_crs_t • crs_t
  +   
  β_comp_crs_v_0 • crs_v_0
  +   
  β_comp_crs_w_0 • crs_w_0
  +   
  β_comp_crs_y_0 • crs_y_0


-- Single variable form of V_wit
def v_wit_sv (a_wit : fin n_wit → F) : polynomial F 
:= ∑ i in finset.fin_range n_wit, a_wit i • v_wit i

/-- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def v_stmt_sv (a_stmt : fin n_stmt → F) : polynomial F 
:= ∑ i in (finset.fin_range n_stmt), a_stmt i • v_stmt i

/-- V_stmt as a multivariable polynomial of vars.X -/
def v_stmt_mv (a_stmt : fin n_stmt → F) : mv_polynomial vars F 
:= (v_stmt_sv a_stmt).eval₂ mv_polynomial.C s_poly

/-- V as a multivariable polynomial -/
def proof_v (a_stmt : fin n_stmt → F) : mv_polynomial vars F 
:= v_stmt_mv a_stmt + proof_v_wit

/-- Multivariable version of t -/
def t_mv : mv_polynomial vars F := t.eval₂ mv_polynomial.C s_poly

/-- Show that if the adversary polynomials obey the equations, 
then the coefficients give a satisfying witness. 
-/
theorem soundness (a_stmt : fin n_stmt → F ) : 
  (0 < m)
  -> proof_α_h = proof_h * crs_α
  -> proof_α_v_wit = proof_v_wit * crs_α
  -> proof_α_y = proof_y * crs_α
  -> proof_α_w = proof_w * crs_α
  -> proof_β * crs_γ = crs_β_v_γ * (proof_v a_stmt) + crs_β_y_γ * proof_y + crs_β_w_γ * proof_w
  -- NOTE: Why does this require 3 pairings according to 
  -> proof_h * t_mv + crs_y_0 + proof_y = (crs_v_0 + v_stmt_mv a_stmt + proof_v a_stmt) * (crs_w_0 + proof_w)
  -- NOTE: This is what the paper says, but it seems wrong
  -> (satisfying a_stmt v_wit_comp_crs_v_wit_k_of_s) 
:=
begin
  sorry
end



end
