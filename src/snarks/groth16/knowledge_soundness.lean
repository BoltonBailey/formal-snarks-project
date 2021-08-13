/-
Author: Bolton Bailey
-/
import snarks.groth16.declarations

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

open mv_polynomial groth16

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


-- /-- Helper for converting mv_polynomial to single -/
-- @[simp]
-- def singlify : vars -> polynomial F
-- | vars.x := polynomial.X 
-- | vars.α := 1
-- | vars.β := 1
-- | vars.γ := 1
-- | vars.δ := 1



-- -- Multivariable version of t 
-- def t_mv : mv_polynomial vars F := t.eval₂ mv_polynomial.C (X vars.x)

-- -- V_stmt as a multivariable polynomial of vars.X 
-- def V_stmt_mv (a_stmt : fin n_stmt → F) : mv_polynomial vars F 
-- := (V_stmt_sv a_stmt).eval₂ mv_polynomial.C (X vars.x)



run_cmd mk_simp_attr `crs
run_cmd tactic.add_doc_string `simp_attr.crs "Attribute for defintions of CRS elements"

-- TODO define the crs elements as field elements rather than polyls
-- Use the pairing equation to get an equation involving these field elements with + * and divisions
-- Multiply through by delta gamma, to get an equation without divisions, only + and *
-- Construct the corresponding mv_polynomials, prove that there exists a small set of valuations such that either the polynomials are equal, or the field elements belong to that evaluation.

-- Toxic waste elements
-- parameter {f : vars → F}

/-- The crs elements 
These funtions are actually multivariate Laurent polynomials of the toxic waste samples, 
but we represent them here as functions on assignments of the variables to values.
-/
@[crs]
def crs_α  (f : vars → F) (x : F) : F := f vars.α
@[crs]
def crs_β (f : vars → F) (x : F) : F := f vars.β
@[crs]
def crs_γ (f : vars → F) (x : F) : F := f vars.γ
@[crs]
def crs_δ (f : vars → F) (x : F) : F := f vars.δ
@[crs]
def crs_powers_of_x (i : fin n_var) (f : vars → F) (x : F) : F := (x)^(i : ℕ)
@[crs]
def crs_l (i : fin n_stmt) (f : vars → F) (x : F) : F := 
((f vars.β / f vars.γ) * (u_stmt i).eval (x)
+
(f vars.α / f vars.γ) * (v_stmt i).eval (x)
+
(w_stmt i).eval (x)) / f vars.γ
@[crs]
def crs_m (i : fin n_wit) (f : vars → F) (x : F) : F := 
((f vars.β / f vars.δ) * (u_wit i).eval (x)
+
(f vars.α / f vars.δ) * (v_wit i).eval (x)
+
(w_wit i).eval (x)) / f vars.δ
@[crs]
def crs_n (i : fin (n_var - 1)) (f : vars → F) (x : F) : F := 
(x)^(i : ℕ) * t.eval (x) / f vars.δ

/-- The coefficients of the CRS elements in the algebraic adversary's representation -/
parameters {A_α A_β A_γ A_δ B_α B_β B_γ B_δ C_α C_β C_γ C_δ  : F}
parameters {A_x B_x C_x : fin n_var → F}
parameters {A_l B_l C_l : fin n_stmt → F}
parameters {A_m B_m C_m : fin n_wit → F}
parameters {A_h B_h C_h : fin (n_var-1) → F}


/-- Polynomial forms of the adversary's proof representation -/
def A (f : vars → F) (x : F) : F := 
  A_α * crs_α f x
  +
  A_β * crs_β f x
  + 
  A_γ * crs_γ f x
  +
  A_δ * crs_δ f x
  +
  ∑ i in (finset.fin_range n_var), (A_x i) * (crs_powers_of_x i f x)
  +
  ∑ i in (finset.fin_range n_stmt), (A_l i) * (crs_l i f x)
  +
  ∑ i in (finset.fin_range n_wit), (A_m i) * (crs_m i f x)
  +
  ∑ i in (finset.fin_range (n_var-1)), (A_h i) * (crs_n i f x)

def B (f : vars → F) (x : F) : F  := 
  B_α * crs_α f x
  +
  B_β * crs_β f x
  + 
  B_γ * crs_γ f x
  +
  B_δ * crs_δ f x
  +
  ∑ i in (finset.fin_range n_var), (B_x i) * (crs_powers_of_x i f x)
  +
  ∑ i in (finset.fin_range n_stmt), (B_l i) * (crs_l i f x)
  +
  ∑ i in (finset.fin_range n_wit), (B_m i) * (crs_m i f x)
  +
  ∑ i in (finset.fin_range (n_var - 1)), (B_h i) * (crs_n i f x)

def C (f : vars → F) (x : F) : F  := 
  C_α * crs_α f x
  +
  C_β * crs_β f x
  + 
  C_γ * crs_γ f x
  +
  C_δ * crs_δ f x
  +
  ∑ i in (finset.fin_range n_var), (C_x i) * (crs_powers_of_x i f x)
  +
  ∑ i in (finset.fin_range n_stmt), (C_l i) * (crs_l i f x)
  +
  ∑ i in (finset.fin_range n_wit), (C_m i) * (crs_m i f x)
  +
  ∑ i in (finset.fin_range (n_var-1)), (C_h i) * (crs_n i f x)


local notation `groth16polynomial` := mv_polynomial vars (polynomial F)


/-- The modified crs elements 
these are multivariate (non-Laurent!) polynomials of the toxic waste samples, 
obtained by multiplying the Laurent polynomial forms of the CRS through by γδ. 
We will later prove that the laurent polynomial equation is equivalent to a similar equation of the modified crs elements, allowing us to construct a proof in terms of polynomials -/
@[crs]
def crs'_α  : groth16polynomial := X vars.α * X vars.γ * X vars.δ
@[crs]
def crs'_β : groth16polynomial := X vars.β * X vars.γ * X vars.δ
@[crs]
def crs'_γ : groth16polynomial := X vars.γ * X vars.γ * X vars.δ
@[crs]
def crs'_δ : groth16polynomial := X vars.δ * X vars.γ * X vars.δ
@[crs]
def crs'_powers_of_x (i : fin n_var) : (groth16polynomial) := mv_polynomial.C (polynomial.X ^ (i : ℕ)) * X vars.γ * X vars.δ
-- I define prodcuts of these crs elements without the division, then later claim identities. Is this right?
@[crs]
def crs'_l (i : fin n_stmt) : (groth16polynomial) := 
(X vars.β * X vars.δ) * mv_polynomial.C (u_stmt i)
+
(X vars.α * X vars.δ) * mv_polynomial.C (v_stmt i)
+
X vars.δ * mv_polynomial.C (w_stmt i)
@[crs]
def crs'_m (i : fin n_wit) : (groth16polynomial) := 
(X vars.β * X vars.γ) * mv_polynomial.C (u_wit i)
+
(X vars.α * X vars.γ) * mv_polynomial.C (v_wit i)
+
X vars.γ * mv_polynomial.C (w_wit i)
@[crs]
def crs'_t (i : fin (n_var - 1)) : (groth16polynomial) := 
X vars.γ * mv_polynomial.C ((polynomial.X)^(i : ℕ) * t)


/-- Polynomial forms of the adversary's proof representation -/
def A'  : groth16polynomial := 
  A_α • crs'_α
  +
  A_β • crs'_β
  + 
  A_γ • crs'_γ
  +
  A_δ • crs'_δ
  +
  ∑ i in (finset.fin_range n_var), (A_x i) • (crs'_powers_of_x i)
  +
  ∑ i in (finset.fin_range n_stmt), (A_l i) • (crs'_l i)
  +
  ∑ i in (finset.fin_range n_wit), (A_m i) • (crs'_m i)
  +
  ∑ i in (finset.fin_range (n_var - 1)), (A_h i) • (crs'_t i)

def B' : groth16polynomial := 
  B_α • crs'_α
  +
  B_β • crs'_β
  + 
  B_γ • crs'_γ
  +
  B_δ • crs'_δ
  +
  ∑ i in (finset.fin_range n_var), (B_x i) • (crs'_powers_of_x i)
  +
  ∑ i in (finset.fin_range n_stmt), (B_l i) • (crs'_l i)
  +
  ∑ i in (finset.fin_range n_wit), (B_m i) • (crs'_m i)
  +
  ∑ i in (finset.fin_range (n_var - 1)), (B_h i) • (crs'_t i)

def C' : groth16polynomial := 
  C_α • crs'_α
  +
  C_β • crs'_β
  + 
  C_γ • crs'_γ
  +
  C_δ • crs'_δ
  +
  ∑ i in (finset.fin_range n_var), (C_x i) • (crs'_powers_of_x i)
  +
  ∑ i in (finset.fin_range n_stmt), (C_l i) • (crs'_l i)
  +
  ∑ i in (finset.fin_range n_wit), (C_m i) • (crs'_m i)
  +
  ∑ i in (finset.fin_range (n_var-1)), (C_h i) • (crs'_t i)

-- def A_x_poly : groth16polynomial := ∑ i in (finset.fin_range n_var), (A_x i) • mv_polynomial.C (polynomial.X ^ (i : ℕ))
-- def A_l_u_poly : groth16polynomial := ∑ i in (finset.fin_range n_stmt), (A_l i) • mv_polynomial.C (u_stmt i)
-- def A_l_v_poly : groth16polynomial := ∑ i in (finset.fin_range n_stmt), (A_l i) • mv_polynomial.C (v_stmt i)
-- def A_l_w_poly : groth16polynomial := ∑ i in (finset.fin_range n_stmt), (A_l i) • mv_polynomial.C (w_stmt i)
-- def A_m_u_poly : groth16polynomial := ∑ i in (finset.fin_range n_wit), (A_m i) • mv_polynomial.C (u_wit i)
-- def A_m_v_poly : groth16polynomial := ∑ i in (finset.fin_range n_wit), (A_m i) • mv_polynomial.C (v_wit i)
-- def A_m_w_poly : groth16polynomial := ∑ i in (finset.fin_range n_wit), (A_m i) • mv_polynomial.C (w_wit i)
-- def A_h_t_poly : groth16polynomial := ∑ i in (finset.fin_range (n_var - 1)), (A_h i) • mv_polynomial.C ((polynomial.X)^(i : ℕ) * t)

-- lemma A_extract_vars : A' = 
--   A_α • crs'_α
--   +
--   A_β • crs'_β
--   + 
--   A_γ • crs'_γ
--   +
--   A_δ • crs'_δ
--   +
--   A_x_poly * X vars.γ * X vars.δ
--   +
--   A_l_u_poly * X vars.β * X vars.δ
--   +
--   A_l_v_poly * X vars.α * X vars.δ
--   +
--   A_l_w_poly * X vars.δ
--   +
--   A_m_u_poly * X vars.β * X vars.γ
--   +
--   A_m_v_poly * X vars.α * X vars.γ
--   +
--   A_m_w_poly * X vars.γ
--   +
--   A_h_t_poly * X vars.γ
-- :=
-- begin
--   rw A',
--   simp only with crs,
--   sorry,
-- end

-- def B_x_poly : groth16polynomial := ∑ i in (finset.fin_range n_var), (B_x i) • mv_polynomial.C (polynomial.X ^ (i : ℕ))
-- def B_l_u_poly : groth16polynomial := ∑ i in (finset.fin_range n_stmt), (B_l i) • mv_polynomial.C (u_stmt i)
-- def B_l_v_poly : groth16polynomial := ∑ i in (finset.fin_range n_stmt), (B_l i) • mv_polynomial.C (v_stmt i)
-- def B_l_w_poly : groth16polynomial := ∑ i in (finset.fin_range n_stmt), (B_l i) • mv_polynomial.C (w_stmt i)
-- def B_m_u_poly : groth16polynomial := ∑ i in (finset.fin_range n_wit), (B_m i) • mv_polynomial.C (u_wit i)
-- def B_m_v_poly : groth16polynomial := ∑ i in (finset.fin_range n_wit), (B_m i) • mv_polynomial.C (v_wit i)
-- def B_m_w_poly : groth16polynomial := ∑ i in (finset.fin_range n_wit), (B_m i) • mv_polynomial.C (w_wit i)
-- def B_h_t_poly : groth16polynomial := ∑ i in (finset.fin_range (n_var - 1)), (B_h i) • mv_polynomial.C ((polynomial.X)^(i : ℕ) * t)

-- lemma B_extract_vars : B' = 
--   B_α • crs'_α
--   +
--   B_β • crs'_β
--   + 
--   B_γ • crs'_γ
--   +
--   B_δ • crs'_δ
--   +
--   B_x_poly * X vars.γ * X vars.δ
--   +
--   B_l_u_poly * X vars.β * X vars.δ
--   +
--   B_l_v_poly * X vars.α * X vars.δ
--   +
--   B_l_w_poly * X vars.δ
--   +
--   B_m_u_poly * X vars.β * X vars.γ
--   +
--   B_m_v_poly * X vars.α * X vars.γ
--   +
--   B_m_w_poly * X vars.γ
--   +
--   B_h_t_poly * X vars.γ
-- :=
-- begin
--   rw B',
--   simp only with crs,
--   sorry,
-- end

-- def C_x_poly : groth16polynomial := ∑ i in (finset.fin_range n_var), (C_x i) • mv_polynomial.C (polynomial.X ^ (i : ℕ))
-- def C_l_u_poly : groth16polynomial := ∑ i in (finset.fin_range n_stmt), (C_l i) • mv_polynomial.C (u_stmt i)
-- def C_l_v_poly : groth16polynomial := ∑ i in (finset.fin_range n_stmt), (C_l i) • mv_polynomial.C (v_stmt i)
-- def C_l_w_poly : groth16polynomial := ∑ i in (finset.fin_range n_stmt), (C_l i) • mv_polynomial.C (w_stmt i)
-- def C_m_u_poly : groth16polynomial := ∑ i in (finset.fin_range n_wit), (C_m i) • mv_polynomial.C (u_wit i)
-- def C_m_v_poly : groth16polynomial := ∑ i in (finset.fin_range n_wit), (C_m i) • mv_polynomial.C (v_wit i)
-- def C_m_w_poly : groth16polynomial := ∑ i in (finset.fin_range n_wit), (C_m i) • mv_polynomial.C (w_wit i)
-- def C_h_t_poly : groth16polynomial := ∑ i in (finset.fin_range (n_var - 1)), (C_h i) • mv_polynomial.C ((polynomial.X)^(i : ℕ) * t)

-- lemma C_extract_vars : C' = 
--   C_α • crs'_α
--   +
--   C_β • crs'_β
--   + 
--   C_γ • crs'_γ
--   +
--   C_δ • crs'_δ
--   +
--   C_x_poly * X vars.γ * X vars.δ
--   +
--   C_l_u_poly * X vars.β * X vars.δ
--   +
--   C_l_v_poly * X vars.α * X vars.δ
--   +
--   C_l_w_poly * X vars.δ
--   +
--   C_m_u_poly * X vars.β * X vars.γ
--   +
--   C_m_v_poly * X vars.α * X vars.γ
--   +
--   C_m_w_poly * X vars.γ
--   +
--   C_h_t_poly * X vars.γ
-- :=
-- begin
--   rw C',
--   simp only with crs,
--   sorry,
-- end


def verified (a_stmt : fin n_stmt → F ) : Prop := A * B = crs_α * crs_β + (∑ i in finset.fin_range n_stmt, a_stmt i • crs_l i ) * crs_γ + C * crs_δ

def verified' (a_stmt : fin n_stmt → F ) : Prop := A' * B' = crs'_α * crs'_β + (∑ i in finset.fin_range n_stmt, a_stmt i • crs'_l i ) * crs'_γ + C' * crs'_δ

lemma modification_equivalence (a_stmt : fin n_stmt → F ) : 
  verified' a_stmt
  ↔
  verified a_stmt
:=
begin
  -- Apply functional extensionality to *both* sides.
  -- TODO different now that we switch to mv_poly vars (poly F)
  sorry,

end




open finsupp


lemma coeff0002 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
    (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) *
          ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
        (∑ (x : fin (n_var - 1)) in
             finset.fin_range (n_var - 1),
             polynomial.X ^ (x : ℕ) * (t * polynomial.C (A_h x))) *
          ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
      ((∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) *
           ∑ (x : fin (n_var - 1)) in
             finset.fin_range (n_var - 1),
             polynomial.X ^ (x : ℕ) * (t * polynomial.C (B_h x)) +
         (∑ (x : fin (n_var - 1)) in
              finset.fin_range (n_var - 1),
              polynomial.X ^ (x : ℕ) * (t * polynomial.C (A_h x))) *
           ∑ (x : fin (n_var - 1)) in
             finset.fin_range (n_var - 1),
             polynomial.X ^ (x : ℕ) * (t * polynomial.C (B_h x))) =
    0 :=
begin
  sorry,
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0002 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.δ 0 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0002,
  simp at congr_coeff0002,
  exact congr_coeff0002,
end


-- lemma coeff0002simpler (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
--   ((∑ (x : fin n_wit) in finset.fin_range n_wit, A_m x • w_wit x) 
--     + ∑ (x : fin (n_var - 1)) in
--              finset.fin_range (n_var - 1), A_h x • (polynomial.X ^ (x : ℕ) * t))
--   *
--   ((∑ (x : fin n_wit) in finset.fin_range n_wit, B_m x • w_wit x)  
--     + 
--     ∑ (x : fin (n_var - 1)) in
--              finset.fin_range (n_var - 1), B_h x • (polynomial.X ^ (x : ℕ) * t))
--   =
--   0
--   :=
-- begin
--   simp only with polynomial_nf,
--   rw <-coeff0002 a_stmt eqn,
--   congr,
--   funext,
--   congr,
--   funext,
--   rw mul_assoc,
--   funext,
--   congr,
--   funext,
--   rw mul_assoc,
-- end

lemma coeff0012 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
    ∑ (x : fin n_wit) in
            finset.fin_range n_wit,
            ∑ (x_1 : fin n_var) in finset.fin_range n_var, B_x x_1 • A_m x • (w_wit x * polynomial.X ^ (x_1 : ℕ)) +
          ∑ (x : fin (n_var - 1)) in
            finset.fin_range (n_var - 1),
            ∑ (x_1 : fin n_var) in
              finset.fin_range n_var,
              B_x x_1 • A_h x • (polynomial.X ^ (x : ℕ) * t * polynomial.X ^ (x_1 : ℕ)) +
        ∑ (x : fin n_var) in
          finset.fin_range n_var,
          ∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • A_x x • (polynomial.X ^ (x : ℕ) * w_wit x_1) +
      ∑ (x : fin n_var) in
        finset.fin_range n_var,
        ∑ (x_1 : fin (n_var - 1)) in
          finset.fin_range (n_var - 1),
          B_h x_1 • A_x x • (polynomial.X ^ (x : ℕ) * (polynomial.X ^ (x_1 : ℕ) * t)) =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0012 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.δ 1 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0012,
  simp at congr_coeff0012,
  exact congr_coeff0012,
end

lemma coeff0013 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
      (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * ⇑polynomial.C (A_m x)) * ⇑polynomial.C B_γ +
          (∑ (x : fin (n_var - 1)) in
               finset.fin_range (n_var - 1),
               polynomial.X ^ ↑x * (t * ⇑polynomial.C (A_h x))) *
            ⇑polynomial.C B_γ +
        ⇑polynomial.C A_γ * ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * ⇑polynomial.C (B_m x) +
      ⇑polynomial.C A_γ *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ ↑x * (t * ⇑polynomial.C (B_h x)) =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0013 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.δ 1 + single vars.γ 3)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0013,
  simp at congr_coeff0013,
  exact congr_coeff0013,
end

lemma coeff0022 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, B_γ • A_l x • w_stmt x +
              (∑ (x : fin n_wit) in finset.fin_range n_wit, B_δ • A_m x • w_wit x +
                 ∑ (x : fin (n_var - 1)) in
                   finset.fin_range (n_var - 1),
                   B_δ • A_h x • (polynomial.X ^ (x : ℕ) * t)) +
            ∑ (x : fin n_var) in
              finset.fin_range n_var,
              ∑ (x_1 : fin n_var) in
                finset.fin_range n_var,
                B_x x_1 • A_x x • (polynomial.X ^ (x : ℕ) * polynomial.X ^ (x_1 : ℕ)) +
          ∑ (x : fin n_stmt) in finset.fin_range n_stmt, B_l x • A_γ • w_stmt x +
        ∑ (x : fin n_wit) in finset.fin_range n_wit, B_m x • A_δ • w_wit x +
      ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), B_h x • A_δ • (polynomial.X ^ (x : ℕ) * t) =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, a_stmt x • w_stmt x +
      (∑ (x : fin n_wit) in finset.fin_range n_wit, C_m x • w_wit x +
         ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), C_h x • (polynomial.X ^ (x : ℕ) * t)) 
:=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0022 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.δ 2 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0022,
  simp at congr_coeff0022,
  exact congr_coeff0022,
end

lemma coeff0024 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  B_γ = 0 ∨ A_γ = 0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0024 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.δ 2 + single vars.γ 4)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0024,
  simp at congr_coeff0024,
  exact congr_coeff0024,
end

lemma coeff0033 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  B_γ • A_δ • 1 + B_δ • A_γ • 1 = C_γ • (1 : polynomial F) :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0033 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.δ 3 + single vars.γ 3)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0033,
  simp at congr_coeff0033,
  exact congr_coeff0033,
end



lemma coeff0042 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  B_δ • A_δ • 1 = C_δ • (1 : polynomial F) :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0042 := congr_arg (coeff (single vars.α 0 + single vars.β 0 + single vars.δ 4 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0042,
  simp at congr_coeff0042,
  exact congr_coeff0042,
end


lemma coeff0102 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_wit) in
            finset.fin_range n_wit,
            ∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • A_m x • (w_wit x * u_wit x_1) +
          ∑ (x : fin (n_var - 1)) in
            finset.fin_range (n_var - 1),
            ∑ (x_1 : fin n_wit) in
              finset.fin_range n_wit,
              B_m x_1 • A_h x • (polynomial.X ^ (x : ℕ) * t * u_wit x_1) +
        ∑ (x : fin n_wit) in
          finset.fin_range n_wit,
          ∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • A_m x • (u_wit x * w_wit x_1) +
      ∑ (x : fin n_wit) in
        finset.fin_range n_wit,
        ∑ (x_1 : fin (n_var - 1)) in
          finset.fin_range (n_var - 1),
          B_h x_1 • A_m x • (u_wit x * (polynomial.X ^ (x_1 : ℕ) * t)) =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0102 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.δ 0 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0102,
  simp at congr_coeff0102,
  exact congr_coeff0102,
end


lemma coeff0112 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
    ∑ (x : fin n_wit) in finset.fin_range n_wit, B_β • A_m x • w_wit x +
            ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), B_β • A_h x • (polynomial.X ^ (x : ℕ) * t) +
          ∑ (x : fin n_wit) in
            finset.fin_range n_wit,
            ∑ (x_1 : fin n_var) in finset.fin_range n_var, B_x x_1 • A_m x • (u_wit x * polynomial.X ^ (x_1 : ℕ)) +
        (∑ (x : fin n_var) in
             finset.fin_range n_var,
             ∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • A_x x • (polynomial.X ^ (x : ℕ) * u_wit x_1) +
           ∑ (x : fin n_wit) in finset.fin_range n_wit, B_m x • A_β • w_wit x) +
      ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), B_h x • A_β • (polynomial.X ^ (x : ℕ) * t) =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0112 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.δ 1 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0112,
  simp at congr_coeff0112,
  exact congr_coeff0112,
end



lemma coeff0113 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
    ∑ (x : fin n_wit) in finset.fin_range n_wit, B_γ • A_m x • u_wit x +
      ∑ (x : fin n_wit) in finset.fin_range n_wit, B_m x • A_γ • u_wit x =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0113 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.δ 1 + single vars.γ 3)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0113,
  simp at congr_coeff0113,
  exact congr_coeff0113,
end

lemma coeff0123 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  B_β • A_γ • 1 + B_γ • A_β • 1 = (0 : polynomial F) :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0123 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.δ 2 + single vars.γ 3)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0123,
  simp at congr_coeff0123,
  exact congr_coeff0123,
end



lemma coeff0132 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  B_β • A_δ • 1 + B_δ • A_β • 1 = C_β • (1 : polynomial F) :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0132 := congr_arg (coeff (single vars.α 0 + single vars.β 1 + single vars.δ 3 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0132,
  simp at congr_coeff0132,
  exact congr_coeff0132,
end

lemma coeff0202 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_wit) in
      finset.fin_range n_wit,
      ∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • A_m x • (u_wit x * u_wit x_1) =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0202 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.δ 0 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0202,
  simp at congr_coeff0202,
  exact congr_coeff0202,
end

lemma coeff0212 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_wit) in finset.fin_range n_wit, B_β • A_m x • u_wit x +
      ∑ (x : fin n_wit) in finset.fin_range n_wit, B_m x • A_β • u_wit x =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0212 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.δ 1 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0212,
  simp at congr_coeff0212,
  exact congr_coeff0212,
end

lemma coeff0222 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  B_β = 0 ∨ A_β = 0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff0222 := congr_arg (coeff (single vars.α 0 + single vars.β 2 + single vars.δ 2 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0222,
  simp at congr_coeff0222,
  exact congr_coeff0222,
end

lemma coeff1002 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_wit) in
            finset.fin_range n_wit,
            ∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • A_m x • (w_wit x * v_wit x_1) +
          ∑ (x : fin (n_var - 1)) in
            finset.fin_range (n_var - 1),
            ∑ (x_1 : fin n_wit) in
              finset.fin_range n_wit,
              B_m x_1 • A_h x • (polynomial.X ^ (x : ℕ) * t * v_wit x_1) +
        ∑ (x : fin n_wit) in
          finset.fin_range n_wit,
          ∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • A_m x • (v_wit x * w_wit x_1) +
      ∑ (x : fin n_wit) in
        finset.fin_range n_wit,
        ∑ (x_1 : fin (n_var - 1)) in
          finset.fin_range (n_var - 1),
          B_h x_1 • A_m x • (v_wit x * (polynomial.X ^ (x_1 : ℕ) * t)) =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff1002 := congr_arg (coeff (single vars.α 1 + single vars.β 0 + single vars.δ 0 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1002,
  simp at congr_coeff1002,
  exact congr_coeff1002,
end

lemma coeff1012 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
    ∑ (x : fin n_wit) in finset.fin_range n_wit, B_α • A_m x • w_wit x +
            ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), B_α • A_h x • (polynomial.X ^ (x : ℕ) * t) +
          ∑ (x : fin n_wit) in
            finset.fin_range n_wit,
            ∑ (x_1 : fin n_var) in finset.fin_range n_var, B_x x_1 • A_m x • (v_wit x * polynomial.X ^ (x_1 : ℕ)) +
        (∑ (x : fin n_var) in
             finset.fin_range n_var,
             ∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • A_x x • (polynomial.X ^ (x : ℕ) * v_wit x_1) +
           ∑ (x : fin n_wit) in finset.fin_range n_wit, B_m x • A_α • w_wit x) +
      ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), B_h x • A_α • (polynomial.X ^ (x : ℕ) * t) =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff1012 := congr_arg (coeff (single vars.α 1 + single vars.β 0 + single vars.δ 1 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1012,
  simp at congr_coeff1012,
  exact congr_coeff1012,
end



lemma coeff1013 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_wit) in finset.fin_range n_wit, B_γ • A_m x • v_wit x +
      ∑ (x : fin n_wit) in finset.fin_range n_wit, B_m x • A_γ • v_wit x =
    0
 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff1013 := congr_arg (coeff (single vars.α 1 + single vars.β 0 + single vars.δ 1 + single vars.γ 3)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1013,
  simp at congr_coeff1013,
  exact congr_coeff1013,
end

lemma coeff1023 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
   B_α • A_γ • 1 + B_γ • A_α • 1 = (0 : polynomial F) :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff1023 := congr_arg (coeff (single vars.α 1 + single vars.β 0 + single vars.δ 2 + single vars.γ 3)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1023,
  simp at congr_coeff1023,
  exact congr_coeff1023,
end




lemma coeff1032 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
    B_α • A_δ • 1 + B_δ • A_α • 1 = C_α • (1 : polynomial F):=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff1032 := congr_arg (coeff (single vars.α 1 + single vars.β 0 + single vars.δ 3 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1032,
  simp at congr_coeff1032,
  exact congr_coeff1032,
end

lemma coeff1102 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_wit) in
        finset.fin_range n_wit,
        ∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • A_m x • (v_wit x * u_wit x_1) +
      ∑ (x : fin n_wit) in
        finset.fin_range n_wit,
        ∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • A_m x • (u_wit x * v_wit x_1) =
    0
 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff1102 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.δ 0 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1102,
  simp at congr_coeff1102,
  exact congr_coeff1102,
end


lemma coeff1112 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_wit) in finset.fin_range n_wit, B_α • A_m x • u_wit x +
        ∑ (x : fin n_wit) in finset.fin_range n_wit, B_β • A_m x • v_wit x +
      (∑ (x : fin n_wit) in finset.fin_range n_wit, B_m x • A_α • u_wit x +
         ∑ (x : fin n_wit) in finset.fin_range n_wit, B_m x • A_β • v_wit x) =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff1112 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.δ 1 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1112,
  simp at congr_coeff1112,
  exact congr_coeff1112,
end

lemma coeff1122 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
   B_α * A_β + B_β * A_α = 1 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff1122 := congr_arg (coeff (single vars.α 1 + single vars.β 1 + single vars.δ 2 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1122,
  simp at congr_coeff1122,

  rw smul_smul at congr_coeff1122,
  rw smul_smul at congr_coeff1122,
  rw <-add_smul at congr_coeff1122,
  rw <-polynomial.C_1 at congr_coeff1122,
  rw polynomial.smul_C at congr_coeff1122,
  let to_field := (polynomial.C_inj ).1 congr_coeff1122,
  simp at to_field,
  exact to_field,
  -- rw has_scalar.smul at congr_coeff1122,
  

end





lemma coeff2002 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_wit) in
      finset.fin_range n_wit,
      ∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • A_m x • (v_wit x * v_wit x_1) =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff2002 := congr_arg (coeff (single vars.α 2 + single vars.β 0 + single vars.δ 0 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff2002,
  simp at congr_coeff2002,
  exact congr_coeff2002,
end

lemma coeff2012 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_wit) in finset.fin_range n_wit, B_α • A_m x • v_wit x +
      ∑ (x : fin n_wit) in finset.fin_range n_wit, B_m x • A_α • v_wit x =
    0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff2012 := congr_arg (coeff (single vars.α 2 + single vars.β 0 + single vars.δ 1 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff2012,
  simp at congr_coeff2012,
  exact congr_coeff2012,
end

lemma coeff2022 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  B_α = 0 ∨ A_α = 0 :=
begin
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  simp only with crs polynomial_nf rearrange at eqn,
  have congr_coeff2022 := congr_arg (coeff (single vars.α 2 + single vars.β 0 + single vars.δ 2 + single vars.γ 2)) eqn,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff2022,
  simp at congr_coeff2022,
  exact congr_coeff2022,

end






-- Some simpler versions



-- lemma coeff2002simpler (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
--   (∑ (x : fin n_wit) in finset.fin_range n_wit, A_m x • v_wit x ) 
--   *
--   (∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • v_wit x_1) 
--   = 0 
-- :=
-- begin
--   simp only with polynomial_nf,
--   rw <-coeff2002 a_stmt eqn,
-- end


-- lemma coeff1102simpler (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
--   (∑ (x : fin n_wit) in finset.fin_range n_wit, A_m x • v_wit x)
--    *     
--   (∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • u_wit x_1) 
--   +
--   (∑ (x : fin n_wit) in finset.fin_range n_wit, A_m x • u_wit x) 
--   *
--   (∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • v_wit x_1) 
--   = 0
--  :=
-- begin
--   simp only with polynomial_nf,
--   rw <-coeff1102 a_stmt eqn,
-- end



-- lemma coeff0202simpler (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
--   (∑ (x : fin n_wit) in finset.fin_range n_wit, A_m x • u_wit x)
--   *
--   (∑ (x : fin n_wit) in finset.fin_range n_wit, B_m x • u_wit x) 
--   = 0 :=
-- begin
--   simp only with polynomial_nf,
--   rw <-coeff0202 a_stmt eqn,
-- end




-- lemma coeff0102simpler (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
--   (∑ (x : fin n_wit) in finset.fin_range n_wit, A_m x • w_wit x ) 
--     * 
--   (∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • (u_wit x_1)) 
--   +
--   t 
--     *
--   (∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), A_h x • polynomial.X ^ (x : ℕ))
--     * 
--   (∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • (u_wit x_1)) 
--   +
--   (∑ (x : fin n_wit) in finset.fin_range n_wit, A_m x • u_wit x) 
--     *
--   (∑ (x_1 : fin n_wit) in finset.fin_range n_wit, B_m x_1 • w_wit x_1) 
--   +
--   (∑ (x : fin n_wit) in finset.fin_range n_wit, A_m x • u_wit x)
--     *
--   (∑ (x_1 : fin (n_var - 1)) in finset.fin_range (n_var - 1), B_h x_1 • (polynomial.X ^ (x_1 : ℕ)))
--     * 
--   t 
--   = 0 
-- :=
-- begin
--   -- Do the same polynomial simplification
--   simp only with polynomial_nf,
--   rw <-coeff0102 a_stmt eqn,
--   congr, 
--   funext,
--   congr,
--   funext,
--   ring,
-- end


-- TODO six possibilities for alpha and beta
-- 12 possibilities for gamma delta

/-- Show that if the adversary polynomials obey the equations, 
then the coefficients give a satisfying witness. -/
theorem case_1 (a_stmt : fin n_stmt → F ) : 
  (0 < m)
  -- -> ∀ i, crs'_1_γ i = crs'_1 i * crs'_γ
  -- -> ∀ i, crs'_2_δ i = crs'_2 i * crs'_δ
  -- -> ∀ i, crs'_t_δ i = crs'_t i * crs'_δ
  -> verified a_stmt
  -> (satisfying a_stmt C_m) -- This shows that (a`+1, . . . , am) = (C`+1, . . . , Cm) is a witness for the statement (a1, . . . , a`)
:=
begin
  
  intros hm eqn,
  rw ←modification_equivalence at eqn,
  rw verified' at eqn,

  -- have eqn_vars_extracted := eqn,
  -- rw [A_extract_vars, B_extract_vars, C_extract_vars] at eqn_vars_extracted,
  -- simp only with crs at eqn_vars_extracted,


  -- old version
  have h2022 := coeff2022 a_stmt eqn,
  have h1122 := coeff1122 a_stmt eqn,
  have h0222 := coeff0222 a_stmt eqn,
  have h2012 := coeff2012 a_stmt eqn,
  have h1112 := coeff1112 a_stmt eqn,
  have h0212 := coeff0212 a_stmt eqn,
  have h1012 := coeff1012 a_stmt eqn,
  have h0112 := coeff0112 a_stmt eqn,
  have h2002 := coeff2002 a_stmt eqn,
  have h1102 := coeff1102 a_stmt eqn,
  have h0202 := coeff0202 a_stmt eqn,
  have h1002 := coeff1002 a_stmt eqn,
  have h0102 := coeff0102 a_stmt eqn,
  have h0002 := coeff0002 a_stmt eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only with crs polynomial_nf rearrange at eqn,

  -- TODO is it helpful to simplify by applying these directly to A' and B'




  cases h2022 B_α_zero A_α_zero,
    {
      clear h2022,
      simp only [zero_add, B_α_zero, zero_mul] at h1122,

      have A_β_zero : A_β = 0,
        { exact or.resolve_left h0222 (left_ne_zero_of_mul (ne_zero_of_eq_one h1122)),},
      clear h0222,
      
      -- simp [B_α_zero] at h2012,
      simp [B_α_zero, A_β_zero] at *,
      clear B_α_zero A_β_zero,

      have foo : ∑ (x : fin n_wit) in finset.fin_range n_wit, A_m x • w_wit x + ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), A_h x • (polynomial.X ^ (x : ℕ) * t) = 0,
      cases h0002 with h0002left h0002right,
        {exact h0002left},
        {--h1012 to help complete
        },

      -- TODO
      -- Simplify hypotheses into x * y = 0 statements, start with 0002
      -- do by_cases 
      -- simplify at * using what you get
      -- repeat
      

      -- simp [A_β_zero] at h0212,
      -- simp [B_α_zero, A_β_zero] at h1012,
      -- simp [B_α_zero, A_β_zero] at h0112,

        
    }








end

end groth16

end groth16


