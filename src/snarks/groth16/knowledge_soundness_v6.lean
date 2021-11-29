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


/-- Polynomial form of A in the adversary's proof representation -/
def A'  : groth16polynomial := 
  crs'_α * mv_polynomial.C (polynomial.C (A_α))
  + -- TODO
  crs'_β * mv_polynomial.C (polynomial.C (A_β))
  + 
  crs'_γ * mv_polynomial.C (polynomial.C (A_γ))
  +
  crs'_δ * mv_polynomial.C (polynomial.C (A_δ))
  +
  X vars.γ * X vars.δ * mv_polynomial.C ∑ i in (finset.fin_range n_var), (polynomial.C (A_x i) * polynomial.X ^ (i : ℕ))
  +
  ∑ i in (finset.fin_range n_stmt), (crs'_l i) * mv_polynomial.C (polynomial.C (A_l i))
  +
  ∑ i in (finset.fin_range n_wit), (crs'_m i) * mv_polynomial.C (polynomial.C (A_m i))
  +
  ∑ i in (finset.fin_range (n_var - 1)), (crs'_t i) * mv_polynomial.C (polynomial.C (A_h i))

/-- Polynomial form of B in the adversary's proof representation -/
def B'  : groth16polynomial := 
  crs'_α * mv_polynomial.C (polynomial.C (B_α))
  + -- TODO
  crs'_β * mv_polynomial.C (polynomial.C (B_β))
  + 
  crs'_γ * mv_polynomial.C (polynomial.C (B_γ))
  +
  crs'_δ * mv_polynomial.C (polynomial.C (B_δ))
  +
  X vars.γ * X vars.δ * mv_polynomial.C ∑ i in (finset.fin_range n_var), (polynomial.C (B_x i) * polynomial.X ^ (i : ℕ))
  +
  ∑ i in (finset.fin_range n_stmt), (crs'_l i) * mv_polynomial.C (polynomial.C (B_l i))
  +
  ∑ i in (finset.fin_range n_wit), (crs'_m i) * mv_polynomial.C (polynomial.C (B_m i))
  +
  ∑ i in (finset.fin_range (n_var - 1)), (crs'_t i) * mv_polynomial.C (polynomial.C (B_h i))

/-- Polynomial form of C in the adversary's proof representation -/
def C'  : groth16polynomial := 
  crs'_α * mv_polynomial.C (polynomial.C (C_α))
  + -- TODO
  crs'_β * mv_polynomial.C (polynomial.C (C_β))
  + 
  crs'_γ * mv_polynomial.C (polynomial.C (C_γ))
  +
  crs'_δ * mv_polynomial.C (polynomial.C (C_δ))
  +
  X vars.γ * X vars.δ * mv_polynomial.C ∑ i in (finset.fin_range n_var), (polynomial.C (C_x i) * polynomial.X ^ (i : ℕ))
  +
  ∑ i in (finset.fin_range n_stmt), (crs'_l i) * mv_polynomial.C (polynomial.C (C_l i))
  +
  ∑ i in (finset.fin_range n_wit), (crs'_m i) * mv_polynomial.C (polynomial.C (C_m i))
  +
  ∑ i in (finset.fin_range (n_var - 1)), (crs'_t i) * mv_polynomial.C (polynomial.C (C_h i))



def verified (a_stmt : fin n_stmt → F ) : Prop := A * B = crs_α * crs_β + (∑ i in finset.fin_range n_stmt, a_stmt i • crs_l i ) * crs_γ + C * crs_δ

def verified' (a_stmt : fin n_stmt → F ) : Prop := A' * B' = crs'_α * crs'_β + (∑ i in finset.fin_range n_stmt, (polynomial.C (a_stmt i)) • crs'_l i ) * crs'_γ + C' * crs'_δ


lemma modification_equivalence (a_stmt : fin n_stmt → F ) : 
  verified a_stmt -> verified' a_stmt
:=
begin
  -- Apply functional extensionality to *both* sides.
  -- TODO different now that we switch to mv_poly vars (poly F)
  rw verified,
  rw verified',
  funext,
  sorry,

end




open finsupp

-- lemma soundness_in_special_case (a_stmt : fin n_stmt -> F) : 
--   (A_α = 1)
--   -> verified' a_stmt
--   -> (satisfying a_stmt C_m)
-- :=
-- begin

-- end

-- lemma special_case_generalization (a_stmt : fin n_stmt -> F) : 
--   ((A_α = 1)
--   -> verified' a_stmt
--   -> (satisfying a_stmt C_m))
--   -> 
--   (verified' a_stmt -> (satisfying a_stmt C_m))
-- :=
-- begin
--   intros simple_case eqn,
--   rw verified' at eqn,
--   rw [A', B', C'] at eqn,
--   -- exact simple_case _ (@verified' ),
-- end

lemma coeff0023 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
        polynomial.C B_γ +
      polynomial.C A_γ *
        ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0023 := congr_arg (coeff (single α 0 + single β 0 + single δ 2 + single γ 3)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0023,
  -- simp at congr_coeff0023,
  -- exact congr_coeff0023,
end


lemma coeff0013 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) * polynomial.C B_γ +
          (∑ (x : fin (n_var - 1)) in
               finset.fin_range (n_var - 1),
               polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
            polynomial.C B_γ +
        polynomial.C A_γ * ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
      polynomial.C A_γ *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0013 := congr_arg (coeff (single α 0 + single β 0 + single δ 1 + single γ 3)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0013,
  -- simp at congr_coeff0013,
  -- exact congr_coeff0013,
end


lemma coeff0012 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) *
            ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) +
          (∑ (x : fin (n_var - 1)) in
               finset.fin_range (n_var - 1),
               polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
            ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) +
        (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
          ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
      (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0012 := congr_arg (coeff (single α 0 + single β 0 + single δ 1 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0012,
  -- simp at congr_coeff0012,
  -- exact congr_coeff0012,
end


lemma coeff0002 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) *
          ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
        (∑ (x : fin (n_var - 1)) in
             finset.fin_range (n_var - 1),
             polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
          ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
      ((∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) *
           ∑ (x : fin (n_var - 1)) in
             finset.fin_range (n_var - 1),
             polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x)) +
         (∑ (x : fin (n_var - 1)) in
              finset.fin_range (n_var - 1),
              polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
           ∑ (x : fin (n_var - 1)) in
             finset.fin_range (n_var - 1),
             polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x))) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0002 := congr_arg (coeff (single α 0 + single β 0 + single δ 0 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0002,
  -- simp at congr_coeff0002,
  -- exact congr_coeff0002,
end


lemma coeff0011 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) *
            ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x) +
          (∑ (x : fin (n_var - 1)) in
               finset.fin_range (n_var - 1),
               polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
            ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x) +
        (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) *
          ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
      (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0011 := congr_arg (coeff (single α 0 + single β 0 + single δ 1 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0011,
  -- simp at congr_coeff0011,
  -- exact congr_coeff0011,
end


lemma coeff0020 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x) = 0 ∨
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x) = 0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0020 := congr_arg (coeff (single α 0 + single β 0 + single δ 2 + single γ 0)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0020,
  -- simp at congr_coeff0020,
  -- exact congr_coeff0020,
end


lemma coeff0021 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) *
        ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) +
      (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
        ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0021 := congr_arg (coeff (single α 0 + single β 0 + single δ 2 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0021,
  -- simp at congr_coeff0021,
  -- exact congr_coeff0021,
end


lemma coeff0022 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) * polynomial.C B_γ +
              ((∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) *
                   polynomial.C B_δ +
                 (∑ (x : fin (n_var - 1)) in
                      finset.fin_range (n_var - 1),
                      polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
                   polynomial.C B_δ) +
            (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
              ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) +
          polynomial.C A_γ * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x) +
        polynomial.C A_δ * ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
      polynomial.C A_δ *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x)) =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, polynomial.C (a_stmt x) * w_stmt x +
      (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (C_m x) +
         ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : nat) * (t * polynomial.C (C_h x)))
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0022 := congr_arg (coeff (single α 0 + single β 0 + single δ 2 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0022,
  -- simp at congr_coeff0022,
  -- exact congr_coeff0022,
end

-- -- Rewriting in terms of polynomial.C
-- lemma coeff0024 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
--  A_γ = 0 ∨ B_γ = 0
-- :=
-- begin
--   sorry,
--   -- rw verified' at eqn,
--   -- rw [A', B', C'] at eqn,
--   -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
--   -- have congr_coeff0024 := congr_arg (coeff (single α 0 + single β 0 + single δ 2 + single γ 4)) eqn,
--   -- clear eqn,
--   -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0024,
--   -- simp at congr_coeff0024,
--   -- exact congr_coeff0024,
-- end

lemma coeff0024 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
 polynomial.C A_γ = 0 ∨ polynomial.C B_γ = 0
:=
begin
  sorry,
end


lemma coeff0111 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) *
              ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) +
            (∑ (x : fin (n_var - 1)) in
                 finset.fin_range (n_var - 1),
                 polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
              ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) +
          (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) *
            ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x) +
        ((∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) *
             ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) +
           (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) *
             ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x)) +
      (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0111 := congr_arg (coeff (single α 0 + single β 1 + single δ 1 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0111,
  -- simp at congr_coeff0111,
  -- exact congr_coeff0111,
end


lemma coeff0033 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  polynomial.C A_δ * polynomial.C B_γ + polynomial.C A_γ * polynomial.C B_δ = polynomial.C C_γ
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0033 := congr_arg (coeff (single α 0 + single β 0 + single δ 3 + single γ 3)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0033,
  -- simp at congr_coeff0033,
  -- exact congr_coeff0033,
end


lemma coeff0102 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) *
            ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) +
          (∑ (x : fin (n_var - 1)) in
               finset.fin_range (n_var - 1),
               polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
            ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) +
        (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) *
          ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
      (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0102 := congr_arg (coeff (single α 0 + single β 1 + single δ 0 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0102,
  -- simp at congr_coeff0102,
  -- exact congr_coeff0102,
end


lemma coeff0042 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
 polynomial.C A_δ * polynomial.C B_δ = polynomial.C C_δ
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0042 := congr_arg (coeff (single α 0 + single β 0 + single δ 4 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0042,
  -- simp at congr_coeff0042,
  -- exact congr_coeff0042,
end


lemma coeff0112 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) * polynomial.C B_β +
            (∑ (x : fin (n_var - 1)) in
                 finset.fin_range (n_var - 1),
                 polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
              polynomial.C B_β +
          (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) *
            ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) +
        ((∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
             ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) +
           polynomial.C A_β * ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x)) +
      polynomial.C A_β *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0112 := congr_arg (coeff (single α 0 + single β 1 + single δ 1 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0112,
  -- simp at congr_coeff0112,
  -- exact congr_coeff0112,
end


lemma coeff0031 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) * polynomial.C B_δ +
      polynomial.C A_δ * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x) =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (C_l x)
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0031 := congr_arg (coeff (single α 0 + single β 0 + single δ 3 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0031,
  -- simp at congr_coeff0031,
  -- exact congr_coeff0031,
end


lemma coeff0032 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
        polynomial.C B_δ +
      polynomial.C A_δ *
        ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) =
    ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (C_x i) * polynomial.X ^ (i : nat)
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0032 := congr_arg (coeff (single α 0 + single β 0 + single δ 3 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0032,
  -- simp at congr_coeff0032,
  -- exact congr_coeff0032,
end


lemma coeff0113 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) * polynomial.C B_γ +
      polynomial.C A_γ * ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0113 := congr_arg (coeff (single α 0 + single β 1 + single δ 1 + single γ 3)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0113,
  -- simp at congr_coeff0113,
  -- exact congr_coeff0113,
end


lemma coeff0120 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) *
        ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) +
      (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) *
        ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0120 := congr_arg (coeff (single α 0 + single β 1 + single δ 2 + single γ 0)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0120,
  -- simp at congr_coeff0120,
  -- exact congr_coeff0120,
end


lemma coeff0123 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
 polynomial.C A_γ * polynomial.C B_β + polynomial.C A_β * polynomial.C B_γ = 0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0123 := congr_arg (coeff (single α 0 + single β 1 + single δ 2 + single γ 3)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0123,
  -- simp at congr_coeff0123,
  -- exact congr_coeff0123,
end


lemma coeff0121 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) * polynomial.C B_β +
        (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) *
          ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) +
      ((∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
           ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) +
         polynomial.C A_β * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0121 := congr_arg (coeff (single α 0 + single β 1 + single δ 2 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0121,
  -- simp at congr_coeff0121,
  -- exact congr_coeff0121,
end


lemma coeff0132 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  polynomial.C A_δ * polynomial.C B_β + polynomial.C A_β * polynomial.C B_δ = polynomial.C C_β
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0132 := congr_arg (coeff (single α 0 + single β 1 + single δ 3 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0132,
  -- simp at congr_coeff0132,
  -- exact congr_coeff0132,
end


lemma coeff0131 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) * polynomial.C B_δ +
      polynomial.C A_δ * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (C_l x)
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0131 := congr_arg (coeff (single α 0 + single β 1 + single δ 3 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0131,
  -- simp at congr_coeff0131,
  -- exact congr_coeff0131,
end


lemma coeff0122 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
                polynomial.C B_β +
              (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) *
                polynomial.C B_γ +
            (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) * polynomial.C B_δ +
          polynomial.C A_β *
            ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) +
        polynomial.C A_γ * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) +
      polynomial.C A_δ * ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, polynomial.C (a_stmt x) * u_stmt x +
      ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (C_m x)
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0122 := congr_arg (coeff (single α 0 + single β 1 + single δ 2 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0122,
  -- simp at congr_coeff0122,
  -- exact congr_coeff0122,
end


lemma coeff0202 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x) = 0 ∨
    ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) = 0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0202 := congr_arg (coeff (single α 0 + single β 2 + single δ 0 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0202,
  -- simp at congr_coeff0202,
  -- exact congr_coeff0202,
end


lemma coeff0212 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) * polynomial.C B_β +
      polynomial.C A_β * ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0212 := congr_arg (coeff (single α 0 + single β 2 + single δ 1 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0212,
  -- simp at congr_coeff0212,
  -- exact congr_coeff0212,
end


lemma coeff0211 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) *
        ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) +
      (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) *
        ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0211 := congr_arg (coeff (single α 0 + single β 2 + single δ 1 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0211,
  -- simp at congr_coeff0211,
  -- exact congr_coeff0211,
end


lemma coeff0220 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x) = 0 ∨
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) = 0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0220 := congr_arg (coeff (single α 0 + single β 2 + single δ 2 + single γ 0)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0220,
  -- simp at congr_coeff0220,
  -- exact congr_coeff0220,
end


lemma coeff0221 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) * polynomial.C B_β +
      polynomial.C A_β * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff0221 := congr_arg (coeff (single α 0 + single β 2 + single δ 2 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0221,
  -- simp at congr_coeff0221,
  -- exact congr_coeff0221,
end

-- -- Rewriting in terms of polynomial.C
-- lemma coeff0222 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
--  A_β = 0 ∨ B_β = 0
-- :=
-- begin
--   sorry,
--   -- rw verified' at eqn,
--   -- rw [A', B', C'] at eqn,
--   -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
--   -- have congr_coeff0222 := congr_arg (coeff (single α 0 + single β 2 + single δ 2 + single γ 2)) eqn,
--   -- clear eqn,
--   -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff0222,
--   -- simp at congr_coeff0222,
--   -- exact congr_coeff0222,
-- end

lemma coeff0222 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
 polynomial.C A_β = 0 ∨ polynomial.C B_β = 0
:=
begin
  sorry,
end


lemma coeff1002 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) *
            ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x) +
          (∑ (x : fin (n_var - 1)) in
               finset.fin_range (n_var - 1),
               polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
            ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x) +
        (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) *
          ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
      (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1002 := congr_arg (coeff (single α 1 + single β 0 + single δ 0 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1002,
  -- simp at congr_coeff1002,
  -- exact congr_coeff1002,
end


lemma coeff1011 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) *
              ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x) +
            (∑ (x : fin (n_var - 1)) in
                 finset.fin_range (n_var - 1),
                 polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
              ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x) +
          (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) *
            ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x) +
        ((∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) *
             ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x) +
           (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) *
             ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x)) +
      (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1011 := congr_arg (coeff (single α 1 + single β 0 + single δ 1 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1011,
  -- simp at congr_coeff1011,
  -- exact congr_coeff1011,
end


lemma coeff1012 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) * polynomial.C B_α +
            (∑ (x : fin (n_var - 1)) in
                 finset.fin_range (n_var - 1),
                 polynomial.X ^ (x : nat) * (t * polynomial.C (A_h x))) *
              polynomial.C B_α +
          (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) *
            ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) +
        ((∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
             ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x) +
           polynomial.C A_α * ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x)) +
      polynomial.C A_α *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : nat) * (t * polynomial.C (B_h x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1012 := congr_arg (coeff (single α 1 + single β 0 + single δ 1 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1012,
  -- simp at congr_coeff1012,
  -- exact congr_coeff1012,
end


lemma coeff1013 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) * polynomial.C B_γ +
      polynomial.C A_γ * ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1013 := congr_arg (coeff (single α 1 + single β 0 + single δ 1 + single γ 3)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1013,
  -- simp at congr_coeff1013,
  -- exact congr_coeff1013,
end


lemma coeff1020 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) *
        ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x) +
      (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) *
        ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1020 := congr_arg (coeff (single α 1 + single β 0 + single δ 2 + single γ 0)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1020,
  -- simp at congr_coeff1020,
  -- exact congr_coeff1020,
end


lemma coeff1021 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)) * polynomial.C B_α +
        (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) *
          ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) +
      ((∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
           ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x) +
         polynomial.C A_α * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1021 := congr_arg (coeff (single α 1 + single β 0 + single δ 2 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1021,
  -- simp at congr_coeff1021,
  -- exact congr_coeff1021,
end


lemma coeff1023 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
 polynomial.C A_γ * polynomial.C B_α + polynomial.C A_α * polynomial.C B_γ = 0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1023 := congr_arg (coeff (single α 1 + single β 0 + single δ 2 + single γ 3)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1023,
  -- simp at congr_coeff1023,
  -- exact congr_coeff1023,
end


lemma coeff1022 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : nat)) *
                polynomial.C B_α +
              (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) *
                polynomial.C B_γ +
            (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) * polynomial.C B_δ +
          polynomial.C A_α *
            ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : nat) +
        polynomial.C A_γ * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x) +
      polynomial.C A_δ * ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x) =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, polynomial.C (a_stmt x) * v_stmt x +
      ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (C_m x)
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1022 := congr_arg (coeff (single α 1 + single β 0 + single δ 2 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1022,
  -- simp at congr_coeff1022,
  -- exact congr_coeff1022,
end


lemma coeff1031 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) * polynomial.C B_δ +
      polynomial.C A_δ * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x) =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (C_l x)
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1031 := congr_arg (coeff (single α 1 + single β 0 + single δ 3 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1031,
  -- simp at congr_coeff1031,
  -- exact congr_coeff1031,
end


lemma coeff1111 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) *
          ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) +
        (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) *
          ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x) +
      ((∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) *
           ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) +
         (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) *
           ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1111 := congr_arg (coeff (single α 1 + single β 1 + single δ 1 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1111,
  -- simp at congr_coeff1111,
  -- exact congr_coeff1111,
end


lemma coeff1102 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) *
        ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) +
      (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) *
        ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1102 := congr_arg (coeff (single α 1 + single β 1 + single δ 0 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1102,
  -- simp at congr_coeff1102,
  -- exact congr_coeff1102,
end


lemma coeff1112 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)) * polynomial.C B_α +
        (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) * polynomial.C B_β +
      (polynomial.C A_α * ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x) +
         polynomial.C A_β * ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1112 := congr_arg (coeff (single α 1 + single β 1 + single δ 1 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1112,
  -- simp at congr_coeff1112,
  -- exact congr_coeff1112,
end


lemma coeff1032 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  polynomial.C A_δ * polynomial.C B_α + polynomial.C A_α * polynomial.C B_δ = polynomial.C C_α
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1032 := congr_arg (coeff (single α 1 + single β 0 + single δ 3 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1032,
  -- simp at congr_coeff1032,
  -- exact congr_coeff1032,
end


lemma coeff1121 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) * polynomial.C B_α +
        (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) * polynomial.C B_β +
      (polynomial.C A_α * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) +
         polynomial.C A_β * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x)) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1121 := congr_arg (coeff (single α 1 + single β 1 + single δ 2 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1121,
  -- simp at congr_coeff1121,
  -- exact congr_coeff1121,
end


lemma coeff1122 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
 polynomial.C A_β * polynomial.C B_α + polynomial.C A_α * polynomial.C B_β = 1
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1122 := congr_arg (coeff (single α 1 + single β 1 + single δ 2 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1122,
  -- simp at congr_coeff1122,
  -- exact congr_coeff1122,
end


lemma coeff1120 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) *
        ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x) +
      (∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)) *
        ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff1120 := congr_arg (coeff (single α 1 + single β 1 + single δ 2 + single γ 0)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff1120,
  -- simp at congr_coeff1120,
  -- exact congr_coeff1120,
end


lemma coeff2011 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) *
        ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x) +
      (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) *
        ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff2011 := congr_arg (coeff (single α 2 + single β 0 + single δ 1 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff2011,
  -- simp at congr_coeff2011,
  -- exact congr_coeff2011,
end


lemma coeff2002 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x) = 0 ∨
    ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x) = 0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff2002 := congr_arg (coeff (single α 2 + single β 0 + single δ 0 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff2002,
  -- simp at congr_coeff2002,
  -- exact congr_coeff2002,
end


lemma coeff2012 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)) * polynomial.C B_α +
      polynomial.C A_α * ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff2012 := congr_arg (coeff (single α 2 + single β 0 + single δ 1 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff2012,
  -- simp at congr_coeff2012,
  -- exact congr_coeff2012,
end


lemma coeff2020 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x) = 0 ∨
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x) = 0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff2020 := congr_arg (coeff (single α 2 + single β 0 + single δ 2 + single γ 0)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff2020,
  -- simp at congr_coeff2020,
  -- exact congr_coeff2020,
end


lemma coeff2021 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
  (∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)) * polynomial.C B_α +
      polynomial.C A_α * ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x) =
    0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff2021 := congr_arg (coeff (single α 2 + single β 0 + single δ 2 + single γ 1)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff2021,
  -- simp at congr_coeff2021,
  -- exact congr_coeff2021,
end

-- -- Replacing this with a version that keeps it in terms of polynomial.C
-- lemma coeff2022 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
--  A_α = 0 ∨ B_α = 0
-- :=
-- begin
--   sorry,
--   -- rw verified' at eqn,
--   -- rw [A', B', C'] at eqn,
--   -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
--   -- have congr_coeff2022 := congr_arg (coeff (single α 2 + single β 0 + single δ 2 + single γ 2)) eqn,
--   -- clear eqn,
--   -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff2022,
--   -- simp at congr_coeff2022,
--   -- exact congr_coeff2022,
-- end

lemma coeff2022 (a_stmt : fin n_stmt → F) (eqn : verified' a_stmt) :
 polynomial.C A_α = 0 ∨ polynomial.C B_α = 0
:=
begin
  sorry,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,
  -- have congr_coeff2022 := congr_arg (coeff (single α 2 + single β 0 + single δ 2 + single γ 2)) eqn,
  -- clear eqn,
  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff2022,
  -- simp at congr_coeff2022,
  -- exact congr_coeff2022,
end


lemma coeff0022reformat (a_stmt : fin n_stmt → F) :   
  (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) * polynomial.C B_δ +
            (∑ (x : fin (n_var - 1)) in
                 finset.fin_range (n_var - 1),
                 polynomial.X ^ (x : ℕ) * (t * polynomial.C (A_h x))) *
              polynomial.C B_δ +
          (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : ℕ)) *
            ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : ℕ) +
        polynomial.C A_δ * ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
      polynomial.C A_δ *
        ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : ℕ) * (t * polynomial.C (B_h x)) =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, polynomial.C (a_stmt x) * w_stmt x +
      (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (C_m x) +
         ∑ (x : fin (n_var - 1)) in
           finset.fin_range (n_var - 1),
           polynomial.X ^ (x : ℕ) * (t * polynomial.C (C_h x)))
  ↔
  ((∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)) +
            (∑ (x : fin (n_var - 1)) in
                 finset.fin_range (n_var - 1),
                 polynomial.X ^ (x : ℕ) * (t * polynomial.C (A_h x))))  *
              polynomial.C B_δ +
          (∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (A_x i) * polynomial.X ^ (i : ℕ)) *
            ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.C (B_x i) * polynomial.X ^ (i : ℕ) +
        polynomial.C A_δ * (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x) +
      ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : ℕ) * (t * polynomial.C (B_h x))) =
    ∑ (x : fin n_stmt) in finset.fin_range n_stmt, polynomial.C (a_stmt x) * w_stmt x +
      (∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (C_m x) +
         ∑ (x : fin (n_var - 1)) in
           finset.fin_range (n_var - 1),
           polynomial.X ^ (x : ℕ) * (t * polynomial.C (C_h x)))
:=
begin
  ring_nf,
end

run_cmd mk_simp_attr `atom
run_cmd tactic.add_doc_string `simp_attr.atom "Attribute for defintions of atoms in the proof"

@[atom]
def p_A_α := polynomial.C A_α
@[atom]
def p_A_β := polynomial.C A_β
@[atom]
def p_A_γ := polynomial.C A_γ
@[atom]
def p_A_δ := polynomial.C A_δ
@[atom]
def p_B_α := polynomial.C B_α
@[atom]
def p_B_β := polynomial.C B_β
@[atom]
def p_B_γ := polynomial.C B_γ
@[atom]
def p_B_δ := polynomial.C B_δ
@[atom]
def p_C_α := polynomial.C C_α
@[atom]
def p_C_β := polynomial.C C_β
@[atom]
def p_C_γ := polynomial.C C_γ
@[atom]
def p_C_δ := polynomial.C C_δ

@[atom]
def p_u_stmt_A_l := ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (A_l x)
@[atom]
def p_v_stmt_A_l := ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (A_l x)
@[atom]
def p_w_stmt_A_l := ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (A_l x)
@[atom]
def p_u_stmt_B_l := ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (B_l x)
@[atom]
def p_v_stmt_B_l := ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (B_l x)
@[atom]
def p_w_stmt_B_l := ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (B_l x)
@[atom]
def p_u_stmt_C_l := ∑ (x : fin n_stmt) in finset.fin_range n_stmt, u_stmt x * polynomial.C (C_l x)
@[atom]
def p_v_stmt_C_l := ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (C_l x)
@[atom]
def p_w_stmt_C_l := ∑ (x : fin n_stmt) in finset.fin_range n_stmt, w_stmt x * polynomial.C (C_l x)

@[atom]
def p_u_wit_A_m := ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (A_m x)
@[atom]
def p_v_wit_A_m := ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (A_m x)
@[atom]
def p_w_wit_A_m := ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (A_m x)
@[atom]
def p_u_wit_B_m := ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (B_m x)
@[atom]
def p_v_wit_B_m := ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (B_m x)
@[atom]
def p_w_wit_B_m := ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (B_m x)
@[atom]
def p_u_wit_C_m := ∑ (x : fin n_wit) in finset.fin_range n_wit, u_wit x * polynomial.C (C_m x)
@[atom]
def p_v_wit_C_m := ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (C_m x)
@[atom]
def p_w_wit_C_m := ∑ (x : fin n_wit) in finset.fin_range n_wit, w_wit x * polynomial.C (C_m x)

@[atom]
def p_t_A_h := ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : ℕ) * (t * polynomial.C (A_h x))
@[atom]
def p_t_B_h := ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : ℕ) * (t * polynomial.C (B_h x))
@[atom]
def p_t_C_h := ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : ℕ) * (t * polynomial.C (C_h x))

@[atom]
def p_A_x := ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.X ^ (i : ℕ) * polynomial.C (A_x i)
@[atom]
def p_B_x := ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.X ^ (i : ℕ) * polynomial.C (B_x i)
@[atom]
def p_C_x := ∑ (i : fin n_var) in finset.fin_range n_var, polynomial.X ^ (i : ℕ) * polynomial.C (C_x i)


-- lemma reformat (a b c d e f g : F) :
--   a * c + b * c + g + d * e + d * f = c * (a + b) + d * (e + f) + g
-- :=
-- begin
--   convert_to _ = d * _ + c * _ + _;
--   ring_nf,
--   ring_nf,

-- end

-- lemma main_theorem (a b c d e f g: F) (h1: a + b = 0) (h2: e + f = 0):
--   a * c + b * c + g + d * e + d * f = g
-- :=
-- begin
--   convert_to d * _ + c * _ + _ = _;
--   ring_nf,
--   ring_nf,
--   simp [h1, h2],
-- end

-- TODO Add to Mathlib next to C_eq_zero
@[simp] lemma polynomial.C_eq_one (a : F) : polynomial.C a = 1 ↔ a = 1 :=
calc polynomial.C a = 1 ↔ polynomial.C a = polynomial.C 1 : by rw polynomial.C_1
         ... ↔ a = 1 : polynomial.C_inj


lemma simplifier1 (x : fin n_stmt) (a_stmt : fin n_stmt → F ) 
  : polynomial.C (a_stmt x) * u_stmt x = u_stmt x * polynomial.C (a_stmt x)
  :=
  by ring

lemma simplifier2 (x : fin n_stmt) (a_stmt : fin n_stmt → F ) 
  : polynomial.C (a_stmt x) * v_stmt x = v_stmt x * polynomial.C (a_stmt x)
  :=
  by ring

lemma polynomial.mul_mod_by_monic (t p : polynomial F) (mt : t.monic) : (t * p) %ₘ t = 0 :=
begin
  rw polynomial.dvd_iff_mod_by_monic_eq_zero,
  apply dvd_mul_right,
  exact mt,
end

example (a b : F) : a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
example (a b c : F) : a - b = c ↔ a = b + c := sub_eq_iff_eq_add'

/-- The main theorem for the soundness of the Groth '16 SNARK. 
Show that if the adversary polynomials obey the equations, 
then the coefficients give a satisfying witness. -/
theorem soundness (a_stmt : fin n_stmt → F ) : 
  verified a_stmt
  -> (satisfying a_stmt C_m)
:=
begin
  -- classical,
  intros eqn,
  rw satisfying,
  simp only [polynomial.smul_eq_C_mul, rearrange_constants_right_hard],
  suffices : 
    (∑ (i : fin n_stmt) in finset.fin_range n_stmt, u_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.fin_range n_wit, u_wit i * polynomial.C (C_m i)) 
    * 
    (∑ (i : fin n_stmt) in finset.fin_range n_stmt, v_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.fin_range n_wit, v_wit i * polynomial.C (C_m i)) 
    = 
    (∑ (i : fin n_stmt) in finset.fin_range n_stmt, w_stmt i * polynomial.C (a_stmt i) + ∑ (i : fin n_wit) in finset.fin_range n_wit, w_wit i * polynomial.C (C_m i)) 
    +
    ∑ (x : fin (n_var - 1)) in finset.fin_range (n_var - 1), polynomial.X ^ (x : ℕ) * (t * polynomial.C (C_h x)),
  {
    rw <-sub_eq_iff_eq_add' at this,
    have h := congr_arg (%ₘ t) this,
    simp only at h,
    rw h,
    clear this h,
    conv
    begin
      to_lhs,
      congr,
      congr,
      skip,
      funext,
      rw mul_comm,   
      rw mul_assoc,
      skip,   
    end,
    rw <-finset.mul_sum,
    apply polynomial.mul_mod_by_monic,
    exact monic_t,
    done,
  },
  -- TODO suffices to satisfy
  have eqn' := modification_equivalence a_stmt (eqn),
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,


  have h0002 := coeff0002 a_stmt eqn',
  have h0011 := coeff0011 a_stmt eqn',
  have h0012 := coeff0012 a_stmt eqn',
  have h0013 := coeff0013 a_stmt eqn',
  have h0020 := coeff0020 a_stmt eqn',
  have h0021 := coeff0021 a_stmt eqn',
  have h0022 := coeff0022 a_stmt eqn',
  have h0023 := coeff0023 a_stmt eqn',
  have h0024 := coeff0024 a_stmt eqn',
  have h0031 := coeff0031 a_stmt eqn',
  have h0032 := coeff0032 a_stmt eqn',
  -- have h0033 := coeff0033 a_stmt eqn', -- definitely useless
  -- have h0042 := coeff0042 a_stmt eqn', -- definitely useless
  have h0102 := coeff0102 a_stmt eqn',
  have h0111 := coeff0111 a_stmt eqn',
  have h0112 := coeff0112 a_stmt eqn',
  have h0113 := coeff0113 a_stmt eqn',
  have h0120 := coeff0120 a_stmt eqn',
  have h0121 := coeff0121 a_stmt eqn',
  have h0122 := coeff0122 a_stmt eqn',
  have h0123 := coeff0123 a_stmt eqn',
  have h0131 := coeff0131 a_stmt eqn',
  -- have h0132 := coeff0132 a_stmt eqn', -- definitely useless
  have h0202 := coeff0202 a_stmt eqn',
  have h0211 := coeff0211 a_stmt eqn',
  have h0212 := coeff0212 a_stmt eqn',
  have h0220 := coeff0220 a_stmt eqn',
  have h0221 := coeff0221 a_stmt eqn',
  have h0222 := coeff0222 a_stmt eqn',
  have h1002 := coeff1002 a_stmt eqn',
  have h1011 := coeff1011 a_stmt eqn',
  have h1012 := coeff1012 a_stmt eqn',
  have h1013 := coeff1013 a_stmt eqn',
  have h1020 := coeff1020 a_stmt eqn',
  have h1021 := coeff1021 a_stmt eqn',
  have h1022 := coeff1022 a_stmt eqn',
  have h1023 := coeff1023 a_stmt eqn',
  have h1031 := coeff1031 a_stmt eqn',
  -- have h1032 := coeff1032 a_stmt eqn', -- definitely useless
  have h1102 := coeff1102 a_stmt eqn',
  have h1111 := coeff1111 a_stmt eqn',
  have h1112 := coeff1112 a_stmt eqn',
  have h1120 := coeff1120 a_stmt eqn',
  have h1121 := coeff1121 a_stmt eqn',
  have h1122 := coeff1122 a_stmt eqn',
  have h2002 := coeff2002 a_stmt eqn',
  have h2011 := coeff2011 a_stmt eqn',
  have h2012 := coeff2012 a_stmt eqn',
  have h2020 := coeff2020 a_stmt eqn',
  have h2021 := coeff2021 a_stmt eqn',
  have h2022 := coeff2022 a_stmt eqn',
  
  -- clear h0033 h1032 h0132 h0042, -- Clear some statements about C_ values that give no info


  clear eqn eqn',
  -- done,


  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  -- simp at *,
  -- my_fail_tactic,
  trace "Moving Cs right",
  simp only [simplifier1, simplifier2] at *,

  trace "Grouping distributivity",
  simp only [<-mul_add, <-add_mul, <-add_assoc, add_mul_distrib, add_mul_distrib'] at *,

  trace "main simplification",
  
  tactic.integral_domain_tactic_v4,



end 

end groth16



