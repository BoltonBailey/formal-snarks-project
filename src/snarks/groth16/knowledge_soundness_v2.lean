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
  verified' a_stmt
  ↔
  verified a_stmt
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

lemma soundness_in_special_case (a_stmt : fin n_stmt -> F) : 
  (A_α = 1)
  -> verified' a_stmt
  -> (satisfying a_stmt C_m)
:=
begin

end

lemma special_case_generalization (a_stmt : fin n_stmt -> F) : 
  ((A_α = 1)
  -> verified' a_stmt
  -> (satisfying a_stmt C_m))
  -> 
  (verified' a_stmt -> (satisfying a_stmt C_m))
:=
begin
  intros simple_case eqn,
  rw verified' at eqn,
  rw [A', B', C'] at eqn,
  -- exact simple_case _ (@verified' ),
end


/-- The main theorem for the soundness of the Groth '16 SNARK. 
Show that if the adversary polynomials obey the equations, 
then the coefficients give a satisfying witness. -/
theorem soundness (a_stmt : fin n_stmt → F ) : 
  verified a_stmt
  -> (satisfying a_stmt C_m)
:=
begin
  classical,
  intros eqn,
  -- rw ←modification_equivalence at eqn,
  -- rw verified' at eqn,
  -- rw [A', B', C'] at eqn,
  -- simp only [<-finset.mul_sum] with crs polynomial_nf_2 at eqn,


  -- have h0002 := congr_arg (coeff (single α 0 + single β 0 + single δ 0 + single γ 2)) eqn,
  -- have h0011 := congr_arg (coeff (single α 0 + single β 0 + single δ 1 + single γ 1)) eqn,
  -- have h0012 := congr_arg (coeff (single α 0 + single β 0 + single δ 1 + single γ 2)) eqn,
  -- have h0013 := congr_arg (coeff (single α 0 + single β 0 + single δ 1 + single γ 3)) eqn,
  -- have h0020 := congr_arg (coeff (single α 0 + single β 0 + single δ 2 + single γ 0)) eqn,
  -- have h0021 := congr_arg (coeff (single α 0 + single β 0 + single δ 2 + single γ 1)) eqn,
  -- have h0022 := congr_arg (coeff (single α 0 + single β 0 + single δ 2 + single γ 2)) eqn,
  -- have h0023 := congr_arg (coeff (single α 0 + single β 0 + single δ 2 + single γ 3)) eqn,
  -- have h0024 := congr_arg (coeff (single α 0 + single β 0 + single δ 2 + single γ 4)) eqn,
  -- have h0031 := congr_arg (coeff (single α 0 + single β 0 + single δ 3 + single γ 1)) eqn,
  -- have h0032 := congr_arg (coeff (single α 0 + single β 0 + single δ 3 + single γ 2)) eqn,
  -- have h0033 := congr_arg (coeff (single α 0 + single β 0 + single δ 3 + single γ 3)) eqn,
  -- have h0042 := congr_arg (coeff (single α 0 + single β 0 + single δ 4 + single γ 2)) eqn,
  -- have h0102 := congr_arg (coeff (single α 0 + single β 1 + single δ 0 + single γ 2)) eqn,
  -- have h0111 := congr_arg (coeff (single α 0 + single β 1 + single δ 1 + single γ 1)) eqn,
  -- have h0112 := congr_arg (coeff (single α 0 + single β 1 + single δ 1 + single γ 2)) eqn,
  -- have h0113 := congr_arg (coeff (single α 0 + single β 1 + single δ 1 + single γ 3)) eqn,
  -- have h0120 := congr_arg (coeff (single α 0 + single β 1 + single δ 2 + single γ 0)) eqn,
  -- have h0121 := congr_arg (coeff (single α 0 + single β 1 + single δ 2 + single γ 1)) eqn,
  -- have h0122 := congr_arg (coeff (single α 0 + single β 1 + single δ 2 + single γ 2)) eqn,
  -- have h0123 := congr_arg (coeff (single α 0 + single β 1 + single δ 2 + single γ 3)) eqn,
  -- have h0131 := congr_arg (coeff (single α 0 + single β 1 + single δ 3 + single γ 1)) eqn,
  -- have h0132 := congr_arg (coeff (single α 0 + single β 1 + single δ 3 + single γ 2)) eqn,
  -- have h0202 := congr_arg (coeff (single α 0 + single β 2 + single δ 0 + single γ 2)) eqn,
  -- have h0211 := congr_arg (coeff (single α 0 + single β 2 + single δ 1 + single γ 1)) eqn,
  -- have h0212 := congr_arg (coeff (single α 0 + single β 2 + single δ 1 + single γ 2)) eqn,
  -- have h0220 := congr_arg (coeff (single α 0 + single β 2 + single δ 2 + single γ 0)) eqn,
  -- have h0221 := congr_arg (coeff (single α 0 + single β 2 + single δ 2 + single γ 1)) eqn,
  -- have h0222 := congr_arg (coeff (single α 0 + single β 2 + single δ 2 + single γ 2)) eqn,
  -- have h1002 := congr_arg (coeff (single α 1 + single β 0 + single δ 0 + single γ 2)) eqn,
  -- have h1011 := congr_arg (coeff (single α 1 + single β 0 + single δ 1 + single γ 1)) eqn,
  -- have h1012 := congr_arg (coeff (single α 1 + single β 0 + single δ 1 + single γ 2)) eqn,
  -- have h1013 := congr_arg (coeff (single α 1 + single β 0 + single δ 1 + single γ 3)) eqn,
  -- have h1020 := congr_arg (coeff (single α 1 + single β 0 + single δ 2 + single γ 0)) eqn,
  -- have h1021 := congr_arg (coeff (single α 1 + single β 0 + single δ 2 + single γ 1)) eqn,
  -- have h1022 := congr_arg (coeff (single α 1 + single β 0 + single δ 2 + single γ 2)) eqn,
  -- have h1023 := congr_arg (coeff (single α 1 + single β 0 + single δ 2 + single γ 3)) eqn,
  -- have h1031 := congr_arg (coeff (single α 1 + single β 0 + single δ 3 + single γ 1)) eqn,
  -- have h1032 := congr_arg (coeff (single α 1 + single β 0 + single δ 3 + single γ 2)) eqn,
  -- have h1102 := congr_arg (coeff (single α 1 + single β 1 + single δ 0 + single γ 2)) eqn,
  -- have h1111 := congr_arg (coeff (single α 1 + single β 1 + single δ 1 + single γ 1)) eqn,
  -- have h1112 := congr_arg (coeff (single α 1 + single β 1 + single δ 1 + single γ 2)) eqn,
  -- have h1120 := congr_arg (coeff (single α 1 + single β 1 + single δ 2 + single γ 0)) eqn,
  -- have h1121 := congr_arg (coeff (single α 1 + single β 1 + single δ 2 + single γ 1)) eqn,
  -- have h1122 := congr_arg (coeff (single α 1 + single β 1 + single δ 2 + single γ 2)) eqn,
  -- have h2002 := congr_arg (coeff (single α 2 + single β 0 + single δ 0 + single γ 2)) eqn,
  -- have h2011 := congr_arg (coeff (single α 2 + single β 0 + single δ 1 + single γ 1)) eqn,
  -- have h2012 := congr_arg (coeff (single α 2 + single β 0 + single δ 1 + single γ 2)) eqn,
  -- have h2020 := congr_arg (coeff (single α 2 + single β 0 + single δ 2 + single γ 0)) eqn,
  -- have h2021 := congr_arg (coeff (single α 2 + single β 0 + single δ 2 + single γ 1)) eqn,
  -- have h2022 := congr_arg (coeff (single α 2 + single β 0 + single δ 2 + single γ 2)) eqn,
  have h2022 : A_α = 0 ∨ B_α = 0, sorry,
  have h1122 : A_β * B_α + A_α * B_β = 1, sorry,
  have h0222 : A_β = 0 ∨ B_β = 0, sorry,

  clear eqn,

  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  -- simp at *,


  cases h2022 with A_α_zero B_α_zero,
    {
      sorry,
    },
    {
      
      simp only [zero_add, B_α_zero, mul_zero] at h1122,

      have A_β_zero : A_β = 0,
        { exact or.resolve_right h0222 (right_ne_zero_of_mul (ne_zero_of_eq_one h1122)),},
      clear h0222,
      
      -- simp [B_α_zero] at h2012,
      simp [B_α_zero, A_β_zero] at *,
      clear B_α_zero A_β_zero,

      

      -- TODO
      -- Simplify hypotheses into x * y = 0 statements, start with 0002
      -- do by_cases 
      -- simplify at * using what you get
      -- repeat
      

      -- simp [A_β_zero] at h0212,
      -- simp [B_α_zero, A_β_zero] at h1012,
      -- simp [B_α_zero, A_β_zero] at h0112,

        
    },


end 

end groth16



