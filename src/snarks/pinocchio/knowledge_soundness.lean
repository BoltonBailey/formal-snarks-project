/-
Author: Bolton Bailey
-/
import data.mv_polynomial.basic
import data.polynomial.div
import data.polynomial.field_division
import algebra.polynomial.big_operators
import .vars
import ...attributes

/-!
# Knowledge Soundness

This file proves the knowledge-soundness property of the second, refined protocol described in the Pinocchio paper.


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




run_cmd mk_simp_attr `poly
run_cmd tactic.add_doc_string `simp_attr.poly "Attribute for defintions of poly elements"

-- Helpers for representing vars as polynomials 

@[poly] def r_v_poly : mv_polynomial vars (polynomial F) := mv_polynomial.X vars.r_v
@[poly] def r_w_poly : mv_polynomial vars (polynomial F) := mv_polynomial.X vars.r_w
@[poly] def s_poly : mv_polynomial vars (polynomial F) := mv_polynomial.C (polynomial.X)
@[poly] def α_v_poly : mv_polynomial vars (polynomial F) := mv_polynomial.X vars.α_v
@[poly] def α_w_poly : mv_polynomial vars (polynomial F) := mv_polynomial.X vars.α_w
@[poly] def α_y_poly : mv_polynomial vars (polynomial F) := mv_polynomial.X vars.α_y
@[poly] def β_poly : mv_polynomial vars (polynomial F) := mv_polynomial.X vars.β
@[poly] def γ_poly : mv_polynomial vars (polynomial F) := mv_polynomial.X vars.γ

/-- Additional variable defined in terms of others -/
@[poly] def r_y_poly : mv_polynomial vars (polynomial F) := r_v_poly * r_w_poly

-- The crs elements as multivariate polynomials of the toxic waste samples: Evaluation key elements
@[poly] def crs_v_wit_k (k : fin n_wit) : mv_polynomial vars (polynomial F) := 
  r_v_poly * mv_polynomial.C (v_wit k)
@[poly] def crs_w_wit_k (k : fin n_wit) : mv_polynomial vars (polynomial F) := 
  r_w_poly * mv_polynomial.C (w_wit k)
@[poly] def crs_y_wit_k (k : fin n_wit) : mv_polynomial vars (polynomial F) := 
  r_y_poly * mv_polynomial.C (y_wit k)

@[poly] def crs_α_v_wit_k (k : fin n_wit) : mv_polynomial vars (polynomial F) := 
  α_v_poly * r_v_poly * mv_polynomial.C (v_wit k)
@[poly] def crs_α_w_wit_k (k : fin n_wit) : mv_polynomial vars (polynomial F) := 
  α_w_poly * r_w_poly * mv_polynomial.C (w_wit k)
@[poly] def crs_α_y_wit_k (k : fin n_wit) : mv_polynomial vars (polynomial F) := 
  α_y_poly * r_y_poly * mv_polynomial.C (y_wit k)

@[poly] def crs_powers (i : fin d) : (mv_polynomial vars (polynomial F)) := mv_polynomial.C (polynomial.X ^ (i : ℕ))

@[poly] def crs_β_v_w_y_k (k : fin n_wit) : mv_polynomial vars (polynomial F) := 
  β_poly * r_v_poly * mv_polynomial.C (v_wit k)
  + β_poly * r_w_poly * mv_polynomial.C (w_wit k)
  + β_poly * r_y_poly * mv_polynomial.C (y_wit k)

-- The crs elements as multivariate polynomials of the toxic waste samples: Verification key elements 

@[poly] def crs_α_v : mv_polynomial vars (polynomial F) := α_v_poly
@[poly] def crs_α_w : mv_polynomial vars (polynomial F) := α_w_poly
@[poly] def crs_α_y : mv_polynomial vars (polynomial F) := α_y_poly
@[poly] def crs_γ : mv_polynomial vars (polynomial F) := γ_poly
@[poly] def crs_βγ : mv_polynomial vars (polynomial F) := β_poly * γ_poly
@[poly] def crs_t : mv_polynomial vars (polynomial F) := 
  r_y_poly * mv_polynomial.C (t)
@[poly] def crs_v_0 : mv_polynomial vars (polynomial F) := 
  r_v_poly * mv_polynomial.C (v_0)
@[poly] def crs_w_0 : mv_polynomial vars (polynomial F) := 
  r_w_poly * mv_polynomial.C (w_0)
@[poly] def crs_y_0 : mv_polynomial vars (polynomial F) := 
  r_y_poly * mv_polynomial.C (y_0)
@[poly] def crs_v_stmt (i : fin n_stmt) : mv_polynomial vars (polynomial F) := 
  r_v_poly * mv_polynomial.C (v_stmt i)
@[poly] def crs_w_stmt (i : fin n_stmt) : mv_polynomial vars (polynomial F) := 
  r_w_poly * mv_polynomial.C (w_stmt i)
@[poly] def crs_y_stmt (i : fin n_stmt) : mv_polynomial vars (polynomial F) := 
  r_y_poly * mv_polynomial.C (y_stmt i)


-- Coefficients of the CRS elements in the representation of the v_wit proof element in the AGM  
parameters {v_wit_comp_crs_v_wit_k : fin n_wit →  F}
parameters {v_wit_comp_crs_w_wit_k : fin n_wit →  F}
parameters {v_wit_comp_crs_y_wit_k : fin n_wit →  F}

parameters {v_wit_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {v_wit_comp_crs_α_w_wit_k : fin n_wit →  F}
parameters {v_wit_comp_crs_α_y_wit_k : fin n_wit →  F}

parameters {v_wit_comp_crs_powers : fin d →  F}

parameters {v_wit_comp_crs_β_v_w_y_k : fin n_wit →  F}

parameters {v_wit_comp_crs_α_v : F}
parameters {v_wit_comp_crs_α_w : F}
parameters {v_wit_comp_crs_α_y : F}
parameters {v_wit_comp_crs_γ : F}
parameters {v_wit_comp_crs_βγ : F}
parameters {v_wit_comp_crs_t : F}
parameters {v_wit_comp_crs_v_0 : F}
parameters {v_wit_comp_crs_w_0 : F}
parameters {v_wit_comp_crs_y_0 : F}
parameters {v_wit_comp_crs_v_stmt : fin n_stmt → F}
parameters {v_wit_comp_crs_w_stmt : fin n_stmt → F}
parameters {v_wit_comp_crs_y_stmt : fin n_stmt → F}


/-- Polynomial form of the representation of the v_wit proof element in the AGM -/
def proof_v_wit : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_y_wit_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_w_wit_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_w_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_α_v_wit_k i))
  + 
  ∑ i in (finset.fin_range n_wit), (crs_α_y_wit_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_α_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_w_wit_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_α_w_wit_k i))
  +
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_powers i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_w_y_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_β_v_w_y_k i))
  +
  crs_α_v * mv_polynomial.C (polynomial.C (v_wit_comp_crs_α_v))
  +   
  crs_α_w * mv_polynomial.C (polynomial.C (v_wit_comp_crs_α_w))
  +
  crs_α_y * mv_polynomial.C (polynomial.C (v_wit_comp_crs_α_y))
  +
  crs_γ * mv_polynomial.C (polynomial.C (v_wit_comp_crs_γ))
  +   
  crs_βγ * mv_polynomial.C (polynomial.C (v_wit_comp_crs_βγ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (v_wit_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (v_wit_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (v_wit_comp_crs_w_0)) 
  +   
  crs_y_0 * mv_polynomial.C (polynomial.C (v_wit_comp_crs_y_0))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_v_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_y_stmt i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_y_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt),  (crs_w_stmt i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_w_stmt i))

-- Coefficients of the CRS elements in the representation of the w_wit proof element in the AGM  
parameters {w_wit_comp_crs_v_wit_k : fin n_wit →  F}
parameters {w_wit_comp_crs_w_wit_k : fin n_wit →  F}
parameters {w_wit_comp_crs_y_wit_k : fin n_wit →  F}

parameters {w_wit_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {w_wit_comp_crs_α_w_wit_k : fin n_wit →  F}
parameters {w_wit_comp_crs_α_y_wit_k : fin n_wit →  F}

parameters {w_wit_comp_crs_powers : fin d →  F}

parameters {w_wit_comp_crs_β_v_w_y_k : fin n_wit →  F}

parameters {w_wit_comp_crs_α_v : F}
parameters {w_wit_comp_crs_α_w : F}
parameters {w_wit_comp_crs_α_y : F}
parameters {w_wit_comp_crs_γ : F}
parameters {w_wit_comp_crs_βγ : F}
parameters {w_wit_comp_crs_t : F}
parameters {w_wit_comp_crs_v_0 : F}
parameters {w_wit_comp_crs_w_0 : F}
parameters {w_wit_comp_crs_y_0 : F}
parameters {w_wit_comp_crs_v_stmt : fin n_stmt → F}
parameters {w_wit_comp_crs_w_stmt : fin n_stmt → F}
parameters {w_wit_comp_crs_y_stmt : fin n_stmt → F}


/-- Polynomial form of the representation of the w_wit proof element in the AGM -/
def proof_w_wit : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (w_wit_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_y_wit_k i) * mv_polynomial.C (polynomial.C (w_wit_comp_crs_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_w_wit_k i) * mv_polynomial.C (polynomial.C (w_wit_comp_crs_w_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (w_wit_comp_crs_α_v_wit_k i))
  + 
  ∑ i in (finset.fin_range n_wit), (crs_α_y_wit_k i) * mv_polynomial.C (polynomial.C (w_wit_comp_crs_α_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_w_wit_k i) * mv_polynomial.C (polynomial.C (w_wit_comp_crs_α_w_wit_k i))
  +
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (w_wit_comp_crs_powers i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_w_y_k i) * mv_polynomial.C (polynomial.C (w_wit_comp_crs_β_v_w_y_k i))
  +
  crs_α_v * mv_polynomial.C (polynomial.C (w_wit_comp_crs_α_v))
  +   
  crs_α_w * mv_polynomial.C (polynomial.C (w_wit_comp_crs_α_w))
  +
  crs_α_y * mv_polynomial.C (polynomial.C (w_wit_comp_crs_α_y))
  +
  crs_γ * mv_polynomial.C (polynomial.C (w_wit_comp_crs_γ))
  +   
  crs_βγ * mv_polynomial.C (polynomial.C (w_wit_comp_crs_βγ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (w_wit_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (w_wit_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (w_wit_comp_crs_w_0)) 
  +   
  crs_y_0 * mv_polynomial.C (polynomial.C (w_wit_comp_crs_y_0))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (w_wit_comp_crs_v_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_y_stmt i) * mv_polynomial.C (polynomial.C (w_wit_comp_crs_y_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt),  (crs_w_stmt i) * mv_polynomial.C (polynomial.C (w_wit_comp_crs_w_stmt i))

-- Coefficients of the CRS elements in the representation of the y_wit proof element in the AGM  
parameters {y_wit_comp_crs_v_wit_k : fin n_wit →  F}
parameters {y_wit_comp_crs_w_wit_k : fin n_wit →  F}
parameters {y_wit_comp_crs_y_wit_k : fin n_wit →  F}

parameters {y_wit_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {y_wit_comp_crs_α_w_wit_k : fin n_wit →  F}
parameters {y_wit_comp_crs_α_y_wit_k : fin n_wit →  F}

parameters {y_wit_comp_crs_powers : fin d →  F}

parameters {y_wit_comp_crs_β_v_w_y_k : fin n_wit →  F}

parameters {y_wit_comp_crs_α_v : F}
parameters {y_wit_comp_crs_α_w : F}
parameters {y_wit_comp_crs_α_y : F}
parameters {y_wit_comp_crs_γ : F}
parameters {y_wit_comp_crs_βγ : F}
parameters {y_wit_comp_crs_t : F}
parameters {y_wit_comp_crs_v_0 : F}
parameters {y_wit_comp_crs_w_0 : F}
parameters {y_wit_comp_crs_y_0 : F}
parameters {y_wit_comp_crs_v_stmt : fin n_stmt → F}
parameters {y_wit_comp_crs_w_stmt : fin n_stmt → F}
parameters {y_wit_comp_crs_y_stmt : fin n_stmt → F}


/-- Polynomial form of the representation of the w_wit proof element in the AGM -/
def proof_y_wit : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (y_wit_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_y_wit_k i) * mv_polynomial.C (polynomial.C (y_wit_comp_crs_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_w_wit_k i) * mv_polynomial.C (polynomial.C (y_wit_comp_crs_w_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (y_wit_comp_crs_α_v_wit_k i))
  + 
  ∑ i in (finset.fin_range n_wit), (crs_α_y_wit_k i) * mv_polynomial.C (polynomial.C (y_wit_comp_crs_α_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_w_wit_k i) * mv_polynomial.C (polynomial.C (y_wit_comp_crs_α_w_wit_k i))
  +
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (y_wit_comp_crs_powers i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_w_y_k i) * mv_polynomial.C (polynomial.C (y_wit_comp_crs_β_v_w_y_k i))
  +
  crs_α_v * mv_polynomial.C (polynomial.C (y_wit_comp_crs_α_v))
  +   
  crs_α_w * mv_polynomial.C (polynomial.C (y_wit_comp_crs_α_w))
  +
  crs_α_y * mv_polynomial.C (polynomial.C (y_wit_comp_crs_α_y))
  +
  crs_γ * mv_polynomial.C (polynomial.C (y_wit_comp_crs_γ))
  +   
  crs_βγ * mv_polynomial.C (polynomial.C (y_wit_comp_crs_βγ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (y_wit_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (y_wit_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (y_wit_comp_crs_w_0)) 
  +   
  crs_y_0 * mv_polynomial.C (polynomial.C (y_wit_comp_crs_y_0))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (y_wit_comp_crs_v_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_y_stmt i) * mv_polynomial.C (polynomial.C (y_wit_comp_crs_y_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt),  (crs_w_stmt i) * mv_polynomial.C (polynomial.C (y_wit_comp_crs_w_stmt i))

-- Coefficients of the CRS elements in the representation of the h proof element in the AGM  
parameters {h_comp_crs_v_wit_k : fin n_wit →  F}
parameters {h_comp_crs_w_wit_k : fin n_wit →  F}
parameters {h_comp_crs_y_wit_k : fin n_wit →  F}

parameters {h_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {h_comp_crs_α_w_wit_k : fin n_wit →  F}
parameters {h_comp_crs_α_y_wit_k : fin n_wit →  F}

parameters {h_comp_crs_powers : fin d →  F}

parameters {h_comp_crs_β_v_w_y_k : fin n_wit →  F}

parameters {h_comp_crs_α_v : F}
parameters {h_comp_crs_α_w : F}
parameters {h_comp_crs_α_y : F}
parameters {h_comp_crs_γ : F}
parameters {h_comp_crs_βγ : F}
parameters {h_comp_crs_t : F}
parameters {h_comp_crs_v_0 : F}
parameters {h_comp_crs_w_0 : F}
parameters {h_comp_crs_y_0 : F}
parameters {h_comp_crs_v_stmt : fin n_stmt → F}
parameters {h_comp_crs_w_stmt : fin n_stmt → F}
parameters {h_comp_crs_y_stmt : fin n_stmt → F}


/-- Polynomial form of the representation of the h proof element in the AGM -/
def proof_h : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_y_wit_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_w_wit_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_w_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_α_v_wit_k i))
  + 
  ∑ i in (finset.fin_range n_wit), (crs_α_y_wit_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_α_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_w_wit_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_α_w_wit_k i))
  +
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (h_comp_crs_powers i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_w_y_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_β_v_w_y_k i))
  +
  crs_α_v * mv_polynomial.C (polynomial.C (h_comp_crs_α_v))
  +   
  crs_α_w * mv_polynomial.C (polynomial.C (h_comp_crs_α_w))
  +
  crs_α_y * mv_polynomial.C (polynomial.C (h_comp_crs_α_y))
  +
  crs_γ * mv_polynomial.C (polynomial.C (h_comp_crs_γ))
  +   
  crs_βγ * mv_polynomial.C (polynomial.C (h_comp_crs_βγ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (h_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (h_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (h_comp_crs_w_0)) 
  +   
  crs_y_0 * mv_polynomial.C (polynomial.C (h_comp_crs_y_0))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (h_comp_crs_v_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_y_stmt i) * mv_polynomial.C (polynomial.C (h_comp_crs_y_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt),  (crs_w_stmt i) * mv_polynomial.C (polynomial.C (h_comp_crs_w_stmt i))

-- Coefficients of the CRS elements in the representation of the α_v_wit proof element in the AGM  
parameters {α_v_wit_comp_crs_v_wit_k : fin n_wit →  F}
parameters {α_v_wit_comp_crs_w_wit_k : fin n_wit →  F}
parameters {α_v_wit_comp_crs_y_wit_k : fin n_wit →  F}

parameters {α_v_wit_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {α_v_wit_comp_crs_α_w_wit_k : fin n_wit →  F}
parameters {α_v_wit_comp_crs_α_y_wit_k : fin n_wit →  F}

parameters {α_v_wit_comp_crs_powers : fin d →  F}

parameters {α_v_wit_comp_crs_β_v_w_y_k : fin n_wit →  F}

parameters {α_v_wit_comp_crs_α_v : F}
parameters {α_v_wit_comp_crs_α_w : F}
parameters {α_v_wit_comp_crs_α_y : F}
parameters {α_v_wit_comp_crs_γ : F}
parameters {α_v_wit_comp_crs_βγ : F}
parameters {α_v_wit_comp_crs_t : F}
parameters {α_v_wit_comp_crs_v_0 : F}
parameters {α_v_wit_comp_crs_w_0 : F}
parameters {α_v_wit_comp_crs_y_0 : F}
parameters {α_v_wit_comp_crs_v_stmt : fin n_stmt → F}
parameters {α_v_wit_comp_crs_w_stmt : fin n_stmt → F}
parameters {α_v_wit_comp_crs_y_stmt : fin n_stmt → F}


/-- Polynomial form of the representation of the α_v_wit proof element in the AGM -/
def proof_α_v_wit : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_y_wit_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_w_wit_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_w_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_α_v_wit_k i))
  + 
  ∑ i in (finset.fin_range n_wit), (crs_α_y_wit_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_α_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_w_wit_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_α_w_wit_k i))
  +
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_powers i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_w_y_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_β_v_w_y_k i))
  +
  crs_α_v * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_α_v))
  +   
  crs_α_w * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_α_w))
  +
  crs_α_y * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_α_y))
  +
  crs_γ * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_γ))
  +   
  crs_βγ * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_βγ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_w_0)) 
  +   
  crs_y_0 * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_y_0))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_v_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_y_stmt i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_y_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt),  (crs_w_stmt i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_w_stmt i))

-- Coefficients of the CRS elements in the representation of the α_w_wit proof element in the AGM  
parameters {α_w_wit_comp_crs_v_wit_k : fin n_wit →  F}
parameters {α_w_wit_comp_crs_w_wit_k : fin n_wit →  F}
parameters {α_w_wit_comp_crs_y_wit_k : fin n_wit →  F}

parameters {α_w_wit_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {α_w_wit_comp_crs_α_w_wit_k : fin n_wit →  F}
parameters {α_w_wit_comp_crs_α_y_wit_k : fin n_wit →  F}

parameters {α_w_wit_comp_crs_powers : fin d →  F}

parameters {α_w_wit_comp_crs_β_v_w_y_k : fin n_wit →  F}

parameters {α_w_wit_comp_crs_α_v : F}
parameters {α_w_wit_comp_crs_α_w : F}
parameters {α_w_wit_comp_crs_α_y : F}
parameters {α_w_wit_comp_crs_γ : F}
parameters {α_w_wit_comp_crs_βγ : F}
parameters {α_w_wit_comp_crs_t : F}
parameters {α_w_wit_comp_crs_v_0 : F}
parameters {α_w_wit_comp_crs_w_0 : F}
parameters {α_w_wit_comp_crs_y_0 : F}
parameters {α_w_wit_comp_crs_v_stmt : fin n_stmt → F}
parameters {α_w_wit_comp_crs_w_stmt : fin n_stmt → F}
parameters {α_w_wit_comp_crs_y_stmt : fin n_stmt → F}


/-- Polynomial form of the representation of the α_w_wit proof element in the AGM -/
def proof_α_w_wit : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_y_wit_k i) * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_w_wit_k i) * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_w_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_α_v_wit_k i))
  + 
  ∑ i in (finset.fin_range n_wit), (crs_α_y_wit_k i) * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_α_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_w_wit_k i) * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_α_w_wit_k i))
  +
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_powers i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_w_y_k i) * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_β_v_w_y_k i))
  +
  crs_α_v * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_α_v))
  +   
  crs_α_w * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_α_w))
  +
  crs_α_y * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_α_y))
  +
  crs_γ * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_γ))
  +   
  crs_βγ * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_βγ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_w_0)) 
  +   
  crs_y_0 * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_y_0))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_v_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_y_stmt i) * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_y_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt),  (crs_w_stmt i) * mv_polynomial.C (polynomial.C (α_w_wit_comp_crs_w_stmt i))

-- Coefficients of the CRS elements in the representation of the α_y_wit proof element in the AGM  
parameters {α_y_wit_comp_crs_v_wit_k : fin n_wit →  F}
parameters {α_y_wit_comp_crs_w_wit_k : fin n_wit →  F}
parameters {α_y_wit_comp_crs_y_wit_k : fin n_wit →  F}

parameters {α_y_wit_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {α_y_wit_comp_crs_α_w_wit_k : fin n_wit →  F}
parameters {α_y_wit_comp_crs_α_y_wit_k : fin n_wit →  F}

parameters {α_y_wit_comp_crs_powers : fin d →  F}

parameters {α_y_wit_comp_crs_β_v_w_y_k : fin n_wit →  F}

parameters {α_y_wit_comp_crs_α_v : F}
parameters {α_y_wit_comp_crs_α_w : F}
parameters {α_y_wit_comp_crs_α_y : F}
parameters {α_y_wit_comp_crs_γ : F}
parameters {α_y_wit_comp_crs_βγ : F}
parameters {α_y_wit_comp_crs_t : F}
parameters {α_y_wit_comp_crs_v_0 : F}
parameters {α_y_wit_comp_crs_w_0 : F}
parameters {α_y_wit_comp_crs_y_0 : F}
parameters {α_y_wit_comp_crs_v_stmt : fin n_stmt → F}
parameters {α_y_wit_comp_crs_w_stmt : fin n_stmt → F}
parameters {α_y_wit_comp_crs_y_stmt : fin n_stmt → F}


/-- Polynomial form of the representation of the α_y_wit proof element in the AGM -/
def proof_α_y_wit : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_y_wit_k i) * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_w_wit_k i) * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_w_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_α_v_wit_k i))
  + 
  ∑ i in (finset.fin_range n_wit), (crs_α_y_wit_k i) * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_α_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_w_wit_k i) * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_α_w_wit_k i))
  +
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_powers i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_w_y_k i) * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_β_v_w_y_k i))
  +
  crs_α_v * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_α_v))
  +   
  crs_α_w * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_α_w))
  +
  crs_α_y * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_α_y))
  +
  crs_γ * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_γ))
  +   
  crs_βγ * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_βγ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_w_0)) 
  +   
  crs_y_0 * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_y_0))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_v_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_y_stmt i) * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_y_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt),  (crs_w_stmt i) * mv_polynomial.C (polynomial.C (α_y_wit_comp_crs_w_stmt i))

-- Coefficients of the CRS elements in the representation of the Z proof element in the AGM  
parameters {Z_comp_crs_v_wit_k : fin n_wit →  F}
parameters {Z_comp_crs_w_wit_k : fin n_wit →  F}
parameters {Z_comp_crs_y_wit_k : fin n_wit →  F}

parameters {Z_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {Z_comp_crs_α_w_wit_k : fin n_wit →  F}
parameters {Z_comp_crs_α_y_wit_k : fin n_wit →  F}

parameters {Z_comp_crs_powers : fin d →  F}

parameters {Z_comp_crs_β_v_w_y_k : fin n_wit →  F}

parameters {Z_comp_crs_α_v : F}
parameters {Z_comp_crs_α_w : F}
parameters {Z_comp_crs_α_y : F}
parameters {Z_comp_crs_γ : F}
parameters {Z_comp_crs_βγ : F}
parameters {Z_comp_crs_t : F}
parameters {Z_comp_crs_v_0 : F}
parameters {Z_comp_crs_w_0 : F}
parameters {Z_comp_crs_y_0 : F}
parameters {Z_comp_crs_v_stmt : fin n_stmt → F}
parameters {Z_comp_crs_w_stmt : fin n_stmt → F}
parameters {Z_comp_crs_y_stmt : fin n_stmt → F}


/-- Polynomial form of the representation of the Z proof element in the AGM -/
def proof_Z : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (Z_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_y_wit_k i) * mv_polynomial.C (polynomial.C (Z_comp_crs_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_w_wit_k i) * mv_polynomial.C (polynomial.C (Z_comp_crs_w_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (Z_comp_crs_α_v_wit_k i))
  + 
  ∑ i in (finset.fin_range n_wit), (crs_α_y_wit_k i) * mv_polynomial.C (polynomial.C (Z_comp_crs_α_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_w_wit_k i) * mv_polynomial.C (polynomial.C (Z_comp_crs_α_w_wit_k i))
  +
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (Z_comp_crs_powers i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_w_y_k i) * mv_polynomial.C (polynomial.C (Z_comp_crs_β_v_w_y_k i))
  +
  crs_α_v * mv_polynomial.C (polynomial.C (Z_comp_crs_α_v))
  +   
  crs_α_w * mv_polynomial.C (polynomial.C (Z_comp_crs_α_w))
  +
  crs_α_y * mv_polynomial.C (polynomial.C (Z_comp_crs_α_y))
  +
  crs_γ * mv_polynomial.C (polynomial.C (Z_comp_crs_γ))
  +   
  crs_βγ * mv_polynomial.C (polynomial.C (Z_comp_crs_βγ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (Z_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (Z_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (Z_comp_crs_w_0)) 
  +   
  crs_y_0 * mv_polynomial.C (polynomial.C (Z_comp_crs_y_0))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (Z_comp_crs_v_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_y_stmt i) * mv_polynomial.C (polynomial.C (Z_comp_crs_y_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt),  (crs_w_stmt i) * mv_polynomial.C (polynomial.C (Z_comp_crs_w_stmt i))

-- Single variable form of V_wit
def v_wit_sv (a_wit : fin n_wit → F) : polynomial F 
:= ∑ i in finset.fin_range n_wit, a_wit i • v_wit i

/-- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def v_stmt_sv (a_stmt : fin n_stmt → F) : polynomial F 
:= ∑ i in (finset.fin_range n_stmt), a_stmt i • v_stmt i

/-- V_stmt as a multivariable polynomial of vars.X -/
@[poly] def v_stmt_mv (a_stmt : fin n_stmt → F) : mv_polynomial vars (polynomial F) 
:= mv_polynomial.C (v_stmt_sv a_stmt)

/-- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def y_stmt_sv (a_stmt : fin n_stmt → F) : polynomial F 
:= ∑ i in (finset.fin_range n_stmt), a_stmt i • y_stmt i

/-- V_stmt as a multivariable polynomial of vars.X -/
@[poly] def y_stmt_mv (a_stmt : fin n_stmt → F) : mv_polynomial vars (polynomial F) 
:= mv_polynomial.C (y_stmt_sv a_stmt)

/-- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def w_stmt_sv (a_stmt : fin n_stmt → F) : polynomial F 
:= ∑ i in (finset.fin_range n_stmt), a_stmt i • w_stmt i

/-- V_stmt as a multivariable polynomial of vars.X -/
@[poly] def w_stmt_mv (a_stmt : fin n_stmt → F) : mv_polynomial vars (polynomial F) 
:= mv_polynomial.C (w_stmt_sv a_stmt)

-- /-- V as a multivariable polynomial -/
-- def proof_v (a_stmt : fin n_stmt → F) : mv_polynomial vars (polynomial F) 
-- := v_stmt_mv a_stmt + proof_v_wit

/-- Multivariable version of t -/
def t_mv : mv_polynomial vars (polynomial F) := mv_polynomial.C t


-- Equations

def eqnI (c_stmt : fin n_stmt → F ) : Prop := 
  (crs_v_0 + v_stmt_mv c_stmt + proof_v_wit) * (crs_w_0 + w_stmt_mv c_stmt + proof_w_wit) = (proof_h * t_mv) + crs_y_0 + y_stmt_mv c_stmt + proof_y_wit

def eqnII : Prop := 
  proof_α_v_wit = proof_v_wit * crs_α_v

def eqnIII : Prop := 
  proof_α_w_wit = proof_w_wit * crs_α_w

def eqnIV : Prop := 
  proof_α_y_wit = proof_y_wit * crs_α_y

def eqnV : Prop := 
  proof_Z * crs_γ = (proof_v_wit + proof_w_wit + proof_y_wit) * crs_βγ

-- Coefficients
open finsupp

lemma eqnIcoeffTODOchoose_good_coeffs (c_stmt : fin n_stmt → F) (eqnI_verified : eqnI c_stmt) :
  1 = 0
:=
begin
  rw [eqnI] at eqnI_verified,
  rw [proof_v_wit, proof_w_wit, proof_y_wit, proof_h] at eqnI_verified,
  simp only [] with poly at eqnI_verified,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqnI_verified,
  simp only [mv_polynomial.X, mv_polynomial.C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, mv_polynomial.sum_monomial_hom] at eqnI_verified,
  have congr_coeff := congr_arg (mv_polynomial.coeff (single vars.r_v 1 + single vars.r_w 1)) eqnI_verified,
  clear eqnI_verified,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff,
  simp only [] with finsupp_simp at  congr_coeff,
  exact congr_coeff,
end

lemma eqnIIcoeffTODOchoose_good_coeffs (eqnII_verified : eqnII) :
  ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (α_v_wit_comp_crs_α_v_wit_k x) = ∑ (x : fin n_wit) in finset.fin_range n_wit, v_wit x * polynomial.C (v_wit_comp_crs_v_wit_k x) + v_0 * polynomial.C v_wit_comp_crs_v_0 + ∑ (x : fin n_stmt) in finset.fin_range n_stmt, v_stmt x * polynomial.C (v_wit_comp_crs_v_stmt x)
:=
begin
  rw [eqnII] at eqnII_verified,
  rw [proof_v_wit, proof_α_v_wit] at eqnII_verified,
  simp only [] with poly at eqnII_verified,
  -- simp only [] with polynomial_nf_3 at eqn,
  -- simp only [mv_polynomial.smul_eq_C_mul] at eqnII_verified,
  simp only [mv_polynomial.X, mv_polynomial.C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, mv_polynomial.sum_monomial_hom] at eqnII_verified,
  have congr_coeff := congr_arg (mv_polynomial.coeff (single vars.r_v 1 + single vars.α_v 1)) eqnII_verified,
  clear eqnII_verified,
  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at congr_coeff,
  simp only [] with finsupp_simp at  congr_coeff,
  exact congr_coeff,
end


/-- Show that if the adversary polynomials obey the equations, 
then the coefficients give a satisfying witness. 
-/
theorem soundness (c_stmt : fin n_stmt → F ) : 
  (0 < m)
  -> eqnI c_stmt
  -> eqnII
  -> eqnIII
  -> eqnIV
  -> eqnV
  -> (satisfying c_stmt v_wit_comp_crs_v_wit_k) -- This shows that (a`+1, . . . , am) = (C`+1, . . . , Cm) is a witness for the statement (a1, . . . , a`)
:=
begin
  intros hm eqnI_verified eqnII_verified eqnIII_verified eqnIV_verified eqnV_verified,
  have foo := congr_arg (mv_polynomial.coeff (finsupp.single vars.r_v 1)) eqnII_verified,
  rw [proof_α_v_wit, proof_v_wit, crs_α_v] at foo,
  simp [crs_v_wit_k] at foo,
  simp only with coeff_simp at foo,
end



end
