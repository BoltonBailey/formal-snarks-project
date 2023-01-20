/-
Author: <Redacted for anonymized submission>
-/
import data.mv_polynomial.comm_ring
import data.polynomial.div
import data.polynomial.field_division
import algebra.polynomial.big_operators
import .vars
import ...attributes
import ...integral_domain_tactic


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
parameters {v_wit'_comp_crs_v_wit_k : fin n_wit →  F}
parameters {v_wit'_comp_crs_w_wit_k : fin n_wit →  F}
parameters {v_wit'_comp_crs_y_wit_k : fin n_wit →  F}

parameters {v_wit'_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {v_wit'_comp_crs_α_w_wit_k : fin n_wit →  F}
parameters {v_wit'_comp_crs_α_y_wit_k : fin n_wit →  F}

parameters {v_wit'_comp_crs_powers : fin d →  F}

parameters {v_wit'_comp_crs_β_v_w_y_k : fin n_wit →  F}

parameters {v_wit'_comp_crs_α_v : F}
parameters {v_wit'_comp_crs_α_w : F}
parameters {v_wit'_comp_crs_α_y : F}
parameters {v_wit'_comp_crs_γ : F}
parameters {v_wit'_comp_crs_βγ : F}
parameters {v_wit'_comp_crs_t : F}
parameters {v_wit'_comp_crs_v_0 : F}
parameters {v_wit'_comp_crs_w_0 : F}
parameters {v_wit'_comp_crs_y_0 : F}
parameters {v_wit'_comp_crs_v_stmt : fin n_stmt → F}
parameters {v_wit'_comp_crs_w_stmt : fin n_stmt → F}
parameters {v_wit'_comp_crs_y_stmt : fin n_stmt → F}


/-- Polynomial form of the representation of the α_v_wit proof element in the AGM -/
def proof_v_wit' : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_y_wit_k i) * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_w_wit_k i) * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_w_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_α_v_wit_k i))
  + 
  ∑ i in (finset.fin_range n_wit), (crs_α_y_wit_k i) * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_α_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_w_wit_k i) * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_α_w_wit_k i))
  +
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_powers i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_w_y_k i) * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_β_v_w_y_k i))
  +
  crs_α_v * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_α_v))
  +   
  crs_α_w * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_α_w))
  +
  crs_α_y * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_α_y))
  +
  crs_γ * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_γ))
  +   
  crs_βγ * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_βγ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_w_0)) 
  +   
  crs_y_0 * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_y_0))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_v_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_y_stmt i) * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_y_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt),  (crs_w_stmt i) * mv_polynomial.C (polynomial.C (v_wit'_comp_crs_w_stmt i))

-- Coefficients of the CRS elements in the representation of the α_w_wit proof element in the AGM  
parameters {w_wit'_comp_crs_v_wit_k : fin n_wit →  F}
parameters {w_wit'_comp_crs_w_wit_k : fin n_wit →  F}
parameters {w_wit'_comp_crs_y_wit_k : fin n_wit →  F}

parameters {w_wit'_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {w_wit'_comp_crs_α_w_wit_k : fin n_wit →  F}
parameters {w_wit'_comp_crs_α_y_wit_k : fin n_wit →  F}

parameters {w_wit'_comp_crs_powers : fin d →  F}

parameters {w_wit'_comp_crs_β_v_w_y_k : fin n_wit →  F}

parameters {w_wit'_comp_crs_α_v : F}
parameters {w_wit'_comp_crs_α_w : F}
parameters {w_wit'_comp_crs_α_y : F}
parameters {w_wit'_comp_crs_γ : F}
parameters {w_wit'_comp_crs_βγ : F}
parameters {w_wit'_comp_crs_t : F}
parameters {w_wit'_comp_crs_v_0 : F}
parameters {w_wit'_comp_crs_w_0 : F}
parameters {w_wit'_comp_crs_y_0 : F}
parameters {w_wit'_comp_crs_v_stmt : fin n_stmt → F}
parameters {w_wit'_comp_crs_w_stmt : fin n_stmt → F}
parameters {w_wit'_comp_crs_y_stmt : fin n_stmt → F}


/-- Polynomial form of the representation of the α_w_wit proof element in the AGM -/
def proof_w_wit' : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_y_wit_k i) * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_w_wit_k i) * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_w_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_α_v_wit_k i))
  + 
  ∑ i in (finset.fin_range n_wit), (crs_α_y_wit_k i) * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_α_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_w_wit_k i) * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_α_w_wit_k i))
  +
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_powers i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_w_y_k i) * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_β_v_w_y_k i))
  +
  crs_α_v * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_α_v))
  +   
  crs_α_w * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_α_w))
  +
  crs_α_y * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_α_y))
  +
  crs_γ * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_γ))
  +   
  crs_βγ * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_βγ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_w_0)) 
  +   
  crs_y_0 * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_y_0))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_v_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_y_stmt i) * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_y_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt),  (crs_w_stmt i) * mv_polynomial.C (polynomial.C (w_wit'_comp_crs_w_stmt i))

-- Coefficients of the CRS elements in the representation of the α_y_wit proof element in the AGM  
parameters {y_wit'_comp_crs_v_wit_k : fin n_wit →  F}
parameters {y_wit'_comp_crs_w_wit_k : fin n_wit →  F}
parameters {y_wit'_comp_crs_y_wit_k : fin n_wit →  F}

parameters {y_wit'_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {y_wit'_comp_crs_α_w_wit_k : fin n_wit →  F}
parameters {y_wit'_comp_crs_α_y_wit_k : fin n_wit →  F}

parameters {y_wit'_comp_crs_powers : fin d →  F}

parameters {y_wit'_comp_crs_β_v_w_y_k : fin n_wit →  F}

parameters {y_wit'_comp_crs_α_v : F}
parameters {y_wit'_comp_crs_α_w : F}
parameters {y_wit'_comp_crs_α_y : F}
parameters {y_wit'_comp_crs_γ : F}
parameters {y_wit'_comp_crs_βγ : F}
parameters {y_wit'_comp_crs_t : F}
parameters {y_wit'_comp_crs_v_0 : F}
parameters {y_wit'_comp_crs_w_0 : F}
parameters {y_wit'_comp_crs_y_0 : F}
parameters {y_wit'_comp_crs_v_stmt : fin n_stmt → F}
parameters {y_wit'_comp_crs_w_stmt : fin n_stmt → F}
parameters {y_wit'_comp_crs_y_stmt : fin n_stmt → F}


/-- Polynomial form of the representation of the α_y_wit proof element in the AGM -/
def proof_y_wit' : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_y_wit_k i) * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_w_wit_k i) * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_w_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_α_v_wit_k i))
  + 
  ∑ i in (finset.fin_range n_wit), (crs_α_y_wit_k i) * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_α_y_wit_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_w_wit_k i) * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_α_w_wit_k i))
  +
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_powers i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_w_y_k i) * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_β_v_w_y_k i))
  +
  crs_α_v * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_α_v))
  +   
  crs_α_w * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_α_w))
  +
  crs_α_y * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_α_y))
  +
  crs_γ * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_γ))
  +   
  crs_βγ * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_βγ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_w_0)) 
  +   
  crs_y_0 * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_y_0))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_v_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt), (crs_y_stmt i) * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_y_stmt i))
  +
  ∑ i in (finset.fin_range n_stmt),  (crs_w_stmt i) * mv_polynomial.C (polynomial.C (y_wit'_comp_crs_w_stmt i))

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
@[poly] def t_mv : mv_polynomial vars (polynomial F) := mv_polynomial.C t


-- Equations

def eqnI (c_stmt : fin n_stmt → F ) : Prop := 
  (crs_v_0 + r_v_poly * v_stmt_mv c_stmt + proof_v_wit) * (crs_w_0 + r_w_poly * w_stmt_mv c_stmt + proof_w_wit) = ((r_y_poly * t_mv) * proof_h) + (crs_y_0 + r_y_poly * y_stmt_mv c_stmt + proof_y_wit)

def eqnII : Prop := 
  proof_v_wit' = proof_v_wit * crs_α_v

def eqnIII : Prop := 
  proof_w_wit' = proof_w_wit * crs_α_w

def eqnIV : Prop := 
  proof_y_wit' = proof_y_wit * crs_α_y

def eqnV : Prop := 
  proof_Z * crs_γ = (proof_v_wit + proof_w_wit + proof_y_wit) * crs_βγ

-- Coefficients
open mv_polynomial finsupp

-- lemma sadojfh (a b c : mv_polynomial vars (polynomial F)) : a + b - c = a -c + b := 
-- begin
--   ring,
-- end

lemma eqnIIresults (eqnII_verified : eqnII) : 
  proof_v_wit 
  = r_v_poly 
    * mv_polynomial.C ( 
        ∑ i in (finset.fin_range n_wit),  (v_wit i) *  (polynomial.C (v_wit_comp_crs_v_wit_k i))
        + v_0 * (polynomial.C v_wit_comp_crs_v_0)
        + ∑ i in finset.fin_range n_stmt, (v_stmt i) * (polynomial.C (v_wit_comp_crs_v_stmt i))
     ) 
    + ∑ x in finset.fin_range d, mv_polynomial.C (polynomial.X ^ (x : ℕ)) * mv_polynomial.C ( polynomial.C (v_wit_comp_crs_powers x)) :=
begin

  rw eqnII at eqnII_verified,

  simp_rw [proof_v_wit, proof_v_wit'] at eqnII_verified ⊢,
  -- simp_rw [proof_v_wit, proof_w_wit, proof_y_wit, proof_h, 
  --       proof_v_wit', proof_w_wit', proof_y_wit', proof_Z] at eqnII_verified,
  simp only [] with poly at eqnII_verified ⊢,
  -- simp only [] with polynomial_nf_3 at eqn',
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnII_verified ⊢,

  have h11eqnII := congr_arg (coeff (single vars.α_v 1 + single vars.β 1 + single vars.γ 1)) eqnII_verified,
  have h19eqnII := congr_arg (coeff (single vars.α_v 1 + single vars.γ 1)) eqnII_verified,
  have h21eqnII := congr_arg (coeff (single vars.r_w 1 + single vars.α_v 1 + single vars.β 1)) eqnII_verified,
  have h22eqnII := congr_arg (coeff (single vars.α_v 2)) eqnII_verified,
  have h32eqnII := congr_arg (coeff (single vars.α_v 1 + single vars.α_w 1)) eqnII_verified,

  have h38eqnII := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_v 1 + single vars.β 1)) eqnII_verified,

  have h52eqnII := congr_arg (coeff (single vars.r_v 1 + single vars.α_v 2)) eqnII_verified,

  have h54eqnII := congr_arg (coeff (single vars.α_v 1 + single vars.α_y 1)) eqnII_verified,

  have h71eqnII := congr_arg (coeff (single vars.r_w 1 + single vars.α_v 1)) eqnII_verified,

  have h74eqnII := congr_arg (coeff (single vars.r_v 1 + single vars.α_v 1 + single vars.β 1)) eqnII_verified,

  have h93eqnII := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_v 1)) eqnII_verified,

  have h94eqnII := congr_arg (coeff (single vars.α_w 1 + single vars.r_w 1 + single vars.α_v 1)) eqnII_verified,
  have h95eqnII := congr_arg (coeff (single vars.α_v 1)) eqnII_verified,
  have h96eqnII := congr_arg (coeff (single vars.α_v 1 + single vars.r_v 1)) eqnII_verified,

  have h101eqnII := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_v 1 + single vars.α_y 1)) eqnII_verified,

  clear eqnII_verified,

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  simp only [] with finsupp_simp at *,  

  simp only [h11eqnII, h19eqnII, h21eqnII, h22eqnII, h32eqnII, h38eqnII, h52eqnII, h54eqnII, h71eqnII, h74eqnII, h93eqnII, h94eqnII, h95eqnII, h96eqnII, h101eqnII],
  simp only [monomial_zero, add_zero, zero_add, <-monomial_add],
 
  rw <-sub_eq_zero,

  have h71eqnII' := congr_arg (monomial (single vars.r_w 1)) h71eqnII,
  have h93eqnII' := congr_arg (monomial (single vars.r_v 1 + single vars.r_w 1)) h93eqnII,
  simp only [monomial_zero, add_zero, zero_add, <-monomial_add] at h71eqnII' h93eqnII',

  rw <-h71eqnII',
  rw <-sub_eq_zero,


  rw <-h93eqnII',
  rw <-sub_eq_zero,
  
  abel,
  abel, -- Why two needed here?

end

-- lemma eqnIIresultsBetter (eqnII_verified : eqnII) (eqnV_verified : eqnV) : 
--   proof_v_wit 
--   = r_v_poly 
--     * ( 
--         ∑ i in (finset.fin_range n_wit), mv_polynomial.C (v_wit i) * mv_polynomial.C (polynomial.C (Z_comp_crs_β_v_w_y_k i))
--      ) 
--     + ∑ x in finset.fin_range d, mv_polynomial.C (polynomial.X ^ (x : ℕ)) * mv_polynomial.C ( polynomial.C (v_wit_comp_crs_powers x)) :=
-- begin

--   rw eqnII at eqnII_verified,
--   rw eqnV at eqnV_verified,

--   simp_rw [proof_v_wit, proof_v_wit'] at eqnII_verified ⊢,
--   simp_rw [proof_v_wit, proof_w_wit, proof_y_wit, proof_Z] at eqnV_verified,

--   simp only [] with poly at eqnII_verified eqnV_verified ⊢,
--   -- simp only [] with polynomial_nf_3 at eqn',
--   simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnII_verified eqnV_verified ⊢,

--   have h11eqnII := congr_arg (coeff (single vars.α_v 1 + single vars.β 1 + single vars.γ 1)) eqnII_verified,
--   have h19eqnII := congr_arg (coeff (single vars.α_v 1 + single vars.γ 1)) eqnII_verified,
--   have h21eqnII := congr_arg (coeff (single vars.r_w 1 + single vars.α_v 1 + single vars.β 1)) eqnII_verified,
--   have h22eqnII := congr_arg (coeff (single vars.α_v 2)) eqnII_verified,
--   have h32eqnII := congr_arg (coeff (single vars.α_v 1 + single vars.α_w 1)) eqnII_verified,

--   have h38eqnII := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_v 1 + single vars.β 1)) eqnII_verified,

--   have h52eqnII := congr_arg (coeff (single vars.r_v 1 + single vars.α_v 2)) eqnII_verified,

--   have h54eqnII := congr_arg (coeff (single vars.α_v 1 + single vars.α_y 1)) eqnII_verified,

--   have h71eqnII := congr_arg (coeff (single vars.r_w 1 + single vars.α_v 1)) eqnII_verified,

--   have h74eqnII := congr_arg (coeff (single vars.r_v 1 + single vars.α_v 1 + single vars.β 1)) eqnII_verified,

--   have h93eqnII := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_v 1)) eqnII_verified,

--   have h94eqnII := congr_arg (coeff (single vars.α_w 1 + single vars.r_w 1 + single vars.α_v 1)) eqnII_verified,
--   -- have h95eqnII := congr_arg (coeff (single vars.α_v 1)) eqnII_verified,
--   -- have h96eqnII := congr_arg (coeff (single vars.α_v 1 + single vars.r_v 1)) eqnII_verified,

--   have h101eqnII := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_v 1 + single vars.α_y 1)) eqnII_verified,

--   have h2eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,


--   clear eqnII_verified,
--   clear eqnV_verified,

--   simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
--   simp only [] with finsupp_simp at *,  

--   rw [h11eqnII, h19eqnII, h21eqnII, h22eqnII, h32eqnII, h38eqnII, h52eqnII, h54eqnII, h74eqnII, h94eqnII, h101eqnII, h2eqnV], -- h95eqnII, h96eqnII, 
--   simp only [monomial_zero, add_zero, zero_add, <-monomial_add],
 
--   rw <-sub_eq_zero,

--   have h71eqnII' := congr_arg (monomial (single vars.r_w 1)) h71eqnII,
--   have h93eqnII' := congr_arg (monomial (single vars.r_v 1 + single vars.r_w 1)) h93eqnII,
--   simp only [monomial_zero, add_zero, zero_add, <-monomial_add] at h71eqnII' h93eqnII',

--   rw <-h71eqnII',
--   rw <-sub_eq_zero,


--   rw <-h93eqnII',
--   rw <-sub_eq_zero,
  
--   abel,

-- end

lemma eqnIIIresults (eqnIII_verified : eqnIII) : 
  proof_w_wit 
  = r_w_poly 
    * mv_polynomial.C ( 
        ∑ i in (finset.fin_range n_wit),  (w_wit i) * (polynomial.C (w_wit_comp_crs_w_wit_k i))
        + w_0 * (polynomial.C w_wit_comp_crs_w_0)
        + ∑ i in finset.fin_range n_stmt, (w_stmt i) * (polynomial.C (w_wit_comp_crs_w_stmt i))
     ) 
    + ∑ x in finset.fin_range d, mv_polynomial.C (polynomial.X ^ (x : ℕ)) * mv_polynomial.C ( polynomial.C (w_wit_comp_crs_powers x)) :=
begin

  rw eqnIII at eqnIII_verified,

  simp_rw [proof_w_wit, proof_w_wit'] at eqnIII_verified ⊢,
  -- simp_rw [proof_v_wit, proof_w_wit, proof_y_wit, proof_h, 
  --       proof_v_wit', proof_w_wit', proof_y_wit', proof_Z] at eqnIII_verified,
  simp only [] with poly at eqnIII_verified ⊢,
  -- simp only [] with polynomial_nf_3 at eqn',
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnIII_verified ⊢,

  have h27eqnIII := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_w 1)) eqnIII_verified,

  have h32eqnIII := congr_arg (coeff (single vars.α_v 1 + single vars.α_w 1)) eqnIII_verified,

  have h33eqnIII := congr_arg (coeff (single vars.r_w 1 + single vars.α_w 1)) eqnIII_verified,

  have h34eqnIII := congr_arg (coeff (single vars.r_v 1 + single vars.α_w 1 + single vars.β 1)) eqnIII_verified,

  have h35eqnIII := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_w 1 + single vars.α_y 1)) eqnIII_verified,

  have h53eqnIII := congr_arg (coeff (single vars.α_w 1 + single vars.β 1 + single vars.γ 1)) eqnIII_verified,

  have h61eqnIII := congr_arg (coeff (single vars.α_w 1 + single vars.γ 1)) eqnIII_verified,

  have h75eqnIII := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_w 1 + single vars.β 1)) eqnIII_verified,

  have h81eqnIII := congr_arg (coeff (single vars.r_v 1 + single vars.α_w 1)) eqnIII_verified,

  have h88eqnIII := congr_arg (coeff (single vars.r_w 1 + single vars.α_w 1 + single vars.β 1)) eqnIII_verified,

  have h89eqnIII := congr_arg (coeff (single vars.α_w 1 + single vars.α_y 1)) eqnIII_verified,

  have h96eqnIII := congr_arg (coeff (single vars.α_w 2)) eqnIII_verified,
  have h97eqnIII := congr_arg (coeff (single vars.α_w 2 + single vars.r_w 1)) eqnIII_verified,
  have h98eqnIII := congr_arg (coeff (single vars.α_w 1 + single vars.α_v 1 + single vars.r_v 1)) eqnIII_verified,


  clear eqnIII_verified,

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  simp only [] with finsupp_simp at *,  

  simp only [h27eqnIII, h32eqnIII, h33eqnIII, h34eqnIII, h35eqnIII, h53eqnIII, h61eqnIII, h75eqnIII, h81eqnIII, h88eqnIII, h89eqnIII, h96eqnIII, h97eqnIII, h98eqnIII],
  simp only [monomial_zero, add_zero, zero_add, <-monomial_add],
 
  rw <-sub_eq_zero,

  have h81eqnIII' := congr_arg (monomial (single vars.r_v 1)) h81eqnIII,
  have h27eqnIII' := congr_arg (monomial (single vars.r_v 1 + single vars.r_w 1)) h27eqnIII,
  simp only [monomial_zero, add_zero, zero_add, <-monomial_add] at h81eqnIII' h27eqnIII',

  rw <-h81eqnIII',
  rw <-sub_eq_zero,


  rw <-h27eqnIII',
  rw <-sub_eq_zero,
  
  abel,
  abel,
end

lemma eqnIVresults (eqnIV_verified : eqnIV) :   
  proof_y_wit 
  = r_y_poly 
    * mv_polynomial.C ( 
        ∑ i in (finset.fin_range n_wit), (y_wit i) * (polynomial.C (y_wit_comp_crs_y_wit_k i))
        + y_0 * (polynomial.C y_wit_comp_crs_y_0)
        + ∑ i in finset.fin_range n_stmt, (y_stmt i) * (polynomial.C (y_wit_comp_crs_y_stmt i))
        + t * (polynomial.C y_wit_comp_crs_t)
     ) 
    + ∑ x in finset.fin_range d, mv_polynomial.C (polynomial.X ^ (x : ℕ)) * mv_polynomial.C ( polynomial.C (y_wit_comp_crs_powers x))  :=
begin
  rw eqnIV at eqnIV_verified,

  simp_rw [proof_y_wit, proof_y_wit'] at eqnIV_verified ⊢,
  -- simp_rw [proof_v_wit, proof_w_wit, proof_y_wit, proof_h, 
  --       proof_v_wit', proof_w_wit', proof_y_wit', proof_Z] at eqnIV_verified,
  simp only [] with poly at eqnIV_verified ⊢,
  -- simp only [] with polynomial_nf_3 at eqn',
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnIV_verified ⊢,

  have h2eqnIV := congr_arg (coeff (single vars.r_w 1 + single vars.α_y 1 + single vars.β 1)) eqnIV_verified,
  have h4eqnIV := congr_arg (coeff (single vars.r_v 1 + single vars.α_v 1 + single vars.α_y 1)) eqnIV_verified,
  have h23eqnIV := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_y 2)) eqnIV_verified,

  have h25eqnIV := congr_arg (coeff (single vars.r_w 1 + single vars.α_w 1 + single vars.α_y 1)) eqnIV_verified,

  have h30eqnIV := congr_arg (coeff (single vars.α_y 1 + single vars.β 1 + single vars.γ 1)) eqnIV_verified,

  have h37eqnIV := congr_arg (coeff (single vars.α_y 1 + single vars.γ 1)) eqnIV_verified,

  have h54eqnIV := congr_arg (coeff (single vars.α_v 1 + single vars.α_y 1)) eqnIV_verified,

  have h55eqnIV := congr_arg (coeff (single vars.r_w 1 + single vars.α_y 1)) eqnIV_verified,

  have h56eqnIV := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_y 1 + single vars.β 1)) eqnIV_verified,

  have h57eqnIV := congr_arg (coeff (single vars.r_v 1 + single vars.α_y 1 + single vars.β 1)) eqnIV_verified,

  have h59eqnIV := congr_arg (coeff (single vars.α_y 2)) eqnIV_verified,

  have h89eqnIV := congr_arg (coeff (single vars.α_w 1 + single vars.α_y 1)) eqnIV_verified,

  have h102eqnIV := congr_arg (coeff (single vars.r_v 1 + single vars.α_y 1)) eqnIV_verified,



  clear eqnIV_verified,

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  simp only [] with finsupp_simp at *,  

  simp only [h2eqnIV, h4eqnIV, h23eqnIV, h25eqnIV, h30eqnIV, h37eqnIV, h54eqnIV, h55eqnIV, h56eqnIV, h57eqnIV, h59eqnIV, h89eqnIV, h102eqnIV],
  simp only [monomial_zero, add_zero, zero_add, <-monomial_add],
 
  rw <-sub_eq_zero,

  have h55eqnIV' := congr_arg (monomial (single vars.r_w 1)) h55eqnIV,
  have h102eqnIV' := congr_arg (monomial (single vars.r_v 1)) h102eqnIV,
  simp only [monomial_zero, add_zero, zero_add, <-monomial_add] at h55eqnIV' h102eqnIV',

  rw <-h55eqnIV',
  rw <-sub_eq_zero,


  rw <-h102eqnIV',
  rw <-sub_eq_zero,
  
  abel,
  abel,
end

lemma polynomial.mul_mod_by_monic (t p : polynomial F) (mt : t.monic) : (t * p) %ₘ t = 0 :=
begin
  rw polynomial.dvd_iff_mod_by_monic_eq_zero,
  apply dvd_mul_right,
  exact mt,
end

lemma move_C_left (p : polynomial F) (f : F) :
  p * polynomial.C f = polynomial.C f * p :=
begin
  ring,
end

lemma soundness (c_stmt : fin n_stmt → F ) (eqnI_verified : eqnI c_stmt) 
  (eqnII_verified : eqnII) (eqnIII_verified : eqnIII) (eqnIV_verified : eqnIV) 
  (eqnV_verified : eqnV) : (satisfying c_stmt Z_comp_crs_β_v_w_y_k) :=
begin
  rw eqnV at eqnV_verified,

  have eqnII' := eqnIIresults eqnII_verified,
  have eqnIII' := eqnIIIresults eqnIII_verified,
  have eqnIV' := eqnIVresults eqnIV_verified,

  simp_rw [eqnII', eqnIII', eqnIV', proof_Z] at eqnV_verified,
  -- simp_rw [proof_v_wit, proof_w_wit, proof_y_wit, proof_h, 
  --       proof_v_wit', proof_w_wit', proof_y_wit', proof_Z] at eqnV_verified,
  simp only [] with poly at eqnV_verified,
  -- simp only [] with polynomial_nf_3 at eqn',
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnV_verified,

  have h2eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,
  have h3eqnV := congr_arg (coeff (single vars.r_w 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,
  have h4eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,
  -- have h4eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.α_v 1 + single vars.α_y 1)) eqnV_verified,
  -- have h23eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_y 2)) eqnV_verified,

  -- have h25eqnV := congr_arg (coeff (single vars.r_w 1 + single vars.α_w 1 + single vars.α_y 1)) eqnV_verified,

  -- have h30eqnV := congr_arg (coeff (single vars.α_y 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,

  -- have h37eqnV := congr_arg (coeff (single vars.α_y 1 + single vars.γ 1)) eqnV_verified,

  -- have h54eqnV := congr_arg (coeff (single vars.α_v 1 + single vars.α_y 1)) eqnV_verified,

  -- have h55eqnV := congr_arg (coeff (single vars.r_w 1 + single vars.α_y 1)) eqnV_verified,

  -- have h56eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_y 1 + single vars.β 1)) eqnV_verified,

  -- have h57eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.α_y 1 + single vars.β 1)) eqnV_verified,

  -- have h59eqnV := congr_arg (coeff (single vars.α_y 2)) eqnV_verified,

  -- have h89eqnV := congr_arg (coeff (single vars.α_w 1 + single vars.α_y 1)) eqnV_verified,

  -- have h102eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.α_y 1)) eqnV_verified,



  clear eqnV_verified,

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  simp only [] with finsupp_simp at *,

  rw [<-h2eqnV] at eqnII',
  rw [<-h3eqnV] at eqnIII',
  rw [<-h4eqnV] at eqnIV',

  rw [eqnI] at eqnI_verified,
  rw satisfying,

  simp_rw [eqnII', eqnIII', eqnIV', proof_h] at eqnI_verified,

  simp only [] with poly at eqnI_verified,
  -- simp only [] with polynomial_nf_3 at eqn',
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnI_verified,

  have h1eqnI := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1)) eqnI_verified,

  clear eqnI_verified,

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at h1eqnI,
  simp only [] with finsupp_simp at h1eqnI,
  rw <-sub_eq_iff_eq_add at h1eqnI,
  -- rw <-sub_eq_zero at h1eqnI,
  -- rw polynomial.dvd_iff_mod_by_monic_eq_zero,

  have h2eqnI := congr_arg (%ₘ t) h1eqnI,
  simp only [polynomial.zero_mod_by_monic] at h2eqnI,
  rw polynomial.mul_mod_by_monic at h2eqnI,
  rw <- h2eqnI,
  congr' 1,
  simp_rw [v_stmt_sv, w_stmt_sv, y_stmt_sv, polynomial.smul_eq_C_mul],
  simp only [add_mul, mul_add],
  simp_rw [move_C_left],
  -- congr' 1,
  -- rw <-sub_eq_zero,

  abel,

  exact monic_t,

end

#exit

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
  -> (satisfying c_stmt Z_comp_crs_β_v_w_y_k) -- This shows that (a`+1, . . . , am) = (C`+1, . . . , Cm) is a witness for the statement (a1, . . . , a`)
:=
begin
  intros hm eqnI_verified eqnII_verified eqnIII_verified eqnIV_verified eqnV_verified,
  -- have foo := congr_arg (mv_polynomial.coeff (finsupp.single vars.r_v 1)) eqnII_verified,
  -- rw [proof_v_wit', proof_v_wit, crs_α_v] at foo,
  -- simp [crs_v_wit_k] at foo,
  -- simp only with coeff_simp at foo,

  rw eqnI at eqnI_verified,
  rw eqnII at eqnII_verified,
  rw eqnIII at eqnIII_verified,
  rw eqnIV at eqnIV_verified,
  rw eqnV at eqnV_verified,
  -- done,
  simp_rw [proof_v_wit, proof_w_wit, proof_y_wit, proof_h, 
        proof_v_wit', proof_w_wit', proof_y_wit', proof_Z] at eqnI_verified eqnII_verified eqnIII_verified eqnIV_verified eqnV_verified,
  simp only [] with poly at eqnI_verified eqnII_verified eqnIII_verified eqnIV_verified eqnV_verified,
  -- simp only [] with polynomial_nf_3 at eqn',
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnI_verified eqnII_verified eqnIII_verified eqnIV_verified eqnV_verified,

  -- clear eqnI_verified,

  -- From II, II and IV, telling us that many coefficients of v_wit, w_wit, y_wit are 0.
  have h1eqnI    := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1)) eqnI_verified,
  have h11eqnII  := congr_arg (coeff (single vars.α_v 1 + single vars.β 1 + single vars.γ 1)) eqnII_verified,
  have h19eqnII  := congr_arg (coeff (single vars.α_v 1 + single vars.γ 1)) eqnII_verified,
  have h21eqnII  := congr_arg (coeff (single vars.α_v 1 + single vars.r_w 1 + single vars.β 1)) eqnII_verified,
  have h22eqnII  := congr_arg (coeff (single vars.α_v 2)) eqnII_verified,
  have h32eqnII  := congr_arg (coeff (single vars.α_v 1 + single vars.α_w 1)) eqnII_verified,
  have h38eqnII  := congr_arg (coeff (single vars.α_v 1 + single vars.r_v 1 + single vars.r_w 1 + single vars.β 1)) eqnII_verified,
  have h52eqnII  := congr_arg (coeff (single vars.α_v 2 + single vars.r_v 1)) eqnII_verified,
  have h54eqnII  := congr_arg (coeff (single vars.α_v 1 + single vars.α_y 1)) eqnII_verified,
  have h71eqnII  := congr_arg (coeff (single vars.α_v 1 + single vars.r_w 1)) eqnII_verified,
  have h74eqnII  := congr_arg (coeff (single vars.α_v 1 + single vars.r_v 1 + single vars.β 1)) eqnII_verified,
  have h93eqnII  := congr_arg (coeff (single vars.α_v 1 + single vars.r_v 1 + single vars.r_w 1)) eqnII_verified,
  have h94eqnII := congr_arg (coeff (single vars.α_w 1 + single vars.r_w 1 + single vars.α_v 1)) eqnII_verified,
  have h101eqnII := congr_arg (coeff (single vars.α_v 1 + single vars.r_v 1 + single vars.r_w 1 + single vars.α_y 1)) eqnII_verified,
  have h27eqnIII := congr_arg (coeff (single vars.α_w 1 + single vars.r_v 1 + single vars.r_w 1)) eqnIII_verified,
  have h32eqnIII := congr_arg (coeff (single vars.α_w 1 + single vars.α_v 1)) eqnIII_verified,
  have h33eqnIII := congr_arg (coeff (single vars.α_w 1 + single vars.r_w 1)) eqnIII_verified,
  have h34eqnIII := congr_arg (coeff (single vars.r_v 1 + single vars.α_w 1 + single vars.β 1)) eqnIII_verified,
  have h35eqnIII := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_w 1 + single vars.α_y 1)) eqnIII_verified,
  have h53eqnIII := congr_arg (coeff (single vars.α_w 1 + single vars.β 1 + single vars.γ 1)) eqnIII_verified,
  have h61eqnIII := congr_arg (coeff (single vars.α_w 1 + single vars.γ 1)) eqnIII_verified,
  have h75eqnIII := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_w 1 + single vars.β 1)) eqnIII_verified,
  have h81eqnIII := congr_arg (coeff (single vars.r_v 1 + single vars.α_w 1)) eqnIII_verified,
  have h88eqnIII := congr_arg (coeff (single vars.r_w 1 + single vars.α_w 1 + single vars.β 1)) eqnIII_verified,
  have h89eqnIII := congr_arg (coeff (single vars.α_w 1 + single vars.α_y 1)) eqnIII_verified,
  have h96eqnIII := congr_arg (coeff (single vars.α_w 2)) eqnIII_verified,
  have h97eqnIII := congr_arg (coeff (single vars.α_w 2 + single vars.r_w 1)) eqnIII_verified,
  have h98eqnIII := congr_arg (coeff (single vars.α_w 1 + single vars.α_v 1 + single vars.r_v 1)) eqnIII_verified,
  have h2eqnIV := congr_arg (coeff (single vars.r_w 1 + single vars.α_y 1 + single vars.β 1)) eqnIV_verified,
  have h4eqnIV := congr_arg (coeff (single vars.r_v 1 + single vars.α_v 1 + single vars.α_y 1)) eqnIV_verified,
  have h23eqnIV := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_y 2)) eqnIV_verified,
  have h25eqnIV := congr_arg (coeff (single vars.r_w 1 + single vars.α_w 1 + single vars.α_y 1)) eqnIV_verified,
  have h30eqnIV := congr_arg (coeff (single vars.α_y 1 + single vars.β 1 + single vars.γ 1)) eqnIV_verified,
  have h37eqnIV := congr_arg (coeff (single vars.α_y 1 + single vars.γ 1)) eqnIV_verified,
  have h54eqnIV := congr_arg (coeff (single vars.α_v 1 + single vars.α_y 1)) eqnIV_verified,
  have h55eqnIV := congr_arg (coeff (single vars.r_w 1 + single vars.α_y 1)) eqnIV_verified,
  have h56eqnIV := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.α_y 1 + single vars.β 1)) eqnIV_verified,
  have h57eqnIV := congr_arg (coeff (single vars.r_v 1 + single vars.α_y 1 + single vars.β 1)) eqnIV_verified,
  have h59eqnIV := congr_arg (coeff (single vars.α_y 2)) eqnIV_verified,
  have h89eqnIV := congr_arg (coeff (single vars.α_w 1 + single vars.α_y 1)) eqnIV_verified,
  have h102eqnIV := congr_arg (coeff (single vars.r_v 1 + single vars.α_y 1)) eqnIV_verified,
  have h2eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,
  have h3eqnV := congr_arg (coeff (single vars.r_w 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,
  have h4eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,

  clear eqnI_verified,
  clear eqnII_verified,
  clear eqnIII_verified,
  clear eqnIV_verified,
  clear eqnV_verified,

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  simp only [] with finsupp_simp at *,

  rw [h2eqnV, h3eqnV, h4eqnV] at h1eqnI,

  done,

  clear h2eqnV h3eqnV h4eqnV,

  simp only [h11eqnII, h19eqnII, h21eqnII, h22eqnII, h32eqnII, h38eqnII, h52eqnII, h54eqnII, h71eqnII, h74eqnII, h93eqnII, h94eqnII, h101eqnII, h27eqnIII, h32eqnIII, h33eqnIII, h34eqnIII, h35eqnIII, h53eqnIII, h61eqnIII, h75eqnIII, h81eqnIII, h88eqnIII, h89eqnIII, h96eqnIII, h97eqnIII, h98eqnIII, h2eqnIV, h4eqnIV, h23eqnIV, h25eqnIV, h30eqnIV, h37eqnIV, h54eqnIV, h55eqnIV, h56eqnIV, h57eqnIV, h59eqnIV, h89eqnIV, h102eqnIV] at h1eqnI, --TODO bring back eqnI


  -- have h12eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,
  -- have h13eqnV := congr_arg (coeff (single vars.r_w 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,
  -- have h14eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,


  -- clear eqnV_verified,

  -- simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  -- simp only [] with finsupp_simp at *,

  -- simp only [*, zero_add, add_zero] at h12eqnV,

  clear h11eqnII h19eqnII h21eqnII h22eqnII h32eqnII h38eqnII h52eqnII h54eqnII h71eqnII h74eqnII h93eqnII h101eqnII h27eqnIII h32eqnIII h33eqnIII h34eqnIII h35eqnIII h53eqnIII h61eqnIII h75eqnIII h81eqnIII h88eqnIII h89eqnIII h96eqnIII h2eqnIV h4eqnIV h23eqnIV h25eqnIV h30eqnIV h37eqnIV h54eqnIV h55eqnIV h56eqnIV h57eqnIV h59eqnIV h89eqnIV h102eqnIV,


  done,


  -- Step 2: Recursively simplify and case-analyze the equations
  
  trace "Moving Cs right",
  simp only [simplifier1, simplifier2] at *,

  trace "Grouping distributivity",
  simp only [<-mul_add, <-add_mul, <-add_assoc, add_mul_distrib, add_mul_distrib'] at *,

  trace "Main simplification",
  simp only [*] with integral_domain_simp at *,
  tactic.integral_domain_tactic_v4,

  done,

  -- Solve remaining four cases by hand
  -- { rw [<-h1022, <-h0122, <-h0022],
  --   simp only [B_β_mul],
  --   simp only [<-mul_assoc],
  --   simp only [A_α_mul],
  --   simp only [<-mul_assoc],
  --   rw h1122,
  --   ring, },

end



end
