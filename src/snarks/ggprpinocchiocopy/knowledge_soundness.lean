/-
Author: Bolton Bailey
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
-- parameter {w_stmt : fin n_stmt → polynomial F }
-- parameter {y_stmt : fin n_stmt → polynomial F }
parameter {v_wit : fin n_wit → polynomial F }
-- parameter {w_wit : fin n_wit → polynomial F }
parameter {w : fin m → polynomial F }
-- parameter {y_wit : fin n_wit → polynomial F }
parameter {v_0 : polynomial F }
parameter {w_0 : polynomial F }
-- parameter {y_0 : polynomial F }

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


def satisfying (a_stmt : fin n_stmt → F) (a_wit : fin n_wit → F) (b : fin m -> F) := 
(
  (v_0 
    + (∑ i in (finset.fin_range n_stmt), a_stmt i • v_stmt i) 
    + ∑ i in (finset.fin_range n_wit), a_wit i • v_wit i)
 * 
  (w_0 
    + (∑ i in (finset.fin_range m), b i • w i)))
   %ₘ t = 0



/- Multivariable polynomial definititons and ultilities -/




run_cmd mk_simp_attr `poly
run_cmd tactic.add_doc_string `simp_attr.poly "Attribute for defintions of poly elements"

-- Helpers for representing vars as polynomials 

@[poly] def β_v_poly : mv_polynomial vars (polynomial F) := mv_polynomial.X vars.β_v
@[poly] def β_w_poly : mv_polynomial vars (polynomial F) := mv_polynomial.X vars.β_w
@[poly] def s_poly : mv_polynomial vars (polynomial F) := mv_polynomial.C (polynomial.X)
@[poly] def α_poly : mv_polynomial vars (polynomial F) := mv_polynomial.X vars.α
@[poly] def γ_poly : mv_polynomial vars (polynomial F) := mv_polynomial.X vars.γ


@[poly] def crs_powers (i : fin d) : (mv_polynomial vars (polynomial F)) := mv_polynomial.C (polynomial.X ^ (i : ℕ))
@[poly] def crs_α_powers (i : fin d) : (mv_polynomial vars (polynomial F)) := α_poly * mv_polynomial.C (polynomial.X ^ (i : ℕ))
@[poly] def crs_v_wit_k (k : fin n_wit) : mv_polynomial vars (polynomial F) := 
  mv_polynomial.C (v_wit k)
@[poly] def crs_w_k (k : fin m) : mv_polynomial vars (polynomial F) := 
  mv_polynomial.C (w k)
@[poly] def crs_α_v_wit_k (k : fin n_wit) : mv_polynomial vars (polynomial F) := 
  α_poly * mv_polynomial.C (v_wit k)
@[poly] def crs_α_w_k (k : fin m) : mv_polynomial vars (polynomial F) := 
  α_poly * mv_polynomial.C (w k)
@[poly] def crs_β_v_wit_k (k : fin n_wit) : mv_polynomial vars (polynomial F) := 
  β_v_poly * mv_polynomial.C (v_wit k)
@[poly] def crs_β_w_k (k : fin m) : mv_polynomial vars (polynomial F) := 
  β_w_poly * mv_polynomial.C (w k)


-- The crs elements as multivariate polynomials of the toxic waste samples: Verification key elements 

@[poly] def crs_α : mv_polynomial vars (polynomial F) := α_poly
@[poly] def crs_γ : mv_polynomial vars (polynomial F) := γ_poly
@[poly] def crs_β_v_γ : mv_polynomial vars (polynomial F) := β_v_poly * γ_poly
@[poly] def crs_β_w_γ : mv_polynomial vars (polynomial F) := β_w_poly * γ_poly
@[poly] def crs_v_0 : mv_polynomial vars (polynomial F) := 
  mv_polynomial.C (v_0)
@[poly] def crs_v_stmt (i : fin n_stmt) : mv_polynomial vars (polynomial F) := 
  mv_polynomial.C (v_stmt i)
@[poly] def crs_w_0 : mv_polynomial vars (polynomial F) := 
  mv_polynomial.C (w_0)
@[poly] def crs_t : mv_polynomial vars (polynomial F) := 
  mv_polynomial.C (t)


-- Coefficients of the CRS elements in the representation of the v_wit proof element in the AGM  
parameters {v_wit_comp_crs_powers : fin d → F}
parameters {v_wit_comp_crs_α_powers : fin d → F}
parameters {v_wit_comp_crs_v_wit_k : fin n_wit →  F}
parameters {v_wit_comp_crs_w_k : fin m → F}
parameters {v_wit_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {v_wit_comp_crs_α_w_k : fin m →  F}
parameters {v_wit_comp_crs_β_v_wit_k : fin n_wit →  F}
parameters {v_wit_comp_crs_β_w_k : fin m →  F}

parameters {v_wit_comp_crs_α : F}
parameters {v_wit_comp_crs_γ : F}
parameters {v_wit_comp_crs_β_v_γ : F}
parameters {v_wit_comp_crs_β_w_γ : F}
parameters {v_wit_comp_crs_v_0 : F}
parameters {v_wit_comp_crs_w_0 : F}

parameters {v_wit_comp_crs_v_stmt : fin n_stmt → F}

parameters {v_wit_comp_crs_t : F}


/-- Polynomial form of the representation of the v_wit proof element in the AGM -/
def proof_v_wit : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_powers i))
  +  
  ∑ i in (finset.fin_range d), (crs_α_powers i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_α_powers i))
  +  
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_w_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_α_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_α_w_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_α_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_wit_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_β_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_β_w_k i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_β_w_k i))
  +
  crs_α * mv_polynomial.C (polynomial.C (v_wit_comp_crs_α))
  +   
  crs_γ * mv_polynomial.C (polynomial.C (v_wit_comp_crs_γ))
  +   
  crs_β_v_γ * mv_polynomial.C (polynomial.C (v_wit_comp_crs_β_v_γ)) 
  +   
  crs_β_w_γ * mv_polynomial.C (polynomial.C (v_wit_comp_crs_β_w_γ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (v_wit_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (v_wit_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (v_wit_comp_crs_w_0)) 
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (v_wit_comp_crs_v_stmt i))

-- Coefficients of the CRS elements in the representation of the w proof element in the AGM  
parameters {w_comp_crs_powers : fin d → F}
parameters {w_comp_crs_α_powers : fin d → F}
parameters {w_comp_crs_v_wit_k : fin n_wit →  F}
parameters {w_comp_crs_w_k : fin m → F}
parameters {w_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {w_comp_crs_α_w_k : fin m →  F}
parameters {w_comp_crs_β_v_wit_k : fin n_wit →  F}
parameters {w_comp_crs_β_w_k : fin m →  F}

parameters {w_comp_crs_α : F}
parameters {w_comp_crs_γ : F}
parameters {w_comp_crs_β_v_γ : F}
parameters {w_comp_crs_β_w_γ : F}
parameters {w_comp_crs_v_0 : F}
parameters {w_comp_crs_w_0 : F}

parameters {w_comp_crs_v_stmt : fin n_stmt → F}

parameters {w_comp_crs_t : F}


/-- Polynomial form of the representation of the w proof element in the AGM -/
def proof_w : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (w_comp_crs_powers i))
  +  
  ∑ i in (finset.fin_range d), (crs_α_powers i) * mv_polynomial.C (polynomial.C (w_comp_crs_α_powers i))
  +  
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (w_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_w_k i) * mv_polynomial.C (polynomial.C (w_comp_crs_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (w_comp_crs_α_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_α_w_k i) * mv_polynomial.C (polynomial.C (w_comp_crs_α_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_wit_k i) * mv_polynomial.C (polynomial.C (w_comp_crs_β_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_β_w_k i) * mv_polynomial.C (polynomial.C (w_comp_crs_β_w_k i))
  +
  crs_α * mv_polynomial.C (polynomial.C (w_comp_crs_α))
  +   
  crs_γ * mv_polynomial.C (polynomial.C (w_comp_crs_γ))
  +   
  crs_β_v_γ * mv_polynomial.C (polynomial.C (w_comp_crs_β_v_γ)) 
  +   
  crs_β_w_γ * mv_polynomial.C (polynomial.C (w_comp_crs_β_w_γ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (w_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (w_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (w_comp_crs_w_0)) 
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (w_comp_crs_v_stmt i))

-- Coefficients of the CRS elements in the representation of the h proof element in the AGM  
parameters {h_comp_crs_powers : fin d → F}
parameters {h_comp_crs_α_powers : fin d → F}
parameters {h_comp_crs_v_wit_k : fin n_wit →  F}
parameters {h_comp_crs_w_k : fin m → F}
parameters {h_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {h_comp_crs_α_w_k : fin m →  F}
parameters {h_comp_crs_β_v_wit_k : fin n_wit →  F}
parameters {h_comp_crs_β_w_k : fin m →  F}

parameters {h_comp_crs_α : F}
parameters {h_comp_crs_γ : F}
parameters {h_comp_crs_β_v_γ : F}
parameters {h_comp_crs_β_w_γ : F}
parameters {h_comp_crs_v_0 : F}
parameters {h_comp_crs_w_0 : F}

parameters {h_comp_crs_v_stmt : fin n_stmt → F}

parameters {h_comp_crs_t : F}


/-- Polynomial form of the representation of the v_wit proof element in the AGM -/
def proof_h : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (h_comp_crs_powers i))
  +  
  ∑ i in (finset.fin_range d), (crs_α_powers i) * mv_polynomial.C (polynomial.C (h_comp_crs_α_powers i))
  +  
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_w_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_α_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_α_w_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_α_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_wit_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_β_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_β_w_k i) * mv_polynomial.C (polynomial.C (h_comp_crs_β_w_k i))
  +
  crs_α * mv_polynomial.C (polynomial.C (h_comp_crs_α))
  +   
  crs_γ * mv_polynomial.C (polynomial.C (h_comp_crs_γ))
  +   
  crs_β_v_γ * mv_polynomial.C (polynomial.C (h_comp_crs_β_v_γ)) 
  +   
  crs_β_w_γ * mv_polynomial.C (polynomial.C (h_comp_crs_β_w_γ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (h_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (h_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (h_comp_crs_w_0)) 
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (h_comp_crs_v_stmt i))

-- Coefficients of the CRS elements in the representation of the α_v_wit proof element in the AGM  
parameters {α_v_wit_comp_crs_powers : fin d → F}
parameters {α_v_wit_comp_crs_α_powers : fin d → F}
parameters {α_v_wit_comp_crs_v_wit_k : fin n_wit →  F}
parameters {α_v_wit_comp_crs_w_k : fin m → F}
parameters {α_v_wit_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {α_v_wit_comp_crs_α_w_k : fin m →  F}
parameters {α_v_wit_comp_crs_β_v_wit_k : fin n_wit →  F}
parameters {α_v_wit_comp_crs_β_w_k : fin m →  F}

parameters {α_v_wit_comp_crs_α : F}
parameters {α_v_wit_comp_crs_γ : F}
parameters {α_v_wit_comp_crs_β_v_γ : F}
parameters {α_v_wit_comp_crs_β_w_γ : F}
parameters {α_v_wit_comp_crs_v_0 : F}
parameters {α_v_wit_comp_crs_w_0 : F}

parameters {α_v_wit_comp_crs_v_stmt : fin n_stmt → F}

parameters {α_v_wit_comp_crs_t : F}


/-- Polynomial form of the representation of the v_wit proof element in the AGM -/
def proof_α_v_wit : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_powers i))
  +  
  ∑ i in (finset.fin_range d), (crs_α_powers i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_α_powers i))
  +  
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_w_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_α_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_α_w_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_α_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_wit_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_β_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_β_w_k i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_β_w_k i))
  +
  crs_α * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_α))
  +   
  crs_γ * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_γ))
  +   
  crs_β_v_γ * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_β_v_γ)) 
  +   
  crs_β_w_γ * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_β_w_γ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_w_0)) 
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (α_v_wit_comp_crs_v_stmt i))

-- Coefficients of the CRS elements in the representation of the α_w proof element in the AGM  
parameters {α_w_comp_crs_powers : fin d → F}
parameters {α_w_comp_crs_α_powers : fin d → F}
parameters {α_w_comp_crs_v_wit_k : fin n_wit →  F}
parameters {α_w_comp_crs_w_k : fin m → F}
parameters {α_w_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {α_w_comp_crs_α_w_k : fin m →  F}
parameters {α_w_comp_crs_β_v_wit_k : fin n_wit →  F}
parameters {α_w_comp_crs_β_w_k : fin m →  F}

parameters {α_w_comp_crs_α : F}
parameters {α_w_comp_crs_γ : F}
parameters {α_w_comp_crs_β_v_γ : F}
parameters {α_w_comp_crs_β_w_γ : F}
parameters {α_w_comp_crs_v_0 : F}
parameters {α_w_comp_crs_w_0 : F}

parameters {α_w_comp_crs_v_stmt : fin n_stmt → F}

parameters {α_w_comp_crs_t : F}


/-- Polynomial form of the representation of the v_wit proof element in the AGM -/
def proof_α_w : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (α_w_comp_crs_powers i))
  +  
  ∑ i in (finset.fin_range d), (crs_α_powers i) * mv_polynomial.C (polynomial.C (α_w_comp_crs_α_powers i))
  +  
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (α_w_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_w_k i) * mv_polynomial.C (polynomial.C (α_w_comp_crs_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (α_w_comp_crs_α_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_α_w_k i) * mv_polynomial.C (polynomial.C (α_w_comp_crs_α_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_wit_k i) * mv_polynomial.C (polynomial.C (α_w_comp_crs_β_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_β_w_k i) * mv_polynomial.C (polynomial.C (α_w_comp_crs_β_w_k i))
  +
  crs_α * mv_polynomial.C (polynomial.C (α_w_comp_crs_α))
  +   
  crs_γ * mv_polynomial.C (polynomial.C (α_w_comp_crs_γ))
  +   
  crs_β_v_γ * mv_polynomial.C (polynomial.C (α_w_comp_crs_β_v_γ)) 
  +   
  crs_β_w_γ * mv_polynomial.C (polynomial.C (α_w_comp_crs_β_w_γ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (α_w_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (α_w_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (α_w_comp_crs_w_0)) 
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (α_w_comp_crs_v_stmt i))

-- Coefficients of the CRS elements in the representation of the α_h proof element in the AGM  
parameters {α_h_comp_crs_powers : fin d → F}
parameters {α_h_comp_crs_α_powers : fin d → F}
parameters {α_h_comp_crs_v_wit_k : fin n_wit →  F}
parameters {α_h_comp_crs_w_k : fin m → F}
parameters {α_h_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {α_h_comp_crs_α_w_k : fin m →  F}
parameters {α_h_comp_crs_β_v_wit_k : fin n_wit →  F}
parameters {α_h_comp_crs_β_w_k : fin m →  F}

parameters {α_h_comp_crs_α : F}
parameters {α_h_comp_crs_γ : F}
parameters {α_h_comp_crs_β_v_γ : F}
parameters {α_h_comp_crs_β_w_γ : F}
parameters {α_h_comp_crs_v_0 : F}
parameters {α_h_comp_crs_w_0 : F}

parameters {α_h_comp_crs_v_stmt : fin n_stmt → F}

parameters {α_h_comp_crs_t : F}


/-- Polynomial form of the representation of the α_h proof element in the AGM -/
def proof_α_h : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (α_h_comp_crs_powers i))
  +  
  ∑ i in (finset.fin_range d), (crs_α_powers i) * mv_polynomial.C (polynomial.C (α_h_comp_crs_α_powers i))
  +  
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (α_h_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_w_k i) * mv_polynomial.C (polynomial.C (α_h_comp_crs_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (α_h_comp_crs_α_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_α_w_k i) * mv_polynomial.C (polynomial.C (α_h_comp_crs_α_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_wit_k i) * mv_polynomial.C (polynomial.C (α_h_comp_crs_β_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_β_w_k i) * mv_polynomial.C (polynomial.C (α_h_comp_crs_β_w_k i))
  +
  crs_α * mv_polynomial.C (polynomial.C (α_h_comp_crs_α))
  +   
  crs_γ * mv_polynomial.C (polynomial.C (α_h_comp_crs_γ))
  +   
  crs_β_v_γ * mv_polynomial.C (polynomial.C (α_h_comp_crs_β_v_γ)) 
  +   
  crs_β_w_γ * mv_polynomial.C (polynomial.C (α_h_comp_crs_β_w_γ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (α_h_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (α_h_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (α_h_comp_crs_w_0)) 
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (α_h_comp_crs_v_stmt i))

  -- Coefficients of the CRS elements in the representation of the y proof element in the AGM  
parameters {y_comp_crs_powers : fin d → F}
parameters {y_comp_crs_α_powers : fin d → F}
parameters {y_comp_crs_v_wit_k : fin n_wit →  F}
parameters {y_comp_crs_w_k : fin m → F}
parameters {y_comp_crs_α_v_wit_k : fin n_wit →  F}
parameters {y_comp_crs_α_w_k : fin m →  F}
parameters {y_comp_crs_β_v_wit_k : fin n_wit →  F}
parameters {y_comp_crs_β_w_k : fin m →  F}

parameters {y_comp_crs_α : F}
parameters {y_comp_crs_γ : F}
parameters {y_comp_crs_β_v_γ : F}
parameters {y_comp_crs_β_w_γ : F}
parameters {y_comp_crs_v_0 : F}
parameters {y_comp_crs_w_0 : F}

parameters {y_comp_crs_v_stmt : fin n_stmt → F}

parameters {y_comp_crs_t : F}


/-- Polynomial form of the representation of the y proof element in the AGM -/
def proof_y : mv_polynomial vars (polynomial F) := 
  ∑ i in (finset.fin_range d), (crs_powers i) * mv_polynomial.C (polynomial.C (y_comp_crs_powers i))
  +  
  ∑ i in (finset.fin_range d), (crs_α_powers i) * mv_polynomial.C (polynomial.C (y_comp_crs_α_powers i))
  +  
  ∑ i in (finset.fin_range n_wit), (crs_v_wit_k i) * mv_polynomial.C (polynomial.C (y_comp_crs_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_w_k i) * mv_polynomial.C (polynomial.C (y_comp_crs_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_α_v_wit_k i) * mv_polynomial.C (polynomial.C (y_comp_crs_α_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_α_w_k i) * mv_polynomial.C (polynomial.C (y_comp_crs_α_w_k i))
  +
  ∑ i in (finset.fin_range n_wit), (crs_β_v_wit_k i) * mv_polynomial.C (polynomial.C (y_comp_crs_β_v_wit_k i))
  +
  ∑ i in (finset.fin_range m), (crs_β_w_k i) * mv_polynomial.C (polynomial.C (y_comp_crs_β_w_k i))
  +
  crs_α * mv_polynomial.C (polynomial.C (y_comp_crs_α))
  +   
  crs_γ * mv_polynomial.C (polynomial.C (y_comp_crs_γ))
  +   
  crs_β_v_γ * mv_polynomial.C (polynomial.C (y_comp_crs_β_v_γ)) 
  +   
  crs_β_w_γ * mv_polynomial.C (polynomial.C (y_comp_crs_β_w_γ)) 
  +   
  crs_t * mv_polynomial.C (polynomial.C (y_comp_crs_t))
  +   
  crs_v_0 * mv_polynomial.C (polynomial.C (y_comp_crs_v_0)) 
  +   
  crs_w_0 * mv_polynomial.C (polynomial.C (y_comp_crs_w_0)) 
  +
  ∑ i in (finset.fin_range n_stmt), (crs_v_stmt i) * mv_polynomial.C (polynomial.C (y_comp_crs_v_stmt i))

-- Single variable form of V_wit
def v_wit_sv (a_wit : fin n_wit → F) : polynomial F 
:= ∑ i in finset.fin_range n_wit, a_wit i • v_wit i

/-- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def v_stmt_sv (a_stmt : fin n_stmt → F) : polynomial F 
:= ∑ i in (finset.fin_range n_stmt), a_stmt i • v_stmt i

@[poly] def v_stmt_mv (a_stmt : fin n_stmt → F) : mv_polynomial vars (polynomial F) 
:= mv_polynomial.C (v_stmt_sv a_stmt)

/-- The statement polynomial that the verifier computes from the statement bits, as a single variable polynomial -/
def w_sv (b : fin m → F) : polynomial F 
:= ∑ i in (finset.fin_range m), b i • w i

@[poly] def w_mv (a : fin m → F) : mv_polynomial vars (polynomial F) 
:= mv_polynomial.C (w_sv a)

/-- Multivariable version of t -/
@[poly] def t_mv : mv_polynomial vars (polynomial F) := mv_polynomial.C t


-- Equations

def eqnI (c_stmt : fin n_stmt → F ) : Prop := 
  (crs_v_0 + v_stmt_mv c_stmt + proof_v_wit) * (crs_w_0 + proof_w) = (t_mv * proof_h)

def eqnII : Prop := 
  proof_α_v_wit = proof_v_wit * crs_α

def eqnIII : Prop := 
  proof_α_w = proof_w * crs_α

def eqnIV : Prop := 
  proof_α_h = proof_h * crs_α

def eqnV : Prop := 
  proof_y * crs_γ = proof_v_wit * crs_β_v_γ + proof_w * crs_β_w_γ

-- Coefficients
open mv_polynomial finsupp

-- lemma sadojfh (a b c : mv_polynomial vars (polynomial F)) : a + b - c = a -c + b := 
-- begin
--   ring,
-- end
-- example (a b c d e f g h i : F) : a + d + b + e + c - (a + b) = 0 :=
-- begin
--   abel,
-- end

lemma move_C_left (p : polynomial F) (f : F) :
  p * polynomial.C f = polynomial.C f * p :=
begin
  ring,
end

-- set_option profiler true

lemma eqnIIresults (eqnII_verified : eqnII) : 
  proof_v_wit 
  = mv_polynomial.C ( 
        ∑ i in (finset.fin_range n_wit),  (v_wit i) *  (polynomial.C (v_wit_comp_crs_v_wit_k i))
        + v_0 * (polynomial.C v_wit_comp_crs_v_0)
        + ∑ i in finset.fin_range n_stmt, (v_stmt i) * (polynomial.C (v_wit_comp_crs_v_stmt i))
        + ∑ x in finset.fin_range d, (polynomial.X ^ (x : ℕ)) * (polynomial.C (v_wit_comp_crs_powers x))
        + polynomial.C v_wit_comp_crs_w_0 * w_0 
        + polynomial.C v_wit_comp_crs_t * t 
        + ∑ (x : fin m) in finset.fin_range m, polynomial.C (v_wit_comp_crs_w_k x) * w x
    )
    :=
begin

  rw eqnII at eqnII_verified,

  simp_rw [proof_v_wit, proof_α_v_wit] at eqnII_verified ⊢,
  -- simp_rw [proof_v_wit, proof_w_wit, proof_y_wit, proof_h, 
  --       proof_v_wit', proof_w_wit', proof_y_wit', proof_Z] at eqnII_verified,
  simp only [] with poly at eqnII_verified ⊢,
  -- simp only [] with polynomial_nf_3 at eqn',
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnII_verified ⊢,

  have h11eqnII := congr_arg (coeff (single vars.α 1 + single vars.β_v 1 + single vars.γ 1)) eqnII_verified,
  have h12eqnII := congr_arg (coeff (single vars.α 1 + single vars.β_w 1 + single vars.γ 1)) eqnII_verified,
  have h19eqnII := congr_arg (coeff (single vars.α 1 + single vars.γ 1)) eqnII_verified,
  have h21eqnII := congr_arg (coeff (single vars.α 1 + single vars.β_v 1)) eqnII_verified,
  have h22eqnII := congr_arg (coeff (single vars.α 2)) eqnII_verified,
  have h71eqnII := congr_arg (coeff (single vars.α 1)) eqnII_verified,
  have h74eqnII := congr_arg (coeff (single vars.α 1 + single vars.β_w 1)) eqnII_verified,

  clear eqnII_verified,

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  simp only [] with finsupp_simp at *,  

  simp only [h11eqnII, h12eqnII, h19eqnII, h21eqnII, h22eqnII,  h71eqnII, h74eqnII],
  simp only [monomial_zero, add_zero, zero_add, <-monomial_add],



  rw <-sub_eq_iff_eq_add',
  ring_nf,
 
  rw <-sub_eq_zero,
  simp_rw [move_C_left],
  ring_nf,

  have h22eqnII' := congr_arg (monomial (single vars.α 1)) h22eqnII,
  simp only [monomial_zero, add_zero, zero_add, <-monomial_add] at h22eqnII',

  rw <-h22eqnII',
  rw <-sub_eq_iff_eq_add,
  -- simp_rw [add_assoc],
  abel,
  rw <-sub_eq_iff_eq_add',
  simp_rw [move_C_left],

  -- simp_rw [add_assoc],
  abel,

end


lemma eqnIIIresults (eqnIII_verified : eqnIII) : 
  proof_w 
  = mv_polynomial.C ( 
        ∑ i in (finset.fin_range n_wit),  (v_wit i) *  (polynomial.C (w_comp_crs_v_wit_k i))
        + v_0 * (polynomial.C w_comp_crs_v_0)
        + ∑ i in finset.fin_range n_stmt, (v_stmt i) * (polynomial.C (w_comp_crs_v_stmt i))
        + ∑ x in finset.fin_range d, (polynomial.X ^ (x : ℕ)) * ( polynomial.C (w_comp_crs_powers x))
        + polynomial.C w_comp_crs_w_0 * w_0 
        + polynomial.C w_comp_crs_t * t 
        + ∑ (x : fin m) in finset.fin_range m, polynomial.C (w_comp_crs_w_k x) * w x
    ) :=
begin

  rw eqnIII at eqnIII_verified,

  simp_rw [proof_w, proof_α_w] at eqnIII_verified ⊢,
  -- simp_rw [proof_v_wit, proof_w_wit, proof_y_wit, proof_h, 
  --       proof_v_wit', proof_w_wit', proof_y_wit', proof_Z] at eqnIII_verified,
  simp only [] with poly at eqnIII_verified ⊢,
  -- simp only [] with polynomial_nf_3 at eqn',
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnIII_verified ⊢,

  have h11eqnIII := congr_arg (coeff (single vars.α 1 + single vars.β_v 1 + single vars.γ 1)) eqnIII_verified,
  have h12eqnIII := congr_arg (coeff (single vars.α 1 + single vars.β_w 1 + single vars.γ 1)) eqnIII_verified,
  have h19eqnIII := congr_arg (coeff (single vars.α 1 + single vars.γ 1)) eqnIII_verified,
  have h21eqnIII := congr_arg (coeff (single vars.α 1 + single vars.β_v 1)) eqnIII_verified,
  have h22eqnIII := congr_arg (coeff (single vars.α 2)) eqnIII_verified,
  have h71eqnIII := congr_arg (coeff (single vars.α 1)) eqnIII_verified,
  have h74eqnIII := congr_arg (coeff (single vars.α 1 + single vars.β_w 1)) eqnIII_verified,

  clear eqnIII_verified,

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  simp only [] with finsupp_simp at *,  

  simp only [h11eqnIII, h12eqnIII, h19eqnIII, h21eqnIII, h22eqnIII, h71eqnIII, h74eqnIII],
  simp only [monomial_zero, add_zero, zero_add, <-monomial_add],
 
  rw <-sub_eq_iff_eq_add',
  ring_nf,
 
  rw <-sub_eq_zero,
  simp_rw [move_C_left],
  ring_nf,

  have h22eqnIII' := congr_arg (monomial (single vars.α 1)) h22eqnIII,
  simp only [monomial_zero, add_zero, zero_add, <-monomial_add] at h22eqnIII',

  rw <-h22eqnIII',
  rw <-sub_eq_iff_eq_add,
  -- simp_rw [add_assoc],
  abel,
  rw <-sub_eq_iff_eq_add',
  simp_rw [move_C_left],

  -- simp_rw [add_assoc],
  abel,
end

-- lemma eqnIVresults (eqnIV_verified : eqnIV) :   
--   proof_h 
--   = mv_polynomial.C ( 
--         ∑ i in (finset.fin_range n_wit),  (v_wit i) *  (polynomial.C (h_comp_crs_v_wit_k i))
--         + v_0 * (polynomial.C h_comp_crs_v_0)
--         + ∑ i in finset.fin_range n_stmt, (v_stmt i) * (polynomial.C (h_comp_crs_v_stmt i))
--         + ∑ x in finset.fin_range d, (polynomial.X ^ (x : ℕ)) * ( polynomial.C (h_comp_crs_powers x))
--         + polynomial.C h_comp_crs_w_0 * w_0 
--         + polynomial.C h_comp_crs_t * t 
--         + ∑ (x : fin m) in finset.fin_range m, polynomial.C (h_comp_crs_w_k x) * w x
--     )  :=
-- begin
--   rw eqnIV at eqnIV_verified,

--   simp_rw [proof_h, proof_α_h] at eqnIV_verified ⊢,
--   -- simp_rw [proof_v_wit, proof_w_wit, proof_y_wit, proof_h, 
--   --       proof_v_wit', proof_w_wit', proof_y_wit', proof_Z] at eqnIV_verified,
--   simp only [] with poly at eqnIV_verified ⊢,
--   -- simp only [] with polynomial_nf_3 at eqn',
--   simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnIV_verified ⊢,

--   have h11eqnIV := congr_arg (coeff (single vars.α 1 + single vars.β_v 1 + single vars.γ 1)) eqnIV_verified,
--   have h12eqnIV := congr_arg (coeff (single vars.α 1 + single vars.β_w 1 + single vars.γ 1)) eqnIV_verified,
--   have h19eqnIV := congr_arg (coeff (single vars.α 1 + single vars.γ 1)) eqnIV_verified,
--   have h21eqnIV := congr_arg (coeff (single vars.α 1 + single vars.β_v 1)) eqnIV_verified,
--   have h22eqnIV := congr_arg (coeff (single vars.α 2)) eqnIV_verified,
--   have h71eqnIV := congr_arg (coeff (single vars.α 1)) eqnIV_verified,
--   have h74eqnIV := congr_arg (coeff (single vars.α 1 + single vars.β_w 1)) eqnIV_verified,

--   clear eqnIV_verified,

--   simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
--   simp only [] with finsupp_simp at *,  

--   simp only [h11eqnIV, h12eqnIV, h19eqnIV, h21eqnIV, h22eqnIV, h71eqnIV, h74eqnIV],
--   simp only [monomial_zero, add_zero, zero_add, <-monomial_add],
 
--   rw <-sub_eq_iff_eq_add',
--   ring_nf,
 
--   rw <-sub_eq_zero,
--   simp_rw [move_C_left],
--   ring_nf,

--   have h22eqnIV' := congr_arg (monomial (single vars.α 1)) h22eqnIV,
--   simp only [monomial_zero, add_zero, zero_add, <-monomial_add] at h22eqnIV',

--   rw <-h22eqnIV',
--   rw <-sub_eq_iff_eq_add,
--   -- simp_rw [add_assoc],
--   abel,
--   rw <-sub_eq_iff_eq_add',
--   simp_rw [move_C_left],

--   -- simp_rw [add_assoc],
--   abel,
-- end

lemma polynomial.mul_mod_by_monic (t p : polynomial F) (mt : t.monic) : (t * p) %ₘ t = 0 :=
begin
  rw polynomial.dvd_iff_mod_by_monic_eq_zero,
  apply dvd_mul_right,
  exact mt,
end

lemma soundness (c_stmt : fin n_stmt → F ) (eqnI_verified : eqnI c_stmt) 
  (eqnII_verified : eqnII) (eqnIII_verified : eqnIII) -- (eqnIV_verified : eqnIV) 
  (eqnV_verified : eqnV) : (satisfying c_stmt y_comp_crs_β_v_wit_k y_comp_crs_β_w_k) :=
begin
  rw eqnV at eqnV_verified,

  have eqnII' := eqnIIresults eqnII_verified,
  have eqnIII' := eqnIIIresults eqnIII_verified,
  -- have eqnIV' := eqnIVresults eqnIV_verified,

  simp_rw [eqnII', eqnIII', proof_y] at eqnV_verified,
  simp only [] with poly at eqnV_verified,
  -- simp only [] with polynomial_nf_3 at eqn',
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnV_verified,

  have h2eqnV := congr_arg (coeff (single vars.β_v 1 + single vars.γ 1)) eqnV_verified,
  have h3eqnV := congr_arg (coeff (single vars.β_w 1 + single vars.γ 1)) eqnV_verified,
  -- have h4eqnV := congr_arg (coeff (single vars.r_v 1 + single vars.r_w 1 + single vars.β 1 + single vars.γ 1)) eqnV_verified,



  clear eqnV_verified,

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at *,
  simp only [] with finsupp_simp at *,

  rw [<-h2eqnV] at eqnII',
  rw [<-h3eqnV] at eqnIII',
  -- rw [<-h4eqnV] at eqnIV',

  rw [eqnI] at eqnI_verified,
  rw satisfying,

  simp_rw [eqnII', eqnIII', proof_h] at eqnI_verified,

  simp only [] with poly at eqnI_verified,
  -- simp only [] with polynomial_nf_3 at eqn',
  simp only [mv_polynomial.X, C_apply, mv_polynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, finset.sum_add_distrib, finset.sum_hom, mul_add, add_mul, sum_monomial_hom] at eqnI_verified,

  have h1eqnI := congr_arg (coeff 0) eqnI_verified,

  clear eqnI_verified,

  simp only [finsupp_vars_eq_ext] with coeff_simp finsupp_eq at h1eqnI,
  simp only [] with finsupp_simp at h1eqnI,
  -- rw <-sub_eq_iff_eq_add at h1eqnI,
  simp_rw [<-mul_add t] at h1eqnI,
  -- rw <-sub_eq_zero at h1eqnI,
  -- rw polynomial.dvd_iff_mod_by_monic_eq_zero,

  have h2eqnI := congr_arg (%ₘ t) h1eqnI,
  simp only [polynomial.zero_mod_by_monic] at h2eqnI,
  rw polynomial.mul_mod_by_monic at h2eqnI,
  rw <- h2eqnI,
  congr' 1,
  simp_rw [v_stmt_sv, polynomial.smul_eq_C_mul],
  simp only [add_mul, mul_add],
  simp_rw [move_C_left],
  -- congr' 1,
  -- rw <-sub_eq_zero,

  abel,

  exact monic_t,

end



end
