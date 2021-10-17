/-
Author: Bolton Bailey
-/
import data.mv_polynomial.basic
import data.mv_polynomial.comm_ring
import data.polynomial.div
import data.polynomial.field_division
import algebra.polynomial.big_operators
import .vars
import ...attributes
-- import ...general_lemmas.sub_for_mv_polynomial

/-!
# Knowledge Soundness

This file proves (TODO) the knowledge-soundness property of the Sonic snark scheme

## Notes

Page 7 " If the constraint system
is not satisfied the equation fails to hold with high probability, given a large enough field"
  What does high probability mean? Probability over Y? Is the probability ~O(1)/|F|? Does this come from schwartz zippel and if so, does it work on Laurent polynomials? 

  Update: after investigating, it seems like there is no practicla reason to use Laurent polynomials over regular ones. One can simply multiply each term of the CRS by ∏ v^{i_v} where i_v is the negative of the largest exponent of v that can occur. This does not seem to interfere with the updatability of the SNARK - the only justification they give for their SNARK being updatable is that "Groth et al. [46] showed that an SRS that contains monomials is
  updatable". This modification does not affect this. Furthermore, it does not seem to interfere with the Fiat-Shamir Heuristic, as far as I can tell.

Page 8
"Sonic demonstrates the constant term of t(X,Y) is zero, thus demonstrating that our constraint system is satisfied."
  Do you mean that the X = 0 polynomial is zero? Does the X^0 Y^0 term being zero mean the whole equation 1 is zero by the high probability thing? Is it really impossible to contrive something where the constant term is one of the ones that happens to be zero?

## Note on the use of the Fiat-Shamir Heuristic

This protocol is different for many of the others previously introduced in this repository in that it constructs a zk-SNARK as a reduction from an interactive proof system using the Fiat-Shamir heuristic. I think actually this has very little effect on the formalization. We still have a collection of group elements, and the fiat shamir random values are not group elements.

-/


open_locale big_operators

section
open mv_polynomial

noncomputable theory


universes u


/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]

parameters {n d Q : ℕ}

/- "Our constraint system has three vectors of length n: a b c ..."-/
parameters {a b c : fin n → F }

/- "We also have Q linear constraints of the form ... where 
u_q, v_q, w_q ∈ F^n are fixed vectors for the q-th linear constraint -/
parameters {u v w : fin Q -> fin n → F }
/- ""... with instance value k_q ∈ Fp" -/
parameter {k :  fin Q → F }

/- Let us define the polynomials ... -/
def u_poly (i : fin n) : polynomial F 
:= ∑ q in finset.fin_range Q, u q i • polynomial.X ^ (d + q + n)
def v_poly (i : fin n) : polynomial F 
:= ∑ q in finset.fin_range Q, v q i • polynomial.X ^ (d + q + n)
def w_poly (i : fin n) : polynomial F 
:= - polynomial.X ^ (d + i) - polynomial.X ^ (d - i) 
  + ∑ q in finset.fin_range Q, u q i • polynomial.X ^ (d + q + n)

def k_poly : polynomial F 
:= ∑ q in finset.fin_range Q, k q • polynomial.X ^ (d + q + n)

def r : mv_polynomial vars F 
:= ∑ i in finset.fin_range n, (
      a i • X vars.x ^ (d + i) * X vars.y ^ (d + i)
      + b i • X vars.x ^ (d - i) * X vars.y ^ (d - i)
      + c i • X vars.x ^ (d - i - n) * X vars.y ^ (d - i - n)
)

def s : mv_polynomial vars F 
:= ∑ i in finset.fin_range n, (
      (u_poly i).eval₂ C (X vars.y) * X vars.x ^ (d - i)
      + (v_poly i).eval₂ C (X vars.y) * X vars.x ^ (d + i)
      + (w_poly i).eval₂ C (X vars.y) * X vars.x ^ (d + i + n)
)

def r' : mv_polynomial vars F := r + s

def t : mv_polynomial vars F := r.eval₂ C (λ var, if var = vars.y then 1 else X var) * r' - k_poly.eval₂ C (X vars.y)

-- Initial CRS
-- G_1 elements
def crs_1_x (i : fin (2 * d + 1)) : (mv_polynomial vars F) := X vars.x ^ (i : ℕ)
def crs_1_α_x (i : fin (2 * d + 1)) : (mv_polynomial vars F) := if i = d then 0 else X vars.α * X vars.x ^ (i : ℕ)
-- G_2 elements
def crs_2_x (i : fin (2 * d + 1)) : (mv_polynomial vars F) := X vars.x ^ (i : ℕ)
def crs_2_α_x (i : fin (2 * d + 1)) : (mv_polynomial vars F) := X vars.α * X vars.x ^ (i : ℕ)
-- G_T element
def crs_target_α : (mv_polynomial vars F) := X vars.α


-- CRS including y

-- CRS including y, z

parameters {R_comp_crs_1_x R_comp_crs_1_α_x : fin (2 * d + 1) → F}

/-- Polynomial forms of the adversary's proof representation -/
def R : mv_polynomial vars F := 
  ∑ i in (finset.fin_range (2 * d + 1)), (R_comp_crs_1_x i) • (crs_1_x i)
  +
  ∑ i in (finset.fin_range (2 * d + 1)), (R_comp_crs_1_α_x i) • (crs_1_α_x i)


parameters {T_comp_crs_1_x T_comp_crs_1_α_x : fin (2 * d + 1) → F}

/-- Polynomial forms of the adversary's proof representation -/
def T : mv_polynomial vars F := 
  ∑ i in (finset.fin_range (2 * d + 1)), (T_comp_crs_1_x i) • (crs_1_x i)
  +
  ∑ i in (finset.fin_range (2 * d + 1)), (T_comp_crs_1_α_x i) • (crs_1_α_x i)





end