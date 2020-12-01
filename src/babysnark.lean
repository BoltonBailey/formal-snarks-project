
import data.mv_polynomial.basic
import data.polynomial.div


section 

universes v

variables {F : Type v}
variables [field F]


-- Variables for the theorem

inductive vars : Type
| X : vars
| Y : vars
| Z : vars

variables {m n l : ℕ}
-- NOTE: u is usually a universe variable in lean
-- here, u is a vector of polynomials
variable {u_stmt : vector (polynomial F) l}
variable {u_wit : vector (polynomial F) (n - l)}
variable {t : polynomial F}



-- A stucture to hold the sample of three field elements from which the CRS is constructed
structure field_sample :=
mk :: (τ : F) (β : F) (γ : F) 

-- The structure to hold a CRS
structure crs :=
mk :: (τs : vector F m) (γ : F) (βγ : F) (βpolys : vector F (n-l)) 

structure proof :=
mk :: (H : F) (V_wit : F) (B_wit : F)



def field_sample.setup (s : field_sample) (u_wit : vector (polynomial F) (n - l)) : crs 
:=
crs.mk 
    (vector.map (λ i, s.τ^i) (vector_range m)) 
    (s.γ) 
    (s.γ * s.β) 
    (vector.map (λ p : polynomial F, s.β * p.eval s.τ) u_wit)

-- FIXME
-- This isn't quite right: it carries out the proof with the field samples, rather than with the crs
-- In theory, the 

def crs.prove (a_wit : vector F (n - l)) (a_stmt : vector F l) (u_stmt) (u_wit) (s : field_sample) : proof :=
let H : polynomial F := polynomial.div_by_monic 
                        (((vector.map₂ (λ a u, (polynomial.C a) * u) a_wit u_wit).to_list.sum + 
                          (vector.map₂ (λ a u, (polynomial.C a) * u) a_stmt u_stmt).to_list.sum
                              )^2 - 1) t
in
let V_wit : polynomial F := ((vector.map₂ (λ a u, (polynomial.C a) * u) a_wit u_wit).to_list.sum)
in      
let B_wit : polynomial F := ((vector.map₂ (λ a u, (polynomial.C a) * s.β * u) a_wit u_wit).to_list.sum)
in                       
proof.mk
    (polynomial.eval H s.τ)
    (polynomial.eval V_wit s.τ)
    (polynomial.eval B_wit s.τ)


end