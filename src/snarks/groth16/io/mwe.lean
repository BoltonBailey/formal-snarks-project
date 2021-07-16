/-
Author: Bolton Bailey
-/
import data.mv_polynomial.basic
import tactic.wlog

section

open mv_polynomial

noncomputable theory


universes u


/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]


/-- The coefficients of the CRS elements in the algebraic adversary's representation -/
parameters {A_α A_β B_α B_β : F}

/-- An inductive type from which to index the variables of the 3-variable polynomials the proof manages -/
@[derive decidable_eq]
inductive vars : Type
| α : vars
| β : vars

parameters {C_α C_β : F}


theorem case_1 : 
  (A_α • X vars.α + A_β • X vars.β) * (B_α • X vars.α + B_β • X vars.β : mv_polynomial vars F) = 0
  -> 1 = 0
:=
begin
  intros eqn,

  wlog h : B_α = 0 using [A_α A_β B_α B_β,
                          B_α B_β A_α A_β],


end

theorem case_2 : 
  (A_α • (X vars.α) + A_β • (X vars.β)) * (B_α • (X vars.α) + B_β • X vars.β : mv_polynomial vars F) = 0
  -> 1 = 0
:=
begin
  intros eqn,

  wlog h : B_α = 0 using [A_α A_β B_α B_β,
                          B_α B_β A_α A_β],


end

theorem case_3 : 
  (A_α • (X vars.α) + A_β • (X vars.β)) * (B_α • X vars.α + B_β • (X vars.β : mv_polynomial vars F)) = 0
  -> 1 = 0
:=
begin
  intros eqn,

  wlog h : B_α = 0 using [A_α A_β B_α B_β,
                          B_α B_β A_α A_β],


end


end
