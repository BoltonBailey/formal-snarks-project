import algebra.field
import tactic.wlog

section

universe u

parameter {F : Type u}
parameter [field F]

open_locale classical

lemma test2 (A_α A_β A_γ A_δ A_x A_l A_m A_n B_α B_β B_γ B_δ B_x B_l B_m B_n : F) (h1 : B_α * A_α = 0) (h2: A_α * B_β + A_β * B_α = 1) (h3 : B_β * A_β = 0) : A_β = 0 :=
begin
  wlog h : B_α = 0 using [A_α A_β A_γ A_δ A_x A_l A_m A_n B_α B_β B_γ B_δ B_x B_l B_m B_n,
                          B_α B_β B_γ B_δ B_x B_l B_m B_n A_α A_β A_γ A_δ A_x A_l A_m A_n],

end

lemma ffo (a b c : F) : a * (b + c) = a * b + c * a 
:=
begin
  simp,
end

end

