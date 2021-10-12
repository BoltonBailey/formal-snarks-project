
import data.mv_polynomial.basic

open tactic

namespace tactic

namespace interactive
open interactive interactive.types expr

meta def get_the_name : expr → option name
| (local_const unique pretty bi type) := some pretty
| _ := none

meta def context_name_getter : tactic (list name) := do
  ctx <- local_context,
  let names := ctx.filter_map get_the_name in do
  trace names,
  return names

meta def context_eq_name_getter : tactic (list name) := do
  ctx <- local_context,
  ctx' <- ctx.mfilter (λ e, do 
    tp <- infer_type e,
    return (option.is_some (is_eq tp) || option.is_some (is_not tp) || option.is_some (is_ne tp))
  ),
  let names := ctx'.filter_map get_the_name in do
  trace ctx',
  return names

end interactive

end tactic

section test

universes u

parameters {R vars : Type u}

example [integral_domain R] (a b c d e f : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) : c * e + f * d = 0 :=
begin
  context_eq_name_getter,
  sorry,
end


end test



