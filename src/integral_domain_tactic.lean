

-- TODO a tactic for resolving statements in integral domain rings

-- This tactic should work as follows:
-- 1. Find all equality statements in the Euclidean ring in the statements (and goal)
-- 2. Break down either side of these equalities into a tree of add and mul operations (do not break down sums or prods)
-- 3. Identify all atoms of R from these, and put these equations in ring normal form
-- 4. Mutually simplify the equations by gaussian elimination. That is - check if subtracting off any statement equation from any other, or any statement from the goal,  "simplifies it" in terms of leaving less added terms. If so, perform this subtraction and resimplify. Repeat until we get through all pairs without a simplification.
-- 5. Check if any atom can be factored out of an equation, with zero on the other side. If so, simplify this to the disjunction of this atom being zero or the other factor being zero. Split on this disjunction, and repeat from step 4 on both sides of the split.

-- This is related to the Nullstellensatz. Specifically [Buchberger's Algorithm](https://en.wikipedia.org/wiki/Buchberger%27s_algorithm) is one way of doing what I do here. Not sure yet what the relation is - probably Buchberger is more general, but more time complex? See also the coq tactic [nsatz](https://coq.inria.fr/refman/addendum/nsatz.html).

-- What is the ["effective nullstellensatz"](https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz#Effective_Nullstellensatz) of these problems



import data.mv_polynomial.basic
import .general_lemmas.mv_X_mul
import .general_lemmas.single_antidiagonal
import tactic.abel
import .attributes

open tactic



namespace tactic

namespace interactive
open interactive interactive.types expr

setup_tactic_parser

meta def my_simp_only (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : tactic unit :=
propagate_tags $
do lms ← simp_core cfg.to_simp_config cfg.discharger tt hs attr_names locat,
  if cfg.trace_lemmas then trace (↑"Try this: simp only " ++ to_fmt lms.to_list) else skip

meta def get_the_name : expr → option name
| (local_const unique pretty bi type) := some pretty
| _ := none

/-- Returns a list of names of propositions in the local context which are either equalities or 
have some logical definition -/
meta def context_prop_name_getter : tactic (list name) := do
  ctx <- local_context,
  ctx' <- ctx.mfilter (λ e, do 
    tp <- infer_type e,
    return (option.is_some (is_eq tp) 
            || option.is_some (is_not tp) 
            || option.is_some (is_ne tp)
            || option.is_some (is_or tp))
  ),
  let names := ctx'.filter_map get_the_name in do
  -- trace ctx',
  return names

/-- For a name in the local context, simplify at it with found_zero, and if that is successful, simplifies again with integral_domain_simp. -/
meta def simplify_at_name (nm : name) : tactic unit :=
  if nm = `found_zero then do skip else do
  found_zero_expr <- get_local `found_zero,
  used_set <- simp_core {fail_if_unchanged := ff} (failed) tt [simp_arg_type.expr (pexpr.of_expr found_zero_expr)] [] (loc.ns [some nm]),
  match name_set.empty used_set with
  | tt := skip
  | ff := do attr_used_set <- simp_core {fail_if_unchanged := ff} (failed) tt [] [`integral_domain_simp] (loc.ns [some nm]), skip
  end

/-- For a name nmat in the local context, simplify at it with nmwith, 
and if that is successful, simplify again at nmat with integral_domain_simp. 
Never fails, but returns tt if the simplification changed something -/
meta def simplify_at_with (nmat nmwith : name) : tactic bool :=
  if nmat = nmwith then do return ff else do
  nmwith_expr <- get_local nmwith,
  used_set <- simp_core {fail_if_unchanged := ff} (failed) tt [simp_arg_type.expr (pexpr.of_expr nmwith_expr)] [] (loc.ns [some nmat]),
  match name_set.empty used_set with
  | tt := return ff
  | ff := do 
    attr_used_set <- simp_core {fail_if_unchanged := ff} (failed) tt [] [`integral_domain_simp] (loc.ns [some nmat]), 
    return attr_used_set.empty
  end
  
/-- For each name in the local context, simplifies with found zero, and if that is successful, simplifies again with integral_domain_simp. -/
meta def simplify_everywhere : tactic unit := do
  names <- context_prop_name_getter,
  names.mmap' simplify_at_name,
  -- Simp the target
  try `[simp only [found_zero] with integral_domain_simp]


meta def mutually_simplify_aux : list name -> list name -> tactic unit 
| [] _ := skip
| (nm_with::to_simplify_withs) other := do
  -- simplify the ones we will simplify with in the future
  to_simplify_withs.mmap' (λ a, simplify_at_with a nm_with), 
  -- Simplify the others, and if they change, remove them from other and add to future
  other_success_labels <- other.mmap (λ a, simplify_at_with a nm_with),
  let others_changed := list.reduce_option (list.zip_with 
                            (λ nm b, match b with 
                              | tt := (some nm : option name) 
                              | ff := none end) 
                            other other_success_labels), 
  let others_unchanged := list.reduce_option (list.zip_with 
                            (λ nm b, match b with 
                              | tt := none 
                              | ff := (some nm : option name)  end) 
                            other other_success_labels),
  let new_to_simplify_with := list.append to_simplify_withs others_changed,           
  mutually_simplify_aux new_to_simplify_with others_unchanged



meta def mutually_simplify : tactic unit := do
  names <- context_prop_name_getter,
  mutually_simplify_aux names []

meta def mutually_simplify_one (nm : name) : tactic unit := do
  names <- context_prop_name_getter,
  let names' := list.erase names nm,
  mutually_simplify_aux (nm::[]) names

end interactive


-- Adapted from Mario's example
meta def integral_domain_tactic : tactic unit := do
  -- trace "\nCall to integral_domain_tactic", 
  -- trace_state, -- printf debugging
  `[my_simp_only [] with integral_domain_simp
    at * {fail_if_unchanged := ff}],
  try `[cases_type* true false],
  _::_ ← get_goals | skip, 
  cases_success <- try_core `[cases ‹_ ∨ _› with nm nm],
  match cases_success with 
  | some _ := all_goals' `[simp only [nm] at *, done <|> id { integral_domain_tactic }]
  -- TODO, I need to change this so that, 
  -- if rw found_zero fails the program stops and doesn't clear found_zero.
  -- for now I remove the clear nm part
  | none := skip
  end

-- Broken version that tries to only simplify things when we know they have changed.
meta def integral_domain_tactic_v2 : tactic unit := do
  trace "\nCall to integral_domain_tactic_v2", 
  -- trace_state, -- printf debugging
  try `[cases_type* true false],
  _::_ ← get_goals | skip, 
  try `[clear found_zero],
  cases_success <- try_core `[cases ‹_ ∨ _› with found_zero found_zero],
  match cases_success with -- simplify everywhere might produce a simplification that can further help.
  | some _ := all_goals' (do tactic.interactive.simplify_everywhere, done <|> integral_domain_tactic_v2)
  | none := skip
  end

-- Adapted from Mario's example
-- I screwed this one up and made the recursive call to integral_domain_tactic
-- instead of integral_domain_tactic_v3. Switching to _4 and leaving this for posterity.
-- _4 below seems to make this take 1 min instead of 30 min, which the amount of time
-- this has been taking the past few weeks.
-- :(
meta def integral_domain_tactic_v3 : tactic unit := do
  trace "\nCall to integral_domain_tactic_v3", 
  -- trace_state, -- printf debugging
  `[my_simp_only [*] with integral_domain_simp
    at * {fail_if_unchanged := ff}],
  try `[cases_type* true false],
  _::_ ← get_goals | skip, 
  try `[clear found_zero],
  cases_success <- try_core `[cases ‹_ ∨ _› with found_zero found_zero],
  match cases_success with 
  | some _ := all_goals' `[done <|> id { integral_domain_tactic }]
  -- TODO, I need to change this so that, 
  -- if rw found_zero fails the program stops and doesn't clear found_zero.
  -- for now I remove the clear found_zero part
  | none := skip
  end
  


meta def integral_domain_tactic_v4 : tactic unit := do
  trace "\nCall to integral_domain_tactic_v4", 
  -- trace_state, -- printf debugging
  `[my_simp_only [*] with integral_domain_simp
    at * {fail_if_unchanged := ff}],
  try `[cases_type* true false],
  _::_ ← get_goals | skip, 
  try `[clear found_zero],
  cases_success <- try_core `[cases ‹_ ∨ _› with found_zero found_zero],
  match cases_success with 
  | some _ := all_goals' `[done <|> id { integral_domain_tactic_v4 }]
  -- TODO, I need to change this so that, 
  -- if rw found_zero fails the program stops and doesn't clear found_zero.
  -- for now I remove the clear found_zero part
  | none := skip
  end


meta def integral_domain_tactic_v5 : tactic unit := do
  trace "\nCall to integral_domain_tactic_v5", 
  `[my_simp_only [*] with integral_domain_simp
    at * {fail_if_unchanged := ff}],
  try `[cases_type* true false],
  _::_ ← get_goals | skip, 
  try `[clear found_zero],
  cases_success <- try_core `[cases ‹_ ∨ _› with found_zero found_zero],
  match cases_success with 
  | some _ := all_goals' `[done <|> id { integral_domain_tactic_v4 }]
  -- TODO, I need to change this so that, 
  -- if rw found_zero fails the program stops and doesn't clear found_zero.
  -- for now I remove the clear found_zero part
  | none := skip
  end
  -- TODO, I need to make it so that I'm not running simp * at * every round.
  -- step 1, get a list of


open expr





end tactic


-- run_cmd add_interactive [`integral_domain_tactic]

section test

universes u


/-- The finite field parameter of our SNARK -/
parameters {R vars : Type u}
-- parameter [ring R]


lemma zero_eq_zero [integral_domain R] : (0 : R) = 0 ↔ true := 
begin
  simp only [eq_self_iff_true],
end

-- example [integral_domain R] (a b c d e f g h i : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) (h4 : h * i = 0): c * e + f * d = h :=
-- begin
--   -- integral_domain_tactic,
--   simp only [] with integral_domain_simp
--     at * {fail_if_unchanged := ff},
--   -- integral_domain_tactic',
--   sorry,
-- end

-- example [integral_domain R] (a b c d e f g h i : R) (h11 : ¬a = 0) (h12 : ¬b = 0) (h4 : h = 0 ∨ i = 0): f * 0 = h :=
-- begin
--   simp only [] with integral_domain_simp
--     at * {fail_if_unchanged := ff},
--   cases ‹_ ∨ _› with found_zero found_zero,
--   -- tactic.context_name_getter,
--   rw found_zero at *,
--   rw found_zero at *,
--   sorry,
-- end

-- example [integral_domain R] (a b c d e f : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) : c * e + f * d = 0 :=
-- begin
--   simp only [] with integral_domain_simp
--     at * {fail_if_unchanged := ff},
--   tactic.integral_domain_tactic_v3,
--   -- tactic.integral_domain_tactic,
-- end

-- example [integral_domain R] (a b c d e f g : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) : c * e + f * d = g :=
-- begin
--   tactic.integral_domain_tactic,
--   sorry, 
-- end

-- example [integral_domain R] (a b c d e f : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) : c * e + f * d = 0 :=
-- begin
--   simp only [] with integral_domain_simp
--     at * {fail_if_unchanged := ff},
--   cases ‹_ ∨ _› with found_zero found_zero,
--   context_prop_name_getter,
--   simplify_everywhere,
--   simplify_at_name `h11,
--   simplify_at_name `h12,
--   simplify_at_name `found_zero,
--   sorry,
--   sorry,

-- end


end test

-- end


