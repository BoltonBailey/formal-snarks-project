
import tactic.basic

-- TODO remove these practice tactics
meta def my_first_tactic : tactic unit := 
do
  tactic.trace "Hello,",
  tactic.trace "World."


meta def my_fail_tactic : tactic unit := 
tactic.fail "This tactic failed, we apologize for the inconvenience."

run_cmd add_interactive [`my_first_tactic, `my_fail_tactic]


/-- A Tactic that goes through the context and repeatedly tries to simplify statements using other statements-/
meta def mutual_simplification : tactic unit :=
do
  tactic.fail "TODO"


/-- A Tactic that goes through the context and removes statements of type true -/
meta def clear_true : tactic unit :=
do
  tactic.fail "TODO"
