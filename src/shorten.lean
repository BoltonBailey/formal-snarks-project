
import tactic
import tactic.abel

open tactic expr


meta def add_nonneg_proof_aux (n : expr) (h : option name) : tactic unit :=
do pf ← mk_app `nat.zero_le [n],
   nm ← get_unused_name,
   note (h.get_or_else nm) none pf,
   skip

namespace tactic
namespace interactive

setup_tactic_parser

meta def add_nonneg_proof (n : parse parser.pexpr) (h : parse ident?) : tactic unit :=
do n ← to_expr n,
   add_nonneg_proof_aux n h

meta def add_nonneg_proofs (n : parse pexpr_list) : tactic unit :=
do l ← mmap to_expr n,
   list.mmap' (λ e, add_nonneg_proof_aux e none) l

end interactive
end tactic


example (n : ℕ) : true :=
begin
  add_nonneg_proof (n + n) hx,
end
