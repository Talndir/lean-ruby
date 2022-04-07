import tactic
import init.meta.interactive
import init.meta.converter.conv
import data.rel

class is_assoc {r : Type → Type → Type} (m : Π {a b c : Type}, r a b → r b c → r a c) :=
(assoc : ∀ {a b c d : Type}, ∀ {x : r a b} {y : r b c} {z : r c d}, m (m x y) z = m x (m y z))

instance rel_is_assoc : is_assoc @rel.comp :=
{ assoc := @rel.comp_assoc }

def assoc := rel_is_assoc.assoc

namespace conv
namespace interactive
open lean
open lean.parser
open _root_.interactive
open interactive.types
open tactic
open tactic_result
open conv

meta def convrw (e : expr ff) (symm : bool) : conv unit :=
  conv.interactive.rw
    {rules := [{pos := {line := 0, column := 0}, symm := symm, rule := to_pexpr e }], end_pos := none}

meta def l : conv unit := congr >> swap >> skip
meta def r : conv unit := congr >> skip
meta def al : conv unit := convrw ``(assoc) tt
meta def ar : conv unit := convrw ``(assoc) ff
meta def all : conv unit := al >> l
meta def alr : conv unit := al >> r
meta def arl : conv unit := ar >> l
meta def arr : conv unit := ar >> r


/-
private meta def is_relation : conv unit :=
(lhs >>= tactic.relation_lhs_rhs >> return ())
<|>
tactic.fail "current expression is not a relation"

meta def get_assoc (fn : expr) : conv expr :=
do  t ← mk_mapp ``is_assoc [none, fn],
    inst ← prod.snd <$> solve_aux t assumption <|>
      (mk_instance t >>= assertv `_inst t) <|>
      fail format!"{fn} is not associative",
    mk_mapp ``is_assoc.assoc [none, fn, inst]


meta def test_rw : tactic unit :=
do  r ← to_expr ``(refl),
    `[rw ← %%r]

meta def assoc_rw_left : conv unit :=
do  e ← target,
    trace (to_string e),
    (t, vs) ← infer_type e >>= fill_args,
    (lhs, rhs) ← match_eq e,
    let fn := lhs.app_fn.app_fn.app_fn.app_fn.app_fn,
    trace (to_string fn),
    assoc ← get_assoc fn,
    trace (to_string assoc),
    r ← to_expr ``(refl),
    `[rw %%r]
-/

end interactive
end conv
