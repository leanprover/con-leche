--#export t_pow_refused
/- End-to-end fixture (task #423 completeness): `Nat.pow 2 (2^32)` on
   literals at the ground site: the exponent does not fit in 32 bits, so
   official's `reduce_pow` refuses (`get_count_arg`) and the declaration
   is rejected (official too: this source without `debug.skipKernelTC`
   fails in the kernel).

   With the ground engine on, the engine finds the same refusal and
   hands the comparison back to the incumbent, which raises the error:
   rejected.  Today 1; target 1.

   `t_pow_refused` is added with `addDecl` under `debug.skipKernelTC`.

   Task #423 soundness (no hand-back): the engine raises the cached
   core's own refusal itself; still rejected (1). -/
import Lean
open Lean Elab Command

def tPowDecl : Declaration :=
  let lhs := mkApp2 (mkConst ``Nat.beq)
    (mkApp2 (mkConst ``Nat.pow) (mkRawNatLit 2) (mkRawNatLit 4294967296)) (mkRawNatLit 0)
  .thmDecl {
    name := Name.mkSimple "t_pow_refused"
    levelParams := []
    type := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) lhs (mkConst ``Bool.true)
    value := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true) }

elab "pow_refused_thm%" : command => liftCoreM (addDecl tPowDecl)

set_option debug.skipKernelTC true
pow_refused_thm%
