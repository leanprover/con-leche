--#export t_and_thm
/- End-to-end fixture (task #423 completeness): `And.rec` on a theorem
   (`hAnd : True ∧ True`) at the ground site.  There is no constructor;
   con-leche's incumbent has an `And` rescue (by ruling; `majorToCtor`'s
   `And` branch) that fabricates `And.intro a b h.1 h.2`, so the
   comparison holds.  Official has no such rescue (`And` is a
   proposition, so `to_cnstr_when_structure` does not fire) and rejects:
   this source without `debug.skipKernelTC` fails in the kernel.

   Today 0 (con-leche's rescue; official 1).  With the ground engine on,
   the engine fabricates the same `And.intro` (the parameters from the
   recursor, the proof fields neutral) and accepts; before, it aborted
   ("struct-eta major") to the incumbent.

   `t_and_thm` is added with `addDecl` under `debug.skipKernelTC`.

   Task #423 soundness (no hand-back, ruling 4): the fabrication has no
   proved rule without the incumbent's certificates, so with the engine on
   this is a decline (2), naming `And.rec`. -/
import Lean
open Lean Elab Command

theorem hAnd : True ∧ True := ⟨trivial, trivial⟩

noncomputable def kAndT : Bool := And.rec (motive := fun _ => Bool) (fun _ _ => true) hAnd

def tAndDecl : Declaration :=
  .thmDecl {
    name := Name.mkSimple "t_and_thm"
    levelParams := []
    type := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) (mkConst ``kAndT) (mkConst ``Bool.true)
    value := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true) }

elab "and_thm%" : command => liftCoreM (addDecl tAndDecl)

set_option debug.skipKernelTC true
and_thm%
