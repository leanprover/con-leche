--#export t_stuck
/- End-to-end fixture (task #423 completeness): a closed `Bool` that does
   not reduce to a constructor (`Classical.choice ⟨true⟩`) compared with
   `Bool.true`.  `Bool` has no η, unit or proof-irrelevance rule, so a
   stuck neutral is not definitionally equal to `true`: rejected
   (official too: this source without `debug.skipKernelTC` fails in the
   kernel).

   With the ground engine on and no fallback (`groundMode = 10`), the
   engine's stuck value is the comparison's answer, `false`: rejected,
   without the incumbent.  Today 1; target 1.

   `t_stuck` is added with `addDecl` under `debug.skipKernelTC`. -/
import Lean
open Lean Elab Command

noncomputable def stuckB : Bool := Classical.choice ⟨true⟩

def tStuckDecl : Declaration :=
  .thmDecl {
    name := Name.mkSimple "t_stuck"
    levelParams := []
    type := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) (mkConst ``stuckB) (mkConst ``Bool.true)
    value := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true) }

elab "stuck_thm%" : command => liftCoreM (addDecl tStuckDecl)

set_option debug.skipKernelTC true
stuck_thm%
