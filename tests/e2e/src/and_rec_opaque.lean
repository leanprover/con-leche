--#export And.opq_use
/- Task #251 probe: `And.rec` into `Type` on a THEOREM-proved major.  The
   elaborator's defeq never unfolds a theorem, so the use-site theorem is
   added through the task #208 probe kit (kernel check skipped). -/
import Lean
open Lean Elab Command

namespace Probe
def probeAdd (d : Declaration) : CommandElabM Unit := do
  liftCoreM <| withOptions (debug.skipKernelTC.set · true) <| addDecl d
def c (n : Name) (ls : List Level := []) : Expr := mkConst n ls
def ap (f : Expr) (as : List Expr) : Expr := mkAppN f as.toArray
def eq (l : Level) (a b d : Expr) : Expr := ap (c ``Eq [l]) [a, b, d]
def rfl' (l : Level) (a b : Expr) : Expr := ap (c ``Eq.refl [l]) [a, b]
def thm (n : Name) (lps : List Name) (ty val : Expr) : Declaration :=
  .thmDecl { name := n, levelParams := lps, type := ty, value := val }
end Probe
open Probe

theorem And.opq : And True True := ⟨trivial, trivial⟩
noncomputable def And.opq_elim : Nat :=
  And.rec (motive := fun _ => Nat) (fun _ _ => Nat.zero) And.opq

/-- `And.opq_use : Eq And.opq_elim Nat.zero` by `Eq.refl Nat.zero`. -/
elab "mk_use" : command => do
  probeAdd (thm `And.opq_use []
    (eq 1 (c ``Nat) (c `And.opq_elim) (c ``Nat.zero))
    (rfl' 1 (c ``Nat) (c ``Nat.zero)))
mk_use
