--#export Iff.opq_use
/- Task #251 probe: `Iff.rec` into `Type` on a THEOREM-proved major.  The
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

theorem Iff.opq : Iff True True := ⟨fun h => h, fun h => h⟩
noncomputable def Iff.opq_elim : Nat :=
  Iff.rec (motive := fun _ => Nat) (fun _ _ => Nat.zero) Iff.opq

/-- `Iff.opq_use : Eq Iff.opq_elim Nat.zero` by `Eq.refl Nat.zero`. -/
elab "mk_use" : command => do
  probeAdd (thm `Iff.opq_use []
    (eq 1 (c ``Nat) (c `Iff.opq_elim) (c ``Nat.zero))
    (rfl' 1 (c ``Nat) (c ``Nat.zero)))
mk_use
