import ConLeche.Kernel.CheckerBase
import ConLeche.Kernel.CoreP

/-!
# The P lane's checker entry point (task #161, S9)

`fueledOps`' twin over the gated knot (`ConLeche/Kernel/CoreP.lean`).
The declaration checker itself is **not** duplicated: `checkDecl` and
`checkDecls` are written once against the `CheckerOps` record, so the
whole gated driver is this one instantiation — `checkDecls μ
(fueledOpsP μ F) ds` is the function a gated-lane capstone would be
stated about.

Nothing here is reachable from `Main.lean`'s import closure: the
executable is byte-identical to master (`--verified` is **not**
wired; see the S9 seal in `DESIGN.md` for why).
-/

namespace ConLeche

variable (mode : CheckMode)

/-- The pure instantiation over the **gated** knot, at an arbitrary
fuel — `fueledOps`' twin, clause for clause. -/
def fueledOpsP (F : Nat) : CheckerOps CheckM where
  annotate env d e := annotateCoreP mode env F d e
  inferType env d e := inferTypeCoreP mode env F d e
  isDefEq env d a b := isDefEqCoreP mode env F d a b
  ensureSort env d e := ensureSortCoreP mode env F d e
  whnf env d e := ConLeche.whnfP mode env F d e

/-- The pure gated instantiation at the standard fuel. -/
def pureOpsP : CheckerOps CheckM := fueledOpsP mode checkFuel

end ConLeche
