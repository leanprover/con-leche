import ConLeche.Kernel.CheckerBase
import ConLeche.Kernel.CoreGated

/-!
# The P lane's checker entry point (task #161, S9)

`fueledOps`' twin over the gated knot (`ConLeche/Kernel/CoreGated.lean`).
The declaration checker itself is **not** duplicated: `checkDecl` and
`checkDeclsPure` are written once against the `CheckerOps` record, so the
whole gated driver is this one instantiation — `checkDeclsPure μ
(fueledOpsGated μ F) ds` is the function a gated-lane capstone would be
stated about.

Nothing here is reachable from `Main.lean`'s import closure: the
executable is byte-identical to master (`--verified` is **not**
wired; see the S9 seal in `DESIGN.md` for why).
-/

namespace ConLeche

variable (mode : CheckMode)

/-- The pure instantiation over the **gated** knot, at an arbitrary
fuel — `fueledOps`' twin, clause for clause. -/
def fueledOpsGated (F : Nat) : CheckerOps CheckM where
  annotate env d e := annotateCoreGated mode env F d e
  inferType env d e := inferTypeCoreGated mode env F d e
  isDefEq env d a b := isDefEqCoreGated mode env F d a b
  ensureSort env d e := ensureSortCoreGated mode env F d e
  whnf env d e := ConLeche.whnfGated mode env F d e

/-- The pure gated instantiation at the standard fuel. -/
def pureOpsGated : CheckerOps CheckM := fueledOpsGated mode checkFuel

end ConLeche
