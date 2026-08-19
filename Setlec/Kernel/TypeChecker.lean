import Setlec.Kernel.Env
import Setlec.Kernel.Level

/-!
# Type inference, reduction and definitional equality

The heart of the checker.  All functions work on the supported fragment and
`throw` a `CheckError` otherwise:

* `.notImplemented`: a positively detected not-yet-supported feature; the
  driver turns this into the arena "declined" exit code.
* `.invalid`: the input is wrong; "rejected".
* `.internal`: an internal failure of unclear cause (e.g. fuel exhaustion);
  never a verdict about the input.

Current fragment: sort expressions only (`Sort u` with full level algebra).

Verification: `Setlec.Verify.TypeChecker`.
-/

namespace Setlec

inductive CheckError where
  | notImplemented (what : String)
  | invalid (msg : String)
  | internal (msg : String)
  deriving Repr

instance : ToString CheckError where
  toString
    | .notImplemented what => s!"not implemented yet: {what}"
    | .invalid msg => s!"invalid: {msg}"
    | .internal msg => s!"internal error: {msg}"

abbrev CheckM := Except CheckError

/-- Lift a fuel-style partial result; `none` is an internal error. -/
def liftFueled (what : String) : Option α → CheckM α
  | some a => pure a
  | none => throw (.internal s!"fuel exhausted: {what}")

/-- Reduce an expression to weak head normal form. -/
def whnf (_env : Env) : Expr → CheckM Expr
  | .sort u => pure (.sort u)
  | _ => throw (.notImplemented "whnf beyond sorts")

/-- Infer the type of a (closed, bvar-free at the top level) expression. -/
def inferType (_env : Env) : Expr → CheckM Expr
  | .sort u => pure (.sort (.succ u))
  | _ => throw (.notImplemented "inferType beyond sorts")

/-- Ensure `e` (a type of some expression) is a sort, returning its level. -/
def ensureSort (env : Env) (e : Expr) : CheckM Level := do
  match ← whnf env e with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

/-- Definitional equality. -/
def isDefEq (env : Env) (a b : Expr) : CheckM Bool := do
  match ← whnf env a, ← whnf env b with
  | .sort u, .sort v => liftFueled "level comparison" (Level.isEquiv u v)
  | _, _ => throw (.notImplemented "defEq beyond sorts")

end Setlec
