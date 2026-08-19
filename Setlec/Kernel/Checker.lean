import Setlec.Kernel.Env
import Setlec.Kernel.TypeChecker

/-!
# The checker

`checkDecl` checks one declaration against the current environment and, on
success, returns the extended environment.  `checkDecls` folds it over a list
of declarations, starting from the empty environment.

Currently supported: `def` declarations in the sort fragment.  Axioms and
theorems are declined.  Verification: `Setlec.Verify.Checker` and
`Setlec.Model.Consistency`.
-/

namespace Setlec

/-- Checks common to all declarations: fresh name, well-formed universe
parameters, and a type that is a type and mentions only declared parameters. -/
def checkConstantVal (env : Env) (cv : ConstantVal) : CheckM Unit := do
  if (env.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless cv.type.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let stype ← inferType env 0 cv.type
  let _u ← ensureSort env stype

/-- Check a single declaration, extending the environment on success. -/
def checkDecl (env : Env) (d : Declaration) : CheckM Env := do
  match d with
  | .defnDecl cv value =>
    checkConstantVal env cv
    unless value.allLevelParamsDefined cv.levelParams do
      throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
    if value.hasFvar then
      throw (.invalid s!"unexpected free variable in value of {cv.name}")
    let vtype ← inferType env 0 value
    unless ← isDefEq env 0 vtype cv.type do
      throw (.invalid s!"type mismatch in definition {cv.name}")
    pure ⟨.defnInfo cv value :: env.consts⟩
  | .thmDecl cv _ => throw (.notImplemented s!"theorem declaration ({cv.name})")
  | .axiomDecl cv => throw (.notImplemented s!"axiom declaration ({cv.name})")

/-- Check a list of declarations in order, starting from the empty
environment. -/
def checkDecls (ds : List Declaration) : CheckM Env :=
  ds.foldlM checkDecl Env.empty

end Setlec
