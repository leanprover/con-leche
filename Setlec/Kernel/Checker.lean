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
parameters, and a type that is a type and mentions only declared
parameters.  Returns the constant with its type **annotated**
(`annotate`); the guards run on the annotated type. -/
def checkConstantVal (env : Env) (cv : ConstantVal) : CheckM ConstantVal := do
  if (env.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  let type ← annotate env 0 cv.type
  unless type.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  if type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  unless type.constsResolve env do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let stype ← inferType env 0 type
  let _u ← ensureSort env stype
  pure { cv with type := type }

/-- Check a single declaration, extending the environment on success. -/
def checkDecl (env : Env) (d : Declaration) : CheckM Env := do
  match d with
  | .defnDecl cv value =>
    let cv ← checkConstantVal env cv
    let value ← annotate env 0 value
    unless value.allLevelParamsDefined cv.levelParams do
      throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
    if value.hasFvar then
      throw (.invalid s!"unexpected free variable in value of {cv.name}")
    unless value.constsResolve env do
      throw (.invalid s!"unknown constant in value of {cv.name}")
    let vtype ← inferType env 0 value
    unless ← isDefEq env 0 vtype cv.type do
      throw (.invalid s!"type mismatch in definition {cv.name}")
    pure ⟨.defnInfo cv value :: env.consts⟩
  | .thmDecl cv value =>
    let cv ← checkConstantVal env cv
    -- the type of a theorem must be a proposition
    let stype ← inferType env 0 cv.type
    let u ← ensureSort env stype
    unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
      throw (.invalid s!"type of theorem {cv.name} is not a proposition")
    let value ← annotate env 0 value
    unless value.allLevelParamsDefined cv.levelParams do
      throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
    if value.hasFvar then
      throw (.invalid s!"unexpected free variable in value of {cv.name}")
    unless value.constsResolve env do
      throw (.invalid s!"unknown constant in value of {cv.name}")
    let vtype ← inferType env 0 value
    unless ← isDefEq env 0 vtype cv.type do
      throw (.invalid s!"type mismatch in theorem {cv.name}")
    pure ⟨.thmInfo cv value :: env.consts⟩
  | .axiomDecl cv => throw (.notImplemented s!"axiom declaration ({cv.name})")

/-- Check a list of declarations in order, starting from the empty
environment. -/
def checkDecls (ds : List Declaration) : CheckM Env :=
  ds.foldlM checkDecl Env.empty

end Setlec
