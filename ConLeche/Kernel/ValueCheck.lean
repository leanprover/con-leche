module

public import ConLeche.Kernel.Checker

@[expose] public section

/-!
# The check of a value declaration

A definition, theorem or opaque is checked in two steps.  Its **guards** are syntactic and read only
the names below it: `headerGuards` for the type, `valueGuards` for the value.  Its **value check**,
`checkValueGroup`, runs the inferences and the conversion: the type's sort, a theorem's
is-a-proposition test, the value's type against the declared one.  The guards of a definition or an
opaque run at the install; a theorem's value is guarded by its value check.

These are the pure functions over `CheckerOps` that the fold's cached twins (`headerGuardsC`,
`checkPending`, `ConLeche/Cached/Installed.lean`) simulate; `checkDecl_of_value_*`
(`ConLeche/Verify/ValueCheck.lean`) assemble `checkDecl`'s run from them.  `valueGroup?` says which
declarations are checked this way: the pinned `Nat` operations and `reduce*` opaques carry
certificates and are not.
-/

namespace ConLeche

/-- The three declaration kinds checked by `checkValueGroup`. -/
inductive ValueKind where
  | defn
  | thm
  | opaque
  deriving DecidableEq, Repr

/-- The kind's word in `checkDecl`'s type-mismatch message. -/
def ValueKind.word : ValueKind → String
  | .defn => "definition"
  | .thm => "theorem"
  | .opaque => "opaque"

/-- A value declaration's check datum: the kind, the header and the value (guarded already for a
definition or an opaque; a theorem is installed by its statement, and `checkValueGroup` guards its
value). -/
structure ValueGroup where
  kind : ValueKind
  cv : ConstantVal
  jv : Expr

/-- A declaration's value group: a definition, a theorem or an opaque, other than a pinned
`Nat` operation or a `reduce*` opaque. -/
def valueGroup? : Declaration → Option ValueGroup
  | .defnDecl cv value _ =>
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then none
    else some ⟨.defn, cv, value⟩
  | .thmDecl cv value => some ⟨.thm, cv, value⟩
  | .opaqueDecl cv value =>
    if reduceOpNames.contains cv.name then none else some ⟨.opaque, cv, value⟩
  | _ => none

variable (mode : CheckMode)
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- The header's syntactic guards: `checkConstantVal` without its inference. -/
def headerGuards (env : Env) (cv : ConstantVal) :
    m Unit := do
  if (env.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if natOpName cv.name then
    throw (.invalid s!"a certified Nat operation's name, not a definition: {cv.name}")
  unless litShapeOk (.axiomInfo cv) do
    throw (.notImplemented s!"a declaration at a literal's name with another shape ({cv.name})")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless cv.type.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  unless cv.type.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless cv.type.constsResolve env do
    throw (unresolvedConstsErrorL (strLitStored env) s!"type of {cv.name}" cv.type)

/-- The value's syntactic guards: those of `check{Defn,Thm,Opaque}Val`. -/
def valueGuards (env : Env) (cv : ConstantVal)
    (value : Expr) : m Unit := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (unresolvedConstsErrorL (strLitStored env) s!"value of {cv.name}" value)

/-- **The value check**, at the environment the constant was installed at: the type's sort, the
theorem's is-a-proposition test and its value's guards, and the value's type against the declared
one: the inference and conversion calls of `checkConstantVal` and `check{Defn,Thm,Opaque}Val`, in
their order, with their messages. -/
def checkValueGroup (ops : CheckerOps m) (env : Env) (g : ValueGroup) : m Unit := do
  let stype ← ops.inferType env 0 g.cv.type
  let u ← ops.ensureSort env 0 stype
  if g.kind = .thm then do
      unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
        throw (.invalid s!"type of theorem {g.cv.name} is not a proposition")
      valueGuards env g.cv g.jv
  let vtype ← ops.inferType env 0 g.jv
  unless ← ops.isDefEq env 0 vtype g.cv.type do
    throw (.invalid s!"type mismatch in {g.kind.word} {g.cv.name}")

end ConLeche
