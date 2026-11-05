module

public import ConLeche.Kernel.Checker

@[expose] public section

/-!
# The declaration checker, split at the install/check seam (task #253)

`checkDecl` (`ConLeche/Kernel/Checker.lean`) installs a declaration and
checks it in one run.  For a `defn`, `thm` or `opaque` the two halves
are separable: the **install half** runs the syntactic guards of the
type — and, for a definition or an opaque, of the value — and pushes
the constant as declared; the **check half** runs the inferences and
the conversion — the type's sort, the theorem's is-a-proposition test,
for a theorem the value's guards (a theorem is installed by its
statement; its value reaches the check half unchecked), the value's
type against the declared one — and reads only
the environment the constant was installed at and the data the
install half produced.  Every
other kind (axioms, inductive and basis blocks, and the pinned
`Nat`-operation and `reduce*` branches, whose certificates are checked
as they are installed) is not separable and its install half IS
`checkDecl`.

`installHeader`, `installValueGuards` and `checkValueGroup` are the two
halves as pure functions over `CheckerOps`, the specification the
fold's cached twins (`installGuardsC`, `checkPending`,
`ConLeche/Cached/Installed.lean`) simulate; `checkDecl_of_split_*`
(`ConLeche/Verify/CheckerSplit.lean`) say the two halves are `checkDecl`.
`ValueGroup` is the datum that crosses the seam.
-/

namespace ConLeche

/-- The three declaration kinds whose value check is separable from
their install. -/
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

/-- What the install half hands the check half: the kind, the header
and the value — guarded for a definition or an opaque (the install
half stored it), unguarded for a theorem (the install half never
looked at it: a theorem is stored by its statement, and the check half
runs the value's guards itself, `checkValueGroup`). -/
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

/-- `checkConstantVal` minus its inference: the syntactic guards. -/
def installHeader (env : Env) (cv : ConstantVal) :
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

/-- The value half of `check{Defn,Thm,Opaque}Val` minus its inference:
the guards. -/
def installValueGuards (env : Env) (cv : ConstantVal)
    (value : Expr) : m Unit := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (unresolvedConstsErrorL (strLitStored env) s!"value of {cv.name}" value)

/-- **The check half of a value declaration**, at the environment the
constant was installed at: the type's sort, the theorem's
is-a-proposition test, for a theorem the value's guards
(`installValueGuards`: a theorem's value reaches the check half raw), and
the value's type against the declared one — the inference and
conversion calls of `checkConstantVal` and `check{Defn,Thm,Opaque}Val`,
in their order, with their messages. -/
def checkValueGroup (ops : CheckerOps m) (env : Env) (g : ValueGroup) : m Unit := do
  let stype ← ops.inferType env 0 g.cv.type
  let u ← ops.ensureSort env 0 stype
  if g.kind = .thm then do
      unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
        throw (.invalid s!"type of theorem {g.cv.name} is not a proposition")
      installValueGuards env g.cv g.jv
  let vtype ← ops.inferType env 0 g.jv
  unless ← ops.isDefEq env 0 vtype g.cv.type do
    throw (.invalid s!"type mismatch in {g.kind.word} {g.cv.name}")

end ConLeche
