import Setlec.Kernel.Env
import Setlec.Kernel.StdAxioms
import Setlec.Kernel.TypeChecker
import Setlec.Kernel.TypeCheckerC
import Setlec.Kernel.CoreI
import Setlec.Kernel.NatOpPins
import Setlec.Kernel.Direct

/-!
# The declaration checker's common ground

The core entry-point record (`CheckerOps`) with its pure and memoized
instantiations, the common per-declaration constant check
(`checkConstantVal`), and the small strategy-independent helpers the
install paths share (`domsMatchAux`, `openPisAtFvars`,
`checkTypedList`, `checkDefEqList`, `piResultSort`).  The
modeled-inductive install builds on this in
`Setlec/Kernel/Modeled.lean`, everything else in
`Setlec/Kernel/Checker.lean`.
-/

namespace Setlec

/-- The core entry points the declaration checker runs on: the checker
is written once against this record, monad-polymorphically, and
instantiated with the pure knot (`fueledOps`/`pureOps`, the
verification's subject) and with the memoized knot (`cachedOps`, what
the binary executes). -/
structure CheckerOps (m : Type → Type) where
  annotate : Env → Nat → Expr → m Expr
  inferType : Env → Nat → Expr → m Expr
  isDefEq : Env → Nat → Expr → Expr → m Bool
  ensureSort : Env → Nat → Expr → m Level
  whnf : Env → Nat → Expr → m Expr

/-- The pure instantiation, at an arbitrary fuel. -/
def fueledOps (F : Nat) : CheckerOps CheckM where
  annotate env d e := annotateCore env F d e
  inferType env d e := inferTypeCore env F d e
  isDefEq env d a b := isDefEqCore env F d a b
  ensureSort env d e := ensureSortCore env F d e
  whnf env d e := Setlec.whnf env F d e

/-- The pure instantiation, at the standard fuel. -/
def pureOps : CheckerOps CheckM := fueledOps checkFuel

/-- The *interned* executable instantiation, at the standard fuel; each
entry call interns its argument into a fresh arena, runs the id-keyed
memoized interned knot (`Setlec/Kernel/CoreI.lean`), and reads the
result back — cache lifetime is exactly the old `KCache`'s (one entry
call, fixed environment).  Faithfulness: `Setlec/Verify/BridgeI.lean`,
consumed by the `cachedOps_*_bridge` lemmas in
`Setlec/Verify/Bridge.lean` — everything above them (the declaration
checker bridge and the consistency layer) is untouched. -/
def cachedOps : CheckerOps CheckM where
  annotate env d e := runEntryE env (fun r => r.annotate) d e
  inferType env d e := runEntryE env (fun r => r.infer) d e
  isDefEq env d a b := runEntryB env d a b
  ensureSort env d e := runEntryS env d e
  whnf env d e := runEntryE env (fun r => r.whnf) d e

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- Checks common to all declarations: fresh name, well-formed universe
parameters, and a type that is a type and mentions only declared
parameters.  Returns the constant with its type **annotated**
(`annotate`); the guards run on the annotated type. -/
def checkConstantVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal) : m ConstantVal := do
  if (env.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless cv.type.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let type ← ops.annotate env 0 cv.type
  unless type.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless type.constsResolve env do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let stype ← ops.inferType env 0 type
  let _u ← ops.ensureSort env 0 stype
  pure { cv with type := type }

/-- Compare binder domains at offsets `o₁`/`o₂` for `n` positions, the
right side viewed through `g` (identity, lifting, or renaming). -/
def domsMatchAux (g : Nat → Expr → Expr)
    (bs₁ bs₂ : List (Name × Expr × BinderMeta)) (o₁ o₂ n : Nat) : Bool :=
  (List.range n).all fun i =>
    match bs₁[o₁ + i]?, bs₂[o₂ + i]? with
    | some b₁, some b₂ => b₁.2.1 == g i b₂.2.1
    | _, _ => false

/-- Open the first `n` `∀`-binders at fresh free variables `0..n-1`
(each fvar's type is the binder domain, instantiated with the earlier
fvars).  Returns the fvars and the opened body. -/
def openPisAtFvars : Nat → Expr → Nat → Option (List Expr × Expr)
  | 0, e, _ => some ([], e)
  | n + 1, .forallE nm dom body _, i =>
    let fv : Expr := .fvar i nm dom
    match openPisAtFvars n (body.instantiate1 fv) (i + 1) with
    | some (fvs, e) => some (fv :: fvs, e)
    | none => none
  | _ + 1, _, _ => none

/-- Check each expression's inferred type against the corresponding
expected type (definitionally); throws on a length mismatch.  Used to
pin a nested rule's stored parameter instantiations to the
constructor's parameter domains. -/
def checkTypedList (ops : CheckerOps m) (env : Env) (depth : Nat) :
    List Expr → List Expr → m Unit
  | [], [] => pure ()
  | a :: as, t :: ts => do
    let ty ← ops.inferType env depth a
    unless ← ops.isDefEq env depth ty t do
      throw (.notImplemented "nested pin type mismatch")
    checkTypedList ops env depth as ts
  | _, _ => throw (.notImplemented "nested pin arity mismatch")

/-- Is the expression the pinned equality former at one level? -/
def isEqHead : Expr → Bool
  | .const c [_ℓ] => c == eqName
  | _ => false

/-- Pairwise definitional-equality check of two spines (throws on any
mismatch, including a length difference). -/
def checkDefEqList (ops : CheckerOps m) (env : Env) (depth : Nat) :
    List Expr → List Expr → m Unit
  | [], [] => pure ()
  | a :: as, b :: bs => do
    unless ← ops.isDefEq env depth a b do
      throw (.notImplemented "iota statement component mismatch")
    checkDefEqList ops env depth as bs
  | _, _ => throw (.notImplemented "iota statement component arity")

/-- Unwrap an optional value or fail with the given error (the
`Option`-shaped checks below stay bind-shaped for the verification
batteries). -/
def unwrapOr {α : Type} (o : Option α) (err : CheckError) : m α :=
  match o with
  | some a => pure a
  | none => throw err

/-- The stored constant under `n`, as a `ConstantVal`, if any.  The
iota-certificate checks below consume only the stored constant's
*type* (any stored constant witnesses its type's inhabitation in the
model — `EnvModel.mem_type` is kind-agnostic), so no theorem-kind
filter is imposed. -/
def Env.findCV? (env : Env) (n : Name) : Option ConstantVal :=
  (env.find? n).map (·.toConstantVal)

/-- The result sort of a syntactic pi telescope (the sort the type
former's type ends in), if it ends in a sort at all. -/
def piResultSort (e : Expr) : Option Level :=
  match e.piResult with
  | .sort u => some u
  | _ => none


end Setlec
