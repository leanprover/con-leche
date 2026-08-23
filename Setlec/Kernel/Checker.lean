import Setlec.Kernel.Env
import Setlec.Kernel.StdAxioms
import Setlec.Kernel.TypeChecker
import Setlec.Kernel.TypeCheckerC
import Setlec.Kernel.CoreI
import Setlec.Kernel.NatOpPins
import Setlec.Kernel.Direct

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
  if modelFamilyTaken env cv.name then
    throw (.invalid s!"model companion {cv.name} declared after its \
      constant (the `_model` family of an installed constant is closed)")
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

/-- Check a *canonical* recursor rule's `iota_j` theorem,
*semantically*: the stored theorem's telescope is opened at free
variables, its body must be an `Eq`, the equation's left side is
structurally the renamed recursor applied to the opened variables and
a canonical major (its index arguments definitionally the
constructor's canonical index tuple), and the right side is
definitionally the rule's applied right-hand side.  The opened
telescope's domains are definitionally the recursor's prefix and the
constructor's field domains (renamed), and the rule's own λ-domains
definitionally the public ones — the memberships the fold fact
quantifies over transfer along these equalities.  Definitional
comparison makes the checks insensitive to hygienic binder names and
reducible wrappers (`optParam` etc.) in the stored types. -/
def checkIotaThm (ops : CheckerOps m) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) : m Unit := do
    let cvt ← unwrapOr
        (env'.findCV? ((cvName.str "_model").str s!"iota_{j}"))
        (.notImplemented s!"missing iota theorem for {cvName}")
    unless cvt.levelParams = lps do
      throw (.notImplemented s!"iota theorem level mismatch for {cvName}")
    -- open the theorem's telescope: params, motives, minors, fields
    let depth := rP + cnF
    let (fvs, tbody) ← unwrapOr (openPisAtFvars depth cvt.type 0)
      (.notImplemented s!"iota statement shape mismatch for {cvName}")
    -- the body is an equation (at one level, like the pinned `Eq`)
    let targs := tbody.getAppArgs
    unless isEqHead tbody.getAppFn do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    unless targs.length = 3 do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    let lhsS := targs.getD 1 (.bvar 0)
    let rhsS := targs.getD 2 (.bvar 0)
    -- the equation's left side: structurally the renamed recursor
    -- applied to the opened prefix variables, `mI - rP` index arguments
    -- (checked below against the constructor's canonical tuple),
    -- and the constructor at its own level parameters applied to
    -- the leading parameter variables and the field variables
    let xFvs := fvs.drop rP
    let largs := lhsS.getAppArgs
    unless lhsS.getAppFn == Expr.const (f cvName) (lps.map .param) do
      throw (.notImplemented s!"iota statement head mismatch for {cvName}")
    unless largs.length = mI + 1 do
      throw (.notImplemented s!"iota statement arity mismatch for {cvName}")
    unless largs.take rP == fvs.take rP do
      throw (.notImplemented s!"iota statement prefix mismatch for {cvName}")
    let major := largs.getLastD (.bvar 0)
    unless major == Expr.mkAppN
        (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ xFvs) do
      throw (.notImplemented s!"iota statement major mismatch for {cvName}")
    -- the constructor's telescope (renamed), instantiated at the
    -- major's arguments: field domains and the canonical index tuple
    unless (cvj.type.stripPis (cnP + cnF)).isSome do
      throw (.notImplemented s!"iota constructor telescope for {cvName}")
    let (cdoms, cres) ← unwrapOr
        (Expr.instPisAt (fvs.take cnP ++ xFvs) (cvj.type.renameConsts f))
        (.notImplemented s!"iota constructor telescope for {cvName}")
    unless cres.getAppArgs.length = cnP + (mI - rP) do
      throw (.notImplemented s!"iota constructor indices for {cvName}")
    checkDefEqList ops envSelf depth ((largs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP)
    checkDefEqList ops envSelf depth (xFvs.map Expr.fvarTypeD)
      (cdoms.drop cnP)
    -- the statement's prefix domains are the recursor's (renamed)
    let (rdoms, _) ← unwrapOr
        (Expr.instPisAt (fvs.take rP) (tyA.renameConsts f))
        (.notImplemented s!"iota recursor telescope for {cvName}")
    checkDefEqList ops envSelf depth
      ((fvs.take rP).map Expr.fvarTypeD) rdoms
    -- the rule's λ-domains are the public recursor prefix and
    -- constructor field domains (the fold fact's value spines fit
    -- the public telescopes; these equalities let them fit the λs)
    let (fvsP, _) ← unwrapOr (openPisAtFvars rP tyA 0)
      (.notImplemented s!"iota recursor telescope for {cvName}")
    let (cdomsP, crestP) ← unwrapOr
      (Expr.instPisAt (fvsP.take cnP) cvj.type)
      (.notImplemented s!"iota constructor telescope for {cvName}")
    -- the constructor's parameter domains are the recursor's (the
    -- λ-tower's parameter values fit both telescopes)
    checkDefEqList ops envSelf depth
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP
    let (xFvsP, _) ← unwrapOr (openPisAtFvars cnF crestP rP)
      (.notImplemented s!"iota constructor telescope for {cvName}")
    let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA)
      (.notImplemented s!"rule shape mismatch for {cvName}")
    checkDefEqList ops envSelf depth ((fvsP ++ xFvsP).map Expr.fvarTypeD)
      ldoms
    -- the right side: definitionally the rule's applied rhs
    let rhsApplied := Expr.mkAppN (rhsA.renameConsts f) fvs
    unless ← ops.isDefEq envSelf depth rhsS rhsApplied do
      throw (.notImplemented s!"iota statement mismatch for {cvName}")

/-- The nested-shape data of a non-canonical rule: the constructor's
level and parameter instantiations, read off the recursor type's
major-premise domain (`∀ …prefix…, ∀ (t : D.{lvls} p₁ … p_cnP), …`).
`none` — the rule stays inert, and a matched major declines at fire
time — when the model stores no `iota_j` constant, the recursor has index
premises (`mI ≠ rP`; not covered by the certified shape), the major
domain is not a constant-headed application of exactly `cnP`
arguments, or an instantiation fails the syntactic well-formedness
guards (closed, bounded by the telescope, constants resolving, levels
declared — the facts `EnvWF` records for the stored rule). -/
def nestedRuleShape (env' envSelf : Env) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP cnP j : Nat) :
    Option (List Level × List Expr) :=
  if (env'.findCV? ((cvName.str "_model").str s!"iota_{j}")).isSome ∧
      mI = rP then
    match tyA.stripPis mI with
    | some (_, .forallE _ dom _ _) =>
      match dom.getAppFn with
      | .const _D lvls =>
        let pins := dom.getAppArgs
        if pins.length = cnP ∧
            pins.all (fun p => !p.hasFvar && p.looseBVarsBounded mI &&
              p.constsResolve envSelf && p.allLevelParamsDefined lps) ∧
            lvls.all (Level.allParamsDefined lps) then
          some (lvls, pins)
        else none
      | _ => none
    | _ => none
  else none

/-- Check a *nested-auxiliary* recursor rule's `iota_j` theorem — the
generalization of `checkIotaThm` to rules whose constructor parameters
and levels are fixed instantiations (`nestedRuleShape`): the theorem's
canonical major applies the constructor at the stored level
instantiations to the stored parameter instantiations (opened at the
statement's prefix variables) and the field variables, and the
constructor's telescope walks are taken at those instantiations.  When
the rule has no certifiable shape the rule is stored inert (`.inert`;
a matched major positively declines at fire time); a shape whose
theorem then fails the pin is a positive decline here. -/
def checkIotaThmN (ops : CheckerOps m) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) : m RecRuleFire := do
    match nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j with
    | none => pure .inert
    | some (lvls, pins) => do
    let cvt ← unwrapOr
        (env'.findCV? ((cvName.str "_model").str s!"iota_{j}"))
        (.notImplemented s!"missing iota theorem for {cvName}")
    unless cvt.levelParams = lps do
      throw (.notImplemented s!"iota theorem level mismatch for {cvName}")
    -- open the theorem's telescope: params, motives, minors, fields
    let depth := rP + cnF
    let (fvs, tbody) ← unwrapOr (openPisAtFvars depth cvt.type 0)
      (.notImplemented s!"iota statement shape mismatch for {cvName}")
    let targs := tbody.getAppArgs
    unless isEqHead tbody.getAppFn do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    unless targs.length = 3 do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    let lhsS := targs.getD 1 (.bvar 0)
    let rhsS := targs.getD 2 (.bvar 0)
    -- the equation's left side: structurally the renamed recursor
    -- applied to the opened prefix variables and the constructor at
    -- the stored level instantiations, applied to the stored parameter
    -- instantiations (renamed, opened at the prefix variables) and the
    -- field variables
    let xFvs := fvs.drop rP
    let pinsF := pins.map fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)
    let largs := lhsS.getAppArgs
    unless lhsS.getAppFn == Expr.const (f cvName) (lps.map .param) do
      throw (.notImplemented s!"iota statement head mismatch for {cvName}")
    unless largs.length = mI + 1 do
      throw (.notImplemented s!"iota statement arity mismatch for {cvName}")
    unless largs.take rP == fvs.take rP do
      throw (.notImplemented s!"iota statement prefix mismatch for {cvName}")
    let major := largs.getLastD (.bvar 0)
    unless major == Expr.mkAppN (.const (f r.ctor) lvls)
        (pinsF ++ xFvs) do
      throw (.notImplemented s!"iota statement major mismatch for {cvName}")
    -- the constructor's telescope at the stored level instantiations
    -- (renamed), instantiated at the major's arguments: field domains
    -- and (`mI = rP`) an index-free residual
    unless (cvj.type.stripPis (cnP + cnF)).isSome do
      throw (.notImplemented s!"iota constructor telescope for {cvName}")
    let (cdoms, cres) ← unwrapOr
        (Expr.instPisAt (pinsF ++ xFvs)
          ((cvj.type.instantiateLevelParams cvj.levelParams
            lvls).renameConsts f))
        (.notImplemented s!"iota constructor telescope for {cvName}")
    unless cres.getAppArgs.length = cnP + (mI - rP) do
      throw (.notImplemented s!"iota constructor indices for {cvName}")
    checkDefEqList ops envSelf depth ((largs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP)
    checkDefEqList ops envSelf depth (xFvs.map Expr.fvarTypeD)
      (cdoms.drop cnP)
    -- the statement's prefix domains are the recursor's (renamed)
    let (rdoms, _) ← unwrapOr
        (Expr.instPisAt (fvs.take rP) (tyA.renameConsts f))
        (.notImplemented s!"iota recursor telescope for {cvName}")
    checkDefEqList ops envSelf depth
      ((fvs.take rP).map Expr.fvarTypeD) rdoms
    -- the rule's λ-domains are the public recursor prefix and the
    -- constructor's field domains at the public instantiations
    let (fvsP, _) ← unwrapOr (openPisAtFvars rP tyA 0)
      (.notImplemented s!"iota recursor telescope for {cvName}")
    let pinsP := pins.map fun p =>
      Expr.instSpine (fvsP.take rP) (rP - 1) p
    let (cdomsP, crestP) ← unwrapOr (Expr.instPisAt pinsP
        (cvj.type.instantiateLevelParams cvj.levelParams lvls))
      (.notImplemented s!"iota constructor telescope for {cvName}")
    -- the stored parameter instantiations inhabit the constructor's
    -- parameter domains (the λ-tower's parameter values fit them)
    checkTypedList ops envSelf depth pinsP cdomsP
    let (xFvsP, crest2P) ← unwrapOr (openPisAtFvars cnF crestP rP)
      (.notImplemented s!"iota constructor telescope for {cvName}")
    -- the auxiliary constructor's residual applies the family to
    -- exactly its parameters: the canonical body carries no index
    -- tuple
    unless crest2P.getAppArgs.length == cnP do
      throw (.notImplemented s!"iota constructor arity for {cvName}")
    let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA)
      (.notImplemented s!"rule shape mismatch for {cvName}")
    checkDefEqList ops envSelf depth ((fvsP ++ xFvsP).map Expr.fvarTypeD)
      ldoms
    -- the right side: definitionally the rule's applied rhs
    let rhsApplied := Expr.mkAppN (rhsA.renameConsts f) fvs
    unless ← ops.isDefEq envSelf depth rhsS rhsApplied do
      throw (.notImplemented s!"iota statement mismatch for {cvName}")
    pure (.nested lvls pins)

/-- Check one modeled recursor rule: generic well-formedness of the
right-hand side, then the model's `iota_j` theorem — for canonical
rules the plain statement pin (`checkIotaThm`), for nested-auxiliary
rules the generalized pin over the stored instantiations
(`checkIotaThmN`; rules without a certifiable shape are stored inert:
`iotaRec` never fires on them and a matched major declines). -/
def checkIotaRule (ops : CheckerOps m) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) : m RecRule := do
    let some (.ctorInfo cvj cnP cnF) := env'.find? r.ctor
      | throw (.invalid s!"iota rule constructor {r.ctor} not stored")
    unless r.nfields = cnF do
      throw (.invalid "rule field count mismatch")
    unless r.rhs.looseBVarsBounded 0 do
      throw (.invalid s!"loose bound variable in rule of {cvName}")
    if r.rhs.hasFvar then
      throw (.invalid s!"free variable in rule of {cvName}")
    let rhsA ← ops.annotate envSelf 0 r.rhs
    unless rhsA.allLevelParamsDefined lps do
      throw (.invalid s!"undeclared universe parameter in rule of {cvName}")
    unless rhsA.constsResolve envSelf do
      throw (.invalid s!"unknown constant in rule of {cvName}")
    -- the rule's rhs must be a λ-telescope over the recursor prefix
    -- and the constructor fields (so it can be applied positionally)
    unless (rhsA.stripLams (rP + cnF)).isSome do
      throw (.notImplemented s!"rule shape mismatch for {cvName}")
    -- infer the rule's type: soundness interprets the (λ-tower)
    -- right-hand side through this inference
    let _rhsTy ← ops.inferType envSelf 0 rhsA
    -- the firing mode is computed once, here, and stored on the rule;
    -- `iotaRec` reads the flag instead of re-walking the recursor type
    -- on every fire
    let fire ← if Expr.recRulePlain tyA mI rP cnP then do
        checkIotaThm ops env' envSelf f cvName lps tyA mI rP j r
          cvj cnP cnF rhsA
        pure RecRuleFire.plain
      else
        checkIotaThmN ops env' envSelf f cvName lps tyA mI rP j r
          cvj cnP cnF rhsA
    pure { r with rhs := rhsA, ctorParams := cnP, fire := fire }

/-- The per-rule check, folded over a modeled recursor's rules. -/
def checkIotaRules (ops : CheckerOps m) (env' envSelf : Env) (f : Name → Name)
    (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP : Nat) : Nat → List RecRule → m (List RecRule)
  | _, [] => pure []
  | j, r :: rest => do
    let r' ← checkIotaRule ops env' envSelf f cvName lps tyA mI rP j r
    let rest' ← checkIotaRules ops env' envSelf f cvName lps tyA mI rP
      (j + 1) rest
    pure (r' :: rest')

/-- Check a block member's constant against its `_model` counterpart:
`checkConstantVal`, the member may not itself be model-shaped, and its
type is the model's under the block renaming — structurally, up to
display-only binder names (`Expr.eqUpToNames`): lean4export interns
expressions irrespective of names, so even a correct preprocessor
stream can differ from the input in binder names only.  On failure the
message dumps both sides, which identifies the offending subterm
immediately. -/
def checkMemberVal (ops : CheckerOps m) (blockNames : List Name)
    (env' : Env) (cv : ConstantVal) : m ConstantVal := do
  let f : Name → Name := fun n =>
    if blockNames.contains n then n.str "_model" else n
  let cvA ← checkConstantVal ops env' cv
  -- a member may not itself be shaped like a model companion, so the
  -- block renaming can never map onto a member
  if cvA.name.isModelSuffix then
    throw (.invalid s!"model-shaped member name {cvA.name}")
  -- the model counterpart
  let some (.defnInfo cvm _mval _) := env'.find? (cvA.name.str "_model")
    | throw (.notImplemented s!"missing model for {cvA.name}")
  unless cvm.levelParams = cvA.levelParams do
    throw (.notImplemented s!"model level parameters mismatch for {cvA.name}")
  unless Expr.eqUpToNames (cvA.type.renameConsts f) cvm.type do
    throw (.notImplemented
      s!"model type mismatch for {cvA.name}\n  member (renamed): \
        {reprStr (cvA.type.renameConsts f)}\n  model: {reprStr cvm.type}")
  pure cvA

/-- Check and install one non-recursor member of a modeled inductive
block against its `_model` counterpart (the step of `checkIndDecl`'s
fold, lifted for verification).  `caps` is the capability record the
block earned (recorded on the inductive type former).  Recursors are
handled by `checkIndRecs`. -/
def checkIndMember (ops : CheckerOps m) (blockNames : List Name)
    (caps : IndCaps) (env' : Env) (ci : ConstantInfo) : m Env := do
  let cvA ← checkMemberVal ops blockNames env' ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (⟨.indInfo cvA caps :: env'.consts⟩ : Env)
  | .ctorInfo _ nP nF => pure ⟨.ctorInfo cvA nP nF :: env'.consts⟩
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- Phase 0 of the recursor group: check each recursor's constant and
provision it *rule-less* on top of the previous ones.  Returns the
fully provisioned environment together with the checked constants (in
order).  Rule right-hand sides may mention any recursor of the block
(mutual and nested blocks), so they are annotated only against the
fully provisioned environment. -/
def provisionRecs (ops : CheckerOps m) (blockNames : List Name) :
    Env → List ConstantInfo →
    m (Env × List (ConstantVal × Nat × Nat × List RecRule))
  | envAcc, [] => pure (envAcc, [])
  | envAcc, ci :: rest =>
    match ci with
    | .recInfo _ mI rP rules => do
      let cvA ← checkMemberVal ops blockNames envAcc ci.toConstantVal
      let (envSelf, others) ← provisionRecs ops blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ rest
      pure (envSelf, (cvA, mI, rP, rules) :: others)
    | _ => throw (.notImplemented "recursor before other block members")

/-- Check and install a block's recursors *as a group*: every rule
right-hand side may mention any of them, so all are provisioned
rule-less together (`envSelf`) and installed together — no
intermediate environment stores a recursor whose rules mention a
missing sibling. -/
def checkIndRecs (ops : CheckerOps m) (blockNames : List Name)
    (env₂ : Env) (recs : List ConstantInfo) : m Env := do
  if recs.isEmpty then
    pure env₂
  else do
    let f : Name → Name := fun n =>
      if blockNames.contains n then n.str "_model" else n
    -- iota statements are equations: pin the pinned equality former
    unless env₂.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (envSelf, checked) ← provisionRecs ops blockNames env₂ recs
    checked.foldlM (fun (acc : Env) c => do
        let rules' ← checkIotaRules ops env₂ envSelf f c.1.name
          c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
      env₂

/-- Rename a model-side projection type back to public names. -/
def projBack (T ctor : Name) (nF : Nat) : Name → Name := fun n =>
  if n = T.str "_model" then T
  else if n = ctor.str "_model" then ctor
  else
    match (List.range nF).find? (fun j => n == projModelName T j) with
    | some j => projFnName T j
    | none => n

/-- The forward (public → model) map on the projection family. -/
def projFwd (T ctor : Name) (nF : Nat) : Name → Name := fun n =>
  if n = T then T.str "_model"
  else if n = ctor then ctor.str "_model"
  else
    match (List.range nF).find? (fun j => n == projFnName T j) with
    | some j => projModelName T j
    | none => n

/-- Stage 1 of `checkProjFn`: the stored constants the projection
depends on — the single constructor (arity-matched), the model's
`proj_i` definition (level-matched), the parent type, and the pinned
equality former; the projection's own name must be free. -/
def checkProjLookups (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : m (ConstantVal × ConstantVal) := do
  let some (.ctorInfo cvj cnP cnF) := env'.find? ctorName
    | throw (.notImplemented "projection constructor not stored")
  unless cnP = nP ∧ cnF = nF do
    throw (.notImplemented "projection constructor arity mismatch")
  let some (.defnInfo mcv _ _) := env'.find? (projModelName T i)
    | throw (.notImplemented "missing projection model")
  unless mcv.levelParams = lps do
    throw (.notImplemented "projection model level mismatch")
  unless (env'.find? (projFnName T i)).isNone do
    throw (.invalid "projection name taken")
  unless (env'.find? T).isSome do
    throw (.notImplemented "projection parent not stored")
  unless env'.find? eqName = some eqA do
    throw (.notImplemented "projection iota requires the pinned Eq basis")
  pure (cvj, mcv)

/-- Stage 2: the public projection type — the model's, renamed back
(pinned by the renaming roundtrip), well-formed and parameter-led. -/
def checkProjTy (env' : Env) (T ctorName : Name) (lps : List Name)
    (mty : Expr) (nP nF : Nat) : m Expr := do
  let pty := mty.renameConsts (projBack T ctorName nF)
  unless (pty.renameConsts (projFwd T ctorName nF)) == mty do
    throw (.notImplemented "projection type roundtrip")
  unless pty.constsResolve env' do
    throw (.notImplemented "projection type resolution")
  unless pty.looseBVarsBounded 0 && !pty.hasFvar &&
      pty.allLevelParamsDefined lps do
    throw (.notImplemented "projection type wellformedness")
  unless (pty.stripPis (nP + 1)).isSome do
    throw (.notImplemented "projection type telescope")
  pure pty

/-- Stage 2b: the projection type's parameter telescope is
*syntactically* the constructor's, and the constructor's residual is
the family applied to exactly the parameters — the syntactic pins the
rule's total λ-equality derivation folds over (task #58; completeness-
safe: both telescopes spell the family's parameter types, and a
structure constructor targets the family at its parameters). -/
def checkProjShape (pty ctorTy : Expr) (nP nF : Nat) : m Unit := do
  let some (_abinders, _) := pty.stripPis nP
    | throw (.notImplemented "projection type telescope")
  let some (_, cbody) := ctorTy.stripPis (nP + nF)
    | throw (.notImplemented "projection constructor telescope")
  unless cbody.getAppArgs.length == nP do
    throw (.notImplemented "projection constructor residual arity")
  match cbody.getAppFn with
  | .const _ _ => pure ()
  | _ => throw (.notImplemented "projection constructor residual head")

/-- Stage 3: the reduction rule — λ over the constructor telescope
returning field `i`, annotated; its λ-domains stay the constructor's. -/
def checkProjRule (ops : CheckerOps m) (env' : Env) (pty : Expr) (cvj : ConstantVal) (lps : List Name)
    (nP nF i : Nat) : m Expr := do
  let some rhs := Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i))
    | throw (.notImplemented "projection rule telescope")
  unless !rhs.hasFvar && rhs.looseBVarsBounded 0 do
    throw (.notImplemented "projection rule scoping")
  let rhsA ← ops.annotate env' 0 rhs
  unless rhsA.allLevelParamsDefined lps && rhsA.constsResolve env' &&
      rhsA.looseBVarsBounded 0 && !rhsA.hasFvar do
    throw (.notImplemented "projection rule wellformedness")
  let some (rbinders, rrbody) := rhsA.stripLams (nP + nF)
    | throw (.notImplemented "projection rule telescope")
  unless rrbody == Expr.bvar (nF - 1 - i) do
    throw (.notImplemented "projection rule body")
  let some (cbindersR, _) := cvj.type.stripPis (nP + nF)
    | throw (.notImplemented "projection constructor telescope")
  unless domsMatchAux (fun _ e => e) rbinders cbindersR 0 0 (nP + nF) do
    throw (.notImplemented "projection rule domain mismatch")
  -- the frame walks and the definitional parameter/domain pins
  -- (task #58): the projection type's opened parameter annotations are
  -- definitionally the constructor's instantiated parameter domains,
  -- and the whole frame's annotations are definitionally the rule
  -- λ-tower's instantiated domains
  let some (fvsP, _) := openPisAtFvars nP pty 0
    | throw (.notImplemented "projection type telescope")
  let some (cdomsP, crestP) := Expr.instPisAt fvsP cvj.type
    | throw (.notImplemented "projection constructor telescope")
  checkDefEqList ops env' (nP + nF) (fvsP.map Expr.fvarTypeD) cdomsP
  let some (xFvs, _) := openPisAtFvars nF crestP nP
    | throw (.notImplemented "projection constructor telescope")
  let some (ldoms, _) := Expr.instLamsAt (fvsP ++ xFvs) rhsA
    | throw (.notImplemented "projection rule telescope")
  checkDefEqList ops env' (nP + nF) ((fvsP ++ xFvs).map Expr.fvarTypeD)
    ldoms
  let _rhsTy ← ops.inferType env' 0 rhsA
  pure rhsA

/-- Stage 4: the model's `proj_i.iota` theorem pins the rule — the
statement's telescope domains are the constructor's (renamed to the
model side) and its body equates the projected constructor spine with
field `i`.  The equality's type slot needs no pin (the collapse
ignores it). -/
def checkProjIota (env' : Env) (T ctorName : Name) (lps : List Name)
    (cvj : ConstantVal) (nP nF i : Nat) : m Unit := do
  let some (.thmInfo tcv _) := env'.find? ((projModelName T i).str "iota")
    | throw (.notImplemented "missing projection iota theorem")
  unless tcv.levelParams = lps do
    throw (.notImplemented "projection iota level mismatch")
  let some (sbinders, sbody) := tcv.type.stripPis (nP + nF)
    | throw (.notImplemented "projection iota telescope")
  let some (cbindersR, _) := cvj.type.stripPis (nP + nF)
    | throw (.notImplemented "projection constructor telescope")
  unless domsMatchAux
      (fun _ e => e.renameConsts (projFwd T ctorName nF))
      sbinders cbindersR 0 0 (nP + nF) do
    throw (.notImplemented "projection iota domain mismatch")
  let depth := nP + nF
  let pArgs := (List.range nP).map fun k => Expr.bvar (depth - 1 - k)
  let xArgs := (List.range nF).map fun k => Expr.bvar (nF - 1 - k)
  let mkSpine := Expr.mkAppN
    (.const (ctorName.str "_model") (cvj.levelParams.map .param))
    (pArgs ++ xArgs)
  let lhsS := Expr.mkAppN
    (.const (projModelName T i) (lps.map .param)) (pArgs ++ [mkSpine])
  match sbody with
  | .app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC =>
    unless c = eqName do
      throw (.notImplemented "projection iota head")
    unless lhsC == lhsS do
      throw (.notImplemented "projection iota redex mismatch")
    unless rhsC == Expr.bvar (nF - 1 - i) do
      throw (.notImplemented "projection iota field mismatch")
  | _ => throw (.notImplemented "projection iota body shape")

/-- Check and install the public projection function for field `i` of
a modeled single-constructor structure, against the model's
`T._model.proj_i` definition and its `iota` theorem.  The function is
stored as a degenerate recursor (no motive, no minors) carrying one
rule, so the generic iota machinery reduces it. -/
def checkProjFn (ops : CheckerOps m) (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : m Env := do
  let (cvj, mcv) ← checkProjLookups env' T ctorName lps nP nF i
  let pty ← checkProjTy env' T ctorName lps mcv.type nP nF
  checkProjShape pty cvj.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRule ops env' pty cvj lps nP nF i
  checkProjIota env' T ctorName lps cvj nP nF i
  -- a degenerate recursor: no motive, no minors, no indices, so the
  -- major sits at position nP and the rule prefix is the parameters;
  -- the canonical flag is computed here, once, like `checkIotaRule`
  pure ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [⟨ctorName, nF, nP,
      if Expr.recRulePlain pty nP nP nP then .plain else .inert, rhsA⟩] ::
    env'.consts⟩

/-- Does the model document structural eta for this single-constructor
block — a `T._model.eta` theorem with the pinned statement
`∀ p⃗ (x : T._model p⃗), x = C._model p⃗ (T._model.proj_0 p⃗ x) …`?
Checked before install; a positive answer records the eta capability
on the stored inductive.  (`Bool`-valued: an absent or differently
shaped artifact just means no capability.)  The parameter telescope is
pinned against the constructor *model*'s (both live on the model side
and are annotated by the same pipeline), and the equality's type slot
is not pinned (the collapse ignores it). -/
def checkEtaThm (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) : Bool :=
  match env'.find? ((T.str "_model").str "eta"),
      env'.find? (T.str "_model"),
      env'.find? (ctorName.str "_model"), env'.find? eqName with
  | some (.thmInfo tcv _), some (.defnInfo cvmT _ _),
      some (.defnInfo cvmC _ _), some eqStored =>
    eqStored == eqA && tcv.levelParams == lps &&
    cvmT.levelParams == lps && cvmC.levelParams == lps &&
    -- the projection models exist at the family's level parameters
    (List.range nF).all (fun j =>
      match env'.find? (projModelName T j) with
      | some (.defnInfo cvmj _ _) => cvmj.levelParams == lps
      | _ => false) &&
    (match tcv.type.stripPis (nP + 1), cvmT.type.stripPis nP with
     | some (sbinders, sbody), some (tbindersM, _) =>
       domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
       (match sbinders[nP]? with
        | some (_, xdom, _) =>
          xdom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
        | none => false) &&
       (match sbody with
        | .app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC =>
          c == eqName && lhsC == Expr.bvar 0 &&
          rhsC == Expr.mkAppN
            (.const (ctorName.str "_model") (lps.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
             (List.range nF).map fun j => Expr.mkAppN
               (.const (projModelName T j) (lps.map .param))
               (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
                [Expr.bvar 0]))
        | _ => false)
     | _, _ => false)
  | _, _, _, _ => false

/-- Does the model document unit-likeness for this block — a
`T._model.unitlike` theorem with the pinned statement
`∀ p⃗ (x y : T._model p⃗), x = y`?  Checked before install; a positive
answer records the unit-like capability on the stored inductive. -/
def checkUnitThm (env' : Env) (T : Name) (lps : List Name)
    (nP : Nat) : Bool :=
  match env'.find? ((T.str "_model").str "unitlike"),
      env'.find? (T.str "_model"), env'.find? eqName with
  | some (.thmInfo tcv _), some (.defnInfo cvmT _ _), some eqStored =>
    eqStored == eqA && tcv.levelParams == lps &&
    cvmT.levelParams == lps &&
    (match tcv.type.stripPis (nP + 2), cvmT.type.stripPis nP with
     | some (sbinders, sbody), some (tbindersM, _) =>
       domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
       (match sbinders[nP]? with
        | some (_, xdom, _) =>
          xdom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
        | none => false) &&
       (match sbinders[nP + 1]? with
        | some (_, ydom, _) =>
          ydom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - k))
        | none => false) &&
       (match sbody with
        | .app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC =>
          c == eqName && lhsC == Expr.bvar 1 && rhsC == Expr.bvar 0
        | _ => false)
     | _, _ => false)
  | _, _, _ => false

/-- The result sort of a syntactic pi telescope (the sort the type
former's type ends in), if it ends in a sort at all. -/
def piResultSort (e : Expr) : Option Level :=
  match e.piResult with
  | .sort u => some u
  | _ => none

/-- Install the Prop-fallback elimination-template entry for field `i`
of a single-constructor block whose `_model.proj_i` artifact is absent
(Prop structures whose projections only exist at certain level
instantiations): the parent's elimination *shape* — a structure
recursor with one rule for the block's constructor, no indices, and a
prefix of params + one motive + one minor — is checked here, once, and
recorded as a `native = false` projection-table entry consumed by
`annotateProjRec`.  When the shape does not support the elimination
the entry is simply not installed, and use sites positively decline —
exactly as the per-use shape checks did before. -/
def installProjTemplate (env : Env) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : m Env := do
  match env.find? (T.str "rec") with
  | some (.recInfo cvR mI rP [rule]) =>
    if (env.find? (projFnName T i)).isNone ∧
        mI = rP ∧ rP = nP + 2 ∧ rule.ctor = ctorName ∧ i < nF then
      pure ⟨.projInfo ⟨T, i, lps, nP, ctorName, nF, .sort .zero,
        .zero, .zero, false,
        cvR.levelParams.length = lps.length + 1⟩ :: env.consts⟩
    else pure env
  | _ => pure env

/-- One projection-function install step (skipped where the model's
projection artifact is absent; those fields get elimination-template
entries in a second pass, `installProjTemplateStep`, so the artifact
phase never sees a template entry). -/
def installProjFnStep (ops : CheckerOps m) (T ctorName : Name)
    (lps : List Name) (nP nF : Nat) (e : Env) (i : Nat) : m Env :=
  if (e.find? (projModelName T i)).isSome then
    checkProjFn ops e T ctorName lps nP nF i
  else pure e

/-- One elimination-template install step (the second pass): indices
whose artifact phase installed a projection function are skipped. -/
def installProjTemplateStep (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (e : Env) (i : Nat) : m Env :=
  if (e.find? (projFnName T i)).isNone then
    installProjTemplate e T ctorName lps nP nF i
  else pure e

/-! ## The direct simple-structure path (task #82)

A block recognised by `directParts?` (`Setlec/Kernel/Direct.lean`)
installs *directly*: no `_model` artifact is consumed, and the
set-theoretic model is constructed from the constructor telescope
(`Setlec/Model/DirectTower.lean`).  What is left for this layer are the
reference checks that need inference and definitional equality — the
per-field universe bound and the definitional pins of the recursor's
binder domains against the constructor's.
-/

/-- The capabilities a direct simple structure earns.  `ruleK` is
`false` by construction (`isKTarget` needs a `Prop` result, lean4lean
`Inductive/Add.lean:289-296`, and the class requires a provably nonzero
sort).

Neither `eta` nor `unitlike` is claimed.  Both are *frame-relative*
laws — they quantify over a parameter-telescope fit at an **arbitrary**
frame, while the constructed values are λ-towers over the frame-0
opening of the stored type, so discharging them needs a relocation of a
closed telescope's fit onto the canonical frame-0 opening that the
value construction does not supply (see DESIGN.md, "The two
frame-relative capabilities").  Claiming fewer capabilities only ever
removes reductions, so this is safe; it costs nothing today because the
direct path is artifact-*absence* gated and every structure carrying an
artifact keeps the modeled route and its capabilities. -/
def directCaps (p : DirectParts) : IndCaps where
  eta := false
  etaCtor := p.cvC.name
  etaParams := p.nP
  etaFields := p.nF
  unitlike := false
  unitParams := p.nP
  ruleK := false

/-- The official per-field universe bound, over the opened constructor
telescope: every field's sort must be `≤` the structure's result sort
(lean4lean `Inductive/Add.lean:225-228`, nanoda
`inductive.rs:828-834`; the `Prop` escape hatch there does not apply —
the class requires a nonzero result sort).  Walks the fields from the
last to the first. -/
def checkDirectFieldUniv (ops : CheckerOps m) (env : Env) (s : Level)
    (nP : Nat) (fvs : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct structure: field index")
    -- each field's domain is inferred at *its own* frame: the variable
    -- `fvs[j]` sits at index `nP + j`, so everything below it is in
    -- scope and nothing above is
    let ty ← ops.inferType env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort env (nP + j) ty
    unless ← liftFueled "level comparison" (Level.leq u s) do
      throw (.invalid "direct structure: field universe too large")
    checkDirectFieldUniv ops env s nP fvs j

/-- Stage 1: the type former.  The ordinary constant check plus a
re-verification of the *annotated* shape — the model reads the
parameter telescope and the result sort off the stored type. -/
def checkDirectInd (ops : CheckerOps m) (env : Env) (p : DirectParts) :
    m (Env × ConstantVal) := do
  let cvTa ← checkConstantVal ops env p.cvT
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis p.nP)
    (.notImplemented "direct structure: type former telescope")
  unless tbody == Expr.sort p.resSort do
    throw (.notImplemented "direct structure: type former result sort")
  pure (⟨.indInfo cvTa (directCaps p) :: env.consts⟩, cvTa)

/-- Stage 2: the constructor — the ordinary constant check, the
annotated result shape, and the per-field universe bound. -/
def checkDirectCtor (ops : CheckerOps m) (env : Env) (p : DirectParts)
    (cvTa : ConstantVal) : m (Env × ConstantVal) := do
  let cvCa ← checkConstantVal ops env p.cvC
  let (_, cbody) ← unwrapOr (cvCa.type.stripPis (p.nP + p.nF))
    (.notImplemented "direct structure: constructor telescope")
  unless cbody == directFam p.cvT.name p.cvT.levelParams p.nP p.nF do
    throw (.notImplemented "direct structure: constructor result")
  -- One opening for the whole block: the **constructor's own**
  -- parameter telescope, which is the frame the model's fits arrive at
  -- (the field types' interpretations, the dependent-pair tower and the
  -- constructor value are all read off it).
  let cq ← unwrapOr (openPisAtFvars p.nP cvCa.type 0)
    (.notImplemented "direct structure: constructor telescope")
  let tq ← unwrapOr (Expr.instPisAt cq.1 cvTa.type)
    (.notImplemented "direct structure: type former telescope")
  -- the type former's parameter domains are the constructor's,
  -- definitionally (lean4lean `Inductive/Add.lean:220-222`, nanoda
  -- `check_ctor`): this is what carries a parameter value's membership
  -- from the constructor's telescope to the type former's, so that the
  -- family's own value folds at the very same parameters
  checkDefEqList ops env (p.nP + p.nF) (cq.1.map Expr.fvarTypeD) tq.1
  let xq ← unwrapOr (openPisAtFvars p.nF cq.2 p.nP)
    (.notImplemented "direct structure: constructor field telescope")
  -- the opened residual is the family at the opened parameter variables
  unless xq.2 == Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) cq.1 do
    throw (.notImplemented "direct structure: opened constructor residual")
  checkDirectFieldUniv ops env p.resSort p.nP xq.1 p.nF
  pure (⟨.ctorInfo cvCa p.nP p.nF :: env.consts⟩, cvCa)

/-- Stage 3: the recursor's type is the generated shape.  The skeleton
(motive dependent over the family, one minor over the constructor's
field telescope ending in `motive (C p⃗ f⃗)`, no indices, major, body
`motive t`) is pinned syntactically by `directShape`; the binder
*domains* are pinned definitionally against the type former's and the
constructor's over one shared opening — exactly the equalities the
model's telescope walks consume. -/
def checkDirectRecTy (ops : CheckerOps m) (env : Env) (p : DirectParts)
    (cvTa cvCa cvRa : ConstantVal) : m Unit := do
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  unless directShape T p.cvC.name lps p.elim p.nP p.nF
      cvTa.type cvCa.type cvRa.type do
    throw (.notImplemented "direct structure: annotated recursor shape")
  let depth := p.nP + 2 + p.nF
  let (fvsP, rest) ← unwrapOr (openPisAtFvars (p.nP + 2) cvRa.type 0)
    (.notImplemented "direct structure: recursor telescope")
  let ps := fvsP.take p.nP
  let famApp := Expr.mkAppN (.const T (lps.map .param)) ps
  -- the parameters: definitionally the constructor's parameter domains
  let (cdomsP, crest) ← unwrapOr (Expr.instPisAt ps cvCa.type)
    (.notImplemented "direct structure: constructor telescope")
  checkDefEqList ops env depth (ps.map Expr.fvarTypeD) cdomsP
  -- the motive: `∀ (t : T p⃗), Sort elim`
  let mfv ← unwrapOr fvsP[p.nP]?
    (.internal "direct structure: motive index")
  let (mbs, mbody) ← unwrapOr (mfv.fvarTypeD.stripPis 1)
    (.notImplemented "direct structure: motive telescope")
  let mdom ← unwrapOr ((mbs[0]?).map (·.2.1))
    (.notImplemented "direct structure: motive telescope")
  unless ← ops.isDefEq env depth mdom famApp do
    throw (.notImplemented "direct structure: motive domain")
  unless mbody == Expr.sort (.param p.elim) do
    throw (.notImplemented "direct structure: motive codomain")
  -- the minor premise: the constructor's field telescope, ending in
  -- the motive applied to the canonical constructor spine
  let minfv ← unwrapOr fvsP[p.nP + 1]?
    (.internal "direct structure: minor index")
  let (xFvs, minBody) ← unwrapOr
    (openPisAtFvars p.nF minfv.fvarTypeD (p.nP + 2))
    (.notImplemented "direct structure: minor telescope")
  let (cdomsF, crest2) ← unwrapOr (Expr.instPisAt xFvs crest)
    (.notImplemented "direct structure: constructor field telescope")
  checkDefEqList ops env depth (xFvs.map Expr.fvarTypeD) cdomsF
  unless crest2 == famApp do
    throw (.notImplemented "direct structure: constructor residual")
  unless minBody == Expr.app mfv
      (Expr.mkAppN (.const p.cvC.name (lps.map .param)) (ps ++ xFvs)) do
    throw (.notImplemented "direct structure: minor conclusion")
  -- the major premise and the conclusion `motive t`
  let (jbs, jbody) ← unwrapOr (rest.stripPis 1)
    (.notImplemented "direct structure: major telescope")
  let jdom ← unwrapOr ((jbs[0]?).map (·.2.1))
    (.notImplemented "direct structure: major telescope")
  unless ← ops.isDefEq env depth jdom famApp do
    throw (.notImplemented "direct structure: major domain")
  unless jbody == Expr.app mfv (.bvar 0) do
    throw (.notImplemented "direct structure: recursor conclusion")

/-- Stage 4: the single rule's right-hand side — `λ p⃗ motive minor f⃗,
minor f⃗` (lean4lean `Inductive/Add.lean:441-447`), annotated and
checked exactly like a projection rule: the body is the canonical
application and the λ-domains are definitionally the recursor's own and
the constructor's field domains. -/
def checkDirectRule (ops : CheckerOps m) (env : Env) (p : DirectParts)
    (cvCa cvRa : ConstantVal) : m Expr := do
  unless !p.rhs.hasFvar && p.rhs.looseBVarsBounded 0 do
    throw (.notImplemented "direct structure: rule scoping")
  let rhsA ← ops.annotate env 0 p.rhs
  unless rhsA.allLevelParamsDefined cvRa.levelParams && rhsA.constsResolve env &&
      rhsA.looseBVarsBounded 0 && !rhsA.hasFvar do
    throw (.notImplemented "direct structure: rule wellformedness")
  let (_, rbody) ← unwrapOr (rhsA.stripLams (p.nP + 2 + p.nF))
    (.notImplemented "direct structure: rule telescope")
  unless rbody == directRuleBody p.nF do
    throw (.notImplemented "direct structure: rule body")
  let depth := p.nP + 2 + p.nF
  let (fvsP, _) ← unwrapOr (openPisAtFvars (p.nP + 2) cvRa.type 0)
    (.notImplemented "direct structure: recursor telescope")
  let (_, crest) ← unwrapOr (Expr.instPisAt (fvsP.take p.nP) cvCa.type)
    (.notImplemented "direct structure: constructor telescope")
  let minfv ← unwrapOr fvsP[p.nP + 1]?
    (.internal "direct structure: minor index")
  let (xFvs, _) ← unwrapOr
    (openPisAtFvars p.nF minfv.fvarTypeD (p.nP + 2))
    (.notImplemented "direct structure: minor telescope")
  let _ ← unwrapOr (Expr.instPisAt xFvs crest)
    (.notImplemented "direct structure: constructor field telescope")
  let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvs) rhsA)
    (.notImplemented "direct structure: rule telescope")
  checkDefEqList ops env depth ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms
  let _rhsTy ← ops.inferType env 0 rhsA
  pure rhsA

/-- Install the projection function for field `i` of a direct simple
structure.  Same slot and same consumer as the modeled path's
`checkProjFn`: a degenerate recursor (no motive, no minors, no indices)
stored under `projFnName T i`, which is the projection-table name
family `annotateProjElim` dispatches on — so `.proj` nodes on a direct
structure rewrite into `T.proj.i` applications exactly as they do on a
modeled one, and the generic iota machinery reduces them.  Only the
*type* comes from a different source: generated from the constructor
telescope (`directProjTy`) instead of read off a `_model.proj_i`
artifact.  Fields are installed in order, since field `i`'s type
mentions the earlier projections. -/
def checkDirectProj (ops : CheckerOps m) (T C : Name) (lps : List Name)
    (nP nF : Nat) (cvTa cvCa : ConstantVal) (env : Env) (i : Nat) : m Env := do
  let pty ← unwrapOr (directProjTy T lps nP nF i cvTa.type cvCa.type)
    (.notImplemented "direct structure: projection type")
  unless !pty.hasFvar && pty.looseBVarsBounded 0 do
    throw (.notImplemented "direct structure: projection type scoping")
  let ptyA ← ops.annotate env 0 pty
  unless ptyA.allLevelParamsDefined lps && ptyA.constsResolve env &&
      ptyA.looseBVarsBounded 0 && !ptyA.hasFvar do
    throw (.notImplemented "direct structure: projection type wellformedness")
  unless (ptyA.stripPis (nP + 1)).isSome do
    throw (.notImplemented "direct structure: projection type telescope")
  let sty ← ops.inferType env 0 ptyA
  let _u ← ops.ensureSort env 0 sty
  unless (env.find? (projFnName T i)).isNone do
    throw (.invalid "projection name taken")
  checkProjShape ptyA cvCa.type nP nF
  let rhsA ← checkProjRule ops env ptyA cvCa lps nP nF i
  pure ⟨.recInfo ⟨projFnName T i, lps, ptyA⟩ nP nP
    [⟨C, nF, nP,
      if Expr.recRulePlain ptyA nP nP nP then .plain else .inert, rhsA⟩] ::
    env.consts⟩

/-- Check and install a **direct simple structure** (task #82): the
type former, the constructor, the recursor with its single rule, and
the projection *templates* the `.proj` annotation falls back on.  No
`_model` artifact is read; the model is constructed at install
(`Setlec/Model/Direct*.lean`).  Recognition happened in
`directParts?`; everything here is a genuine check of the declaration,
so a failure is a verdict, not a fall-through. -/
def checkDirectStruct (ops : CheckerOps m) (env : Env) (p : DirectParts) :
    m Env := do
  let (env₁, cvTa) ← checkDirectInd ops env p
  let (env₂, cvCa) ← checkDirectCtor ops env₁ p cvTa
  let cvRa ← checkConstantVal ops env₂ p.cvR
  checkDirectRecTy ops env₂ p cvTa cvCa cvRa
  let rhsA ← checkDirectRule ops env₂ p cvCa cvRa
  let env₃ : Env :=
    ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP,
        if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
          .plain else .inert,
        rhsA⟩] :: env₂.consts⟩
  unless (List.range p.nF).all
      (fun j => (env₃.find? (projFnName p.cvT.name j)).isNone) do
    throw (.invalid "projection name family taken")
  (List.range p.nF).foldlM
    (checkDirectProj ops p.cvT.name p.cvC.name p.cvT.levelParams
      p.nP p.nF cvTa cvCa) env₃

/-- Install one pinned basis declaration (duplicate-checked). -/
def installBasisDecl (env : Env) (ci : ConstantInfo) : m Env := do
  unless (env.find? ci.name).isNone do
    throw (.invalid s!"duplicate declaration {ci.name}")
  pure (⟨ci :: env.consts⟩ : Env)

/-- The capabilities recorded for a single-constructor modeled block. -/
def indBlockCaps (env : Env) (cvT cvC : ConstantVal) (nP nF : Nat) :
    IndCaps where
  eta := (cvC.levelParams = cvT.levelParams) &&
    checkEtaThm env cvT.name cvC.name cvT.levelParams nP nF
  etaCtor := cvC.name
  etaParams := nP
  etaFields := nF
  unitlike := checkUnitThm env cvT.name cvT.levelParams nP
  unitParams := nP
  ruleK := nF == 0 && piResultIsProp cvT.type

/-- Check and install a modeled inductive block: every member is
checked against its `_model` counterpart (type up to the public↔model
renaming, iota rules against the model's `iota_j` theorems), then
stored as a real inductive-kind constant.  Single-constructor blocks
determine their capability record first (recorded on the inductive)
and additionally install the projection functions the model documents
(skipped where the artifacts are absent).  The K flag is computed from
shape exactly as the official kernel does — an inductive proposition
with a single constructor taking only the parameters; the reduction
site carries the semantic load (proof irrelevance), so no model
theorem backs the flag. -/
def checkIndDecl (ops : CheckerOps m) (env : Env) (block : List ConstantInfo) : m Env := do
  -- the recursors must form a suffix of the block: their rules may
  -- mention each other, so they install as a group after everything
  -- else
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  unless block = nonrecs ++ recs do
    throw (.notImplemented "recursor before other block members")
  let blockNames := block.map (·.name)
  match block.filter (fun ci => match ci with
      | .indInfo _ _ => true | _ => false),
    block.filter (fun ci => match ci with
      | .ctorInfo _ _ _ => true | _ => false) with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] =>
    let caps ← pure (indBlockCaps env cvT cvC nP nF)
    let env₂ ← nonrecs.foldlM
      (checkIndMember ops blockNames caps) env
    let env₃ ← checkIndRecs ops blockNames env₂ recs
    -- the whole projection name family must be ours to install
    unless (List.range nF).all
        (fun j => (env₃.find? (projFnName cvT.name j)).isNone) do
      throw (.invalid "projection name family taken")
    let env₄ ← (List.range nF).foldlM
      (installProjFnStep ops cvT.name cvC.name cvT.levelParams nP nF) env₃
    (List.range nF).foldlM
      (installProjTemplateStep cvT.name cvC.name cvT.levelParams nP nF)
      env₄
  | _, _ => do
    let env₂ ← nonrecs.foldlM (checkIndMember ops blockNames {}) env
    checkIndRecs ops blockNames env₂ recs

/-- Check a `def` declaration's value against its checked constant.
The reducibility hint is stored untouched: it steers only the lazy
delta unfolding order in `isDefEq`, never a verdict, so nothing about
it needs checking. -/
def checkDefnVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (value : Expr) (hint : ReducibilityHint) : m Env := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (.invalid s!"unknown constant in value of {cv.name}")
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in definition {cv.name}")
  pure ⟨.defnInfo cv value hint :: env.consts⟩

/-- Check a `theorem` declaration's value against its checked constant
(whose type must additionally be a proposition). -/
def checkThmVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (value : Expr) : m Env := do
  -- the type of a theorem must be a proposition
  let stype ← ops.inferType env 0 cv.type
  let u ← ops.ensureSort env 0 stype
  unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
    throw (.invalid s!"type of theorem {cv.name} is not a proposition")
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (.invalid s!"unknown constant in value of {cv.name}")
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in theorem {cv.name}")
  pure ⟨.thmInfo cv value :: env.consts⟩

/-- Check an `opaque` declaration's value against its checked
constant: exactly the theorem check without the is-a-proposition
requirement.  The result is stored as a `thmInfo` — "checked value,
never delta-unfolded" is precisely opaque semantics. -/
def checkOpaqueVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (value : Expr) : m Env := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (.invalid s!"unknown constant in value of {cv.name}")
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in opaque {cv.name}")
  pure ⟨.thmInfo cv value :: env.consts⟩
/-- Certify a list of recurrence equations by definitional equality
(at depth 2: the equations' variables are `fvar 0`/`fvar 1`). -/
def certifyNatEqs (ops : CheckerOps m) (env : Env) :
    List (Expr × Expr) → m Bool
  | [] => pure true
  | eq :: rest => do
    if ← ops.isDefEq env 2 eq.1 eq.2 then
      certifyNatEqs ops env rest
    else pure false

/-- The pinned defining expression of a pin-certified WF-recursive op
(`Setlec/Kernel/NatOpPins.lean`, generated at build time from the toolchain's own
prelude). -/
def divModDeclPin (c : Name) : Expr :=
  if c = natDivName then natDivDeclPin
  else if c = natGcdName then natGcdDeclPin
  else if c = natLandName then natLandDeclPin
  else if c = natLorName then natLorDeclPin
  else if c = natXorName then natXorDeclPin
  else if c = natShiftLeftName then natShiftLeftDeclPin
  else if c = natShiftRightName then natShiftRightDeclPin
  else if c = natLog2Name then natLog2DeclPin
  else natModDeclPin

/-- The vendored certificate proof terms of a pin-certified
WF-recursive op (`Setlec/Kernel/NatOpPins.lean`), one per statement of
`divModCertStmts`. -/
def divModCertProofs (c : Name) : List Expr :=
  if c = natDivName then natDivCertProofs
  else if c = natGcdName then natGcdCertProofs
  else if c = natLandName then natLandCertProofs
  else if c = natLorName then natLorCertProofs
  else if c = natXorName then natXorCertProofs
  else if c = natShiftLeftName then natShiftLeftCertProofs
  else if c = natShiftRightName then natShiftRightCertProofs
  else if c = natLog2Name then natLog2CertProofs
  else natModCertProofs

/-- The pinned characterization statements of a pin-certified
WF-recursive op, in *open* form over `x := fvar 0`, `y := fvar 1` (the
hypotheses become `fvar 2, fvar 3`): per certificate, the list of
hypothesis types and the characteristic equation `Eq Nat lhs rhs`.
The guards are spelled with the already-certified `Nat.ble` (never the
`Nat.le`/`Nat.lt` `Prop` inductives) and the numeral `1` as
`Nat.succ Nat.zero`, so the model side consumes them through the
existing `NatOpsOk` literal semantics for `ble`/`sub`.  The op's
self-reference is `.const c []`, substituted with the stored annotated
value before checking (all statement components are application
spines, so `Expr.substConst0` applies). -/
def divModCertStmts (c : Name) : List (List Expr × Expr) :=
  let natTy : Expr := .const natName []
  let x : Expr := .fvar 0 (.str .anonymous "x") natTy
  let y : Expr := .fvar 1 (.str .anonymous "y") natTy
  let one : Expr := .app (.const natSuccName []) (.const natZeroName [])
  let ble2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natBleName []) a) b
  let eqB : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) (.const boolName [])) a) b
  let eqN : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) natTy) a) b
  let op2 : Expr → Expr → Expr := fun a b => .app (.app (.const c []) a) b
  let sub2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natSubName []) a) b
  let bT : Expr := .const boolTrueName []
  let bF : Expr := .const boolFalseName []
  let z : Expr := .const natZeroName []
  let two : Expr := .app (.const natSuccName []) one
  let mod2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natModName []) a) b
  let div2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natDivName []) a) b
  let add2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natAddName []) a) b
  let mul2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natMulName []) a) b
  let op1 : Expr → Expr := fun a => .app (.const c []) a
  let s1 : Expr → Expr := fun a => .app (.const natSuccName []) a
  if c = natGcdName then
    -- `gcd`: `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`
    [([eqB (ble2 one x) bT], eqN (op2 x y) (op2 (mod2 y x) x)),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c = natShiftLeftName then
    -- `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`
    [([eqB (ble2 one y) bT], eqN (op2 x y) (op2 (mul2 two x) (sub2 y one))),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c = natShiftRightName then
    -- `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`, `y = 0 → x >>> y = x`
    [([eqB (ble2 one y) bT], eqN (op2 x y) (div2 (op2 x (sub2 y one)) two)),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c = natLog2Name then
    -- unary: `2 ≤ x → log2 x = succ (log2 (x/2))`, `x < 2 → log2 x = 0`
    -- (the statement frame still has both variables; `y` is unused)
    [([eqB (ble2 two x) bT], eqN (op1 x) (s1 (op1 (div2 x two)))),
     ([eqB (ble2 two x) bF], eqN (op1 x) z)]
  else if c = natLandName then
    -- `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`,
    -- `x = 0 → x &&& y = 0`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mul2 (mod2 x two) (mod2 y two)))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) z)]
  else if c = natLorName then
    -- `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`,
    -- `x = 0 → x ||| y = y`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (sub2 (add2 (mod2 x two) (mod2 y two))
          (mul2 (mod2 x two) (mod2 y two))))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c = natXorName then
    -- `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`,
    -- `x = 0 → x ^^^ y = y`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mod2 (add2 (mod2 x two) (mod2 y two)) two))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else
  let recRhs : Expr :=
    if c = natDivName then .app (.const natSuccName []) (op2 (sub2 x y) y)
    else op2 (sub2 x y) y
  let baseRhs : Expr := if c = natDivName then .const natZeroName [] else x
  [([eqB (ble2 y x) bT, eqB (ble2 one y) bT], eqN (op2 x y) recRhs),
   ([eqB (ble2 y x) bF], eqN (op2 x y) baseRhs),
   ([eqB (ble2 one y) bF], eqN (op2 x y) baseRhs)]

/-- The vendored proof applied to the statement's free variables
(`x`, `y`, then one `fvar` per hypothesis, carrying the hypothesis
*type* as its `fvar` annotation — the checker's implicit local
context). -/
def divModCertApplied (proofS : Expr) (hyps : List Expr) : Expr :=
  let base : Expr :=
    .app (.app proofS (.fvar 0 (.str .anonymous "x") (.const natName [])))
      (.fvar 1 (.str .anonymous "y") (.const natName []))
  match hyps with
  | [h1] => .app base (.fvar 2 (.str .anonymous "h1") h1)
  | [h1, h2] =>
    .app (.app base (.fvar 2 (.str .anonymous "h1") h1))
      (.fvar 3 (.str .anonymous "h2") h2)
  | _ => base

/-- The syntactic guards of one certificate check: the substituted
proof is closed, level-monomorphic and resolving, and the substituted
statement components resolve. -/
def divModCertGuard (env : Env) (c : Name) (annVal : Expr)
    (hyps : List Expr) (eqE proof : Expr) : Bool :=
  (Expr.substConstAll c annVal proof).looseBVarsBounded 0 &&
  !(Expr.substConstAll c annVal proof).hasFvar &&
  (Expr.substConstAll c annVal proof).allLevelParamsDefined [] &&
  (Expr.substConstAll c annVal proof).constsResolve env &&
  (hyps.map (Expr.substConst0 c annVal)).all
    (fun h => h.constsResolve env) &&
  (Expr.substConst0 c annVal eqE).constsResolve env

/-- Check the pinned certificates of op `c`: per certificate, the
vendored proof (with the op's self-references replaced by the stored
annotated value — the checks run in the *pre-insertion* environment,
exactly like the structural-Nat certification: post-insertion the op's
own just-enabled fast path would participate in checking the very
certificates that justify it) is applied to free variables typed by
the pinned open statement, its type inferred, and compared against the
pinned characteristic equation.  This checks each certificate exactly
like a theorem declaration over an opened telescope — nothing is
installed. -/
def checkDivModCerts (ops : CheckerOps m) (env : Env) (c : Name)
    (annVal : Expr) : List (List Expr × Expr) → List Expr → m Bool
  | [], [] => pure true
  | (hyps, eqE) :: srest, proof :: prest => do
    if divModCertGuard env c annVal hyps eqE proof then
      let appliedA ← ops.annotate env 4
        (divModCertApplied (Expr.substConstAll c annVal proof)
          (hyps.map (Expr.substConst0 c annVal)))
      let tp ← ops.inferType env 4 appliedA
      if ← ops.isDefEq env 4 tp (Expr.substConst0 c annVal eqE) then
        checkDivModCerts ops env c annVal srest prest
      else pure false
    else pure false
  | _, _ => pure false

/-- Environment prerequisites of a certified `Nat.div`/`Nat.mod`:
dependency guard, pinned dependencies, the pinned `Eq` basis (the
certificate statements are equations in the pinned equality), and the
`Bool` constructors stored at the type `Bool` itself (the guards'
`true`/`false` must inhabit the `Bool` value semantically). -/
def divModEnvGuard (env2 : Env) (c : Name) : Bool :=
  natOpGuard env2 c && (natOpDeps c).all (natOpStoredOk env2) &&
  env2.find? eqName == some eqA &&
  (match env2.find? boolTrueName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false) &&
  (match env2.find? boolFalseName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false)

/-- Syntactic guards on the vendored pin (generated; checked once at
install rather than proven about the blob). -/
def divModPinGuard (env : Env) (c : Name) : Bool :=
  (divModDeclPin c).looseBVarsBounded 0 && !(divModDeclPin c).hasFvar &&
  (divModDeclPin c).allLevelParamsDefined [] &&
  (divModDeclPin c).constsResolve env

/-- All certificates' syntactic guards at once.  Checked *before* the
pin comparison and declined on failure: a stream may legitimately stop
short of the constants the vendored proofs mention, which is an
unsupported environment, not an internal inconsistency. -/
def divModCertsGuard (env : Env) (c : Name) (annVal : Expr) : Bool :=
  ((divModCertStmts c).zip (divModCertProofs c)).all
    (fun p => divModCertGuard env c annVal p.1.1 p.1.2 p.2)

/-- The `Nat.div`/`Nat.mod` install gate, run after the ordinary
definition check (`env2` is the already-extended environment, `env`
the pre-insertion one all checks run in): dependency and pinned-`Eq`
guards, then definitional equality of the stored value against the
vendored pin of the toolchain's own helper-unfolded definition —
elaborator drift surfaces as a decline (exit 2), never silently — and
on a match the pinned certificates (`checkDivModCerts`).  A
certificate failure after a pin match is an internal inconsistency
(exit 3). -/
def checkDivModPin (ops : CheckerOps m) (env env2 : Env) (c : Name) :
    m Unit := do
  if divModEnvGuard env2 c then
    match env2.find? c with
    | some (.defnInfo _ value' _) =>
      if divModPinGuard env c && divModCertsGuard env c value' then do
        let pinA ← ops.annotate env 0 (divModDeclPin c)
        let okPin ← ops.isDefEq env 0 value' pinA
        if okPin then do
          let ok ← checkDivModCerts ops env c value'
            (divModCertStmts c) (divModCertProofs c)
          if ok then pure ()
          else throw (.internal
            s!"pinned Nat.div/mod certificate failed after pin match ({c})")
        else throw (.notImplemented
          s!"unsupported Nat.div/mod spelling ({c})")
      else throw (.notImplemented
        s!"unsupported Nat.div/mod spelling ({c}: pin ground constants absent)")
    | _ => throw (.internal s!"Nat.div/mod operation not stored ({c})")
  else throw (.notImplemented
    s!"unsupported Nat.div/mod environment ({c})")

/-- Check a single declaration, extending the environment on success. -/
def checkDecl (ops : CheckerOps m) (env : Env) (d : Declaration) : m Env := do
  match d with
  | .defnDecl cv value hint => do
    let cv ← checkConstantVal ops env cv
    let env2 ← checkDefnVal ops env cv value hint
    -- Structural-Nat pins: the fast-path ops must be the standard
    -- structural recursions — their recurrence equations are checked
    -- by definitional equality here, once, so the literal fast path's
    -- reduction-time certification never fails on an accepted
    -- environment.  A nonstandard definition under one of these names
    -- is positively unsupported.  The equations are certified in the
    -- *pre-insertion* environment with the operation's self-references
    -- replaced by its stored value (see `Setlec/Kernel/Core.lean`:
    -- certifying after insertion would let the operation's own fast
    -- path discharge its all-literal equations vacuously), and the
    -- operation's and its dependencies' stored types are pinned.
    if natOpNames.contains cv.name then
      unless natOpGuard env2 cv.name &&
          (natOpDeps cv.name).all (natOpStoredOk env2) do
        throw (.notImplemented
          s!"nonstandard structural Nat operation environment ({cv.name})")
      match env2.find? cv.name with
      | some (.defnInfo _ value' _) =>
        let ok ← certifyNatEqs ops env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2))
        unless ok do
          throw (.notImplemented
            s!"nonstandard structural Nat operation ({cv.name})")
      | _ => throw (.internal s!"structural Nat operation not stored ({cv.name})")
    -- WF-recursive Nat pins (`Nat.div`/`Nat.mod`): the stored value must
    -- be definitionally equal to the vendored pin of the toolchain's own
    -- (helper-unfolded) definition — elaborator drift surfaces as a
    -- decline (exit 2), never silently.  On a match, the pinned
    -- `Nat.ble`-guarded characterization certificates are checked (in
    -- the pre-insertion environment, self-references substituted; see
    -- `checkDivModCerts`) but not installed; their success is what the
    -- model side consumes for the literal fast path.  A certificate
    -- failure after a pin match is an internal inconsistency (exit 3).
    if natDivModNames.contains cv.name then
      checkDivModPin ops env env2 cv.name
    pure env2
  | .thmDecl cv value =>
    let cv ← checkConstantVal ops env cv
    checkThmVal ops env cv value
  | .opaqueDecl cv value =>
    let cv ← checkConstantVal ops env cv
    checkOpaqueVal ops env cv value
  | .axiomDecl cv => do
    -- Only the two standard axioms the preprocessor's generated routes
    -- use are *installed*, with their types and the shapes of the
    -- inductives they quantify over pinned (up to the exporter's
    -- unstable hygienic binder names); both are true in the set model
    -- (`propext` via the stored `Iff` recursor and extensionality of
    -- propositions, `Classical.choice` via the stored `Nonempty`
    -- recursor and global choice).  The tolerated whitelist
    -- (`toleratedAxiomNames` — `sorryAx` and the `Init` compiler-trust
    -- axioms, user ruling: exactly these) is well-formedness-checked
    -- but not stored; the run continues and the frontend positively
    -- declines any later declaration that references the skipped
    -- axiom.  Any other axiom is a positive decline at its own record;
    -- a *pinned name* with a non-pinned shape likewise (the pin would
    -- otherwise shadow).
    let cvA ← checkConstantVal ops env cv
    if stdAxiomOk env cvA then
      pure ⟨.axiomInfo cvA :: env.consts⟩
    else if cvA.name = propextName ∨ cvA.name = choiceName then
      throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
    else if toleratedAxiomNames.contains cvA.name then
      pure env
    else
      throw (.notImplemented s!"non-standard axiom ({cv.name})")
  | .basisDecl kind => do
    -- Install the pinned (pre-annotated) basis block; the frontend has
    -- already matched the incoming record against the pinned shapes.
    -- The quotient block's types mention the pinned equality former.
    if kind = .quotK then
      unless env.find? eqName = some eqA do
        throw (.notImplemented "quotient basis requires the pinned Eq basis")
    kind.declsA.foldlM installBasisDecl env
  | .indDecl block => checkIndDecl ops env block

/-- Check a list of declarations in order, starting from the empty
environment. -/
def checkDecls (ops : CheckerOps m) (ds : List Declaration) : m Env :=
  ds.foldlM (checkDecl ops) Env.empty

end Setlec
