import ConLeche.Kernel.Inductives.Modeled
import ConLeche.Kernel.TrustAxioms
import ConLeche.Kernel.Inductives.SumInstall
import ConLeche.Kernel.Inductives.NativeInstall

/-!
# The checker

`checkDecl` checks one declaration against the current environment and,
on success, returns the extended environment.  `checkDeclsPure` folds it
over a list of declarations, starting from the empty environment.  The
entry-point records (`CheckerOps` and its instantiations) and the
common `checkConstantVal` live in `ConLeche/Kernel/CheckerBase.lean`;
the modeled-inductive install in `ConLeche/Kernel/Inductives/Modeled.lean`; the
direct simple-structure install in `ConLeche/Kernel/Inductives/StructInstall.lean`.
Verification: `ConLeche.Verify.*` (inversions and claims) and
`ConLeche.Model.*` (the graded model's capstones).
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-- Install one pinned basis declaration (duplicate-checked). -/
def installBasisDecl (env : Env) (ci : ConstantInfo) : m Env := do
  unless (env.find? ci.name).isNone do
    throw (.invalid s!"duplicate declaration {ci.name}")
  pure (⟨ci :: env.consts⟩ : Env)

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
requirement.  The result is stored as an `axiomInfo` — the checked
value is a *realizability witness*, consumed by the model extension
and then discarded: the official kernel's `is_delta` never unfolds an
opaque (unlike theorems, task #66), so storing the value in an
unfoldable kind would be a reduction-strategy superset (it would
e.g. compute `Lean.reduceBool b` where the reference kernels are
stuck; the task-#95 honest limit relies on that stuckness). -/
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
  pure ⟨.axiomInfo cv :: env.consts⟩
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
(`ConLeche/Kernel/NatOpPins.lean`, generated at build time from the toolchain's own
prelude). -/
def divModDeclPin (c : Name) : Expr :=
  if c = natDivName then natDivDeclPin
  else if c = natGcdName then natGcdDeclPin
  else if c = natLandName then natLandDeclPin
  else if c = natLorName then natLorDeclPin
  else if c = natXorName then natXorDeclPin
  else if c = natShiftLeftName then natShiftLeftDeclPin
  else if c = natShiftRightName then natShiftRightDeclPin
  else natModDeclPin

/-- The vendored certificate proof terms of a pin-certified
WF-recursive op (`ConLeche/Kernel/NatOpPins.lean`), one per statement of
`divModCertStmts`. -/
def divModCertProofs (c : Name) : List Expr :=
  if c = natDivName then natDivCertProofs
  else if c = natGcdName then natGcdCertProofs
  else if c = natLandName then natLandCertProofs
  else if c = natLorName then natLorCertProofs
  else if c = natXorName then natXorCertProofs
  else if c = natShiftLeftName then natShiftLeftCertProofs
  else if c = natShiftRightName then natShiftRightCertProofs
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
  let x : Expr := .fvar 0 natTy
  let y : Expr := .fvar 1 natTy
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
    .app (.app proofS (.fvar 0 (.const natName [])))
      (.fvar 1 (.const natName []))
  match hyps with
  | [h1] => .app base (.fvar 2 h1)
  | [h1, h2] =>
    .app (.app base (.fvar 2 h1))
      (.fvar 3 h2)
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

/-- The `Lean.reduceNat`/`Lean.reduceBool` install gate, run after the
ordinary opaque check (`env2` is the already-extended environment,
`env` the pre-insertion one the comparisons run in; `value` the
declaration's raw witness value, annotated again here — the stored
constant is an `axiomInfo`, which carries no value):

* the stored constant must carry the pinned type;
* the witness value must be definitionally equal to the build-time pin
  of the toolchain's own defining expression
  (`ConLeche/Kernel/TrustPins.lean`) — toolchain drift surfaces as a
  decline (exit 2), never silently;
* the *identity certificate*: `value x ≡ x` over an opened `fvar` at
  the element type.  This is what the model consumes
  (`EnvModel.reduce_ops`): with the operation interpreted as the
  identity, the `ofReduce*` axioms' types are trivially inhabited.  A
  certificate failure after the pin matched is an internal
  inconsistency (the pin *is* the identity function). -/
def checkReducePin (ops : CheckerOps m) (env env2 : Env) (c : Name)
    (value : Expr) : m Unit := do
  if reduceStoredOk env2 c && reduceElemOk env c then
    if reducePinGuard env c then do
      let valA ← ops.annotate env 0 value
      let pinA ← ops.annotate env 0 (reduceDeclPin c)
      let okPin ← ops.isDefEq env 0 valA pinA
      if okPin then do
        let x := reduceCertVar c
        let ok ← ops.isDefEq env 1 (.app valA x) x
        if ok then pure ()
        else throw (.internal
          s!"pinned compiler-trust opaque is not the identity ({c})")
      else throw (.notImplemented
        s!"unsupported compiler-trust opaque spelling ({c})")
    else throw (.notImplemented
      s!"unsupported compiler-trust opaque spelling ({c}: pin ground constants absent)")
  else throw (.notImplemented
    s!"unsupported compiler-trust opaque declaration ({c})")

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
    -- replaced by its stored value (see `ConLeche/Kernel/Core.lean`:
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
  | .opaqueDecl cv value => do
    let cv ← checkConstantVal ops env cv
    let env2 ← checkOpaqueVal ops env cv value
    -- Compiler-trust opaques (`Lean.reduceNat`/`Lean.reduceBool`,
    -- task #95): the stored value must be definitionally equal to the
    -- build-time pin of the toolchain's own defining expression — the
    -- gate that lets the `ofReduce*` axioms' identity certificates
    -- never fail on an accepted environment.
    if reduceOpNames.contains cv.name then
      checkReducePin ops env env2 cv.name value
    pure env2
  | .axiomDecl cv => do
    -- Pinned axioms are *installed*: the two standard axioms
    -- (`propext` via the stored `Iff` recursor and extensionality of
    -- propositions, `Classical.choice` via the stored `Nonempty`
    -- recursor and global choice) and the `Init` compiler-trust
    -- family (task #95: `Lean.trustCompiler` as an opaque with value
    -- `True.intro`; `Lean.ofReduceNat`/`Lean.ofReduceBool` over the
    -- pinned identity opaques, trivially true).  All types and the
    -- shapes of the inductives they quantify over are pinned (up to
    -- the exporter's unstable hygienic binder names).  The tolerated
    -- whitelist (`toleratedAxiomNames` — exactly `sorryAx`, user
    -- ruling) is well-formedness-checked but not stored; the run
    -- continues and the frontend positively declines any later
    -- declaration that references the skipped axiom.  Any other axiom
    -- is a positive decline at its own record; a *pinned name* with a
    -- non-pinned shape likewise (the pin would otherwise shadow).
    let cvA ← checkConstantVal ops env cv
    if stdAxiomOk env cvA then
      pure ⟨.axiomInfo cvA :: env.consts⟩
    else if cvA.name = trustCompilerName then
      -- `Lean.trustCompiler : True` is trivially realizable (task
      -- #95): installed exactly like a checked `opaque` with witness
      -- value `True.intro` over the pinned `True` family — the pin
      -- guarantees everything the ordinary opaque check would have
      -- checked for that value, and the model interprets the constant
      -- by `True.intro`'s interpretation.
      if trustCompilerOk env cvA then
        pure ⟨.axiomInfo cvA :: env.consts⟩
      else throw (.notImplemented
        s!"unsupported Lean.trustCompiler shape ({cv.name})")
    else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
      -- The pinned `ofReduce*` axioms (task #95): over the pinned
      -- `Eq` basis, the element inductive and the identity-certified
      -- reduce opaque, `∀ a b, reduce a = b → a = b` interprets to an
      -- inhabited proposition (the hypothesis *is* the conclusion).
      if ofReduceAxOk env cvA then
        pure ⟨.axiomInfo cvA :: env.consts⟩
      else throw (.notImplemented
        s!"unsupported compiler-trust axiom environment ({cv.name})")
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
  | .indDecl block nP =>
    -- TASK #228 — THE DECLARED PARAMETER COUNT, first and for both
    -- routes.  Official reads `nparams` off the declaration and checks
    -- the block against it (`check_inductive_types`' telescope loop,
    -- and the replay's structural comparison of every constructor
    -- record with the generated one); `indParamsOk` is that check,
    -- one-sided, so a `false` is official's own reject.  It runs
    -- BEFORE the dispatch because it is a property of the DECLARATION
    -- and not of a route: the modeled path reaches it too, which is
    -- where a block with no constructor and no recursor record — the
    -- shape neither route recognises — is rejected rather than
    -- declined (arena 047).
    if indParamsOk nP block then
      -- ONE ROUTE (task #210): the fixpoint route takes every block it
      -- RECOGNISES — one type former, one recursor, ordinary,
      -- finitary-recursive or reflexive fields (the structure and sum
      -- routes it replaced were deleted at Part C).  Everything else is
      -- the modeled path's, and its model is the in-process modeller's
      -- (`ConLeche/Frontend/InModel.lean`), whose records precede the
      -- block in the very same parse; `checkModeled` DECLINES, naming the
      -- block, when there is none.  The dispatch is the RECOGNISER alone
      -- (task #219): a mutual or nested block carries several type
      -- formers, resp. several recursors, so `sumSplit` refuses it
      -- outright and no model lookup is needed to route it — which is why
      -- a stream record that happens to be named `T._model` has no effect
      -- on any block.  The module split (`CheckerBase ← Modeled ←
      -- Checker`) is why the dispatch lives here and not inside
      -- `checkModeled`.
      match nativeParts? nP block with
      | some p => checkNative ops env p
      | none => checkModeled mode ops env block
    else throw (.invalid "number of parameters mismatch")

/-- Check a list of declarations in order, starting from the empty
environment. -/
def checkDeclsPure (ops : CheckerOps m) (ds : List Declaration) : m Env :=
  ds.foldlM (checkDecl mode ops) Env.empty

end ConLeche
