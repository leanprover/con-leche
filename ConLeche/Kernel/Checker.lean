module

public import ConLeche.Kernel.Inductives.BlockInstall

@[expose] public section

/-!
# The checker

The stages `checkDecl` (`ConLeche/Kernel/CheckDecl.lean`) dispatches to:
the value checks, the basis installs, the certified `Nat` operations.  The
entry-point records (`CheckerOps` and its instantiations) and the
common `checkConstantVal` live in `ConLeche/Kernel/CheckerBase.lean`; the
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
  pure (⟨ci :: env.consts, env.tables⟩ : Env)

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
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (unresolvedConstsErrorL (strLitSupported env) s!"value of {cv.name}" value)
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in definition {cv.name}")
  pure ⟨.defnInfo cv value hint :: env.consts, env.tables⟩

/-- Check a `theorem` declaration's value against its checked constant
(whose type must additionally be a proposition).  **A theorem is
stored by its statement only**: `thmInfo` carries no value — a theorem
is opaque to reduction (`unfoldDefinition` has no `thmInfo` arm), and
the checked value is a *realizability witness*, checked against the
statement and then discarded, exactly as an opaque's is: the result
environment does not mention `value`, so nothing downstream can read a
proof term.  This is what lets the driver install a theorem before its
value is looked at at all (phase A pushes the statement; phase B
checks the value from the pending record,
`ConLeche/Cached/Installed.lean`). -/
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
  let jv := value
  unless jv.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless jv.constsResolve env do
    throw (unresolvedConstsErrorL (strLitSupported env) s!"value of {cv.name}" jv)
  let vtype ← ops.inferType env 0 jv
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in theorem {cv.name}")
  pure ⟨.thmInfo cv :: env.consts, env.tables⟩

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
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (unresolvedConstsErrorL (strLitSupported env) s!"value of {cv.name}" value)
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in opaque {cv.name}")
  pure ⟨.axiomInfo cv :: env.consts, env.tables⟩
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
in one **pin variant** (`ConLeche/Kernel/NatOpPinSet.lean`: one
toolchain's generated pins, `ConLeche/Kernel/NatOpPins.lean` splices one
per committed dump). -/
def divModDeclPin (ps : NatOpPinSet) (c : Name) : Expr :=
  if c = natDivName then ps.divPin
  else if c = natGcdName then ps.gcdPin
  else if c = natLandName then ps.landPin
  else if c = natLorName then ps.lorPin
  else if c = natXorName then ps.xorPin
  else if c = natShiftLeftName then ps.shiftLeftPin
  else if c = natShiftRightName then ps.shiftRightPin
  else ps.modPin

/-- The certificate proof terms of a pin-certified WF-recursive op in
one pin variant, one per statement of `divModCertStmts`. -/
def divModCertProofs (ps : NatOpPinSet) (c : Name) : List Expr :=
  if c = natDivName then ps.divProofs
  else if c = natGcdName then ps.gcdProofs
  else if c = natLandName then ps.landProofs
  else if c = natLorName then ps.lorProofs
  else if c = natXorName then ps.xorProofs
  else if c = natShiftLeftName then ps.shiftLeftProofs
  else if c = natShiftRightName then ps.shiftRightProofs
  else ps.modProofs

/-- The type pins of a pin-certified WF-recursive op in one pin variant
(task #364): the constants its certificates use whose types differ
between supported toolchains, each with its type in this variant's
toolchain. -/
def divModTypePins (ps : NatOpPinSet) (c : Name) : List (Name × Expr) :=
  if c = natDivName then ps.divTypePins
  else if c = natGcdName then ps.gcdTypePins
  else if c = natLandName then ps.landTypePins
  else if c = natLorName then ps.lorTypePins
  else if c = natXorName then ps.xorTypePins
  else if c = natShiftLeftName then ps.shiftLeftTypePins
  else if c = natShiftRightName then ps.shiftRightTypePins
  else ps.modTypePins

/-- The stored type a type pin is compared against: the constant's type
in the environment.  An absent constant gives `Sort 0`, which nothing
is compared against: the guard (`divModPinGuard`) requires every
type-pinned constant present. -/
def typePinStored (env : Env) (n : Name) : Expr :=
  match env.find? n with
  | some ci => ci.toConstantVal.type
  | none => .sort .zero

/-- The pinned characterization statements of a pin-certified
WF-recursive op, in *open* form over `x := fvar 0`, `y := fvar 1` (the
hypotheses become `fvar 2, fvar 3`): per certificate, the list of
hypothesis types and the characteristic equation `Eq Nat lhs rhs`.
The guards are spelled with the already-certified `Nat.ble` (never the
`Nat.le`/`Nat.lt` `Prop` inductives) and the numeral `1` as
`Nat.succ Nat.zero`, so the model side consumes them through the
existing `NatOps` literal semantics for `ble`/`sub`.  The op's
self-reference is `.const c []`, substituted with the stored
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
value — the checks run in the *pre-insertion* environment,
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
      let appliedA :=
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
  (env2.find? eqName).isSome &&
  (match env2.find? boolTrueName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false) &&
  (match env2.find? boolFalseName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false)

/-- Syntactic guards on one variant's pin (generated; checked once at
install rather than proven about the blob), and on its type pins: each
type-pinned constant stored with a closed type, each pinned type closed
over constants the stream declares. -/
def divModPinGuard (ps : NatOpPinSet) (env : Env) (c : Name) : Bool :=
  (divModDeclPin ps c).looseBVarsBounded 0 && !(divModDeclPin ps c).hasFvar &&
  (divModDeclPin ps c).allLevelParamsDefined [] &&
  (divModDeclPin ps c).constsResolve env &&
  (divModTypePins ps c).all fun p =>
    (env.find? p.1).isSome && !(typePinStored env p.1).hasFvar &&
    p.2.looseBVarsBounded 0 && !p.2.hasFvar && p.2.constsResolve env

/-- All of one variant's certificates' syntactic guards at once.
Checked *before* the pin comparison; a failure moves on to the next
variant: a stream may legitimately stop short of the constants a
variant's proofs mention. -/
def divModCertsGuard (ps : NatOpPinSet) (env : Env) (c : Name)
    (annVal : Expr) : Bool :=
  ((divModCertStmts c).zip (divModCertProofs ps c)).all
    (fun p => divModCertGuard env c annVal p.1.1 p.1.2 p.2)

/-- The type pins (task #364): each type-pinned constant's stored type
against the variant's pinned one, by definitional equality. -/
def checkTypePins (ops : CheckerOps m) (env : Env) :
    List (Name × Expr) → m Bool
  | [] => pure true
  | p :: rest => do
    if ← ops.isDefEq env 0 (typePinStored env p.1) p.2 then
      checkTypePins ops env rest
    else pure false

/-- **One pin variant's attempt** (task #273): the variant's type pins
(`checkTypePins`), then the stored value against the variant's pin by
definitional equality, and on a match the variant's certificates
(`checkDivModCerts`).  `true` = matched, the fast path is justified;
`false` = a type pin or the pin is not definitionally equal, or a
certificate did not check.

**The type pins come first** (task #364).  The value pin alone cannot
tell toolchains apart where the certificates differ: the pins mention
`ite`/`dite`/`Nat.decLe` BY NAME, so a stream of one toolchain can
match another's pin while that variant's certificate blobs are
ill-typed against it (the v4.33.0 blobs eliminate `Decidable` with
two minor premises; since lean4 master made it a structure it has
one).  The type pins compare the types of exactly the constants whose
types differ between supported toolchains, so on every supported
stream a foreign variant fails here by a boolean `false` and its
certificates are never inferred.  A certificate that still throws is
an error of the run, not a variant mismatch: nothing recovers from it. -/
def checkDivModPinAt (ops : CheckerOps m) (env : Env) (c : Name)
    (value' : Expr) (ps : NatOpPinSet) : m Bool := do
  if ← checkTypePins ops env (divModTypePins ps c) then
    let pinA := (divModDeclPin ps c)
    let okPin ← ops.isDefEq env 0 value' pinA
    if okPin then
      checkDivModCerts ops env c value' (divModCertStmts c)
        (divModCertProofs ps c)
    else pure false
  else pure false

/-- What a variant whose guards passed failed on, for the decline
message. -/
def divModAttemptReason (ps : NatOpPinSet) : String :=
  s!"{ps.toolchain}: a type pin or the pin not definitionally equal, or \
    a certificate failed"

/-- **The variant loop**: the first variant whose guards pass and whose
attempt succeeds enables the fast path; every other outcome moves on
to the next variant, and when none is left the stream DECLINES with
the per-variant reasons (`scripts/diagnose_natop_prefix.py` explains a
"ground constants absent" entry).  Every step is a boolean decision:
the guards, then the attempt's `true`/`false` (`checkDivModPinAt`). -/
def checkDivModPinLoop (ops : CheckerOps m) (env : Env) (c : Name)
    (value' : Expr) : List NatOpPinSet → List String → m Unit
  | [], tried =>
    throw (.notImplemented s!"unsupported Nat.div/mod spelling ({c}: no \
      pin variant matched — {String.intercalate "; " tried})")
  | ps :: rest, tried =>
    if divModPinGuard ps env c && divModCertsGuard ps env c value' then do
      if ← checkDivModPinAt ops env c value' ps then pure ()
      else
        checkDivModPinLoop ops env c value' rest
          (tried ++ [divModAttemptReason ps])
    else
      checkDivModPinLoop ops env c value' rest
        (tried ++ [s!"{ps.toolchain}: pin or certificate ground constants \
          absent"])

/-- The pin-certified operations' install gate, run after the ordinary
definition check (`env2` is the already-extended environment, `env`
the pre-insertion one all checks run in): the dependency and
pinned-`Eq` guards, then the pin variants in `pins` order
(`checkDivModPinLoop`) — each variant's type pins (`checkTypePins`),
then the stored value against the variant's pin of its toolchain's own
helper-unfolded definition by definitional equality, and on a match
that variant's certificates (`checkDivModCerts`).  No variant matching is a decline (exit 2),
never a silent accept; the operation's literal fast path is enabled
exactly when a variant's certificates checked in this run.

**The variant list is a parameter** (task #304): every function from
here up to the fold takes it, and the shipped checker passes
`natOpPinSets` — so a statement about the checker can be made for an
arbitrary list, which is what the pin list being data rather than a
constant buys.  The parameter sits right after `ops` (the "how to
check" arguments) all the way up, and right after `mode` in the cached
driver. -/
def checkDivModPin (ops : CheckerOps m) (pins : List NatOpPinSet)
    (env env2 : Env) (c : Name) : m Unit := do
  if divModEnvGuard env2 c then
    match env2.find? c with
    | some (.defnInfo _ value' _) =>
      checkDivModPinLoop ops env c value' pins []
    | _ => throw (.internal s!"Nat.div/mod operation not stored ({c})")
  else throw (.notImplemented
    s!"unsupported Nat.div/mod environment ({c})")

/-- The `Lean.reduceNat`/`Lean.reduceBool` install gate, run after the
ordinary opaque check (`env2` is the already-extended environment,
`env` the pre-insertion one the comparisons run in; `value` the
declaration's witness value, checked again here — the stored
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
      let valA := value
      let pinA := (reduceDeclPin c)
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

/-- **A pinned block's check and install**: the records compared with
the pin, and each pin installed at the names its record declares.  A
block with a pinned block's names that is not the pin is invalid input
(a basis redefinition). -/
def checkBasisBlock (env : Env) (kind : BasisKind) (block : List ConstantInfo) : m Env := do
  unless pinListOk block kind.decls do
    throw (.invalid "reserved basis name: the block is not the pinned one")
  (kind.atBlock block).foldlM installBasisDecl env

/-- **A quotient record's check and install**: compared with its slot's
pin, the slots it needs stored, and installed at its own names.  A record
that does not match is a quotient this checker positively does not
support. -/
def checkQuotRecord (env : Env) (k : QuotKind) (cv : ConstantVal) : m Env := do
  unless quotPinHit k cv do
    throw (.notImplemented (match k with
      | .sound => "quotient soundness axiom mismatch"
      | _ => "quotient declaration mismatch"))
  unless quotPredsOk env.find? k cv.levelParams do
    throw (.notImplemented "quotient declaration before what it needs")
  installBasisDecl env (quotAt k cv)

end ConLeche
