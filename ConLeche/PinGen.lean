module
public import Lean
public meta import Lech.Kernel.Expr
public meta import Lech.PinGen.Dump

/-!
# The generator for the pinned Nat-operation declarations

This module is the *computation* half of the pin machinery: it reads
the pin-certified operations from a full-view toolchain environment and
produces, per operation, the data the committed dump carries
(`Lech/PinGen/Dump.lean`).  It is the successor of the offline
`scripts/GenDivModPins.lean` generator (task #47) and of the elab-time
`#gen_natop_pins` command (task #53).

**Task #176 moved the splice out of the checker's build.**  Until then
`Lech/Kernel/NatOpPins.lean` invoked `#gen_natop_pins`, which loaded
`Lech/PinGen/Certs.olean` BY NAME (`importModules` at
`OLeanLevel.private` — the only way to see the certificate proofs from
a `module`).  Loading an olean by name is not an import edge, Lake
never ordered the two, and on a cold tree `lake build lech` failed
with "object file '…/Lech/PinGen/Certs.olean' … does not exist".  Per
the user's ruling the pins are now a COMMITTED file written by the
`natop-pins-export` executable (`PinDump.lean`), whose root *imports*
the certificate library; `#gen_natop_pins` is gone and nothing in the
checker's build depends on the certificates any more.  Their trust is
unchanged: they are still kernel-checked theorems, and their proof
terms are still re-checked by this checker at install time against the
hand-pinned statements.

What `computeOp`/`computeDump` produce, per operation:

* per operation, the *pinned defining expression*: the toolchain's own
  definition value with every local helper (`Nat.modCore`,
  `Nat.div.go`, `._unary` functionals, matchers, …) delta-unfolded and
  every non-stream-prefix definition inlined, so the pin is one closed
  expression over stream-present ground constants.  At install the
  checker compares the stream's definition value against the pin by
  *definitional equality*; mismatch declines.
* per certificate, the *proof blob*: the proof of the corresponding
  theorem from `Lech/PinGen/Certs.lean`, elaborated against the real
  toolchain prelude and made **self-contained** (task #113): every
  constant outside the operation's own dependency cone (and the
  guard-enforced ground/statement constants) is inlined, with
  beta/projection simplification cleaning up instance sugar — so the
  blobs check against *dependency-sliced* streams, which carry the
  operation's cone but not the surrounding prelude.  A residual that
  cannot be justified this way is a **hard build error**.

The corresponding *certificate statements* stay hand-pinned in
`Lech/Kernel/Checker.lean` — they are the stable specification
interface; a toolchain bump regenerates pins and proofs, and the
checker does not care as long as the statements still check.

Each operation gets one pinned definition (`…DeclPin : Expr`) and one
certificate-proof list (`…CertProofs : List Expr`), under the same
names the vendored `Lech/Kernel/DivModPins.lean` used.

The stream-prefix allowlists are extracted by
`scripts/extract_natop_prefix.py` into `scripts/natop_prefix.json`
(embedded below via `include_str`).

Layering: this module depends on `Lean`, and since #176 the checker
does not import it at all (`Lech/Kernel/NatOpPins.lean` reaches only
`Lech/PinGen/Dump.lean`, the format module).  Its remaining in-tree
consumers are the generator executable, `Lech/Kernel/TrustPins.lean`
(`#gen_trust_pins`, which reads only the toolchain's `Init` and so
needs no build ordering) and `Lech/Kernel/ZeroSetPin.lean`.  No
checker runtime code may call into `Lean.*` APIs.
-/

public meta section

namespace Lech.PinGen

open Lean

/-! ## `ToExpr` instances for the checker's expression types

`nameT`/`levelT`/`exprT` and the whole share-table emitter now live in
`Lech/PinGen/Dump.lean`, the interchange format the committed dump
and the loader both go through (task #176). -/

def toExprName : Lech.Name → Lean.Expr
  | .anonymous => .const ``Lech.Name.anonymous []
  | .str p s => mkApp2 (.const ``Lech.Name.str []) (toExprName p) (mkStrLit s)
  | .num p n => mkApp2 (.const ``Lech.Name.num []) (toExprName p) (mkRawNatLit n)

instance : ToExpr Lech.Name where
  toExpr := toExprName
  toTypeExpr := nameT

def toExprLevel : Lech.Level → Lean.Expr
  | .zero => .const ``Lech.Level.zero []
  | .succ u => .app (.const ``Lech.Level.succ []) (toExprLevel u)
  | .max u v =>
    mkApp2 (.const ``Lech.Level.max []) (toExprLevel u) (toExprLevel v)
  | .imax u v =>
    mkApp2 (.const ``Lech.Level.imax []) (toExprLevel u) (toExprLevel v)
  | .param n => .app (.const ``Lech.Level.param []) (toExpr n)

instance : ToExpr Lech.Level where
  toExpr := toExprLevel
  toTypeExpr := levelT

instance : ToExpr Lech.PropWhen where
  toExpr pw :=
    match pw.toList? with
    | none => .const ``Lech.PropWhen.never []
    | some ps => .app (.const ``Lech.PropWhen.ifAllZero []) (toExpr ps)
  toTypeExpr := .const ``Lech.PropWhen []

instance : ToExpr Lech.BinderMeta where
  toExpr m := .app (.const ``Lech.BinderMeta.mk []) (toExpr m.pw)
  toTypeExpr := .const ``Lech.BinderMeta []

instance : ToExpr Lech.Literal where
  toExpr
    | .natVal n =>
      .app (.const ``Lech.Literal.natVal []) (mkRawNatLit n)
    | .strVal s =>
      .app (.const ``Lech.Literal.strVal []) (mkStrLit s)
  toTypeExpr := .const ``Lech.Literal []

/-- Plain structural `ToExpr` for `Lech.Expr`.  Fine for small terms
(the pinned statements); the *pins* are emitted through the sharing
builder below, which represents every distinct subobject once. -/
def toExprExpr : Lech.Expr → Lean.Expr
  | .bvar i => .app (.const ``Lech.Expr.bvar []) (mkRawNatLit i)
  | .fvar idx ty =>
    mkApp2 (.const ``Lech.Expr.fvar []) (mkRawNatLit idx) (toExprExpr ty)
  | .sort u => .app (.const ``Lech.Expr.sort []) (toExpr u)
  | .const n us =>
    mkApp2 (.const ``Lech.Expr.const []) (toExpr n) (toExpr us)
  | .app f a => mkApp2 (.const ``Lech.Expr.app []) (toExprExpr f) (toExprExpr a)
  | .lam ty b m =>
    mkApp3 (.const ``Lech.Expr.lam []) (toExprExpr ty) (toExprExpr b) (toExpr m)
  | .forallE ty b m =>
    mkApp3 (.const ``Lech.Expr.forallE []) (toExprExpr ty) (toExprExpr b)
      (toExpr m)
  | .letE ty v b =>
    mkApp3 (.const ``Lech.Expr.letE []) (toExprExpr ty) (toExprExpr v)
      (toExprExpr b)
  | .lit l => .app (.const ``Lech.Expr.lit []) (toExpr l)
  | .proj s i e =>
    mkApp3 (.const ``Lech.Expr.proj []) (toExpr s) (mkRawNatLit i)
      (toExprExpr e)

instance : ToExpr Lech.Expr where
  toExpr := toExprExpr
  toTypeExpr := exprT

/-! ## Conversion `Lean.Expr` → `Lech.Expr` -/

def toLechName : Lean.Name → Lech.Name := Lech.Name.ofLeanName

partial def toLechLevel : Lean.Level → Except String Lech.Level
  | .zero => .ok .zero
  | .succ u => .succ <$> toLechLevel u
  | .max u v => Lech.Level.max <$> toLechLevel u <*> toLechLevel v
  | .imax u v => Lech.Level.imax <$> toLechLevel u <*> toLechLevel v
  | .param n => .ok (.param (toLechName n))
  | .mvar _ => .error "level mvar"

/-- Conversion; `letE` is zeta-expanded (pins are compared by
definitional equality, and let-free pins keep the pin machinery
independent of the kernel's letE rules), `mdata` stripped, binder
metadata carries only the display info (task #100: annotation-free). -/
partial def toLech : Lean.Expr → Except String Lech.Expr
  | .bvar i => .ok (.bvar i)
  | .sort u => (Lech.Expr.sort ·) <$> toLechLevel u
  | .const c us => do
    .ok (.const (toLechName c) (← us.mapM toLechLevel))
  | .app f a => Lech.Expr.app <$> toLech f <*> toLech a
  | .lam _ ty b _ => do
    -- pw: parse-default placeholder at P1; the P2 generator computes
    -- the codomain prop-ness from the host elaborator (task #161);
    -- name and binder info: the checker's single normal form
    -- (`.anonymous`, `.default` — task #203, as the frontend strips
    -- a stream and the pin builder emits the hand-written pins)
    .ok (.lam (← toLech ty) (← toLech b) ⟨.never⟩)
  | .forallE _ ty b _ => do
    .ok (.forallE (← toLech ty) (← toLech b) ⟨.never⟩)
  | .letE _ _ v b _ => toLech (b.instantiate1 v)
  | .lit (.natVal n) => .ok (.lit (.natVal n))
  | .lit (.strVal s) => .ok (.lit (.strVal s))
  | .mdata _ e => toLech e
  | .proj s i e => (Lech.Expr.proj (toLechName s) i ·) <$> toLech e
  | .fvar _ => .error "fvar in closed term"
  | .mvar _ => .error "mvar in closed term"

/-! ## Helper unfolding and prefix-closure inlining -/

/-- One pass of delta-expansion of the constants selected by `p`. -/
def unfoldStep (p : Lean.Name → Bool) (e : Lean.Expr) : CoreM Lean.Expr := do
  let env ← getEnv
  Core.transform e (pre := fun e => do
    let .const c us := e.getAppFn | return .continue
    unless p c do return .continue
    let some ci := env.find? c | return .continue
    let some v := ci.value? (allowOpaque := true) | return .continue
    let v := v.instantiateLevelParams ci.levelParams us
    return .visit (v.beta e.getAppArgs))

partial def unfoldFix (p : Lean.Name → Bool) (e : Lean.Expr) :
    CoreM Lean.Expr := do
  let e' ← unfoldStep p e
  if e' == e then return e else unfoldFix p e'

/-- Collect the constants of an expression. -/
def constsOf (e : Lean.Expr) : NameSet :=
  e.foldConsts {} fun c s => s.insert c

/-- Inline every constant not accepted by `allowed`: theorems and
definitions are replaced by their (level-instantiated) values; anything
else — an inductive, a constructor, a recursor outside the stream
prefix — aborts the build. -/
partial def inlineClosure (allowed : Lean.Name → Bool) (e : Lean.Expr) :
    CoreM Lean.Expr := do
  let env ← getEnv
  let e' ← unfoldStep (fun c => !allowed c) e
  if e' == e then
    -- fixpoint: check nothing un-inlinable remains
    for c in (constsOf e).toList do
      unless allowed c do
        let kind := match env.find? c with
          | some ci =>
            if (ci.value? (allowOpaque := true)).isSome then "has value"
            else "NO VALUE (inductive-kind?)"
          | none => "absent"
        throwError "cannot inline non-prefix constant {c} ({kind})"
    return e
  else inlineClosure allowed e'

/-! ## Self-contained certificate closure (task #113)

The certificate proofs are closed not over a stream-prefix allowlist
(which dependency-*sliced* streams need not respect) but over the
operation's **own dependency cone**: a residual constant must be the
operation itself (substituted away at install), one of the
guard-enforced ground constants (`natOpGuard`/`divModEnvGuard` decline
the install anyway when these are absent), or a member of the
transitive type/value dependency closure of the operation — which
*every* stream declaring the operation necessarily declares first.
Everything else (auxiliary theorems like `funext`, `Eq.subst`,
`of_decide_eq_true`, and the instance definitions of arithmetic
sugar) is inlined; instance-structure
packaging (`HMul.mk` …) additionally reduces away via beta/projection
simplification. -/

/-- The transitive type/value dependency closure of `root`
(inductives contribute their constructor types; recursor and
constructor names resolve through their stored inductive block, so
their presence follows from the inductive's). -/
partial def coneOf (env : Environment) (root : Lean.Name) : NameSet :=
  Id.run do
    let mut seen : NameSet := {}
    let mut work : List Lean.Name := [root]
    while h : work ≠ [] do
      let c := work.head h
      work := work.tail
      if seen.contains c then continue
      seen := seen.insert c
      match env.find? c with
      | none => continue
      | some ci =>
        let mut es := [ci.type]
        if let some v := ci.value? (allowOpaque := true) then es := v :: es
        if let .inductInfo iv := ci then
          for ctor in iv.ctors do
            if let some cci := env.find? ctor then es := cci.type :: es
        for e in es do
          for d in (constsOf e).toList do
            unless seen.contains d do work := d :: work
    return seen

/-- One pass of beta and projection-of-constructor reduction (the
instance sugar `HMul.hMul … instHMul instMulNat a b` reduces to the
ground `Nat.mul a b` once the instance definitions are inlined). -/
def simpStep (e : Lean.Expr) : CoreM Lean.Expr := do
  let env ← getEnv
  Core.transform e (pre := fun e => do
    let eb := e.headBeta
    unless eb == e do return .visit eb
    if let .proj _ i s := e then
      if let .const c _ := s.getAppFn then
        if let some (.ctorInfo cv) := env.find? c then
          let args := s.getAppArgs
          if cv.numParams + i < args.size then
            return .visit args[cv.numParams + i]!
    return .continue)

/-- Certificate-proof closure: inline-and-simplify to fixpoint, then
verify the residuals (`allowed` must justify every remaining
constant). -/
partial def inlineCertClosure (allowed : Lean.Name → Bool)
    (e : Lean.Expr) : CoreM Lean.Expr := do
  let env ← getEnv
  let e' ← unfoldStep (fun c => !allowed c) e
  let e' ← simpStep e'
  if e' == e then
    for c in (constsOf e).toList do
      unless allowed c do
        let kind := match env.find? c with
          | some ci =>
            if (ci.value? (allowOpaque := true)).isSome then "has value"
            else "NO VALUE (inductive-kind?)"
          | none => "absent"
        throwError "certificate residual outside the op's dependency \
          cone: {c} ({kind})"
    return e
  else inlineCertClosure allowed e'

/-- Statement-machinery constants: every certificate install already
requires these stored (`natOpGuard`'s `natLitSupported`,
`divModEnvGuard`'s pinned `Eq` and `Bool` constructors; `.rec`/`.refl`
resolve through the stored inductive blocks), so a stream that lacks
them declines before the proofs are ever consulted. -/
def stmtMachineryNames : List Lean.Name :=
  [`Nat, `Nat.zero, `Nat.succ, `Nat.rec,
   `Bool, `Bool.true, `Bool.false, `Bool.rec,
   `Eq, `Eq.refl, `Eq.rec]

/-- Equation-compiler internals (`.…._f` functionals, `match_i`
matchers) are force-inlined even when they lie in the operation's
*toolchain* dependency cone: the export pipeline beta-inlines the
brecOn functional into the stored `go` values, so the *stream's* cone
of the operation need not declare them (observed: a pure-cone slice of
`init-full-pre` declares `Nat.div.go` but not `Nat.div.go._f`). -/
partial def eqCompilerInternal : Lean.Name → Bool
  | .str p s => s == "_f" || s.startsWith "match_" || eqCompilerInternal p
  | .num p _ => eqCompilerInternal p
  | .anonymous => false

def checkConsts (what : String) (allowed : Lean.Name → Bool)
    (e : Lean.Expr) : CoreM Unit := do
  let bad := (constsOf e).toList.filter (fun c => !allowed c)
  unless bad.isEmpty do
    throwError "{what}: constants outside the allowed prefix: {bad}"

/-! ## The sharing builder

Moved to `Lech/PinGen/Dump.lean` at task #176 — the share table IS
the interchange format, so `ShareSt`/`blobOf`/`buildExprValue` belong
with the entries they build and with the loader that rebuilds them.
-/


/-! ## Operation specifications -/

/-- Name-component prefixes of local helper machinery.  Any *definition*
under one of these (except the public operations themselves) is
delta-unfolded into the pin, so the pin survives helper refactoring in
either the toolchain or the stream. -/
structure OpSpec where
  /-- The pinned operation. -/
  op : Lean.Name
  /-- The generated definitions' names: `pinName : Expr` (the pinned
  defining expression) and `proofsName : List Expr` (the certificate
  proofs). -/
  pinName : Lean.Name
  proofsName : Lean.Name
  /-- Helper-name prefixes to delta-unfold into the pin. -/
  helperPrefixes : List Lean.Name
  /-- Certificate proofs: generator theorem names, in the order of the
  hand-pinned statements (`Lech/Kernel/Checker.lean`). -/
  certs : List Lean.Name
  /-- Guard-enforced ground operations, mirroring `natOpDeps` in
  `Lech/Kernel/Core.lean` (`Core` is a classic library, out of reach
  of this `module`): the install's `divModEnvGuard` requires each of
  these stored, so they may stay residual in the certificate proofs
  even outside the operation's own dependency cone. -/
  groundOps : List Lean.Name

def opSpecs : List OpSpec :=
  [{ op := `Nat.mod, pinName := `Lech.natModDeclPin,
     proofsName := `Lech.natModCertProofs,
     helperPrefixes := [`Nat.div, `Nat.mod, `Nat.modCore, `Nat.divCore],
     certs := [`Lech.PinGen.modRecCert, `Lech.PinGen.modBaseGtCert, `Lech.PinGen.modBaseZeroCert],
     groundOps := [`Nat.pred, `Nat.sub, `Nat.ble, `Nat.mod] },
   { op := `Nat.div, pinName := `Lech.natDivDeclPin,
     proofsName := `Lech.natDivCertProofs,
     helperPrefixes := [`Nat.div, `Nat.mod, `Nat.modCore, `Nat.divCore],
     certs := [`Lech.PinGen.divRecCert, `Lech.PinGen.divBaseGtCert, `Lech.PinGen.divBaseZeroCert],
     groundOps := [`Nat.pred, `Nat.sub, `Nat.ble, `Nat.div] },
   { op := `Nat.gcd, pinName := `Lech.natGcdDeclPin,
     proofsName := `Lech.natGcdCertProofs,
     helperPrefixes := [`Nat.gcd],
     certs := [`Lech.PinGen.gcdRecCert, `Lech.PinGen.gcdBaseCert],
     groundOps := [`Nat.ble, `Nat.mod, `Nat.gcd] },
   { op := `Nat.shiftLeft, pinName := `Lech.natShiftLeftDeclPin,
     proofsName := `Lech.natShiftLeftCertProofs,
     helperPrefixes := [`Nat.shiftLeft],
     certs := [`Lech.PinGen.shiftLeftRecCert, `Lech.PinGen.shiftLeftBaseCert],
     groundOps := [`Nat.sub, `Nat.mul, `Nat.ble, `Nat.shiftLeft] },
   { op := `Nat.shiftRight, pinName := `Lech.natShiftRightDeclPin,
     proofsName := `Lech.natShiftRightCertProofs,
     helperPrefixes := [`Nat.shiftRight],
     certs := [`Lech.PinGen.shiftRightRecCert, `Lech.PinGen.shiftRightBaseCert],
     groundOps := [`Nat.sub, `Nat.ble, `Nat.div, `Nat.shiftRight] },
   { op := `Nat.land, pinName := `Lech.natLandDeclPin,
     proofsName := `Lech.natLandCertProofs,
     helperPrefixes := [`Nat.land],
     certs := [`Lech.PinGen.landRecCert, `Lech.PinGen.landBaseCert],
     groundOps := [`Nat.add, `Nat.mul, `Nat.ble, `Nat.div, `Nat.mod, `Nat.land] },
   { op := `Nat.lor, pinName := `Lech.natLorDeclPin,
     proofsName := `Lech.natLorCertProofs,
     helperPrefixes := [`Nat.lor],
     certs := [`Lech.PinGen.lorRecCert, `Lech.PinGen.lorBaseCert],
     groundOps := [`Nat.add, `Nat.sub, `Nat.mul, `Nat.ble, `Nat.div, `Nat.mod, `Nat.lor] },
   { op := `Nat.xor, pinName := `Lech.natXorDeclPin,
     proofsName := `Lech.natXorCertProofs,
     helperPrefixes := [`Nat.xor],
     certs := [`Lech.PinGen.xorRecCert, `Lech.PinGen.xorBaseCert],
     groundOps := [`Nat.add, `Nat.mul, `Nat.ble, `Nat.div, `Nat.mod, `Nat.xor] }]

/-! ## The generator command -/

/-- The stream-prefix allowlists (`scripts/extract_natop_prefix.py`).
The embed is a static string object in the emitted code — free at
process init. -/
def natopPrefixJson : String :=
  include_str "../scripts/natop_prefix.json"

/-- The repository's pinned toolchain (`lean-toolchain`).  The dump
records it and is *named* after it, so a second toolchain's dump can
sit beside the first (task #176). -/
def toolchainString : String :=
  (include_str "../lean-toolchain").trimAscii.toString

/-- Parse the stream-prefix allowlists.  Deliberately a *function* (of
the JSON text), not a closed `def`: a 0-ary definition is evaluated in
the module initializer, and this module's object code is still linked
into the `lech` executable — through the `meta import` in
`Lech/Kernel/TrustPins.lean` since #176 moved `NatOpPins` off it —
so a closed parse of the 1.96 MB embed would cost ~0.26 G instructions
at every process start (twice, under the OOM supervisor re-exec).  As a
function it runs only when the generator asks, at export time (the
embedded `lean-toolchain` string above is 25 bytes and does not repay
the same treatment).  (Closed subterms
extracted from function bodies are lazy `once`-cells in the emitted
code, so no eager work remains.) -/
def loadPrefixes (json : String) : Except String (Std.HashMap String (List String)) := do
  let j ← Json.parse json
  let o ← j.getObj?
  let mut m : Std.HashMap String (List String) := {}
  for ⟨k, v⟩ in o.toArray do
    let arr ← v.getArr?
    m := m.insert k (arr.toList.filterMap (·.getStr?.toOption))
  return m

def isHelper (env : Environment) (spec : OpSpec) (c : Lean.Name) :
    Bool :=
  c != spec.op &&
  spec.helperPrefixes.any (·.isPrefixOf c) &&
  match env.find? c with
  | some (.defnInfo _) => true
  | _ => false

/-- Compute one operation's pin and certificate proofs from the
compiling environment (no splicing). -/
def computeOp (prefixes : Std.HashMap String (List String)) (spec : OpSpec) :
    MetaM (Lech.Expr × List Lech.Expr) := do
  let env ← getEnv
  let some allowedList := prefixes[spec.op.toString]? |
    throwError "no stream prefix for {spec.op} in scripts/natop_prefix.json"
  let allowedSet : NameSet :=
    allowedList.foldl (fun s n => s.insert n.toName) {}
  let allowed := fun c => allowedSet.contains c
  -- the pinned defining expression: unfold local helpers, then inline
  -- any remaining non-prefix definition (e.g. `and` spelled `Bool.and`
  -- in the stream)
  let some (.defnInfo v) := env.find? spec.op |
    throwError "{spec.op} is not a definition in the compiling environment"
  let pin ← unfoldFix (isHelper env spec) v.value
  let pin ← inlineClosure allowed pin
  checkConsts s!"pin {spec.op}" allowed pin
  let pinS ← match toLech pin with
    | .ok e => pure e
    | .error m => throwError "pin conversion ({spec.op}): {m}"
  -- the certificate proofs, closed over the operation's own
  -- dependency cone (self-contained, task #113): residuals may only
  -- be the op itself, the guard-enforced ground constants, or cone
  -- members — every stream declaring the op declares those first
  let cone := coneOf env spec.op
  let groundSet : NameSet :=
    (spec.groundOps ++ stmtMachineryNames).foldl (·.insert ·) {}
  let certAllowed := fun c =>
    !eqCompilerInternal c &&
    (c == spec.op || groundSet.contains c || cone.contains c)
  let mut proofsS : List Lech.Expr := []
  for thmName in spec.certs do
    let some ci := env.find? thmName | throwError "{thmName} missing"
    let some pf := ci.value? (allowOpaque := true) |
      throwError "{thmName} has no value"
    let pf ← inlineCertClosure certAllowed pf
    checkConsts s!"certificate proof {thmName}" certAllowed pf
    match toLech pf with
    | .ok e => proofsS := proofsS ++ [e]
    | .error m => throwError "proof conversion ({thmName}): {m}"
  return (pinS, proofsS)

/-! ## The dump generator (task #176)

The splice used to happen here, while `Lech/Kernel/NatOpPins.lean`
elaborated, over an environment obtained by loading
`Lech/PinGen/Certs.olean` **by name**.  That is not an import edge,
so Lake never ordered the two and a cold `lake build lech` failed on
a missing `Certs.olean`.  Per the user's ruling the pins are now a
committed file: this module only *computes* them (into the interchange
format of `Lech/PinGen/Dump.lean`), the `natop-pins-export`
executable (`PinDump.lean`) writes them, and the checker-side loader in
`Lech/Kernel/NatOpPins.lean` splices the committed dump with no
dependency on the certificate library at all.

The computation still runs in a dedicated full-view environment
(`importModules` at `OLeanLevel.private`): the certificate module's
theorem *proofs* must be visible, and a `module`'s ambient environment
strips imported proofs. -/

/-- Compute the whole pin dump.  `Lean.initSearchPath` must have run
(the executable's `main` does it); `Lech.PinGen.Certs` is an import
of the generator executable, so Lake has built its olean by the time
this runs. -/
def computeOps : IO (Environment × Array (OpSpec × Lech.Expr × List Lech.Expr)) := do
  let prefixes ← match loadPrefixes natopPrefixJson with
    | .ok m => pure m
    | .error e => throw (IO.userError s!"bad scripts/natop_prefix.json: {e}")
  let genEnv ← importModules (loadExts := false) (level := .private)
    #[{module := `Init}, {module := `Lech.PinGen.Certs}] {} 0
  let mut results : Array (OpSpec × Lech.Expr × List Lech.Expr) := #[]
  for spec in opSpecs do
    let (r, _, _) ←
      try
        (computeOp prefixes spec).toIO
          { fileName := "<natop-pins-export>", fileMap := default,
            options := {}, maxRecDepth := 1000000, maxHeartbeats := 0 }
          { env := genEnv }
      catch e =>
        throw (IO.userError s!"pin generation for {spec.op} failed: {e}")
    results := results.push (spec, r)
  return (genEnv, results)

/-- The dump's per-operation half, from `computeOps`' results.  The
prelude half (task #191) is computed by `Lech/PinGen/Prelude.lean`,
which sits above this module; `computeDumpAndPrelude` there assembles
the whole file. -/
def opDumpsOf (results : Array (OpSpec × Lech.Expr × List Lech.Expr)) :
    Array PinOpDump :=
  results.map fun (spec, pin, proofs) => {
    op := spec.op.toString
    pinName := spec.pinName.toString
    proofsName := spec.proofsName.toString
    pin := blobOf pin
    proofs := (proofs.map blobOf).toArray }


/-! ## Compiler-trust pins (task #95)

The pinned defining expressions of the toolchain's `Lean.reduceNat` /
`Lean.reduceBool` opaques (identity functions modulo the
`have := trustCompiler` wrapper, which the conversion's zeta-expansion
removes).  Compared by definitional equality at install
(`checkReducePin`); the model never inspects these blobs. -/

/-- `(toolchain opaque, generated pin name)`. -/
def trustOpSpecs : List (Lean.Name × Lean.Name) :=
  [(`Lean.reduceNat, `Lech.reduceNatDeclPin),
   (`Lean.reduceBool, `Lech.reduceBoolDeclPin)]

/-- Read one reduce operation's opaque value from the compiling
environment and convert it. -/
def computeTrustOp (op : Lean.Name) : MetaM Lech.Expr := do
  let env ← getEnv
  let some ci := env.find? op |
    throwError "{op} is absent from the compiling environment"
  let some v := ci.value? (allowOpaque := true) |
    throwError "{op} has no value in the compiling environment"
  checkConsts s!"trust pin {op}"
    (fun c => c == `Nat || c == `Bool || c == `True ||
      c == `Lean.trustCompiler) v
  match toLech v with
  | .ok e => return e
  | .error m => throwError "trust pin conversion ({op}): {m}"

/-- Generate the compiler-trust pins (see `Lech/Kernel/TrustPins.lean`). -/
elab "#gen_trust_pins" : command => do
  let genEnv ← importModules (loadExts := false) (level := .private)
    #[{module := `Init}] {} 0
  let mut results : List (Lean.Name × Lech.Expr) := []
  let opts ← getOptions
  for (op, pinName) in trustOpSpecs do
    let (r, _, _) ←
      try
        (computeTrustOp op).toIO
          { fileName := "<gen_trust_pins>", fileMap := default,
            options := opts, maxRecDepth := 1000000, maxHeartbeats := 0 }
          { env := genEnv }
      catch e =>
        throwError "trust pin generation for {op} failed: {e.toMessageData}"
    results := results ++ [(pinName, r)]
  Elab.Command.liftTermElabM do
    for (pinName, pinS) in results do
      let pinDecl := Declaration.defnDecl {
        name := pinName, levelParams := [], type := exprT,
        value := buildExprValue pinS, hints := .abbrev, safety := .safe }
      addDecl pinDecl
      compileDecl pinDecl

end Lech.PinGen
