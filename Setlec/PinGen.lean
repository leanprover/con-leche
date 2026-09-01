module
public import Lean
public meta import Setlec.Kernel.Expr

/-!
# Elab-time generator for the pinned Nat-operation declarations

This module is the *elab-time* successor of the offline
`scripts/GenDivModPins.lean` generator (task #47): instead of vendoring
generated blobs, the `#gen_natop_pins` command (invoked from
`Setlec/Kernel/NatOpPins.lean`) reads the pin-certified operations from
its **own compiling environment** — the toolchain prelude — at `lake
build` time and splices the pinned definitions into the invoking
module:

* per operation, the *pinned defining expression*: the toolchain's own
  definition value with every local helper (`Nat.modCore`,
  `Nat.div.go`, `._unary` functionals, matchers, …) delta-unfolded and
  every non-stream-prefix definition inlined, so the pin is one closed
  expression over stream-present ground constants.  At install the
  checker compares the stream's definition value against the pin by
  *definitional equality*; mismatch declines.
* per certificate, the *proof blob*: the proof of the corresponding
  theorem from `Setlec/PinGen/Certs.lean`, elaborated against the real
  toolchain prelude and made **self-contained** (task #113): every
  constant outside the operation's own dependency cone (and the
  guard-enforced ground/statement constants) is inlined, with
  beta/projection simplification cleaning up instance sugar — so the
  blobs check against *dependency-sliced* streams, which carry the
  operation's cone but not the surrounding prelude.  A residual that
  cannot be justified this way is a **hard build error**.

The corresponding *certificate statements* stay hand-pinned in
`Setlec/Kernel/Checker.lean` — they are the stable specification
interface; a toolchain bump regenerates pins and proofs, and the
checker does not care as long as the statements still check.

Each operation gets one pinned definition (`…DeclPin : Expr`) and one
certificate-proof list (`…CertProofs : List Expr`), under the same
names the vendored `Setlec/Kernel/DivModPins.lean` used.

The stream-prefix allowlists are extracted by
`scripts/extract_natop_prefix.py` into `scripts/natop_prefix.json`
(embedded below via `include_str`).

Layering: this module (and everything importing it) depends on `Lean`
at *elaboration* time; the definitions it splices mention only
`Setlec.Expr` and friends.  No checker runtime code may call into
`Lean.*` APIs.
-/

public meta section

namespace Setlec.PinGen

open Lean

/-! ## `ToExpr` instances for the checker's expression types -/

def nameT : Lean.Expr := .const ``Setlec.Name []
def levelT : Lean.Expr := .const ``Setlec.Level []
def exprT : Lean.Expr := .const ``Setlec.Expr []

def toExprName : Setlec.Name → Lean.Expr
  | .anonymous => .const ``Setlec.Name.anonymous []
  | .str p s => mkApp2 (.const ``Setlec.Name.str []) (toExprName p) (mkStrLit s)
  | .num p n => mkApp2 (.const ``Setlec.Name.num []) (toExprName p) (mkRawNatLit n)

instance : ToExpr Setlec.Name where
  toExpr := toExprName
  toTypeExpr := nameT

def toExprLevel : Setlec.Level → Lean.Expr
  | .zero => .const ``Setlec.Level.zero []
  | .succ u => .app (.const ``Setlec.Level.succ []) (toExprLevel u)
  | .max u v =>
    mkApp2 (.const ``Setlec.Level.max []) (toExprLevel u) (toExprLevel v)
  | .imax u v =>
    mkApp2 (.const ``Setlec.Level.imax []) (toExprLevel u) (toExprLevel v)
  | .param n => .app (.const ``Setlec.Level.param []) (toExpr n)

instance : ToExpr Setlec.Level where
  toExpr := toExprLevel
  toTypeExpr := levelT

instance : ToExpr Setlec.BinderInfo where
  toExpr
    | .default => .const ``Setlec.BinderInfo.default []
    | .implicit => .const ``Setlec.BinderInfo.implicit []
    | .strictImplicit => .const ``Setlec.BinderInfo.strictImplicit []
    | .instImplicit => .const ``Setlec.BinderInfo.instImplicit []
  toTypeExpr := .const ``Setlec.BinderInfo []

instance : ToExpr Setlec.PropWhen where
  toExpr
    | .never => .const ``Setlec.PropWhen.never []
    | .ifAllZero ps =>
      .app (.const ``Setlec.PropWhen.ifAllZero []) (toExpr ps)
  toTypeExpr := .const ``Setlec.PropWhen []

instance : ToExpr Setlec.BinderMeta where
  toExpr m :=
    .app (.app (.const ``Setlec.BinderMeta.mk []) (toExpr m.bi))
      (toExpr m.pw)
  toTypeExpr := .const ``Setlec.BinderMeta []

instance : ToExpr Setlec.Literal where
  toExpr
    | .natVal n =>
      .app (.const ``Setlec.Literal.natVal []) (mkRawNatLit n)
    | .strVal s =>
      .app (.const ``Setlec.Literal.strVal []) (mkStrLit s)
  toTypeExpr := .const ``Setlec.Literal []

/-- Plain structural `ToExpr` for `Setlec.Expr`.  Fine for small terms
(the pinned statements); the *pins* are emitted through the sharing
builder below, which represents every distinct subobject once. -/
def toExprExpr : Setlec.Expr → Lean.Expr
  | .bvar i => .app (.const ``Setlec.Expr.bvar []) (mkRawNatLit i)
  | .fvar idx n ty =>
    mkApp3 (.const ``Setlec.Expr.fvar []) (mkRawNatLit idx) (toExpr n)
      (toExprExpr ty)
  | .sort u => .app (.const ``Setlec.Expr.sort []) (toExpr u)
  | .const n us =>
    mkApp2 (.const ``Setlec.Expr.const []) (toExpr n) (toExpr us)
  | .app f a => mkApp2 (.const ``Setlec.Expr.app []) (toExprExpr f) (toExprExpr a)
  | .lam n ty b m =>
    mkApp4 (.const ``Setlec.Expr.lam []) (toExpr n) (toExprExpr ty)
      (toExprExpr b) (toExpr m)
  | .forallE n ty b m =>
    mkApp4 (.const ``Setlec.Expr.forallE []) (toExpr n) (toExprExpr ty)
      (toExprExpr b) (toExpr m)
  | .letE n ty v b =>
    mkApp4 (.const ``Setlec.Expr.letE []) (toExpr n) (toExprExpr ty)
      (toExprExpr v) (toExprExpr b)
  | .lit l => .app (.const ``Setlec.Expr.lit []) (toExpr l)
  | .proj s i e =>
    mkApp3 (.const ``Setlec.Expr.proj []) (toExpr s) (mkRawNatLit i)
      (toExprExpr e)

instance : ToExpr Setlec.Expr where
  toExpr := toExprExpr
  toTypeExpr := exprT

/-! ## Conversion `Lean.Expr` → `Setlec.Expr` -/

def toSetlecName : Lean.Name → Setlec.Name := Setlec.Name.ofLeanName

partial def toSetlecLevel : Lean.Level → Except String Setlec.Level
  | .zero => .ok .zero
  | .succ u => .succ <$> toSetlecLevel u
  | .max u v => Setlec.Level.max <$> toSetlecLevel u <*> toSetlecLevel v
  | .imax u v => Setlec.Level.imax <$> toSetlecLevel u <*> toSetlecLevel v
  | .param n => .ok (.param (toSetlecName n))
  | .mvar _ => .error "level mvar"

def toSetlecBI : Lean.BinderInfo → Setlec.BinderInfo
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

/-- Binder names are display-only in the checker; erase hygiene scopes so
the generated pins stay small. -/
def sanitizeBinderName (n : Lean.Name) : Setlec.Name :=
  toSetlecName n.eraseMacroScopes

/-- Conversion; `letE` is zeta-expanded (pins are compared by
definitional equality, and let-free pins keep the pin machinery
independent of the kernel's letE rules), `mdata` stripped, binder
metadata carries only the display info (task #100: annotation-free). -/
partial def toSetlec : Lean.Expr → Except String Setlec.Expr
  | .bvar i => .ok (.bvar i)
  | .sort u => (Setlec.Expr.sort ·) <$> toSetlecLevel u
  | .const c us => do
    .ok (.const (toSetlecName c) (← us.mapM toSetlecLevel))
  | .app f a => Setlec.Expr.app <$> toSetlec f <*> toSetlec a
  | .lam n ty b bi => do
    -- pw: parse-default placeholder at P1; the P2 generator computes
    -- the codomain prop-ness from the host elaborator (task #161)
    .ok (.lam (sanitizeBinderName n) (← toSetlec ty) (← toSetlec b)
      ⟨toSetlecBI bi, .never⟩)
  | .forallE n ty b bi => do
    .ok (.forallE (sanitizeBinderName n) (← toSetlec ty) (← toSetlec b)
      ⟨toSetlecBI bi, .never⟩)
  | .letE _ _ v b _ => toSetlec (b.instantiate1 v)
  | .lit (.natVal n) => .ok (.lit (.natVal n))
  | .lit (.strVal s) => .ok (.lit (.strVal s))
  | .mdata _ e => toSetlec e
  | .proj s i e => (Setlec.Expr.proj (toSetlecName s) i ·) <$> toSetlec e
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
`of_decide_eq_true`, `Nat.log2_terminates`, and the instance
definitions of arithmetic sugar) is inlined; instance-structure
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

The pins share subterms heavily (every distinct name, level and
expression node occurs many times).  Emitting them through the plain
`ToExpr` instance would lose all sharing, so each distinct subobject is
bound once in a `let`-chain: during construction, references are
*absolute* entry indices disguised as `.bvar j`; `assemble` converts
them to proper de Bruijn indices.  (The built constructor applications
contain no real bound variables, so the disguise is unambiguous.) -/

structure ShareSt where
  /-- Emitted let entries: binder name, type, value (with absolute
  `.bvar` entry references). -/
  entries : Array (Lean.Name × Lean.Expr × Lean.Expr) := #[]
  nameMap : Std.HashMap Setlec.Name Lean.Expr := {}
  levelMap : Std.HashMap Setlec.Level Lean.Expr := {}
  exprMap : Std.HashMap Setlec.Expr Lean.Expr := {}

abbrev ShareM := StateM ShareSt

def pushEntry (pfx : String) (ty val : Lean.Expr) :
    ShareM Lean.Expr := do
  let n := (← get).entries.size
  modify fun st =>
    { st with entries := st.entries.push (.mkSimple s!"{pfx}{n}", ty, val) }
  return .bvar n

partial def shareName (n : Setlec.Name) : ShareM Lean.Expr := do
  if let some r := (← get).nameMap[n]? then return r
  let r ← match n with
    | .anonymous => pure (toExpr Setlec.Name.anonymous)
    | .str p s => do
      let pv ← shareName p
      pushEntry "n" nameT (mkApp2 (.const ``Setlec.Name.str []) pv (mkStrLit s))
    | .num p i => do
      let pv ← shareName p
      pushEntry "n" nameT
        (mkApp2 (.const ``Setlec.Name.num []) pv (mkRawNatLit i))
  modify fun st => { st with nameMap := st.nameMap.insert n r }
  return r

partial def shareLevel (l : Setlec.Level) : ShareM Lean.Expr := do
  if let some r := (← get).levelMap[l]? then return r
  let r ← match l with
    | .zero => pure (toExpr Setlec.Level.zero)
    | .succ u => do
      let uv ← shareLevel u
      pushEntry "l" levelT (.app (.const ``Setlec.Level.succ []) uv)
    | .max u w => do
      let uv ← shareLevel u; let wv ← shareLevel w
      pushEntry "l" levelT (mkApp2 (.const ``Setlec.Level.max []) uv wv)
    | .imax u w => do
      let uv ← shareLevel u; let wv ← shareLevel w
      pushEntry "l" levelT (mkApp2 (.const ``Setlec.Level.imax []) uv wv)
    | .param n => do
      let nv ← shareName n
      pushEntry "l" levelT (.app (.const ``Setlec.Level.param []) nv)
  modify fun st => { st with levelMap := st.levelMap.insert l r }
  return r

def levelListE (us : List Lean.Expr) : Lean.Expr :=
  us.foldr (fun u acc => mkApp3 (.const ``List.cons [.zero]) levelT u acc)
    (.app (.const ``List.nil [.zero]) levelT)

partial def shareExpr (e : Setlec.Expr) : ShareM Lean.Expr := do
  if let some r := (← get).exprMap[e]? then return r
  let r ← match e with
    | .bvar i =>
      pushEntry "e" exprT (.app (.const ``Setlec.Expr.bvar []) (mkRawNatLit i))
    | .fvar idx n ty => do
      let nv ← shareName n
      let tv ← shareExpr ty
      pushEntry "e" exprT
        (mkApp3 (.const ``Setlec.Expr.fvar []) (mkRawNatLit idx) nv tv)
    | .sort u => do
      let uv ← shareLevel u
      pushEntry "e" exprT (.app (.const ``Setlec.Expr.sort []) uv)
    | .const n us => do
      let nv ← shareName n
      let uvs ← us.mapM shareLevel
      pushEntry "e" exprT
        (mkApp2 (.const ``Setlec.Expr.const []) nv (levelListE uvs))
    | .app f a => do
      let fv ← shareExpr f
      let av ← shareExpr a
      pushEntry "e" exprT (mkApp2 (.const ``Setlec.Expr.app []) fv av)
    | .lam n ty b m => do
      let nv ← shareName n
      let tv ← shareExpr ty
      let bv ← shareExpr b
      pushEntry "e" exprT
        (mkApp4 (.const ``Setlec.Expr.lam []) nv tv bv (toExpr m))
    | .forallE n ty b m => do
      let nv ← shareName n
      let tv ← shareExpr ty
      let bv ← shareExpr b
      pushEntry "e" exprT
        (mkApp4 (.const ``Setlec.Expr.forallE []) nv tv bv (toExpr m))
    | .letE n ty v b => do
      let nv ← shareName n
      let tv ← shareExpr ty
      let vv ← shareExpr v
      let bv ← shareExpr b
      pushEntry "e" exprT (mkApp4 (.const ``Setlec.Expr.letE []) nv tv vv bv)
    | .lit l =>
      pushEntry "e" exprT (.app (.const ``Setlec.Expr.lit []) (toExpr l))
    | .proj s i x => do
      let sv ← shareName s
      let xv ← shareExpr x
      pushEntry "e" exprT
        (mkApp3 (.const ``Setlec.Expr.proj []) sv (mkRawNatLit i) xv)
  modify fun st => { st with exprMap := st.exprMap.insert e r }
  return r

/-- Convert absolute entry references (`.bvar j`) into de Bruijn indices
for a position under `k` enclosing let binders.  The emitted values are
pure application trees, so only `app` recurses. -/
partial def relat (k : Nat) : Lean.Expr → Lean.Expr
  | .bvar j => .bvar (k - 1 - j)
  | .app f a => .app (relat k f) (relat k a)
  | e => e

/-- Wrap `root` (with absolute references) in the collected `let`-chain. -/
def assemble (entries : Array (Lean.Name × Lean.Expr × Lean.Expr))
    (root : Lean.Expr) : Lean.Expr := Id.run do
  let n := entries.size
  let mut body := relat n root
  for i in [0:n] do
    let k := n - 1 - i
    let (nm, ty, v) := entries[k]!
    body := .letE nm ty (relat k v) body false
  return body

/-- Build the value of a single-expression definition (`… : Expr`) as a
shared `let`-chain. -/
def buildExprValue (e : Setlec.Expr) : Lean.Expr :=
  let (root, st) := Id.run (StateT.run (s := ({} : ShareSt)) (shareExpr e))
  assemble st.entries root

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
  hand-pinned statements (`Setlec/Kernel/Checker.lean`). -/
  certs : List Lean.Name
  /-- Guard-enforced ground operations, mirroring `natOpDeps` in
  `Setlec/Kernel/Core.lean` (`Core` is a classic library, out of reach
  of this `module`): the install's `divModEnvGuard` requires each of
  these stored, so they may stay residual in the certificate proofs
  even outside the operation's own dependency cone. -/
  groundOps : List Lean.Name

def opSpecs : List OpSpec :=
  [{ op := `Nat.mod, pinName := `Setlec.natModDeclPin,
     proofsName := `Setlec.natModCertProofs,
     helperPrefixes := [`Nat.div, `Nat.mod, `Nat.modCore, `Nat.divCore],
     certs := [`Setlec.PinGen.modRecCert, `Setlec.PinGen.modBaseGtCert, `Setlec.PinGen.modBaseZeroCert],
     groundOps := [`Nat.pred, `Nat.sub, `Nat.ble, `Nat.mod] },
   { op := `Nat.div, pinName := `Setlec.natDivDeclPin,
     proofsName := `Setlec.natDivCertProofs,
     helperPrefixes := [`Nat.div, `Nat.mod, `Nat.modCore, `Nat.divCore],
     certs := [`Setlec.PinGen.divRecCert, `Setlec.PinGen.divBaseGtCert, `Setlec.PinGen.divBaseZeroCert],
     groundOps := [`Nat.pred, `Nat.sub, `Nat.ble, `Nat.div] },
   { op := `Nat.gcd, pinName := `Setlec.natGcdDeclPin,
     proofsName := `Setlec.natGcdCertProofs,
     helperPrefixes := [`Nat.gcd],
     certs := [`Setlec.PinGen.gcdRecCert, `Setlec.PinGen.gcdBaseCert],
     groundOps := [`Nat.ble, `Nat.mod, `Nat.gcd] },
   { op := `Nat.shiftLeft, pinName := `Setlec.natShiftLeftDeclPin,
     proofsName := `Setlec.natShiftLeftCertProofs,
     helperPrefixes := [`Nat.shiftLeft],
     certs := [`Setlec.PinGen.shiftLeftRecCert, `Setlec.PinGen.shiftLeftBaseCert],
     groundOps := [`Nat.sub, `Nat.mul, `Nat.ble, `Nat.shiftLeft] },
   { op := `Nat.shiftRight, pinName := `Setlec.natShiftRightDeclPin,
     proofsName := `Setlec.natShiftRightCertProofs,
     helperPrefixes := [`Nat.shiftRight],
     certs := [`Setlec.PinGen.shiftRightRecCert, `Setlec.PinGen.shiftRightBaseCert],
     groundOps := [`Nat.sub, `Nat.ble, `Nat.div, `Nat.shiftRight] },
   { op := `Nat.log2, pinName := `Setlec.natLog2DeclPin,
     proofsName := `Setlec.natLog2CertProofs,
     helperPrefixes := [`Nat.log2],
     certs := [`Setlec.PinGen.log2RecCert, `Setlec.PinGen.log2BaseCert],
     groundOps := [`Nat.ble, `Nat.div, `Nat.log2] },
   { op := `Nat.land, pinName := `Setlec.natLandDeclPin,
     proofsName := `Setlec.natLandCertProofs,
     helperPrefixes := [`Nat.land],
     certs := [`Setlec.PinGen.landRecCert, `Setlec.PinGen.landBaseCert],
     groundOps := [`Nat.add, `Nat.mul, `Nat.ble, `Nat.div, `Nat.mod, `Nat.land] },
   { op := `Nat.lor, pinName := `Setlec.natLorDeclPin,
     proofsName := `Setlec.natLorCertProofs,
     helperPrefixes := [`Nat.lor],
     certs := [`Setlec.PinGen.lorRecCert, `Setlec.PinGen.lorBaseCert],
     groundOps := [`Nat.add, `Nat.sub, `Nat.mul, `Nat.ble, `Nat.div, `Nat.mod, `Nat.lor] },
   { op := `Nat.xor, pinName := `Setlec.natXorDeclPin,
     proofsName := `Setlec.natXorCertProofs,
     helperPrefixes := [`Nat.xor],
     certs := [`Setlec.PinGen.xorRecCert, `Setlec.PinGen.xorBaseCert],
     groundOps := [`Nat.add, `Nat.mul, `Nat.ble, `Nat.div, `Nat.mod, `Nat.xor] }]

/-! ## The generator command -/

/-- The stream-prefix allowlists (`scripts/extract_natop_prefix.py`).
The embed is a static string object in the emitted code — free at
process init. -/
def natopPrefixJson : String :=
  include_str "../scripts/natop_prefix.json"

/-- Parse the stream-prefix allowlists.  Deliberately a *function* (of
the JSON text), not a closed `def`: a 0-ary definition is evaluated in
the module initializer, and this module's object code is linked into
the `setlec` executable via the `meta import` in
`Setlec/Kernel/NatOpPins.lean` — a closed parse of the 1.96 MB embed
cost ~0.26 G instructions at every process start (twice, under the OOM
supervisor re-exec).  As a function it runs only when
`#gen_natop_pins` elaborates, at `lake build` time.  (Closed subterms
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
    MetaM (Setlec.Expr × List Setlec.Expr) := do
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
  let pinS ← match toSetlec pin with
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
  let mut proofsS : List Setlec.Expr := []
  for thmName in spec.certs do
    let some ci := env.find? thmName | throwError "{thmName} missing"
    let some pf := ci.value? (allowOpaque := true) |
      throwError "{thmName} has no value"
    let pf ← inlineCertClosure certAllowed pf
    checkConsts s!"certificate proof {thmName}" certAllowed pf
    match toSetlec pf with
    | .ok e => proofsS := proofsS ++ [e]
    | .error m => throwError "proof conversion ({thmName}): {m}"
  return (pinS, proofsS)

/-- Splice one operation's computed pin and certificate proofs into the
ambient environment (kernel-checked, then compiled).

Each certificate proof becomes its **own** definition
(`…CertProofs_i`), and `…CertProofs` is the shallow list of those
constants: consumers that reduce the *list* structure (the model
bridge's `CertRuns` destructuring in `Setlec/Model/DivModCert.lean`)
then never zeta through the blobs' `let`-chains — the self-contained
blobs of task #113 are deep enough that doing so exceeds the kernel's
recursion depth, and the blobs are meant to stay opaque to the model
anyway. -/
def spliceOp (spec : OpSpec) (pinS : Setlec.Expr)
    (proofsS : List Setlec.Expr) : Elab.TermElabM Unit := do
  let pinDecl := Declaration.defnDecl {
    name := spec.pinName, levelParams := [], type := exprT,
    value := buildExprValue pinS, hints := .abbrev, safety := .safe }
  addDecl pinDecl
  compileDecl pinDecl
  let mut proofConsts : List Lean.Expr := []
  let mut i := 0
  for pf in proofsS do
    let elemName := spec.proofsName.appendAfter s!"_{i}"
    let elemDecl := Declaration.defnDecl {
      name := elemName, levelParams := [], type := exprT,
      value := buildExprValue pf, hints := .abbrev,
      safety := .safe }
    addDecl elemDecl
    compileDecl elemDecl
    proofConsts := proofConsts ++ [.const elemName []]
    i := i + 1
  let proofsDecl := Declaration.defnDecl {
    name := spec.proofsName, levelParams := [],
    type := Lean.Expr.app (.const ``List [.zero]) exprT,
    value := proofConsts.foldr
      (fun p acc => mkApp3 (.const ``List.cons [.zero]) exprT p acc)
      (.app (.const ``List.nil [.zero]) exprT),
    hints := .abbrev, safety := .safe }
  addDecl proofsDecl
  compileDecl proofsDecl

/-- Generate the pin definitions for every operation in `opSpecs`.

The *computation* runs in a dedicated full-view environment
(`importModules` at `OLeanLevel.private`, over the same oleans the
compiling environment was built from): the invoking module is a
`module`, whose ambient environment has imported theorem *proofs*
stripped, and the generator must inline exactly those proofs when it
closes the certificates over the stream prefix.  The *splicing* targets
the ambient environment. -/
elab "#gen_natop_pins" : command => do
  let prefixes ← match loadPrefixes natopPrefixJson with
    | .ok m => pure m
    | .error e => throwError "bad scripts/natop_prefix.json: {e}"
  let genEnv ← importModules (loadExts := false) (level := .private)
    #[{module := `Init}, {module := `Setlec.PinGen.Certs}] {} 0
  let mut results : List (OpSpec × Setlec.Expr × List Setlec.Expr) := []
  let opts ← getOptions
  for spec in opSpecs do
    let (r, _, _) ←
      try
        (computeOp prefixes spec).toIO
          { fileName := "<gen_natop_pins>", fileMap := default,
            options := opts, maxRecDepth := 1000000, maxHeartbeats := 0 }
          { env := genEnv }
      catch e =>
        throwError "pin generation for {spec.op} failed: {e.toMessageData}"
    results := results ++ [(spec, r.1, r.2)]
  Elab.Command.liftTermElabM do
    for (spec, pinS, proofsS) in results do
      spliceOp spec pinS proofsS

/-! ## Compiler-trust pins (task #95)

The pinned defining expressions of the toolchain's `Lean.reduceNat` /
`Lean.reduceBool` opaques (identity functions modulo the
`have := trustCompiler` wrapper, which the conversion's zeta-expansion
removes).  Compared by definitional equality at install
(`checkReducePin`); the model never inspects these blobs. -/

/-- `(toolchain opaque, generated pin name)`. -/
def trustOpSpecs : List (Lean.Name × Lean.Name) :=
  [(`Lean.reduceNat, `Setlec.reduceNatDeclPin),
   (`Lean.reduceBool, `Setlec.reduceBoolDeclPin)]

/-- Read one reduce operation's opaque value from the compiling
environment and convert it. -/
def computeTrustOp (op : Lean.Name) : MetaM Setlec.Expr := do
  let env ← getEnv
  let some ci := env.find? op |
    throwError "{op} is absent from the compiling environment"
  let some v := ci.value? (allowOpaque := true) |
    throwError "{op} has no value in the compiling environment"
  checkConsts s!"trust pin {op}"
    (fun c => c == `Nat || c == `Bool || c == `True ||
      c == `Lean.trustCompiler) v
  match toSetlec v with
  | .ok e => return e
  | .error m => throwError "trust pin conversion ({op}): {m}"

/-- Generate the compiler-trust pins (see `Setlec/Kernel/TrustPins.lean`). -/
elab "#gen_trust_pins" : command => do
  let genEnv ← importModules (loadExts := false) (level := .private)
    #[{module := `Init}] {} 0
  let mut results : List (Lean.Name × Setlec.Expr) := []
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

end Setlec.PinGen
