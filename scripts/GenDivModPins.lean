/-
# Generator for the pinned `Nat.div`/`Nat.mod` declarations and their
characterization certificates (dev-time only; NOT part of the checker build).

Run with:

    lake env lean --run scripts/GenDivModPins.lean

(after `python3 scripts/extract_divmod_prefix.py <stream> scripts/divmod_prefix.json`).

It produces `Setlec/Kernel/DivModPins.lean`, containing per operation

* the *pinned defining expression*: the toolchain's own definition value with
  every local helper (`Nat.modCore`, `Nat.modCore.go`, `Nat.div.go`, matchers,
  `._f` functionals, …) delta-unfolded away, so the pin is one closed
  expression over stream-universal ground constants.  At install the checker
  compares the stream's definition value against this pin by *definitional
  equality* (robust to helper factoring/naming drift); mismatch declines.
* the *certificate* statements and proofs: `Nat.ble`-guarded recurrence
  characterizations of the pinned operation, elaborated against the real
  toolchain prelude and closed over the stream prefix by inlining every
  constant that does not exist in the stream before the operation
  (theorems/definitions are inlined by their values; a non-prefix *inductive*
  aborts generation).  The checker CHECKS these like theorem declarations at
  install (but does not install them); their success is what justifies the
  literal fast path semantically.

The generator fails loudly if a pin or certificate mentions a constant
outside the stream prefix (plus the operation itself).
-/
import Lean
import Setlec.Kernel.Expr

set_option Elab.async false

open Lean Meta

/-! ## The certificate theorems

Elaborated against the ambient (toolchain) prelude, where `Nat.div`/`Nat.mod`
are the real operations.  The *statements* fix the pinned spellings: guards
via the already-certified `Nat.ble` (never `Nat.le`/`Nat.lt` Prop inductives),
numerals via `Nat.succ`/`Nat.zero` (never `OfNat`), so the model-side
consumption rides the existing `NatOpsOk` literal semantics for `ble`/`sub`.
-/

section CertProofs

/- Support lemmas, proved with *controlled* dependencies: no `simp`, no
`decide` — the core lemmas (`Nat.mod_eq` …) are proved with simp steps
whose terms mention `eq_true`/`and_self` and hence `Iff`/`propext`, which
do not exist in the stream before `Nat.mod`.  Everything below reduces to
`Eq`-rewriting, `Nat`/`Decidable` case analysis, and prefix-present
arithmetic lemmas. -/

/-- One-step unfolding of the fuel-recursive worker (the auto-generated
`eq_def`, coerced through the definitional match reduction at `succ`). -/
private theorem divGoStep (y : Nat) (hy : 0 < y) (f x : Nat)
    (h : x < Nat.succ f) :
    Nat.div.go y hy (Nat.succ f) x h =
      dite (y ≤ x)
        (fun hle => Nat.succ (Nat.div.go y hy f (x - y)
          (Nat.div_rec_fuel_lemma hy hle h)))
        (fun _ => 0) :=
  Nat.div.go.eq_def y hy (Nat.succ f) x h

private theorem modGoStep (y : Nat) (hy : 0 < y) (f x : Nat)
    (h : x < Nat.succ f) :
    Nat.modCore.go y hy (Nat.succ f) x h =
      dite (y ≤ x)
        (fun hle => Nat.modCore.go y hy f (x - y)
          (Nat.div_rec_fuel_lemma hy hle h))
        (fun _ => x) :=
  Nat.modCore.go.eq_def y hy (Nat.succ f) x h

private theorem divGoFuelCongr (y : Nat) (hy : 0 < y) :
    ∀ (f1 x : Nat) (h1 : x < f1) (f2 : Nat) (h2 : x < f2),
      Nat.div.go y hy f1 x h1 = Nat.div.go y hy f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro x h1 f2 h2; exact absurd h1 (Nat.not_succ_le_zero x)
  | succ f1 ih =>
    intro x h1 f2 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_succ_le_zero x)
    | succ f2 =>
      rw [divGoStep, divGoStep]
      match Nat.decLe y x with
      | .isTrue hle =>
        rw [dif_pos hle, dif_pos hle]
        exact congrArg Nat.succ (ih _ _ _ _)
      | .isFalse hnle => rw [dif_neg hnle, dif_neg hnle]

private theorem modGoFuelCongr (y : Nat) (hy : 0 < y) :
    ∀ (f1 x : Nat) (h1 : x < f1) (f2 : Nat) (h2 : x < f2),
      Nat.modCore.go y hy f1 x h1 = Nat.modCore.go y hy f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro x h1 f2 h2; exact absurd h1 (Nat.not_succ_le_zero x)
  | succ f1 ih =>
    intro x h1 f2 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_succ_le_zero x)
    | succ f2 =>
      rw [modGoStep, modGoStep]
      match Nat.decLe y x with
      | .isTrue hle =>
        rw [dif_pos hle, dif_pos hle]
        exact ih _ _ _ _
      | .isFalse hnle => rw [dif_neg hnle, dif_neg hnle]

/-- The dispatcher, unfolded (the auto-generated `eq_def`). -/
private theorem divUnfold (x y : Nat) :
    Nat.div x y =
      dite (0 < y)
        (fun hy => Nat.div.go y hy (Nat.succ x) x (Nat.lt_succ_self x))
        (fun _ => Nat.zero) :=
  Nat.div.eq_def x y

private theorem modCoreUnfold (x y : Nat) :
    Nat.modCore x y =
      dite (0 < y)
        (fun hy => Nat.modCore.go y hy (Nat.succ x) x (Nat.lt_succ_self x))
        (fun _ => x) :=
  Nat.modCore.eq_def x y

/-- `Nat.mod` agrees with `Nat.modCore` (the dispatcher's `x`-match and
`≤`-test collapse against `modCore`'s own tests). -/
private theorem modEqModCore (x y : Nat) (hy : 0 < y) :
    Nat.mod x y = Nat.modCore x y := by
  cases x with
  | zero =>
    show Nat.zero = Nat.modCore Nat.zero y
    rw [modCoreUnfold, dif_pos hy, modGoStep,
      dif_neg (fun hle => absurd (Nat.lt_of_lt_of_le hy hle) (Nat.lt_irrefl Nat.zero))]
  | succ n =>
    show ite (y ≤ Nat.succ n) (Nat.modCore (Nat.succ n) y) (Nat.succ n) = _
    match Nat.decLe y (Nat.succ n) with
    | .isTrue hle => rw [if_pos hle]
    | .isFalse hnle =>
      rw [if_neg hnle, modCoreUnfold, dif_pos hy, modGoStep, dif_neg hnle]

end CertProofs

/-! The six certificate theorems proper. -/

theorem modRecCert : ∀ (x y : Nat), Nat.ble y x = Bool.true →
    Nat.ble (Nat.succ Nat.zero) y = Bool.true →
    Nat.mod x y = Nat.mod (Nat.sub x y) y := by
  intro x y hyx h1y
  have hy : 0 < y := Nat.le_of_ble_eq_true h1y
  have hxy : y ≤ x := Nat.le_of_ble_eq_true hyx
  rw [modEqModCore x y hy, modEqModCore (Nat.sub x y) y hy,
    modCoreUnfold, modCoreUnfold, dif_pos hy, dif_pos hy,
    modGoStep, dif_pos hxy]
  exact modGoFuelCongr y hy _ _ _ _ _

theorem modBaseGtCert : ∀ (x y : Nat), Nat.ble y x = Bool.false →
    Nat.mod x y = x := by
  intro x y hf
  have hnle : ¬ (y ≤ x) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  cases x with
  | zero => rfl
  | succ n =>
    show ite (y ≤ Nat.succ n) (Nat.modCore (Nat.succ n) y) (Nat.succ n) = _
    rw [if_neg hnle]

theorem modBaseZeroCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.false →
    Nat.mod x y = x := by
  intro x y hf
  have hny : ¬ (0 < y) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  cases x with
  | zero => rfl
  | succ n =>
    show ite (y ≤ Nat.succ n) (Nat.modCore (Nat.succ n) y) (Nat.succ n) = _
    match Nat.decLe y (Nat.succ n) with
    | .isTrue hle => rw [if_pos hle, modCoreUnfold, dif_neg hny]
    | .isFalse hnle => rw [if_neg hnle]

theorem divRecCert : ∀ (x y : Nat), Nat.ble y x = Bool.true →
    Nat.ble (Nat.succ Nat.zero) y = Bool.true →
    Nat.div x y = Nat.succ (Nat.div (Nat.sub x y) y) := by
  intro x y hyx h1y
  have hy : 0 < y := Nat.le_of_ble_eq_true h1y
  have hxy : y ≤ x := Nat.le_of_ble_eq_true hyx
  rw [divUnfold, divUnfold, dif_pos hy, dif_pos hy, divGoStep, dif_pos hxy]
  exact congrArg Nat.succ (divGoFuelCongr y hy _ _ _ _ _)

theorem divBaseGtCert : ∀ (x y : Nat), Nat.ble y x = Bool.false →
    Nat.div x y = Nat.zero := by
  intro x y hf
  have hnle : ¬ (y ≤ x) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  rw [divUnfold]
  match Nat.decLt 0 y with
  | .isTrue hy => rw [dif_pos hy, divGoStep, dif_neg hnle]
  | .isFalse hny => rw [dif_neg hny]

theorem divBaseZeroCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.false →
    Nat.div x y = Nat.zero := by
  intro x y hf
  have hny : ¬ (0 < y) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  rw [divUnfold, dif_neg hny]

/-! ## Helper unfolding and prefix-closure inlining -/

/-- The public operations themselves (never unfolded in the pin). -/
def publicOps : List Name := [`Nat.div, `Nat.mod]

/-- Name-component prefixes of local helper machinery.  Any *definition*
under one of these (except the public ops) is delta-unfolded into the pin,
so the pin survives helper refactoring in either the toolchain or the
stream. -/
def helperPrefixes : List Name :=
  [`Nat.div, `Nat.mod, `Nat.modCore, `Nat.divCore]

def isHelper (env : Environment) (c : Name) : Bool :=
  !publicOps.contains c &&
  helperPrefixes.any (·.isPrefixOf c) &&
  match env.find? c with
  | some (.defnInfo _) => true
  | _ => false

/-- One pass of helper delta-expansion. -/
def unfoldStep (p : Name → Bool) (e : Expr) : CoreM Expr := do
  let env ← getEnv
  Core.transform e (pre := fun e => do
    let .const c us := e.getAppFn | return .continue
    unless p c do return .continue
    let some ci := env.find? c | return .continue
    let some v := ci.value? (allowOpaque := true) | return .continue
    let v := v.instantiateLevelParams ci.levelParams us
    return .visit (v.beta e.getAppArgs))

partial def unfoldFix (p : Name → Bool) (e : Expr) : CoreM Expr := do
  let e' ← unfoldStep p e
  if e' == e then return e else unfoldFix p e'

/-- Collect the constants of an expression. -/
def constsOf (e : Expr) : NameSet :=
  e.foldConsts {} fun c s => s.insert c

/-- Inline every constant not in `allowed`: theorems and definitions are
replaced by their (level-instantiated) values; anything else aborts. -/
partial def inlineClosure (allowed : Name → Bool) (e : Expr) : CoreM Expr := do
  let env ← getEnv
  let e' ← unfoldStep (fun c => !allowed c) e
  if e' == e then
    -- fixpoint: check nothing un-inlinable remains
    for c in (constsOf e).toList do
      unless allowed c do
        let kind := match env.find? c with
          | some ci => if (ci.value? (allowOpaque := true)).isSome then "has value" else "NO VALUE (inductive-kind?)"
          | none => "absent"
        throwError "cannot inline non-prefix constant {c} ({kind})"
    return e
  else inlineClosure allowed e'

/-! ## Conversion `Lean.Expr` → `Setlec.Expr` -/

def toSetlecName : Name → Setlec.Name := Setlec.Name.ofLeanName

partial def toSetlecLevel : Level → Except String Setlec.Level
  | .zero => .ok .zero
  | .succ u => .succ <$> toSetlecLevel u
  | .max u v => Setlec.Level.max <$> toSetlecLevel u <*> toSetlecLevel v
  | .imax u v => Setlec.Level.imax <$> toSetlecLevel u <*> toSetlecLevel v
  | .param n => .ok (.param (toSetlecName n))
  | .mvar _ => .error "level mvar"

def toSetlecBI : BinderInfo → Setlec.BinderInfo
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

/-- Binder names are display-only in the checker; erase hygiene scopes so
the vendored pins stay readable and small. -/
def sanitizeBinderName (n : Name) : Setlec.Name :=
  toSetlecName n.eraseMacroScopes

/-- Conversion; `letE` is zeta-expanded (the checker frontend does the
same), `mdata` stripped, binder metadata carries `cod := none` (the raw
form: the checker's annotation pass computes the codomain sorts). -/
partial def toSetlec : Expr → Except String Setlec.Expr
  | .bvar i => .ok (.bvar i)
  | .sort u => (Setlec.Expr.sort ·) <$> toSetlecLevel u
  | .const c us => do
    .ok (.const (toSetlecName c) (← us.mapM toSetlecLevel))
  | .app f a => Setlec.Expr.app <$> toSetlec f <*> toSetlec a
  | .lam n ty b bi => do
    .ok (.lam (sanitizeBinderName n) (← toSetlec ty) (← toSetlec b)
      ⟨toSetlecBI bi, none⟩)
  | .forallE n ty b bi => do
    .ok (.forallE (sanitizeBinderName n) (← toSetlec ty) (← toSetlec b)
      ⟨toSetlecBI bi, none⟩)
  | .letE _ _ v b _ => toSetlec (b.instantiate1 v)
  | .lit (.natVal n) => .ok (.lit (.natVal n))
  | .lit (.strVal s) => .ok (.lit (.strVal s))
  | .mdata _ e => toSetlec e
  | .proj s i e => (Setlec.Expr.proj (toSetlecName s) i ·) <$> toSetlec e
  | .fvar _ => .error "fvar in closed term"
  | .mvar _ => .error "mvar in closed term"

/-! ## Serialization with sharing

Every distinct subobject (name/level/expr) is emitted once as a `let`
binding; the vendored file is linear in the number of distinct nodes and
the runtime value shares subterms. -/

structure EmitState where
  lines : Array String := #[]
  names : Std.HashMap Setlec.Name String := {}
  levels : Std.HashMap Setlec.Level String := {}
  exprs : Std.HashMap Setlec.Expr String := {}

abbrev EmitM := StateM EmitState

def emitLine (s : String) : EmitM Unit :=
  modify fun st => { st with lines := st.lines.push s }

partial def emitName (n : Setlec.Name) : EmitM String := do
  if let some v := (← get).names[n]? then return v
  let v ← match n with
    | .anonymous => pure "Setlec.Name.anonymous"
    | .str p s => do
      let pv ← emitName p
      let id := s!"n{(← get).names.size}"
      emitLine s!"  let {id} := Setlec.Name.str {pv} {reprStr s}"
      pure id
    | .num p i => do
      let pv ← emitName p
      let id := s!"n{(← get).names.size}"
      emitLine s!"  let {id} := Setlec.Name.num {pv} {i}"
      pure id
  modify fun st => { st with names := st.names.insert n v }
  return v

partial def emitLevel (l : Setlec.Level) : EmitM String := do
  if let some v := (← get).levels[l]? then return v
  let v ← match l with
    | .zero => pure "Setlec.Level.zero"
    | .succ u => do
      let uv ← emitLevel u
      let id := s!"l{(← get).levels.size}"
      emitLine s!"  let {id} := Setlec.Level.succ {uv}"
      pure id
    | .max u w => do
      let uv ← emitLevel u; let wv ← emitLevel w
      let id := s!"l{(← get).levels.size}"
      emitLine s!"  let {id} := Setlec.Level.max {uv} {wv}"
      pure id
    | .imax u w => do
      let uv ← emitLevel u; let wv ← emitLevel w
      let id := s!"l{(← get).levels.size}"
      emitLine s!"  let {id} := Setlec.Level.imax {uv} {wv}"
      pure id
    | .param n => do
      let nv ← emitName n
      let id := s!"l{(← get).levels.size}"
      emitLine s!"  let {id} := Setlec.Level.param {nv}"
      pure id
  modify fun st => { st with levels := st.levels.insert l v }
  return v

def emitBI : Setlec.BinderInfo → String
  | .default => ".default"
  | .implicit => ".implicit"
  | .strictImplicit => ".strictImplicit"
  | .instImplicit => ".instImplicit"

partial def emitExpr (e : Setlec.Expr) : EmitM String := do
  if let some v := (← get).exprs[e]? then return v
  let mk (parts : List String) : EmitM String := do
    let id := s!"e{(← get).exprs.size}_{(← get).lines.size}"
    emitLine s!"  let {id} := {String.intercalate " " parts}"
    pure id
  let v ← match e with
    | .bvar i => mk ["Setlec.Expr.bvar", toString i]
    | .fvar .. => panic! "fvar in pin"
    | .sort u => do mk ["Setlec.Expr.sort", ← emitLevel u]
    | .const n us => do
      let nv ← emitName n
      let uvs ← us.mapM emitLevel
      mk ["Setlec.Expr.const", nv, "[" ++ String.intercalate ", " uvs ++ "]"]
    | .app f a => do mk ["Setlec.Expr.app", ← emitExpr f, ← emitExpr a]
    | .lam n ty b m => do
      let nv ← emitName n
      mk ["Setlec.Expr.lam", nv, ← emitExpr ty, ← emitExpr b,
          s!"⟨{emitBI m.bi}, none⟩"]
    | .forallE n ty b m => do
      let nv ← emitName n
      mk ["Setlec.Expr.forallE", nv, ← emitExpr ty, ← emitExpr b,
          s!"⟨{emitBI m.bi}, none⟩"]
    | .letE .. => panic! "letE in pin"
    | .lit (.natVal n) => mk ["Setlec.Expr.lit (Setlec.Literal.natVal", toString n ++ ")"]
    | .lit (.strVal s) => mk ["Setlec.Expr.lit (Setlec.Literal.strVal", reprStr s ++ ")"]
    | .proj s i x => do
      let sv ← emitName s
      mk ["Setlec.Expr.proj", sv, toString i, ← emitExpr x]
  modify fun st => { st with exprs := st.exprs.insert e v }
  return v

/-- Emit one `def name : Expr := let … ; root`. -/
def emitDef (name : String) (e : Setlec.Expr) : EmitM String := do
  -- fresh sharing tables per def, so each def is self-contained
  modify fun st => { st with names := {}, levels := {}, exprs := {}, lines := #[] }
  let root ← emitExpr e
  let st ← get
  let body := String.intercalate "\n" st.lines.toList
  return s!"def {name} : Expr :=\n{body}\n  {root}\n"

/-! ## Driver -/

def countNodes : Setlec.Expr → Nat
  | .app f a => countNodes f + countNodes a + 1
  | .lam _ t b _ | .forallE _ t b _ => countNodes t + countNodes b + 1
  | .letE _ t v b => countNodes t + countNodes v + countNodes b + 1
  | .proj _ _ e => countNodes e + 1
  | _ => 1

def loadPrefix (path : System.FilePath) : IO (Std.HashMap String (List String)) := do
  let s ← IO.FS.readFile path
  let some j := (Json.parse s).toOption | throw (IO.userError "bad prefix json")
  let some o := j.getObj?.toOption | throw (IO.userError "bad prefix json obj")
  let mut m : Std.HashMap String (List String) := {}
  for ⟨k, v⟩ in o.toArray do
    let some arr := v.getArr?.toOption | throw (IO.userError "bad prefix arr")
    m := m.insert k (arr.toList.filterMap (·.getStr?.toOption))
  return m

structure OpSpec where
  op : Name
  certs : List (String × Name)   -- (label, generator theorem name)

def opSpecs : List OpSpec :=
  [{ op := `Nat.mod,
     certs := [("modRec", ``modRecCert), ("modBaseGt", ``modBaseGtCert),
               ("modBaseZero", ``modBaseZeroCert)] },
   { op := `Nat.div,
     certs := [("divRec", ``divRecCert), ("divBaseGt", ``divBaseGtCert),
               ("divBaseZero", ``divBaseZeroCert)] }]

def checkConsts (what : String) (allowed : Name → Bool) (e : Expr) :
    CoreM Unit := do
  let bad := (constsOf e).toList.filter (fun c => !allowed c)
  unless bad.isEmpty do
    throwError "{what}: constants outside the allowed prefix: {bad}"

def genOp (prefixes : Std.HashMap String (List String)) (spec : OpSpec) :
    MetaM (List (String × String)) := do
  let env ← getEnv
  let some allowedList := prefixes[spec.op.toString]? |
    throwError "no prefix for {spec.op}"
  let allowedSet : NameSet := allowedList.foldl (fun s n =>
    s.insert n.toName) {}
  let allowed := fun c => allowedSet.contains c
  let allowedOrSelf := fun c => allowed c || c == spec.op
  -- the pinned defining expression
  let some (.defnInfo v) := env.find? spec.op | throwError "{spec.op} not a defn"
  let pin ← unfoldFix (isHelper env) v.value
  checkConsts s!"pin {spec.op}" allowed pin
  let pinS ← match toSetlec pin with
    | .ok e => pure e
    | .error m => throwError "pin conversion ({spec.op}): {m}"
  IO.println s!"{spec.op}: pin nodes = {countNodes pinS}, consts = {(constsOf pin).toList.length}"
  let opTag := if spec.op == `Nat.div then "Div" else "Mod"
  let mut out : List (String × String) := []
  out := out.append [(s!"nat{opTag}DeclPin",
    (emitDef s!"nat{opTag}DeclPin" pinS).run' {})]
  -- certificate proofs (the statements are pinned by hand in
  -- `Setlec/Kernel/Checker.lean` — `divModCertStmts` — in open
  -- fvar-telescope form; only the proofs are vendored blobs)
  let mut certNames : List String := []
  for (label, thmName) in spec.certs do
    let some ci := env.find? thmName | throwError "{thmName} missing"
    let some pf := ci.value? (allowOpaque := true) | throwError "{thmName} has no value"
    let pf ← inlineClosure allowedOrSelf pf
    checkConsts s!"cert proof {label}" allowedOrSelf pf
    let pfS ← match toSetlec pf with
      | .ok e => pure e | .error m => throwError "proof conv ({label}): {m}"
    IO.println s!"  cert {label}: proof nodes = {countNodes pfS}, proof consts = {(constsOf pf).toList}"
    out := out.append
      [(s!"{label}Proof", (emitDef s!"{label}Proof" pfS).run' {})]
    certNames := certNames.append [s!"{label}Proof"]
  out := out.append [(s!"nat{opTag}CertProofs",
    s!"def nat{opTag}CertProofs : List Expr :=\n  [" ++
      String.intercalate ", " certNames ++ "]\n")]
  return out

def header : String :=
"/-
Pinned `Nat.div`/`Nat.mod` declarations and characterization certificates.

GENERATED FILE — do not edit by hand.  Regenerate with:

    python3 scripts/extract_divmod_prefix.py <init-prelude.ndjson> scripts/divmod_prefix.json
    lake env lean --run scripts/GenDivModPins.lean

See scripts/GenDivModPins.lean for the design; DESIGN.md \"Nat.div/Nat.mod
literal reduction\" for how the checker consumes these.
-/
import Setlec.Kernel.Expr

namespace Setlec

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

"

def footer : String := "
end Setlec
"

/- Run in the ambient elaboration environment (which contains the
certificate theorems above): `lake env lean scripts/GenDivModPins.lean`. -/
run_meta do
  let prefixes ← loadPrefix "scripts/divmod_prefix.json"
  let mut pieces : List String := []
  for spec in opSpecs do
    let outs ← genOp prefixes spec
    pieces := pieces ++ outs.map (·.2)
  let content := header ++ String.intercalate "\n" pieces ++ footer
  IO.FS.writeFile "Setlec/Kernel/DivModPins.lean" content
  IO.println s!"wrote Setlec/Kernel/DivModPins.lean ({content.length} chars)"
