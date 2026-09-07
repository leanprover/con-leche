import Lean
import Lech.Kernel.TypeChecker

/-!
# `#annotate_basis` — the pinned declarations, annotated at elaboration time

The pinned basis blocks, the standard-axiom prerequisite families and
the compiler-trust pins are *stored annotated*: the installation
(`installBasisDecl`, `Lech/Kernel/Checker.lean`) puts them into the
environment verbatim, and the model proofs read their `pw` data off
the stored constants.  The annotated forms are not a second source of
truth — they are what **this checker's own annotation pass**
(`annotateCore` at `.verified`) computes from the raw pins.

Until 2026-09-06 that computation lived in an offline generator
(`AnnotateBasis.lean`, a `[[lean_exe]]`) whose `Repr` output was pasted
into the pin modules as ~1 900 lines of fully-qualified constructor
spellings.  The literals were therefore a *committed cache with no
checked relation to their source*: nothing in the build re-ran the
generator, and a stale paste would have been invisible.

`#annotate_basis` replaces the paste.  It runs the same recipe while
the pin module elaborates and defines the annotated constants with
`addDecl`/`compileDecl`, so the definition's value is the very term
`annotateCore` produced — the same closed literal the `decide`/`rfl`
consumers in `Lech/SetP/*` saw before, now *derived* rather than
transcribed, and re-derived on every build.  An annotation failure is
an elaboration error, never a silently stale constant.

## The recipe

Exactly what `checkDecl`'s `.basisDecl` install would do, in
dependency order:

* the constant's **type** is annotated over the environment holding
  the pins annotated so far (`over` gives that environment's tail);
* for a recursor, the install-computed rule fields are filled first —
  `ctorParams` from the stored constructor, `fire` from
  `Expr.recRulePlain` — and then each rule's **rhs** is annotated over
  the environment extended by the recursor itself (a rule's rhs may
  mention it, as `Nat.rec`'s successor rule does);
* the result is appended to the environment for the next entry.

## The two commands

```
#annotate_basis over <env : List ConstantInfo>
  | eqA := eqRaw
  | ...
```
defines `ConstantInfo` constants and threads each one into the
environment for the entries that follow.

```
#annotate_pins over <env : List ConstantInfo>
  | propextA := propextRaw
  | ...
```
defines `ConstantVal` constants (the two standard axioms and the four
compiler-trust pins), each annotated over the *same* environment; a
pin that must be visible to a later one is passed in the next
command's `over`.

The `over` term is elaborated and evaluated at `List ConstantInfo`, so
it may name constants this command defined earlier in the file.
-/

namespace Lech.BasisGen

open Lean Elab Command Term Meta

/-! ## Quoting a `Lech` value back into a `Lean.Expr`

The annotation runs on real `Lech` values; the definition it splices
must carry them as terms.  These are the structural quoters — one
constructor application each, with no sharing (the pins are small; the
biggest is `Quot.lift`'s rule, a few hundred nodes). -/

private def qBool : Bool → Lean.Expr
  | true => mkConst ``Bool.true
  | false => mkConst ``Bool.false

private def qList (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Lean.Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Lean.Level.zero]) ty)

private def nameTy : Lean.Expr := mkConst ``Lech.Name
private def levelTy : Lean.Expr := mkConst ``Lech.Level
private def exprTy : Lean.Expr := mkConst ``Lech.Expr
private def recRuleTy : Lean.Expr := mkConst ``Lech.RecRule
private def constantInfoTy : Lean.Expr := mkConst ``Lech.ConstantInfo
private def constantValTy : Lean.Expr := mkConst ``Lech.ConstantVal

private def qName : Lech.Name → Lean.Expr
  | .anonymous => mkConst ``Lech.Name.anonymous
  | .str p s => mkApp2 (mkConst ``Lech.Name.str) (qName p) (mkStrLit s)
  | .num p i => mkApp2 (mkConst ``Lech.Name.num) (qName p) (mkRawNatLit i)

private def qNames (ns : List Lech.Name) : Lean.Expr :=
  qList nameTy (ns.map qName)

private def qLevel : Lech.Level → Lean.Expr
  | .zero => mkConst ``Lech.Level.zero
  | .succ a => mkApp (mkConst ``Lech.Level.succ) (qLevel a)
  | .max a b => mkApp2 (mkConst ``Lech.Level.max) (qLevel a) (qLevel b)
  | .imax a b => mkApp2 (mkConst ``Lech.Level.imax) (qLevel a) (qLevel b)
  | .param n => mkApp (mkConst ``Lech.Level.param) (qName n)

private def qLevels (us : List Lech.Level) : Lean.Expr :=
  qList levelTy (us.map qLevel)

/-- The zero-ness datum through its public API (the representation is
`private` to `Lech/Kernel/PropWhen.lean`): `never`, or `ifAllZero`
of its parameter list. -/
private def qPropWhen (pw : Lech.PropWhen) : Lean.Expr :=
  match pw.toList? with
  | none => mkConst ``Lech.PropWhen.never
  | some ps => mkApp (mkConst ``Lech.PropWhen.ifAllZero) (qNames ps)

private def qBinderMeta (m : Lech.BinderMeta) : Lean.Expr :=
  mkApp (mkConst ``Lech.BinderMeta.mk) (qPropWhen m.pw)

private def qLiteral : Lech.Literal → Lean.Expr
  | .natVal n => mkApp (mkConst ``Lech.Literal.natVal) (mkRawNatLit n)
  | .strVal s => mkApp (mkConst ``Lech.Literal.strVal) (mkStrLit s)

private def qExpr : Lech.Expr → Lean.Expr
  | .bvar i => mkApp (mkConst ``Lech.Expr.bvar) (mkRawNatLit i)
  | .fvar i ty => mkApp2 (mkConst ``Lech.Expr.fvar) (mkRawNatLit i) (qExpr ty)
  | .sort u => mkApp (mkConst ``Lech.Expr.sort) (qLevel u)
  | .const n us => mkApp2 (mkConst ``Lech.Expr.const) (qName n) (qLevels us)
  | .app f a => mkApp2 (mkConst ``Lech.Expr.app) (qExpr f) (qExpr a)
  | .lam ty b m =>
    mkApp3 (mkConst ``Lech.Expr.lam) (qExpr ty) (qExpr b) (qBinderMeta m)
  | .forallE ty b m =>
    mkApp3 (mkConst ``Lech.Expr.forallE) (qExpr ty) (qExpr b) (qBinderMeta m)
  | .letE ty v b =>
    mkApp3 (mkConst ``Lech.Expr.letE) (qExpr ty) (qExpr v) (qExpr b)
  | .lit l => mkApp (mkConst ``Lech.Expr.lit) (qLiteral l)
  | .proj s i e =>
    mkApp3 (mkConst ``Lech.Expr.proj) (qName s) (mkRawNatLit i) (qExpr e)

private def qConstantVal (cv : Lech.ConstantVal) : Lean.Expr :=
  mkApp3 (mkConst ``Lech.ConstantVal.mk) (qName cv.name)
    (qNames cv.levelParams) (qExpr cv.type)

private def qRecRuleFire : Lech.RecRuleFire → Lean.Expr
  | .inert => mkConst ``Lech.RecRuleFire.inert
  | .plain => mkConst ``Lech.RecRuleFire.plain
  | .nested lvls pins =>
    mkApp2 (mkConst ``Lech.RecRuleFire.nested) (qLevels lvls)
      (qList exprTy (pins.map qExpr))

private def qRecRule (r : Lech.RecRule) : Lean.Expr :=
  mkAppN (mkConst ``Lech.RecRule.mk)
    #[qName r.ctor, mkRawNatLit r.nfields, mkRawNatLit r.ctorParams,
      qRecRuleFire r.fire, qExpr r.rhs]

private def qIndCaps (c : Lech.IndCaps) : Lean.Expr :=
  mkAppN (mkConst ``Lech.IndCaps.mk)
    #[qBool c.eta, qName c.etaCtor, mkRawNatLit c.etaParams,
      mkRawNatLit c.etaFields, qBool c.unitlike, mkRawNatLit c.unitParams,
      qBool c.ruleK]

private def qReducibilityHint : Lech.ReducibilityHint → Lean.Expr
  | .«opaque» => mkConst ``Lech.ReducibilityHint.«opaque»
  | .«abbrev» => mkConst ``Lech.ReducibilityHint.«abbrev»
  | .regular h => mkApp (mkConst ``Lech.ReducibilityHint.regular) (mkRawNatLit h)

private def qConstantInfo : Lech.ConstantInfo → CoreM Lean.Expr
  | .axiomInfo cv => pure (mkApp (mkConst ``Lech.ConstantInfo.axiomInfo) (qConstantVal cv))
  | .defnInfo cv v h =>
    pure (mkApp3 (mkConst ``Lech.ConstantInfo.defnInfo) (qConstantVal cv)
      (qExpr v) (qReducibilityHint h))
  | .thmInfo cv v =>
    pure (mkApp2 (mkConst ``Lech.ConstantInfo.thmInfo) (qConstantVal cv) (qExpr v))
  | .indInfo cv caps =>
    pure (mkApp2 (mkConst ``Lech.ConstantInfo.indInfo) (qConstantVal cv) (qIndCaps caps))
  | .ctorInfo cv nP nF =>
    pure (mkApp3 (mkConst ``Lech.ConstantInfo.ctorInfo) (qConstantVal cv)
      (mkRawNatLit nP) (mkRawNatLit nF))
  | .recInfo cv mI rP rules =>
    pure (mkAppN (mkConst ``Lech.ConstantInfo.recInfo)
      #[qConstantVal cv, mkRawNatLit mI, mkRawNatLit rP,
        qList recRuleTy (rules.map qRecRule)])
  | .projInfo _ =>
    throwError "#annotate_basis: a projection table is not a pinnable declaration"

/-! ## The recipe -/

/-- Annotate one raw `ConstantInfo` over `env`, exactly as the basis
install does: the type first, then — for a recursor — the
install-computed rule fields (`ctorParams` off the stored constructor,
`fire` off `Expr.recRulePlain`) and the rules' right-hand sides over
the environment extended with the recursor itself. -/
def annotateInfo (env : Lech.Env) (ci : Lech.ConstantInfo) :
    Lech.CheckM Lech.ConstantInfo := do
  let cv := ci.toConstantVal
  let ty' ← Lech.annotateCore .verified env Lech.checkFuel 0 cv.type
  let cv' : Lech.ConstantVal := { cv with type := ty' }
  match ci with
  | .indInfo _ caps => return .indInfo cv' caps
  | .ctorInfo _ nP nF => return .ctorInfo cv' nP nF
  | .axiomInfo _ => return .axiomInfo cv'
  | .defnInfo _ v h => return .defnInfo cv' v h
  | .thmInfo _ v => return .thmInfo cv' v
  | .projInfo tbl => return .projInfo tbl
  | .recInfo _ mI rP rules =>
    let rules := rules.map fun r =>
      let cnP := match env.find? r.ctor with
        | some (.ctorInfo _ nP _) => nP
        | _ => 0
      { r with ctorParams := cnP,
               fire := if Lech.Expr.recRulePlain ty' mI rP cnP then .plain else .inert }
    let envSelf : Lech.Env := ⟨.recInfo cv' mI rP rules :: env.consts⟩
    let mut out : List Lech.RecRule := []
    for r in rules do
      let rhs' ← Lech.annotateCore .verified envSelf Lech.checkFuel 0 r.rhs
      out := out ++ [{ r with rhs := rhs' }]
    return .recInfo cv' mI rP out

/-- Annotate one raw `ConstantVal` pin's type over `env`. -/
def annotateVal (env : Lech.Env) (cv : Lech.ConstantVal) :
    Lech.CheckM Lech.ConstantVal := do
  let ty' ← Lech.annotateCore .verified env Lech.checkFuel 0 cv.type
  return { cv with type := ty' }

/-! ## Evaluating the raw pins

`Lean.Elab.Term.evalTerm` is `unsafe`; the safe wrappers below are the
standard `@[implemented_by]` pairing (their own bodies are never run —
`implemented_by` replaces the compiled code). -/

private unsafe def evalInfoUnsafe (stx : Syntax) : TermElabM Lech.ConstantInfo :=
  Term.evalTerm Lech.ConstantInfo constantInfoTy stx

@[implemented_by evalInfoUnsafe]
private def evalInfo (_stx : Syntax) : TermElabM Lech.ConstantInfo :=
  throwError "unreachable"

private unsafe def evalValUnsafe (stx : Syntax) : TermElabM Lech.ConstantVal :=
  Term.evalTerm Lech.ConstantVal constantValTy stx

@[implemented_by evalValUnsafe]
private def evalVal (_stx : Syntax) : TermElabM Lech.ConstantVal :=
  throwError "unreachable"

private unsafe def evalEnvUnsafe (stx : Syntax) : TermElabM (List Lech.ConstantInfo) :=
  Term.evalTerm (List Lech.ConstantInfo)
    (mkApp (mkConst ``List [Lean.Level.zero]) constantInfoTy) stx

@[implemented_by evalEnvUnsafe]
private def evalEnv (_stx : Syntax) : TermElabM (List Lech.ConstantInfo) :=
  throwError "unreachable"

/-! ## Splicing -/

/-- Define `declName : ty := value` (kernel-checked, then compiled),
with the reducibility hint an ordinary `def` of the same body would
get. -/
private def splice (declName : Lean.Name) (ty value : Lean.Expr) :
    TermElabM Unit := do
  let hints : Lean.ReducibilityHints := .regular (getMaxHeight (← getEnv) value + 1)
  let decl : Lean.Declaration := .defnDecl
    (← mkDefinitionValInferringUnsafe declName [] ty value hints)
  addDecl decl
  compileDecl decl

/-! ## The commands -/

/-- One `| name := rawTerm` entry.  The leading `|` is what keeps the
entries from being parsed as one applied term. -/
syntax annotEntry := " | " ident " := " term

/-- `#annotate_basis over <env> | nameA := nameRaw ...` — annotate raw
`ConstantInfo` pins in order, each over the environment of `<env>`
extended by the ones already annotated, and define the results. -/
syntax (name := annotateBasisCmd)
  "#annotate_basis" " over " term (annotEntry)+ : command

/-- `#annotate_pins over <env> | nameA := nameRaw ...` — annotate raw
`ConstantVal` pins, each over the *same* environment, and define the
results. -/
syntax (name := annotatePinsCmd)
  "#annotate_pins" " over " term (annotEntry)+ : command

@[command_elab annotateBasisCmd]
def elabAnnotateBasis : CommandElab := fun stx => do
  let entries := stx[3].getArgs
  let mut consts : List Lech.ConstantInfo ←
    liftTermElabM (evalEnv stx[2])
  for e in entries do
    let id := e[1]
    let rawStx := e[3]
    let raw ← liftTermElabM (evalInfo rawStx)
    let ci ←
      match annotateInfo ⟨consts⟩ raw with
      | .ok ci => pure ci
      | .error err =>
        throwErrorAt rawStx
          "#annotate_basis: annotating {id.getId} failed: {toString err}"
    liftTermElabM do
      splice ((← getCurrNamespace) ++ id.getId) constantInfoTy (← qConstantInfo ci)
    consts := ci :: consts

@[command_elab annotatePinsCmd]
def elabAnnotatePins : CommandElab := fun stx => do
  let entries := stx[3].getArgs
  let consts : List Lech.ConstantInfo ← liftTermElabM (evalEnv stx[2])
  for e in entries do
    let id := e[1]
    let rawStx := e[3]
    let raw ← liftTermElabM (evalVal rawStx)
    let cv ←
      match annotateVal ⟨consts⟩ raw with
      | .ok cv => pure cv
      | .error err =>
        throwErrorAt rawStx
          "#annotate_pins: annotating {id.getId} failed: {toString err}"
    liftTermElabM do
      splice ((← getCurrNamespace) ++ id.getId) constantValTy (qConstantVal cv)

end Lech.BasisGen
