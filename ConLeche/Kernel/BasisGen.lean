module

public meta import Lean
public meta import ConLeche.Kernel.TypeChecker

/- `public section`, deliberately NOT `@[expose]`: every definition here is
elaboration-time machinery whose body no importer unfolds, and an exposed
body may not mention the module's `private` helpers (`splice`, the quoters,
the `evalX` wrappers). -/
public section

/-!
# `#stored_basis` — the pinned basis blocks, as the installation stores them

The pinned basis blocks are *stored* by the installation
(`installBasisDecl`, `ConLeche/Kernel/Checker.lean`) verbatim, and the
model proofs read the stored constants.  The stored forms differ from
the raw pins (`ConLeche/Kernel/Basis/*`, which are what a stream's
records are compared against) in one place only: a recursor's rules
carry the fields the installation computes — `ctorParams` from the
stored constructor and the K/η bits (`recRuleBits`).  They are not a second source of truth:
`#stored_basis` computes them from the raw pins while the module
elaborates (`pinRecRuleFields`) and defines the results with
`addDecl`/`compileDecl`, so the definition's value is a closed literal
the `decide`/`rfl` consumers in `ConLeche/Model/*` read, re-derived on
every build.

```
#stored_basis over <env : List ConstantInfo>
  | eqA := eqRaw
  | ...
```
defines `ConstantInfo` constants, in dependency order, each computed
over the environment of `<env>` extended by the ones already defined
(a recursor's rule reads its constructor's parameter count off it).
The `over` term is elaborated and evaluated at `List ConstantInfo`.
-/

/- The whole module is elaboration-time code: quoters, the `#eval`-style
evaluator and the command elaborator.  The module system wants a
`CommandElab` to be `meta` (`Cannot add attribute … must be marked as
`meta``), and `meta section` is how a file that is meta THROUGHOUT says
so once. -/
meta section

namespace ConLeche.BasisGen

open Lean Elab Command Term Meta

/-! ## Quoting a `ConLeche` value back into a `Lean.Expr`

The rule fields are computed on real `ConLeche` values; the definition
the command splices must carry them as terms.  These are the structural quoters — one
constructor application each, with no sharing (the pins are small; the
biggest is `Quot.lift`'s rule, a few hundred nodes). -/

private def qBool : Bool → Lean.Expr
  | true => mkConst ``Bool.true
  | false => mkConst ``Bool.false

private def qList (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Lean.Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Lean.Level.zero]) ty)

private def nameTy : Lean.Expr := mkConst ``ConLeche.Name
private def levelTy : Lean.Expr := mkConst ``ConLeche.Level
private def exprTy : Lean.Expr := mkConst ``ConLeche.Expr
private def recRuleTy : Lean.Expr := mkConst ``ConLeche.RecRule
private def constantInfoTy : Lean.Expr := mkConst ``ConLeche.ConstantInfo
private def constantValTy : Lean.Expr := mkConst ``ConLeche.ConstantVal

private def qName : ConLeche.Name → Lean.Expr
  | .anonymous => mkConst ``ConLeche.Name.anonymous
  | .str p s => mkApp2 (mkConst ``ConLeche.Name.str) (qName p) (mkStrLit s)
  | .num p i => mkApp2 (mkConst ``ConLeche.Name.num) (qName p) (mkRawNatLit i)

private def qNames (ns : List ConLeche.Name) : Lean.Expr :=
  qList nameTy (ns.map qName)

private def qLevel : ConLeche.Level → Lean.Expr
  | .zero => mkConst ``ConLeche.Level.zero
  | .succ a => mkApp (mkConst ``ConLeche.Level.succ) (qLevel a)
  | .max a b => mkApp2 (mkConst ``ConLeche.Level.max) (qLevel a) (qLevel b)
  | .imax a b => mkApp2 (mkConst ``ConLeche.Level.imax) (qLevel a) (qLevel b)
  | .param n => mkApp (mkConst ``ConLeche.Level.param) (qName n)

private def qLevels (us : List ConLeche.Level) : Lean.Expr :=
  qList levelTy (us.map qLevel)

/-- The zero-ness datum. -/
private def qPropWhen : ConLeche.PropWhen → Lean.Expr
  | .never => mkConst ``ConLeche.PropWhen.never
  | .ifAllZero ps => mkApp (mkConst ``ConLeche.PropWhen.ifAllZero) (qNames ps)

private def qLiteral : ConLeche.Literal → Lean.Expr
  | .natVal n => mkApp (mkConst ``ConLeche.Literal.natVal) (mkRawNatLit n)
  | .strVal s => mkApp (mkConst ``ConLeche.Literal.strVal) (mkStrLit s)

private def qExpr : ConLeche.Expr → Lean.Expr
  | .bvar i => mkApp (mkConst ``ConLeche.Expr.bvar) (mkRawNatLit i)
  | .fvar i ty => mkApp2 (mkConst ``ConLeche.Expr.fvar) (mkRawNatLit i) (qExpr ty)
  | .sort u => mkApp (mkConst ``ConLeche.Expr.sort) (qLevel u)
  | .const n us => mkApp2 (mkConst ``ConLeche.Expr.const) (qName n) (qLevels us)
  | .app f a => mkApp2 (mkConst ``ConLeche.Expr.app) (qExpr f) (qExpr a)
  | .lam ty b =>
    mkApp2 (mkConst ``ConLeche.Expr.lam) (qExpr ty) (qExpr b)
  | .forallE ty b =>
    mkApp2 (mkConst ``ConLeche.Expr.forallE) (qExpr ty) (qExpr b)
  | .letE ty v b =>
    mkApp3 (mkConst ``ConLeche.Expr.letE) (qExpr ty) (qExpr v) (qExpr b)
  | .lit l => mkApp (mkConst ``ConLeche.Expr.lit) (qLiteral l)
  | .proj s i e =>
    mkApp3 (mkConst ``ConLeche.Expr.proj) (qName s) (mkRawNatLit i) (qExpr e)

private def qConstantVal (cv : ConLeche.ConstantVal) : Lean.Expr :=
  mkApp3 (mkConst ``ConLeche.ConstantVal.mk) (qName cv.name)
    (qNames cv.levelParams) (qExpr cv.type)

private def qRecRuleFire : ConLeche.RecRuleFire → Lean.Expr
  | .plain => mkConst ``ConLeche.RecRuleFire.plain
  | .nested lvls pins =>
    mkApp2 (mkConst ``ConLeche.RecRuleFire.nested) (qLevels lvls)
      (qList exprTy (pins.map qExpr))

private def qRecRule (r : ConLeche.RecRule) : Lean.Expr :=
  mkAppN (mkConst ``ConLeche.RecRule.mk)
    #[qName r.ctor, mkRawNatLit r.nfields, mkRawNatLit r.ctorParams,
      qRecRuleFire r.fire, qExpr r.rhs, qBool r.k]

private def qIndCaps (c : ConLeche.IndCaps) : Lean.Expr :=
  mkAppN (mkConst ``ConLeche.IndCaps.mk)
    #[qBool c.eta, qName c.etaCtor, mkRawNatLit c.etaParams,
      mkRawNatLit c.etaFields, qBool c.unitlike, mkRawNatLit c.unitParams,
      qBool c.ruleK, qPropWhen c.sortZ, qNames c.all, mkRawNatLit c.nparams,
      qNames c.ctors]

private def qReducibilityHint : ConLeche.ReducibilityHint → Lean.Expr
  | .«opaque» => mkConst ``ConLeche.ReducibilityHint.«opaque»
  | .«abbrev» => mkConst ``ConLeche.ReducibilityHint.«abbrev»
  | .regular h => mkApp (mkConst ``ConLeche.ReducibilityHint.regular) (mkRawNatLit h)

private def qConstantInfo : ConLeche.ConstantInfo → CoreM Lean.Expr
  | .axiomInfo cv => pure (mkApp (mkConst ``ConLeche.ConstantInfo.axiomInfo) (qConstantVal cv))
  | .defnInfo cv v h =>
    pure (mkApp3 (mkConst ``ConLeche.ConstantInfo.defnInfo) (qConstantVal cv)
      (qExpr v) (qReducibilityHint h))
  | .thmInfo cv =>
    pure (mkApp (mkConst ``ConLeche.ConstantInfo.thmInfo) (qConstantVal cv))
  | .indInfo cv caps =>
    pure (mkApp2 (mkConst ``ConLeche.ConstantInfo.indInfo) (qConstantVal cv) (qIndCaps caps))
  | .ctorInfo cv nP nF =>
    pure (mkApp3 (mkConst ``ConLeche.ConstantInfo.ctorInfo) (qConstantVal cv)
      (mkRawNatLit nP) (mkRawNatLit nF))
  | .recInfo cv mI rP rules =>
    pure (mkAppN (mkConst ``ConLeche.ConstantInfo.recInfo)
      #[qConstantVal cv, mkRawNatLit mI, mkRawNatLit rP,
        qList recRuleTy (rules.map qRecRule)])

/-! ## The recipe -/

/-- The stored form of a raw pin over `env`: the pin itself, except
that a recursor's rules carry the install-computed fields
(`ctorParams` off the stored constructor, and `recRuleBits`; `fire`
stays `.plain`, every basis recursor's major being a member), exactly as
the basis install computes them. -/
def pinRecRuleFields (env : ConLeche.Env) : ConLeche.ConstantInfo → ConLeche.ConstantInfo
  | .recInfo cv mI rP rules =>
    .recInfo cv mI rP (rules.map fun r =>
      let cnP := match env.find? r.ctor with
        | some (.ctorInfo _ nP _) => nP
        | _ => 0
      ConLeche.recRuleBits env.find?
        { r with ctorParams := cnP })
  | ci => ci

/-! ## Evaluating the raw pins

`Lean.Elab.Term.evalTerm` is `unsafe`; the safe wrappers below are the
standard `@[implemented_by]` pairing (their own bodies are never run —
`implemented_by` replaces the compiled code). -/

private unsafe def evalInfoUnsafe (stx : Syntax) : TermElabM ConLeche.ConstantInfo :=
  Term.evalTerm ConLeche.ConstantInfo constantInfoTy stx

@[implemented_by evalInfoUnsafe]
private def evalInfo (_stx : Syntax) : TermElabM ConLeche.ConstantInfo :=
  throwError "unreachable"

private unsafe def evalEnvUnsafe (stx : Syntax) : TermElabM (List ConLeche.ConstantInfo) :=
  Term.evalTerm (List ConLeche.ConstantInfo)
    (mkApp (mkConst ``List [Lean.Level.zero]) constantInfoTy) stx

@[implemented_by evalEnvUnsafe]
private def evalEnv (_stx : Syntax) : TermElabM (List ConLeche.ConstantInfo) :=
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
  -- MODULE SYSTEM (task #231).  A spliced constant must land in the *public*
  -- scope with its body exposed, exactly as the `def` it replaces would:
  -- `addDecl` otherwise derives an opaque `axiom` presentation for the public
  -- view (`Lean/AddDecl.lean`), and downstream `rfl`/`decide` proofs over the
  -- pins — every `Model/Basis*` consumer — would lose the value they read.
  withExporting (isExporting := true) do
    addDecl decl (forceExpose := true)
  compileDecl decl

/-! ## The commands -/

/-- One `| name := rawTerm` entry.  The leading `|` is what keeps the
entries from being parsed as one applied term. -/
syntax pinEntry := " | " ident " := " term

/-- `#stored_basis over <env> | nameA := nameRaw ...` — compute the
stored forms of raw `ConstantInfo` pins in order, each over the
environment of `<env>` extended by the ones already defined, and
define the results. -/
syntax (name := storedBasisCmd)
  "#stored_basis" " over " term (pinEntry)+ : command

@[command_elab storedBasisCmd]
def elabStoredBasis : CommandElab := fun stx => do
  let entries := stx[3].getArgs
  let mut consts : List ConLeche.ConstantInfo ←
    liftTermElabM (evalEnv stx[2])
  for e in entries do
    let id := e[1]
    let rawStx := e[3]
    let raw ← liftTermElabM (evalInfo rawStx)
    let ci := pinRecRuleFields ⟨consts, []⟩ raw
    liftTermElabM do
      splice ((← getCurrNamespace) ++ id.getId) constantInfoTy (← qConstantInfo ci)
    consts := ci :: consts

end ConLeche.BasisGen

end  -- meta section
