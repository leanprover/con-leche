module

public import Lean
public meta import ConLeche.PinGen
public meta import ConLeche.Rules.BVQuote

/-!
# The stored shapes the `bv_decide` model reads

`Model/BVQuoteSem.lean` computes the readings of the stored types of a
few `bv_decide` constants (the recursors at a `Prop` motive, the
constructors, two `Nat` theorems) by `simp` over the stored `Expr`.  The
shapes are the toolchain's own declarations, translated here while the
module elaborates (the `PinGen` pattern), never written by hand:

* `spliceExprShape`: the stored form (`toConLecheKeepLet`), with every
  constant written by a *named* `ConLeche.Name` definition from a table
  (so `simp` lemmas about `.const finN []` match) and `2 ^ #i` written
  `Rules.pow2E (.bvar i)` (so it matches the gate's own spelling);
* `spliceTermShape`: the reading the `simp` computation produces, over a
  leaf assignment `acv`: a constant is `acv n ψ` at the all-`k` level
  assignment its levels evaluate to (levels evaluated with every
  parameter at `0`, the `Prop` motive), `2 ^ #i` is `powT acv (.bvar i)`.

Each shape is checked against the checker's pin of the same constant by
`rfl` where it is used.
-/

public meta section

namespace ConLeche.PinGen.BVShapes

open Lean Meta Elab
open Lean.Elab.Term (TermElabM)

/-- The level a stored level evaluates to with every parameter at `0`. -/
def eval0 : ConLeche.Level → Nat
  | .zero => 0
  | .succ u => eval0 u + 1
  | .max u v => max (eval0 u) (eval0 v)
  | .imax u v => if eval0 v = 0 then 0 else max (eval0 u) (eval0 v)
  | .param _ => 0

/-- The name tables: Lean's constant and level-parameter names to the
declarations of their `ConLeche.Name`s. -/
structure Tables where
  consts : List (Lean.Name × Lean.Name)
  levels : List (Lean.Name × Lean.Name)

def nameRef (tbl : List (Lean.Name × Lean.Name)) (n : ConLeche.Name) : MetaM Lean.Expr := do
  match tbl.find? (fun (l, _) => ConLeche.Name.ofLeanName l == n) with
  | some (_, d) => pure (mkConst d)
  | none => throwError "bvShapes: no name declaration for {repr n}"

partial def qLevel (t : Tables) : ConLeche.Level → MetaM Lean.Expr
  | .zero => pure (mkConst ``ConLeche.Level.zero)
  | .succ u => do pure (mkApp (mkConst ``ConLeche.Level.succ) (← qLevel t u))
  | .max u v => do pure (mkApp2 (mkConst ``ConLeche.Level.max) (← qLevel t u) (← qLevel t v))
  | .imax u v => do pure (mkApp2 (mkConst ``ConLeche.Level.imax) (← qLevel t u) (← qLevel t v))
  | .param n => do pure (mkApp (mkConst ``ConLeche.Level.param) (← nameRef t.levels n))

def listOf (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [.zero]) ty)

/-- `2 ^ #i`, as the gate spells it. -/
def pow2Var? (e : ConLeche.Expr) : Option Nat :=
  match e with
  | .app _ (.bvar i) => if e == Rules.pow2E (.bvar i) then some i else none
  | _ => none

partial def qExpr (t : Tables) (e : ConLeche.Expr) : MetaM Lean.Expr := do
  if let some i := pow2Var? e then
    return mkApp (mkConst ``ConLeche.Rules.pow2E)
      (mkApp (mkConst ``ConLeche.Expr.bvar) (mkRawNatLit i))
  match e with
  | .bvar i => pure (mkApp (mkConst ``ConLeche.Expr.bvar) (mkRawNatLit i))
  | .sort u => pure (mkApp (mkConst ``ConLeche.Expr.sort) (← qLevel t u))
  | .const n us =>
    pure (mkApp2 (mkConst ``ConLeche.Expr.const) (← nameRef t.consts n)
      (listOf (mkConst ``ConLeche.Level) (← us.mapM (qLevel t))))
  | .app f a => pure (mkApp2 (mkConst ``ConLeche.Expr.app) (← qExpr t f) (← qExpr t a))
  | .lam ty b => pure (mkApp2 (mkConst ``ConLeche.Expr.lam) (← qExpr t ty) (← qExpr t b))
  | .forallE ty b =>
    pure (mkApp2 (mkConst ``ConLeche.Expr.forallE) (← qExpr t ty) (← qExpr t b))
  | _ => throwError "bvShapes: unexpected node in a shape"

/-- The reading `simp` computes, over the leaf assignment `acv` (a bound
variable of the generated definition, `#0` outside every binder). -/
partial def qTerm (t : Tables) (ψ0 powT : Lean.Name) (acv : Lean.Expr) (e : ConLeche.Expr) :
    MetaM Lean.Expr := do
  if let some i := pow2Var? e then
    return mkApp2 (mkConst powT) acv
      (mkApp (mkConst `ConLeche.Term.Term.bvar) (mkRawNatLit i))
  match e with
  | .bvar i => pure (mkApp (mkConst `ConLeche.Term.Term.bvar) (mkRawNatLit i))
  | .sort u => pure (mkApp (mkConst `ConLeche.Term.Term.sort) (mkRawNatLit (eval0 u)))
  | .const n us =>
    let ks := us.map eval0
    let k := ks.headD 0
    unless ks.all (· == k) do throwError "bvShapes: mixed levels at {repr n}"
    let lv := if k == 0 then mkConst ψ0 else
      .lam `_ (mkConst ``ConLeche.Name) (mkRawNatLit k) .default
    pure (mkApp2 acv (← nameRef t.consts n) lv)
  | .app f a =>
    pure (mkApp2 (mkConst `ConLeche.Term.Term.app) (← qTerm t ψ0 powT acv f)
      (← qTerm t ψ0 powT acv a))
  | .lam ty b =>
    pure (mkApp2 (mkConst `ConLeche.Term.Term.lam) (← qTerm t ψ0 powT acv ty)
      (← qTerm t ψ0 powT acv b))
  | .forallE ty b =>
    pure (mkApp2 (mkConst `ConLeche.Term.Term.pi) (← qTerm t ψ0 powT acv ty)
      (← qTerm t ψ0 powT acv b))
  | _ => throwError "bvShapes: unexpected node in a shape"

def splice (declName : Lean.Name) (ty value : Lean.Expr) : TermElabM Unit := do
  let decl : Lean.Declaration := .defnDecl
    (← mkDefinitionValInferringUnsafe declName [] ty value
      (.regular (getMaxHeight (← getEnv) value + 1)))
  withExporting (isExporting := true) do
    addDecl decl (forceExpose := true)
  enableRealizationsForConst declName

/-- The stored form of `c`'s type (`val := false`) or value. -/
def storedOf (c : Lean.Name) (val : Bool) : TermElabM ConLeche.Expr := do
  let ci ← getConstInfo c
  let e ← if val then
      match ci.value? with
      | some v => pure v
      | none => throwError "bvShapes: {c} has no value"
    else pure ci.type
  match ConLeche.PinGen.toConLecheKeepLet e with
  | .ok x => pure x
  | .error m => throwError "bvShapes: {m}"

/-- `declName : ConLeche.Expr`, the stored shape of `c`'s type or value. -/
def spliceExprShape (t : Tables) (declName c : Lean.Name) (val : Bool) : TermElabM Unit := do
  splice declName (mkConst ``ConLeche.Expr) (← qExpr t (← storedOf c val))

/-- `declName : (Name → (Name → Nat) → Term) → Term`, its reading. -/
def spliceTermShape (t : Tables) (ψ0 powT declName c : Lean.Name) (val : Bool) :
    TermElabM Unit := do
  let nameT := mkConst ``ConLeche.Name
  let natT := mkConst ``Nat
  let termT := mkConst `ConLeche.Term.Term
  let acvTy ← mkArrow nameT (← mkArrow (← mkArrow nameT natT) termT)
  let body ← qTerm t ψ0 powT (.bvar 0) (← storedOf c val)
  splice declName (← mkArrow acvTy termT) (.lam `acv acvTy body .default)

end ConLeche.PinGen.BVShapes

end
