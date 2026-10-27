module

public import Lean
public meta import ConLeche.PinGen
public meta import ConLeche.Kernel.Env

/-!
# The pinned data of a boosted closure, as the installation stores it
(task #368)

`splicePinData` defines, per constant `c`, `BoostPins.c.name`, `.lps`, and
`.val` (definition), `.type` (recursor, constructor, inductive, theorem),
`.rules` (recursor): the data a pin premise (`DefPin`, `RecPin`, …) and the
checker's install gate compare with the stored declaration.  The data is
the STORED form, not Lean's:

* values keep their `let`s (`toConLecheKeepLet`): the installation
  stores a value as declared;
* a recursor's rules carry the bits the installation computes
  (`recRuleBits`: the K bit, and the η-rescue bit of a structure's rule);
* a basis constant (`Eq`, `Eq.refl`, `Eq.rec`, the `Nat` block, …) is the
  checker's pin (`ConLeche/Kernel/BasisA.lean`), stored verbatim by the
  basis install: its data is a term over that pin, evaluated by the kernel.

Shared by the checker's gate (`Kernel/BVUnsatPins.lean`) and the boost
generator (`Verify/BoostRed/Boost.lean`), so a pin premise and the gate's
check name the same constants.
-/

public meta section

namespace ConLeche.PinGen.Boost

open Lean Meta Elab Term

def pinNS : Lean.Name := `BoostPins

def splice (declName : Lean.Name) (ty value : Lean.Expr) : TermElabM Unit := do
  let hints : Lean.ReducibilityHints := .regular (getMaxHeight (← getEnv) value + 1)
  let decl : Lean.Declaration := .defnDecl
    (← mkDefinitionValInferringUnsafe declName [] ty value hints)
  withExporting (isExporting := true) do
    addDecl decl (forceExpose := true)
  compileDecl decl

def clExprT : Lean.Expr := Lean.mkConst ``ConLeche.Expr
def clNameT : Lean.Expr := Lean.mkConst ``ConLeche.Name
def clLevelT : Lean.Expr := Lean.mkConst ``ConLeche.Level
def clRuleT : Lean.Expr := Lean.mkConst ``ConLeche.RecRule
def liftExcept {α} (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "toConLeche: {e}"

def qLps (ps : List Lean.Name) : Lean.Expr :=
  toExpr (ps.map ConLeche.Name.ofLeanName)

def listOf (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [.zero]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [.zero]) ty)

/-- The checker's raw pin of a basis constant (stored verbatim but for the
rule fields), if `c` is one. -/
def basisPin? (c : Lean.Name) : Option Lean.Name :=
  if c == ``Eq then some `ConLeche.eqRaw
  else if c == ``Eq.refl then some `ConLeche.eqReflRaw
  else if c == ``Eq.rec then some `ConLeche.eqRecRaw
  else if c == ``Nat then some `ConLeche.natRaw
  else if c == ``Nat.zero then some `ConLeche.natZeroRaw
  else if c == ``Nat.succ then some `ConLeche.natSuccRaw
  else if c == ``Nat.rec then some `ConLeche.natRecRaw
  else if c == ``Empty then some `ConLeche.emptyRaw
  else if c == ``Empty.rec then some `ConLeche.emptyRecRaw
  else if c == ``False then some `ConLeche.falseRaw
  else if c == ``False.rec then some `ConLeche.falseRecRaw
  else none

/-- A family's result sort is literally `Prop`. -/
def indIsProp (iv : InductiveVal) : MetaM Bool :=
  forallTelescopeReducing iv.type fun _ b => return b.isProp

/-- The η-rescue bit the installation stamps on a rule
(`recRuleEtaOf` over `blockCapsAt`'s `eta`): the rule's constructor is
the single constructor of an index-free, non-`Prop`, non-recursive family,
at the family's level parameters. -/
def ruleEtaBit (ctor : Lean.Name) : MetaM Bool := do
  let some (.ctorInfo cv) := (← getEnv).find? ctor | return false
  let some (.inductInfo iv) := (← getEnv).find? cv.induct | return false
  if iv.ctors.length != 1 || iv.numIndices != 0 || iv.isRec || iv.all.length != 1 ||
      iv.isNested then
    return false
  if ← indIsProp iv then return false
  return cv.levelParams == iv.levelParams

/-- The stored rules of a non-basis recursor, quoted. -/
def storedRules (rv : RecursorVal) : MetaM (List Lean.Expr) := do
  let mut out : List Lean.Expr := []
  for r in rv.rules do
    let rhs ← liftExcept (ConLeche.PinGen.toConLeche r.rhs)
    let eta ← ruleEtaBit r.ctor
    let k := rv.k && r.nfields == 0
    out := out ++ [mkAppN (Lean.mkConst ``ConLeche.RecRule.mk)
      #[toExpr (ConLeche.Name.ofLeanName r.ctor), mkRawNatLit r.nfields, mkRawNatLit rv.numParams,
        Lean.mkConst ``ConLeche.RecRuleFire.plain, toExpr rhs, toExpr k, toExpr eta]]
  return out

/-- Splice each constant's pinned data under `ns`. -/
def splicePinData (ns : Lean.Name) (cs : Array Lean.Name) : TermElabM Unit := do
  for c in cs do
    let ci ← getConstInfo c
    let base := ns ++ c
    splice (base ++ `name) clNameT (toExpr (ConLeche.Name.ofLeanName c))
    match basisPin? c with
    | some pin =>
      -- the checker's own pin, stored verbatim by the basis install
      let pinE := Lean.mkConst pin
      let cvE := mkApp (Lean.mkConst ``ConLeche.ConstantInfo.toConstantVal) pinE
      splice (base ++ `lps) (mkApp (Lean.mkConst ``List [.zero]) clNameT)
        (mkApp (Lean.mkConst ``ConLeche.ConstantVal.levelParams) cvE)
      splice (base ++ `type) clExprT (mkApp (Lean.mkConst ``ConLeche.ConstantVal.type) cvE)
      if let .recInfo rv := ci then
        -- the raw pin's rules with the fields the basis install stamps
        let k := rv.k && rv.rules.all (·.nfields == 0)
        splice (base ++ `rules) (mkApp (Lean.mkConst ``List [.zero]) clRuleT)
          (mkApp4 (Lean.mkConst ``List.map [.zero, .zero]) clRuleT clRuleT
            (mkApp2 (Lean.mkConst `ConLeche.RecRule.withBits) (mkRawNatLit rv.numParams) (toExpr k))
            (mkApp (Lean.mkConst `ConLeche.ConstantInfo.recRulesOf) pinE))
    | none =>
      splice (base ++ `lps) (mkApp (Lean.mkConst ``List [.zero]) clNameT) (qLps ci.levelParams)
      let ty ← liftExcept (ConLeche.PinGen.toConLecheKeepLet ci.type)
      splice (base ++ `type) clExprT (toExpr ty)
      match ci with
      | .defnInfo dv =>
        let v ← liftExcept (ConLeche.PinGen.toConLecheKeepLet dv.value)
        splice (base ++ `val) clExprT (toExpr v)
      | .recInfo rv =>
        splice (base ++ `rules) (mkApp (Lean.mkConst ``List [.zero]) clRuleT)
          (listOf clRuleT (← storedRules rv))
      | _ => pure ()

/-- Splice the pinned data of the constants not pinned yet. -/
def ensurePinData (cs : Array Lean.Name) : TermElabM Unit := do
  let env ← getEnv
  let todo := cs.filter fun c => !env.contains (pinNS ++ c ++ `name)
  unless todo.isEmpty do splicePinData pinNS todo

end ConLeche.PinGen.Boost

end
