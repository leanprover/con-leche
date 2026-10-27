module

import ConLeche.Kernel.Env
import ConLeche.Kernel.Basis
public import ConLeche.Kernel.CoreDefs
public meta import Lean
public meta import ConLeche.PinGen.BoostPins
public meta import ConLeche.Kernel.Level
public meta import ConLeche.Kernel.CoreDefs
public meta import ConLeche.PinGen
public meta import ConLeche.PinGen.Dump
public meta import Std.Tactic.BVDecide.Reflect
-- `Nat.land`/`Nat.lor`/`Nat.xor` (in `Unsat`'s closure through the
-- bitwise `BitVec` operations) have bodies the module system hides; the
-- generator below reads them to pin them.
meta import all Init.Data.Nat.Bitwise.Basic

/-!
# The pinned closure of `BVLogicalExpr.Unsat` (task #368)

`bvUnsatPins` lists every constant of the closure of
`Std.Tactic.BVDecide.BVLogicalExpr.Unsat` (types, definition values,
constructors and recursor rules; theorems by their statement), plus the
constants the formula reader reads (`OfNat.ofNat`, `instOfNatNat`,
`BitVec.ofNat`), plus the statement of
`Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true`, as the
toolchain this checker is built with declares them, translated by
`PinGen.toConLeche`.  They are computed while this module elaborates.
-/

@[expose] public section

namespace ConLeche

/-- One pinned constant. -/
inductive BVPin where
  | defn (n : Name) (lps : List Name) (ty v : Expr)
  | thm (n : Name) (lps : List Name) (ty : Expr)
  | ind (n : Name) (lps : List Name) (ty : Expr)
  | ctor (n : Name) (lps : List Name) (ty : Expr)
  /-- a recursor: its rules as `(constructor, fields, rhs)` -/
  | recr (n : Name) (lps : List Name) (ty : Expr) (rules : List (Name × Nat × Expr))
  deriving Inhabited

def BVPin.name : BVPin → Name
  | .defn n .. | .thm n .. | .ind n .. | .ctor n .. | .recr n .. => n

/-- **One check of the boost premises** (the kinds of `Verify/BoostRed/Kit`'s
pins and facts): the stored declaration is the pinned one. -/
inductive BoostCheck where
  | defn (n : Name) (lps : List Name) (v : Expr)
  | recr (n : Name) (lps : List Name) (ty : Expr) (mI rP : Nat) (rules : List RecRule)
  | ctor (n : Name) (lps : List Name) (ty : Expr)
  | indNever (T : Name) (k : Nat)
  | proj (sn : Name) (i : Nat) (ctor : Name) (lps : List Name) (nP nF : Nat)
  | natLit
  | natOp (c : Name)
  deriving Inhabited

end ConLeche

end

meta section

namespace BVUnsatGen

open Lean Elab Command

partial def closure (env : Environment) (roots : Array Lean.Name) : Array Lean.Name := Id.run do
  let mut seen : Std.HashSet Lean.Name := {}
  let mut order : Array Lean.Name := #[]
  let mut todo := roots
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    order := order.push n
    let some ci := env.find? n | continue
    let mut cs := ci.type.getUsedConstants
    if !(ci matches .thmInfo _) then
      if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    match ci with
    | .inductInfo ii => cs := cs ++ ii.ctors.toArray
    | .recInfo ri => cs := cs ++ ri.rules.toArray.flatMap (·.rhs.getUsedConstants)
    | .ctorInfo ci => cs := cs.push ci.induct
    | _ => pure ()
    for c in cs do
      unless seen.contains c do todo := todo.push c
  return order

def liftE {α} (x : Except String α) : CommandElabM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "toConLeche: {e}"

def qName (n : Lean.Name) : Lean.Expr := toExpr (ConLeche.Name.ofLeanName n)
def qLps (ps : List Lean.Name) : Lean.Expr := toExpr (ps.map ConLeche.Name.ofLeanName)

def exprDecl (k : Nat) (e : Lean.Expr) : CommandElabM Lean.Expr := do
  let c ← liftE (ConLeche.PinGen.toConLecheKeepLet e)
  let declName := (`ConLeche.BVUnsatPinData).str s!"e{k}"
  let value := ConLeche.PinGen.buildExprValue c
  let decl := Declaration.defnDecl
    { name := declName, levelParams := [], type := mkConst ``ConLeche.Expr, value,
      hints := .regular 1, safety := .safe }
  liftCoreM do
    withExporting (isExporting := true) do addDecl decl (forceExpose := true)
    compileDecl decl
  return mkConst declName

def pinOf (k : IO.Ref Nat) (n : Lean.Name) (ci : ConstantInfo) : CommandElabM Lean.Expr := do
  let next : CommandElabM Nat := do let i ← k.get; k.set (i + 1); pure i
  let ty ← exprDecl (← next) ci.type
  let qn := qName n
  let lps := qLps ci.levelParams
  match ci with
  | .defnInfo dv =>
    let v ← exprDecl (← next) dv.value
    return mkAppN (mkConst ``ConLeche.BVPin.defn) #[qn, lps, ty, v]
  | .thmInfo _ | .axiomInfo _ => return mkAppN (mkConst ``ConLeche.BVPin.thm) #[qn, lps, ty]
  | .inductInfo _ => return mkAppN (mkConst ``ConLeche.BVPin.ind) #[qn, lps, ty]
  | .ctorInfo _ => return mkAppN (mkConst ``ConLeche.BVPin.ctor) #[qn, lps, ty]
  | .recInfo rv =>
    let ruleT := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``ConLeche.Name)
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``ConLeche.Expr))
    let mut rs : Array Lean.Expr := #[]
    for r in rv.rules do
      let rhs ← exprDecl (← next) r.rhs
      rs := rs.push (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``ConLeche.Name)
        (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``ConLeche.Expr))
        (qName r.ctor)
        (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``ConLeche.Expr)
          (mkRawNatLit r.nfields) rhs))
    let lst := rs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ruleT x acc)
      (mkApp (mkConst ``List.nil [0]) ruleT)
    return mkAppN (mkConst ``ConLeche.BVPin.recr) #[qn, lps, ty, lst]
  | _ => throwError "bvUnsatPins: unsupported constant kind at {n}"

run_cmd do
  let env ← getEnv
  let roots := #[``Std.Tactic.BVDecide.BVLogicalExpr.Unsat, ``OfNat.ofNat, ``instOfNatNat,
    ``BitVec.ofNat, ``Bool.true, ``Bool.false,
    -- the model's reading of `Assignment` (`Model/BVQuoteSem.lean`): the
    -- recursors at a `Prop` motive, `True`, and the two `Nat` facts that
    -- bound a quoted bit-vector's value (statements only)
    ``Lean.RArray.rec, ``Std.Tactic.BVDecide.BVExpr.PackedBitVec.rec, ``BitVec.rec, ``Fin.rec,
    ``True.intro, ``Nat.le_of_ble_eq_true, ``Nat.not_lt_of_le]
  let cs := closure env roots
  let k ← IO.mkRef 0
  let mut pins : Array Lean.Expr := #[]
  let mut pinNames : Array Lean.Name := #[]
  for n in cs do
    -- the `Eq` block is a basis block: the installation stores the
    -- checker's pin (`Kernel/Basis`, level parameter `u`), not Lean's
    -- declaration (`u_1`), and guarantees it
    if n == ``Eq || n == ``Eq.refl || n == ``Eq.rec then continue
    let some ci := env.find? n | throwError "bvUnsatPins: {n} not found"
    pins := pins.push (← pinOf k n ci)
    pinNames := pinNames.push n
  -- the theorem's statement only (its proof's closure is not pinned)
  let some u := env.find? ``Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true
    | throwError "no unsat_of_verifyBVExpr_eq_true"
  let uty ← exprDecl (← k.get) u.type
  pins := pins.push (mkAppN (mkConst ``ConLeche.BVPin.thm)
    #[qName u.name, qLps u.levelParams, uty])
  pinNames := pinNames.push u.name
  -- the pins the model reads, under names of their own
  let modelNames : List (Lean.Name × String) := [
    (``Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true, "U"),
    (``Std.Tactic.BVDecide.BVLogicalExpr.Unsat, "Unsat"),
    (``Std.Tactic.BVDecide.BVLogicalExpr.eval, "eval"),
    (``Std.Tactic.BVDecide.BVExpr.Assignment, "Assignment"),
    (``Std.Tactic.BVDecide.BVLogicalExpr, "BVLE"),
    (``Bool, "Bool"), (``Bool.false, "BoolFalse"),
    (``Bool.true, "BoolTrue"), (``Nat.ble, "NatBle"), (``False, "False"), (``Not, "Not"),
    (``True, "True"), (``True.intro, "TrueIntro"),
    (``Nat, "Nat"), (``Nat.zero, "NatZero"), (``Nat.succ, "NatSucc"), (``LT, "LTcls"), (``LT.lt, "LTlt"), (``instLTNat, "instLTNat"), (``LE.le, "LEle"), (``instLENat, "instLENat"),
    (``Nat.le_of_ble_eq_true, "leOfBle"), (``Nat.not_lt_of_le, "notLtOfLe"),
    (``HPow.hPow, "hPow"), (``instHPow, "instHPow"), (``instPowNat, "instPowNat"),
    (``instNatPowNat, "instNatPowNat"), (``OfNat.ofNat, "ofNat"), (``instOfNatNat, "instOfNatNat"),
    (``Lean.RArray, "RArray"), (``Lean.RArray.leaf, "RArrayLeaf"),
    (``Lean.RArray.branch, "RArrayBranch"), (``Lean.RArray.rec, "RArrayRec"),
    (``Std.Tactic.BVDecide.BVExpr.PackedBitVec, "PBV"),
    (``Std.Tactic.BVDecide.BVExpr.PackedBitVec.mk, "PBVMk"),
    (``Std.Tactic.BVDecide.BVExpr.PackedBitVec.rec, "PBVRec"),
    (``BitVec, "BitVec"), (``BitVec.ofFin, "BitVecOfFin"), (``BitVec.rec, "BitVecRec"),
    (``Fin, "Fin"), (``Fin.mk, "FinMk"), (``Fin.rec, "FinRec")]
  let mut named : Array Lean.Expr := #[]
  for (n, tag) in modelNames do
    let some i := pinNames.toList.idxOf? n | throwError "bvUnsatPins: no pin for {n}"
    let declName := (`ConLeche.bvPin).str tag
    let decl := Declaration.defnDecl
      { name := declName, levelParams := [], type := mkConst ``ConLeche.BVPin,
        value := pins[i]!, hints := .regular 1, safety := .safe }
    liftCoreM do
      withExporting (isExporting := true) do addDecl decl (forceExpose := true)
      compileDecl decl
    named := named.push (mkConst declName)
  let pinT := mkConst ``ConLeche.BVPin
  let mlst := named.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) pinT x acc)
    (mkApp (mkConst ``List.nil [0]) pinT)
  let mdecl := Declaration.defnDecl
    { name := `ConLeche.bvModelPins, levelParams := [],
      type := mkApp (mkConst ``List [0]) pinT, value := mlst,
      hints := .regular 1, safety := .safe }
  liftCoreM do
    withExporting (isExporting := true) do addDecl mdecl (forceExpose := true)
    compileDecl mdecl
  -- **the boost checks**: the pinned data (`PinGen/BoostPins.lean`, the
  -- names the boost premises use), one check per closure constant
  liftTermElabM <| ConLeche.PinGen.Boost.ensurePinData cs
  let P (c : Lean.Name) (f : Lean.Name) : Lean.Expr := mkConst (`BoostPins ++ c ++ f)
  let mut checks : Array Lean.Expr := #[]
  for n in cs do
    let some ci := env.find? n | continue
    let cn := ConLeche.Name.ofLeanName n
    match ci with
    | .defnInfo _ =>
      unless (ConLeche.PinGen.Boost.basisPin? n).isSome do
        checks := checks.push (mkAppN (mkConst ``ConLeche.BoostCheck.defn) #[P n `name, P n `lps, P n `val])
    | .recInfo rv =>
      checks := checks.push (mkAppN (mkConst ``ConLeche.BoostCheck.recr)
        #[P n `name, P n `lps, P n `type,
          mkRawNatLit (rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices),
          mkRawNatLit (rv.numParams + rv.numMotives + rv.numMinors), P n `rules])
    | .ctorInfo _ =>
      checks := checks.push (mkAppN (mkConst ``ConLeche.BoostCheck.ctor) #[P n `name, P n `lps, P n `type])
    | .inductInfo iv =>
      -- never `Prop` at any instantiation (the install's `sortZ`)
      let sortL ← liftTermElabM <| Meta.forallTelescopeReducing iv.type fun _ b =>
        match b with | .sort u => pure (some u) | _ => pure none
      if let some u := sortL then
        if let .ok cu := ConLeche.PinGen.toConLecheLevel u then
          if ConLeche.Level.zeronessOf cu == .never then
            checks := checks.push (mkAppN (mkConst ``ConLeche.BoostCheck.indNever)
              #[P n `name, mkRawNatLit iv.levelParams.length])
            -- a structure's projection slots
            if let [c] := iv.ctors then
              if iv.numIndices == 0 && !iv.isRec then
                let some (.ctorInfo cv) := env.find? c | continue
                for i in [0:cv.numFields] do
                  checks := checks.push (mkAppN (mkConst ``ConLeche.BoostCheck.proj)
                    #[toExpr cn, mkRawNatLit i, P c `name, P c `lps,
                      mkRawNatLit cv.numParams, mkRawNatLit cv.numFields])
    | _ => pure ()
  checks := checks.push (mkConst ``ConLeche.BoostCheck.natLit)
  for op in [``ConLeche.natAddName, ``ConLeche.natSubName, ``ConLeche.natMulName,
      ``ConLeche.natDivName, ``ConLeche.natModName, ``ConLeche.natBeqName, ``ConLeche.natBleName] do
    checks := checks.push (mkApp (mkConst ``ConLeche.BoostCheck.natOp) (mkConst op))
  let chkT := mkConst ``ConLeche.BoostCheck
  let clst := checks.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) chkT x acc)
    (mkApp (mkConst ``List.nil [0]) chkT)
  let cdecl := Declaration.defnDecl
    { name := `ConLeche.bvBoostChecks, levelParams := [],
      type := mkApp (mkConst ``List [0]) chkT, value := clst,
      hints := .regular 1, safety := .safe }
  liftCoreM do
    withExporting (isExporting := true) do addDecl cdecl (forceExpose := true)
    compileDecl cdecl
  logInfo m!"bvUnsatPins: {pins.size} model-pin candidates, {checks.size} boost checks"


end BVUnsatGen

end
