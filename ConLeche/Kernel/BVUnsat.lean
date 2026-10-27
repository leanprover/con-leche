module

import ConLeche.Kernel.ExprOps
public import ConLeche.Kernel.BVUnsatPins
public import Std.Tactic.BVDecide.Reflect

/-!
# `bv_decide` certificates, checked natively (task #368)

A `bv_decide` proof contains
`Std.Tactic.BVDecide.Reflect.unsat_of_verifyBVExpr_eq_true E C ax`
(`U E C ax` below), where `ax : verifyBVExpr E C = true` is a native
axiom (`<decl>._native.bv_decide.ax_N`), `E` the reflected formula and
`C` the LRAT certificate (a string literal behind a definition).

The checker types `U E C a` as `BVLogicalExpr.Unsat E` **without
inferring `a`** when `bvUnsatOk` holds:

* the stored closure of `Unsat` and of `U`'s type is syntactically
  Lean's (`bvUnsatPins`, one comparison per constant);
* `E` is closed and reads as a shallow `e : BVLogicalExpr`
  (`readLogical`: δ of argument-free definitions, constructor
  applications, `Nat` literals and `OfNat.ofNat Nat n (instOfNatNat n)`,
  `BitVec.ofNat w n`);
* `C` reads as a string literal `c`;
* con-leche's own compiled `verifyBVExpr e c` returns `true`.

The justification is Std's shallow theorem
`unsat_of_verifyBVExpr_eq_true e c` in con-leche's own Lean, which holds
whatever the opaque and `partial` constants of the checker's closure
are; the model relates `⟦Unsat E⟧` to the shallow `Unsat e` through
the boost relation of `BVLogicalExpr.eval` (`Infer.bvUnsat`, DESIGN
#368).  The native axiom itself is installed as a stub of type `True`
(`bvStubOk`): every other use of it declines (`bvNativeUseMsg`).
-/

@[expose] public section

namespace ConLeche

open Std.Tactic.BVDecide

/-! ## Names -/

/-- A dotted name from its components (reduces by `rfl`). -/
def BVUnsat.nmL (parts : List String) : Name :=
  parts.foldl Name.str .anonymous

def unsatThmName : Name := BVUnsat.nmL ["Std", "Tactic", "BVDecide", "Reflect", "unsat_of_verifyBVExpr_eq_true"]
def bvUnsatName : Name := BVUnsat.nmL ["Std", "Tactic", "BVDecide", "BVLogicalExpr", "Unsat"]
def bvLogicalExprName : Name := BVUnsat.nmL ["Std", "Tactic", "BVDecide", "BVLogicalExpr"]

namespace BVUnsat

def ofNatN : Name := nmL ["OfNat", "ofNat"]
def instOfNatNatN : Name := nmL ["instOfNatNat"]
def natN : Name := nmL ["Nat"]
def bvOfNatN : Name := nmL ["BitVec", "ofNat"]
def boolTrueN : Name := nmL ["Bool", "true"]
def boolFalseN : Name := nmL ["Bool", "false"]

def beLiteralN : Name := nmL ["Std", "Tactic", "BVDecide", "BoolExpr", "literal"]
def beConstN : Name := nmL ["Std", "Tactic", "BVDecide", "BoolExpr", "const"]
def beNotN : Name := nmL ["Std", "Tactic", "BVDecide", "BoolExpr", "not"]
def beGateN : Name := nmL ["Std", "Tactic", "BVDecide", "BoolExpr", "gate"]
def beIteN : Name := nmL ["Std", "Tactic", "BVDecide", "BoolExpr", "ite"]
def predBinN : Name := nmL ["Std", "Tactic", "BVDecide", "BVPred", "bin"]
def predLsbN : Name := nmL ["Std", "Tactic", "BVDecide", "BVPred", "getLsbD"]
def exVarN : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "var"]
def exConstN : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "const"]
def exExtractN : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "extract"]
def exBinN : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "bin"]
def exUnN : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "un"]
def exAppendN : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "append"]
def exReplicateN : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "replicate"]
def exShlN : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "shiftLeft"]
def exShrN : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "shiftRight"]
def exAshrN : Name := nmL ["Std", "Tactic", "BVDecide", "BVExpr", "arithShiftRight"]

/-! ## The pin gate -/

/-- One pinned constant, as the installation stores it. -/
def pinOk (find? : Name → Option ConstantInfo) : BVPin → Bool
  | .defn n lps ty v =>
    match find? n with
    | some (.defnInfo cv v' _) => cv.levelParams == lps && cv.type == ty && v' == v
    | _ => false
  | .thm n lps ty =>
    match find? n with
    | some (.thmInfo cv) | some (.axiomInfo cv) => cv.levelParams == lps && cv.type == ty
    | _ => false
  | .ind n lps ty =>
    match find? n with
    | some (.indInfo cv _) => cv.levelParams == lps && cv.type == ty
    | _ => false
  | .ctor n lps ty =>
    match find? n with
    | some (.ctorInfo cv _ _) => cv.levelParams == lps && cv.type == ty
    | _ => false
  | .recr n lps ty rules =>
    match find? n with
    | some (.recInfo cv _ _ rs) =>
      cv.levelParams == lps && cv.type == ty &&
        rs.length == rules.length &&
        (rs.zip rules).all fun (r, (c, nf, rhs)) => r.ctor == c && r.nfields == nf && r.rhs == rhs
    | _ => false

/-- One boost check (the B-checks of `Verify/BoostRed/Kit.lean`'s pins). -/
def boostCheckOk (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) : BoostCheck → Bool
  | .defn n lps v =>
    match find? n with
    | some (.defnInfo cv v' _) => cv.levelParams == lps && v' == v
    | _ => false
  | .recr n lps ty mI rP rules =>
    match find? n with
    | some (.recInfo cv mI' rP' rules') =>
      cv.levelParams == lps && cv.type == ty && mI' == mI && rP' == rP && rules' == rules
    | _ => false
  | .ctor n lps ty =>
    match find? n with
    | some (.ctorInfo cv _ _) => cv.levelParams == lps && cv.type == ty
    | _ => false
  | .indNever T k =>
    match find? T with
    | some (.indInfo cvT caps) => cvT.levelParams.length == k && caps.sortZ == .never
    | _ => false
  | .proj sn i ctor lps nP nF =>
    match findProj? sn i with
    | some e => e.ctor == ctor && e.levelParams == lps && e.numParams == nP &&
        e.numFields == nF && !(Level.isEquiv e.structSort .zero == some true)
    | none => false
  | .natLit =>
    natIndOk (find? natName) && natZeroOk (find? natZeroName) && natSuccOk (find? natSuccName)
  | .natOp c =>
    match find? c with
    | some (.defnInfo _ _ _) => true
    | _ => false

def pinsOk (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) : Bool :=
  bvModelPins.all (pinOk find?) && bvBoostChecks.all (boostCheckOk find? findProj?)

/-! ## Reading the reflected formula -/

/-- An argument-free definition's closed value (the `_expr_def`/`_cert_def`
auxiliaries; closedness is what the reading's relation states of every
constructor argument). -/
def unfold? (find? : Name → Option ConstantInfo) : Expr → Option Expr
  | .const n [] =>
    match find? n with
    | some (.defnInfo cv v _) =>
      if cv.levelParams.isEmpty && v.looseBVarsBounded 0 then some v else none
    | _ => none
  | _ => none

/-- A constructor-like application without level arguments: its head
and arguments. -/
def ctorApp? (e : Expr) : Option (Name × List Expr) :=
  match e.getAppFn with
  | .const n [] => some (n, e.getAppArgs)
  | _ => none

/-- A `Nat`: a literal or `OfNat.ofNat Nat n (instOfNatNat n)`. -/
def readNat : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .app (.app (.app (.const c [.zero]) (.const t [])) (.lit (.natVal n)))
      (.app (.const i []) (.lit (.natVal m))) =>
    if c == ofNatN && t == natN && i == instOfNatNatN && n == m then some n else none
  | _ => none

/-- A nullary constructor, by a table of names. -/
def readEnum {α : Type} (t : List (Name × α)) (e : Expr) : Option α :=
  match ctorApp? e with
  | some (c, []) => (t.find? (·.1 == c)).map (·.2)
  | _ => none

def boolTable : List (Name × Bool) := [(boolTrueN, true), (boolFalseN, false)]

def gateTable : List (Name × Gate) :=
  [(nmL ["Std", "Tactic", "BVDecide", "Gate", "and"], .and),
   (nmL ["Std", "Tactic", "BVDecide", "Gate", "xor"], .xor),
   (nmL ["Std", "Tactic", "BVDecide", "Gate", "beq"], .beq),
   (nmL ["Std", "Tactic", "BVDecide", "Gate", "or"], .or)]

def binOpTable : List (Name × BVBinOp) :=
  [(nmL ["Std", "Tactic", "BVDecide", "BVBinOp", "and"], .and),
   (nmL ["Std", "Tactic", "BVDecide", "BVBinOp", "or"], .or),
   (nmL ["Std", "Tactic", "BVDecide", "BVBinOp", "xor"], .xor),
   (nmL ["Std", "Tactic", "BVDecide", "BVBinOp", "add"], .add),
   (nmL ["Std", "Tactic", "BVDecide", "BVBinOp", "mul"], .mul),
   (nmL ["Std", "Tactic", "BVDecide", "BVBinOp", "udiv"], .udiv),
   (nmL ["Std", "Tactic", "BVDecide", "BVBinOp", "umod"], .umod)]

def binPredTable : List (Name × BVBinPred) :=
  [(nmL ["Std", "Tactic", "BVDecide", "BVBinPred", "eq"], .eq),
   (nmL ["Std", "Tactic", "BVDecide", "BVBinPred", "ult"], .ult)]

def unOpTable0 : List (Name × BVUnOp) :=
  [(nmL ["Std", "Tactic", "BVDecide", "BVUnOp", "not"], .not),
   (nmL ["Std", "Tactic", "BVDecide", "BVUnOp", "reverse"], .reverse),
   (nmL ["Std", "Tactic", "BVDecide", "BVUnOp", "clz"], .clz),
   (nmL ["Std", "Tactic", "BVDecide", "BVUnOp", "cpop"], .cpop)]

def unOpTable1 : List (Name × (Nat → BVUnOp)) :=
  [(nmL ["Std", "Tactic", "BVDecide", "BVUnOp", "rotateLeft"], .rotateLeft),
   (nmL ["Std", "Tactic", "BVDecide", "BVUnOp", "rotateRight"], .rotateRight),
   (nmL ["Std", "Tactic", "BVDecide", "BVUnOp", "arithShiftRightConst"], .arithShiftRightConst)]

def readBool (e : Expr) : Option Bool := readEnum boolTable e
def readGate (e : Expr) : Option Gate := readEnum gateTable e
def readBinOp (e : Expr) : Option BVBinOp := readEnum binOpTable e
def readBinPred (e : Expr) : Option BVBinPred := readEnum binPredTable e

def readUnOp (e : Expr) : Option BVUnOp :=
  match ctorApp? e with
  | some (c, []) => (unOpTable0.find? (·.1 == c)).map (·.2)
  | some (c, [n]) =>
    match unOpTable1.find? (·.1 == c), readNat n with
    | some (_, f), some k => some (f k)
    | _, _ => none
  | _ => none

/-- A `BitVec w` constant: `BitVec.ofNat w' n` with `w' = w`. -/
def readBitVec (w : Nat) (e : Expr) : Option (BitVec w) :=
  match ctorApp? e with
  | some (c, [w', n]) =>
    if c == bvOfNatN then
      match readNat w', readNat n with
      | some w'', some k => if w'' == w then some (BitVec.ofNat w k) else none
      | _, _ => none
    else none
  | _ => none

variable (find? : Name → Option ConstantInfo)

/-- A `BVExpr w`. -/
def readExpr : Nat → (w : Nat) → Expr → Option (BVExpr w)
  | 0, _, _ => none
  | fuel + 1, w, e =>
    match unfold? find? e with
    | some v => readExpr fuel w v
    | none =>
    match ctorApp? e with
    | some (c, args) =>
      if c == exVarN then
        match args with
        | [w', i] => do
          let w'' ← readNat w'
          let k ← readNat i
          if w'' == w then some (.var k) else none
        | _ => none
      else if c == exConstN then
        match args with
        | [w', v] => do
          let w'' ← readNat w'
          if w'' == w then some (.const (← readBitVec w v)) else none
        | _ => none
      else if c == exExtractN then
        match args with
        | [w0, s, l, x] => do
          let w0' ← readNat w0
          let s' ← readNat s
          let l' ← readNat l
          let x' ← readExpr fuel w0' x
          if h : l' = w then some (h ▸ BVExpr.extract s' l' x') else none
        | _ => none
      else if c == exBinN then
        match args with
        | [w', l, op, r] => do
          let w'' ← readNat w'
          if w'' == w then some (.bin (← readExpr fuel w l) (← readBinOp op) (← readExpr fuel w r))
          else none
        | _ => none
      else if c == exUnN then
        match args with
        | [w', op, x] => do
          let w'' ← readNat w'
          if w'' == w then some (.un (← readUnOp op) (← readExpr fuel w x)) else none
        | _ => none
      else if c == exAppendN then
        match args with
        | [l, r, w', x, y, _] => do
          let l' ← readNat l
          let r' ← readNat r
          let w'' ← readNat w'
          if w'' == w then
            if h : w = l' + r' then
              some (.append (← readExpr fuel l' x) (← readExpr fuel r' y) h)
            else none
          else none
        | _ => none
      else if c == exReplicateN then
        match args with
        | [w0, w', n, x, _] => do
          let w0' ← readNat w0
          let w'' ← readNat w'
          let n' ← readNat n
          if w'' == w then
            if h : w = w0' * n' then
              some (.replicate n' (← readExpr fuel w0' x) h)
            else none
          else none
        | _ => none
      else if c == exShlN || c == exShrN || c == exAshrN then
        match args with
        | [m, n, x, y] => do
          let m' ← readNat m
          let n' ← readNat n
          if h : m' = w then
            let x' ← readExpr fuel m' x
            let y' ← readExpr fuel n' y
            some (h ▸ (if c == exShlN then BVExpr.shiftLeft x' y'
              else if c == exShrN then BVExpr.shiftRight x' y'
              else BVExpr.arithShiftRight x' y'))
          else none
        | _ => none
      else none
    | none => none

def readPred (fuel : Nat) (e : Expr) : Option BVPred :=
  match unfold? find? e with
  | some v => match fuel with
    | 0 => none
    | f + 1 => readPred f v
  | none =>
  match ctorApp? e with
  | some (c, [w, l, op, r]) =>
    if c == predBinN then do
      let w' ← readNat w
      some (.bin (← readExpr find? fuel w' l) (← readBinPred op) (← readExpr find? fuel w' r))
    else none
  | some (c, [w, x, i]) =>
    if c == predLsbN then do
      let w' ← readNat w
      some (.getLsbD (← readExpr find? fuel w' x) (← readNat i))
    else none
  | _ => none

/-- A `BVLogicalExpr` (`BoolExpr BVPred`; the type argument is not read). -/
def readLogical : Nat → Expr → Option BVLogicalExpr
  | 0, _ => none
  | fuel + 1, e =>
    match unfold? find? e with
    | some v => readLogical fuel v
    | none =>
    match ctorApp? e with
    | some (c, args) =>
      if c == beLiteralN then
        match args with
        | [_, p] => (readPred find? fuel p).map .literal
        | _ => none
      else if c == beConstN then
        match args with
        | [_, b] => (readBool b).map .const
        | _ => none
      else if c == beNotN then
        match args with
        | [_, x] => (readLogical fuel x).map .not
        | _ => none
      else if c == beGateN then
        match args with
        | [_, g, x, y] => do some (.gate (← readGate g) (← readLogical fuel x) (← readLogical fuel y))
        | _ => none
      else if c == beIteN then
        match args with
        | [_, d, x, y] => do
          some (.ite (← readLogical fuel d) (← readLogical fuel x) (← readLogical fuel y))
        | _ => none
      else none
    | none => none

/-- The certificate: a string literal, possibly behind definitions. -/
def readStr : Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, e =>
    match e with
    | .lit (.strVal s) => some s
    | _ => match unfold? find? e with
      | some v => readStr fuel v
      | none => none

/-- The reading fuel: the formula's syntactic size bounds every reading
(each step consumes a node or unfolds a definition), so any large bound
is complete; the number is a guard, not a measurement. -/
def readFuel : Nat := 1 <<< 40

end BVUnsat

open BVUnsat in
/-- **The gate**: `U E C _` is typed `Unsat E` without inferring its
third argument. -/
def bvUnsatOk (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) (E C : Expr) : Bool :=
  E.looseBVarsBounded 0 && !E.hasFvar && C.looseBVarsBounded 0 && pinsOk find? findProj? &&
  match readLogical find? readFuel E, readStr find? readFuel C with
  | some e, some c => Std.Tactic.BVDecide.Reflect.verifyBVExpr e c
  | _, _ => false

/-- The type the gate gives `U E C _`. -/
def bvUnsatType (E : Expr) : Expr := .app (.const bvUnsatName []) E

/-- A native `bv_decide` axiom: installed as a stub of type `True`
whose every use outside the recognised position declines. -/
def isBVNativeAxName : Name → Bool
  | .str (.str (.str _ "_native") "bv_decide") ax => ax.startsWith "ax"
  | _ => false

end ConLeche

namespace ConLeche

/-- The third argument is a stored constant without level arguments
(so it reads; its type is not inferred). -/
def bvUnsatArgOk (find? : Name → Option ConstantInfo) : Expr → Bool
  | .const n [] =>
    match find? n with
    | some ci => ci.toConstantVal.levelParams.isEmpty
    | none => false
  | _ => false

/-- `f a` is `U E C a`, `a` a stored constant, and the gate accepts `E C`. -/
def bvUnsatHit (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) (f a : Expr) : Bool :=
  match f with
  | .app (.app (.const c []) E) C => c == unsatThmName && bvUnsatArgOk find? a && bvUnsatOk find? findProj? E C
  | _ => false

/-- The type of `f a` for a `bvUnsatHit` head `f = U E C`. -/
def bvUnsatTypeOf : Expr → Expr
  | .app (.app _ E) _ => bvUnsatType E
  | _ => default

/-- A stored native-axiom stub. -/
def bvNativeStub : ConstantInfo → Bool
  | .axiomInfo cv => isBVNativeAxName cv.name
  | _ => false

def bvNativeUseMsg (n : Name) : String :=
  s!"non-standard axiom ({n}), apparently added by the `bv_decide` tactic, used \
    outside a natively checked certificate; con-leche does not support such axioms \
    at the moment"

end ConLeche

namespace ConLeche

/-- The spine shape `U E C a rest` (the gate is `bvUnsatSkip`'s). -/
def bvUnsatSpine (h : Expr) (args : List Expr) : Option (Expr × Expr × Expr × List Expr) :=
  match h, args with
  | .const c [], E :: C :: a :: rest => if c == unsatThmName then some (E, C, a, rest) else none
  | _, _ => none

end ConLeche

namespace ConLeche

/-- **The argument check `U E C a` skips** (both cores): the gate accepts
and the application's type is `Unsat E` (the head's Π-type body at `a`). -/
def bvUnsatSkip (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) (f a body : Expr) : Bool :=
  bvUnsatHit find? findProj? f a && !f.hasFvar && !a.hasFvar && !body.hasFvar &&
    body.instantiate1 a == bvUnsatTypeOf f

end ConLeche
