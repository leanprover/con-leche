module

public import ConLeche.Kernel.PropRead
import ConLeche.Kernel.Level
import ConLeche.Kernel.ExprOps
public import ConLeche.Kernel.Basis

@[expose] public section

/-!
# The checker core's fuel-free helpers

The definitions of the core checker that mention no monad, no
`CoreFns` record and no fuel: the delta step and its readers
(`unfoldDefinition`, `unfoldableHead`, `headHint`, `sameConstHeads`),
the literal shapes and their guards (`natLitToConstructor`,
`natLitStored`, `strLitToConstructor`, `strLitStored`, `litShapeOk`,
`rawNatLit?`), the certified `Nat` operations' names, recurrences,
reducts and pins (`natOpNames`, `natDivModNames`, `natOpEquations`,
`natOpResult`, `natOpStoredOk`, …), the structure-η fabrications
(`etaProjs`, `etaFabArgsE`, `andRescueSlots`), the rule
data (`etaRescueOk`, `recFireComparands`), the ι case split
(`iotaCtorNeverProp`, `iotaCase3`) and the tower entry's readers
(`projGuardRows`, `ProjEntry.typeAt`).

Split out of `ConLeche/Kernel/Core.lean` at task #305 (prep): a
relational description of the core's moves — a relation over `Expr`
and `Env` — must name these without importing the executable bodies,
and every one of them is exactly what such a relation needs.  The
bodies (`whnfCoreBody`, `whnfBody`, `inferBody`, `defeqBody`,
the knot and the fuel constants) stay in `Core.lean`,
which re-exports this module, so every importer of `Core` sees the
names unchanged.  Nothing here was rewritten: the definitions keep
their names, docstrings, attributes and relative order.
-/

namespace ConLeche

/-- **Is the spine's head neither a λ nor a `let`** (nor a loose bound
variable)?  The io grade's claim of such a term, where the term is not
the point, is a membership of its io-inferred type (task #342 L18,
`IORel`): a hereditary claim arises only at an abstraction.  A term in
weak-head normal form that is not a λ has such a head. -/
def Expr.ioNeutral (e : Expr) : Bool :=
  match e.getAppFn with
  | .lam .. | .letE .. | .bvar _ => false
  | _ => true


/-- Is the expression headed by a stored constructor? -/
def isCtorApp (env : Env) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const c _ =>
    match env.find? c with
    | some (.ctorInfo _ _ _) => true
    | _ => false
  | _ => false

/-- **A stored inductive's result sort, read where it is needed**: the sort
its stored type ends in.  `none` where the type does not end in one.
Nothing about it is stored. -/
def formerResSort (ty : Expr) : Option Level :=
  match ty.piResult with
  | .sort s => some s
  | _ => none

/-- A stored former that does not show its telescope. -/
def formerDefHeaded (cv : ConstantVal) : Bool :=
  (formerResSort cv.type).isNone

/-- **The family's result-sort zero-ness datum**, read off its type; where the
sort is not read, `ifAllZero []`, "zero at every valuation", which no rescue
passes. -/
def formerZ (cvT : ConstantVal) : PropWhen :=
  match formerResSort cvT.type with
  | some s => Level.zeronessOf s
  | none => .ifAllZero []

/-- Is a stored inductive's result sort, at the given level
instantiation, provably nonzero (official `is_never_zero`)?  The
official kernel's structure rescue (`to_cnstr_when_structure`)
requires this of the major's type; `majorToCtor`'s structure-η
rescue mirrors it (`Sort u` at a concrete level such as `Unit`'s `1` passes, the
parameter `u` itself does not).  The instantiated zero-ness datum is
unsatisfiable exactly where the instantiated sort is never zero. -/
def formerNeverZero (cvT : ConstantVal) (us : List Level) : Bool :=
  (Level.substPW cvT.levelParams us (formerZ cvT)).isNever

/-- **The family a constructor's type concludes in**: its former and its
capabilities.  `none` where its type concludes in no stored inductive. -/
def ctorFamily (find? : Name → Option ConstantInfo) (cvj : ConstantVal) :
    Option (ConstantVal × IndCaps) :=
  match (cvj.type.piResult).getAppFn with
  | .const T _ =>
    match find? T with
    | some (.indInfo cvT caps) => some (cvT, caps)
    | _ => none
  | _ => none

/-- Unfold the (application of a) definition at the head, one step.
`none` when the head is not an unfoldable constant.  **Theorems are
opaque to reduction**: a stored `thmInfo` never unfolds, so whether a
declaration type-checks never depends on a theorem's value — this
anticipates https://github.com/leanprover/lean4/pull/14896 (theorems
become opaque to the kernel: `is_delta` stops unfolding them).  The
one known input whose typing needs a theorem to unfold, the arena's
`subject-reduction-redex`, is rejected (an accept-subset of the
reference kernels until that PR lands). -/
def unfoldDefinition (env : Env) (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const n us =>
    match env.find? n with
    | some (.defnInfo cv value _) =>
      if us.length = cv.levelParams.length then
        some (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
          e.getAppArgs)
      else none
    | _ => none
  | _ => none

/-- May the delta step unfold `e`'s head — is it a constant whose
stored declaration carries a value at a matching level-parameter count
(the official kernel's `is_delta`)?  This is the *decision* the lazy
delta step takes; the unfolding itself is materialized only inside the
branch that consumes it (`unfoldDefinition`), never in both slots of a
match scrutinee.  By construction
`unfoldableHead env e = (unfoldDefinition env e).isSome`. -/
def unfoldableHead (env : Env) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n us =>
    match env.find? n with
    | some (.defnInfo cv _ _) => us.length == cv.levelParams.length
    | _ => false
  | _ => false

/-- The reducibility hint of the constant at the head of `e` (`opaque`
when the head is not a stored definition — a theorem included, which
never unfolds). -/
def headHint (env : Env) (e : Expr) : ReducibilityHint :=
  match e.getAppFn with
  | .const n _ =>
    match env.find? n with
    | some (.defnInfo _ _ hint) => hint
    | _ => .opaque
  | _ => .opaque

/-- Are `a` and `b` applications of the *same* constant (the lazy delta
same-head short-circuit: try level and spine congruence before
unfolding both sides)?  Mirrors the official kernel's
`try_eq_const_app`: both sides must actually be applications. -/
def sameConstHeads : Expr → Expr → Bool
  | .app f₁ _, .app f₂ _ =>
    match f₁.getAppFn, f₂.getAppFn with
    | .const n₁ _, .const n₂ _ => n₁ == n₂
    | _, _ => false
  | _, _ => false

/-- The constructor form of a `Nat` literal, one layer:
`n + 1` becomes `Nat.succ (lit n)`, `0` becomes `Nat.zero` (the
official kernel's `natLitToConstructor`, used on recursor majors). -/
def natLitToConstructor (n : Nat) : Expr :=
  match n with
  | 0 => .const natZeroName []
  | k + 1 => .app (.const natSuccName []) (.lit (.natVal k))

/-- The stored `Nat` declaration has the expected shape. -/
def natIndOk : Option ConstantInfo → Bool
  | some (.indInfo cv _) =>
    cv.levelParams.isEmpty && cv.type == .sort (.succ .zero)
  | _ => false

/-- The stored `Nat.zero` declaration has the expected shape. -/
def natZeroOk : Option ConstantInfo → Bool
  | some (.ctorInfo cv _ _) =>
    cv.levelParams.isEmpty && cv.type == .const natName []
  | _ => false

/-- The stored `Nat.succ` declaration has the expected shape. -/
def natSuccOk : Option ConstantInfo → Bool
  | some (.ctorInfo cv _ _) =>
    cv.levelParams.isEmpty &&
    (match cv.type with
     | .forallE (.const c1 []) (.const c2 []) =>
       c1 == natName && c2 == natName
     | _ => false)
  | _ => false

/-- `Nat`, `Nat.zero` and `Nat.succ` are stored with exactly the expected kinds, level parameters and
types.  The model interprets a literal by iterating the `Nat.succ` value on the `Nat.zero` value and
reads those shapes off this; a certified operation's check asks it of the environment it runs at. -/
def natLitSupported (env : Env) : Bool :=
  natIndOk (env.find? natName) && natZeroOk (env.find? natZeroName) &&
    natSuccOk (env.find? natSuccName)

/-- Whether a `Nat` literal's constants are stored.  What they are is the declarations' own check
(`litShapeOk`), so this reads no type: it says only that a literal may be read at all. -/
def natLitStored (env : Env) : Bool :=
  (env.find? natName).isSome && (env.find? natZeroName).isSome && (env.find? natSuccName).isSome

/-- Do all constants referenced in `e` (including inside `fvar` type
annotations) resolve in `env`?  A `Nat` literal implicitly references
the `Nat` basis constants (and a `String` literal additionally the
string-support constants).  Checked once per declaration; keeps the
environment well-formedness invariant syntactic. -/
def Expr.constsResolve (env : Env) : Expr → Bool
  | .bvar _ | .sort _ => true
  | .lit (.natVal _) =>
    (env.find? natName).isSome && (env.find? natZeroName).isSome &&
      (env.find? natSuccName).isSome
  | .lit (.strVal _) =>
    -- a string literal implicitly references the `Nat` trio (its
    -- character numerals) and the seven string-support constants
    (env.find? natName).isSome && (env.find? natZeroName).isSome &&
      (env.find? natSuccName).isSome && (env.find? stringName).isSome &&
      (env.find? stringOfListName).isSome && (env.find? listName).isSome &&
      (env.find? listNilName).isSome && (env.find? listConsName).isSome &&
      (env.find? charName).isSome && (env.find? charOfNatName).isSome
  | .const n _ => (env.find? n).isSome
  | .fvar _ ty => ty.constsResolve env
  | .app f a => f.constsResolve env && a.constsResolve env
  | .lam ty body | .forallE ty body =>
    ty.constsResolve env && body.constsResolve env
  | .letE ty val body =>
    ty.constsResolve env && val.constsResolve env && body.constsResolve env
  | .proj s _ e => (env.find? s).isSome && e.constsResolve env

/-- Convert a `Nat`-literal major premise to constructor form, one
layer; anything else passes through. -/
def litToCtorIfNat (env : Env) : Expr → Expr
  | .lit (.natVal n) =>
    if natLitStored env then natLitToConstructor n else .lit (.natVal n)
  | e => e

/-- A `Nat` literal reading of a whnf'd expression: literals and the
`Nat.zero` constant (the official kernel's `rawNatLitExt?`). -/
def rawNatLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .const c [] => if c = natZeroName then some 0 else none
  | _ => none

/-! ## String literals

A string literal unfolds on demand to `String.ofList [c₁, …, cₙ]` with
each character built by `Char.ofNat` from a `Nat` literal — the
reference kernels' `strLitToConstructor` (lean4lean `Expr.lean`, nanoda
`expr.rs`), mirrored exactly.  The names below are *pinned* like the
`Nat` literal names: a declaration at one of them has exactly the expected
type (`litShapeOk`, checked at the declaration), which is what the model's
interpretation of a string literal reads its meaning off.  A string
literal in the input without its constants is a positively detected
unsupported feature: inference *declines* (exit 2), and so does the
constant-resolution guard's error path (`unresolvedConstsErrorL`). -/

/-- The constructor form of a `String` literal:
`String.ofList (List.cons.{0} Char (Char.ofNat (lit c₁)) (… (List.nil.{0}
Char)))` — the official kernel's `strLitToConstructor`, spelling as in
lean4lean (`Expr.strLitToConstructor`) and nanoda
(`str_lit_to_constructor`). -/
def strLitToConstructor (s : String) : Expr :=
  .app (.const stringOfListName []) <|
    s.toList.foldr
      (init := .app (.const listNilName [.zero]) (.const charName []))
      fun c e =>
        .app (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e

/-- The stored `String` declaration has the expected shape
(`String : Type`, no level parameters; any constant kind). -/
def stringTyOk : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      ci.toConstantVal.type == .sort (.succ .zero)
  | none => false

/-- The stored `Char` declaration has the expected shape (`Char : Type`,
no level parameters). -/
def charTyOk : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      ci.toConstantVal.type == .sort (.succ .zero)
  | none => false

/-- The stored `List` declaration has the expected shape
`List.{p} : Type p → Type p`. -/
def listTyOk : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE (.sort u1) (.sort u2) =>
         u1 == .succ (.param p) && u2 == .succ (.param p)
       | _ => false)
    | _ => false
  | none => false

/-- The stored `List.nil` declaration has the expected shape
`List.nil.{p} : ∀ (α : Type p), List.{p} α`. -/
def listNilTyOk : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE (.sort u1) (.app (.const l1 us1) (.bvar 0)) =>
         u1 == .succ (.param p) && l1 == listName && us1 == [.param p]
       | _ => false)
    | _ => false
  | none => false

/-- The stored `List.cons` declaration has the expected shape
`List.cons.{p} : ∀ (α : Type p) (head : α) (tail : List.{p} α),
List.{p} α`. -/
def listConsTyOk : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE (.sort u1)
           (.forallE (.bvar 0)
             (.forallE (.app (.const l1 us1) (.bvar 1))
               (.app (.const l2 us2) (.bvar 2)))) =>
         u1 == .succ (.param p) && l1 == listName && l2 == listName &&
           us1 == [.param p] && us2 == [.param p]
       | _ => false)
    | _ => false
  | none => false

/-- The stored `Char.ofNat` declaration has the expected
shape `Char.ofNat : Nat → Char`. -/
def charOfNatTyOk : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      (match ci.toConstantVal.type with
       | .forallE (.const c1 []) (.const c2 []) =>
         c1 == natName && c2 == charName
       | _ => false)
  | none => false

/-- The stored `String.ofList` declaration has the expected
shape `String.ofList : List.{0} Char → String`. -/
def stringOfListTyOk : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      (match ci.toConstantVal.type with
       | .forallE (.app (.const l1 us1) (.const c1 [])) (.const c2 []) =>
         l1 == listName && us1 == [.zero] && c1 == charName &&
           c2 == stringName
       | _ => false)
  | none => false

/-- `natLitSupported` plus `String`, `String.ofList`, `List`, `List.nil`, `List.cons`, `Char` and
`Char.ofNat` stored with exactly the expected level parameters and types.  The model interprets a
string literal through the values of these constants and reads those shapes off this.  (The reference kernels only check
*existence* of `Char.ofNat` and `String.ofList`; the type pins are what
makes the interpretation well-defined, in the spirit of the `Nat`
literal guard.) -/
def strLitSupported (env : Env) : Bool :=
  natLitSupported env &&
    stringTyOk (env.find? stringName) &&
    stringOfListTyOk (env.find? stringOfListName) &&
    listTyOk (env.find? listName) &&
    listNilTyOk (env.find? listNilName) &&
    listConsTyOk (env.find? listConsName) &&
    charTyOk (env.find? charName) &&
    charOfNatTyOk (env.find? charOfNatName)

/-- Whether a `String` literal's constants are stored (`natLitStored`). -/
def strLitStored (env : Env) : Bool :=
  natLitStored env && (env.find? stringName).isSome && (env.find? stringOfListName).isSome &&
    (env.find? listName).isSome && (env.find? listNilName).isSome &&
    (env.find? listConsName).isSome && (env.find? charName).isSome &&
    (env.find? charOfNatName).isSome

/-- **The shape a declaration at a literal's name must have**: what a literal's meaning reads off
it.  Checked at the declaration, once; nothing at a literal's use compares a stored type. -/
def litShapeOk (c : ConstantInfo) : Bool :=
  if c.name = natName then natIndOk (some c)
  else if c.name = natZeroName then natZeroOk (some c)
  else if c.name = natSuccName then natSuccOk (some c)
  else if c.name = stringName then stringTyOk (some c)
  else if c.name = stringOfListName then stringOfListTyOk (some c)
  else if c.name = listName then listTyOk (some c)
  else if c.name = listNilName then listNilTyOk (some c)
  else if c.name = listConsName then listConsTyOk (some c)
  else if c.name = charName then charTyOk (some c)
  else if c.name = charOfNatName then charOfNatTyOk (some c)
  else true

/-! ## Structural-Nat literal acceleration

The official kernel accelerates the structural `Nat` operations on
literals (GMP-backed there).  Here the fast path is *certified*: an
operation participates only when its defining recurrence equations
hold by definitional equality — checked once, at install: `checkDecl`
positively rejects a nonstandard definition under one of these names,
so *presence in the store is the certificate* (no runtime flag, no
re-checking; a reduction-time re-check would in fact livelock — the
certification's own `pred zero` equation re-enters the fast path).

The certification runs in the environment *before* the operation is
stored, on the equations with the operation's self-references replaced
by its stored definition value (`Expr.substConst0`): running it
after insertion would let the operation's own just-enabled fast path
discharge its all-literal-argument equations (`pred zero ≡ zero`,
`beq zero zero ≡ true`) vacuously — accepting definitions that
disagree with the fast path on those points, which is unsound.  The
install also pins the operation's and its dependencies' types to the
expected `Nat → … → Nat`/`Bool` shapes (`natOpStoredOk`): the model
reads the operations' function-space memberships off these shapes.

The environment model carries the matching semantic clause: a stored
definition under one of these names satisfies its recurrences, from
which meta-level induction over the literal yields the computed
value.  WF-recursive operations (`div`, `mod`, `gcd`) and string
literals are deferred. -/

def natPredName : Name := natName.str "pred"
def natAddName : Name := natName.str "add"
def natSubName : Name := natName.str "sub"
def natMulName : Name := natName.str "mul"
def natPowName : Name := natName.str "pow"
def natBeqName : Name := natName.str "beq"
def natBleName : Name := natName.str "ble"
def natDivName : Name := natName.str "div"
def natModName : Name := natName.str "mod"
def natGcdName : Name := natName.str "gcd"
def natLandName : Name := natName.str "land"
def natLorName : Name := natName.str "lor"
def natXorName : Name := natName.str "xor"
def natShiftLeftName : Name := natName.str "shiftLeft"
def natShiftRightName : Name := natName.str "shiftRight"
def boolName : Name := .str .anonymous "Bool"

/-- `eagerReduce` (`Init/Core.lean`: `def eagerReduce (a : α) : α := a`),
the gadget that sets the official kernel's eager flag (task #353). -/
def eagerReduceName : Name := .str .anonymous "eagerReduce"

/-- Is `e` of the form `eagerReduce _ _` — official `is_eager_reduce`
(`type_checker.cpp`): the head constant `eagerReduce`, exactly two
arguments, any universe levels. -/
@[inline] def Expr.isEagerReduce : Expr → Bool
  | .app (.app (.const c _) _) _ => c == eagerReduceName
  | _ => false
def boolTrueName : Name := boolName.str "true"
def boolFalseName : Name := boolName.str "false"

/-- Is `e` the constant `Bool.true` — the official kernel's
`is_constant(e, Bool.true)` (`type_checker.cpp:1097`): the name, no
universe levels. -/
def Expr.isBoolTrue : Expr → Bool
  | .const c [] => c == boolTrueName
  | _ => false

/-- The certified structural-`Nat` operations.  Six of them
(`add sub mul pow beq ble`) carry a literal fast path; `Nat.pred` is
here without one — it has no fast path (official's `reduce_nat` folds
nothing unary but `Nat.succ`), but `Nat.sub`'s recurrence
`sub x (succ y) = pred (sub x y)` names it, so its own recurrences
must be certified for `sub`'s literal fold to be sound. -/
def natOpNames : List Name :=
  [natPredName, natAddName, natSubName, natMulName, natPowName,
   natBeqName, natBleName]

/-- The WF-recursive operations with a *pinned-declaration* certified
fast path: at install, `checkDecl` compares the stream's definition
against a vendored pin of the toolchain's own (helper-unfolded)
definition by definitional equality, and then checks the pinned
`Nat.ble`-guarded characterization certificates
(`ConLeche/Kernel/NatOpPins.lean`) like theorem declarations — without
installing them.  Presence in the store is therefore again the
capability: a stored operation under one of these names has passed pin
and certificates, or the install declined.  (The name is historic:
the family started with `Nat.div`/`Nat.mod` and now covers every
pin-certified WF-recursive kernel-accelerated `Nat` operation —
`Nat.log2` left the list when its fast path did, official folding no
unary operation but `Nat.succ`.) -/
def natDivModNames : List Name :=
  [natDivName, natModName, natGcdName, natLandName, natLorName,
   natXorName, natShiftLeftName, natShiftRightName]

/-- **The certified operations' names**: the fast path fires on them by name, so only a
definition may take one, and its job holds it to the pin; any other declaration at such a
name is refused (`checkConstantVal`, `reservedRecName`). -/
def natOpName (n : Name) : Bool :=
  natOpNames.contains n || natDivModNames.contains n

/-! ## The names the environment's own guards look up

`natLitStored` and `strLitStored` decide whether a literal may be READ,
by looking ten fixed names up in the store; `litShapeOk` says what a
declaration at one of them is.  Three of them (`Nat`, `Nat.zero`,
`Nat.succ`) are reserved basis names, so no stream declaration can ever
fill or change them; the other seven — `String`, `String.ofList`, `List`,
`List.nil`, `List.cons`, `Char`, `Char.ofNat` — are ORDINARY stream
declarations, and a stream is free to install them (it must: that is how
a stream earns string literals).

What must not happen is a *recursor* taking one of these names: it would
never pass the shape test as what it is.  The block's check refuses such
a name outright (`blockRecNamesUnreserved`,
`ConLeche/Kernel/Inductives/BlockParts.lean`). -/

/-- The ten names the two literal guards look up: the `Nat` guard's
three and the `String` guard's seven. -/
def litGuardNames : List Name :=
  [natName, natZeroName, natSuccName,
   stringName, stringOfListName, listName, listNilName, listConsName,
   charName, charOfNatName]

/-- **A name no block RECURSOR may take**: one the pinned basis blocks
reserve, one a literal guard looks up, one of the certified `Nat`
operations (whose presence in the store IS their certificate, so a
recursor stored under such a name would claim a capability nothing
certified), or `Bool` and its two constructors, whose stored entries the
certified operations' guards read (`natOpTyPinned`, `natOpGuard`; task
#431: the stored recursors replace the generated ones' types, which
must not move a guard).  Type formers and constructors are NOT held to this — a
stream must be able to declare `List`, `List.cons` and `Nat.add` —
which is why the block install spends this predicate on the recursors
alone and keeps `reservedBasisNames` for every declaration. -/
def reservedRecName (n : Name) : Bool :=
  reservedBasisNames.contains n || litGuardNames.contains n ||
    natOpNames.contains n || natDivModNames.contains n ||
    n == boolName || n == boolTrueName || n == boolFalseName

/-- The operations (transitively) involved in `c`'s recurrences. -/
def natOpDeps (c : Name) : List Name :=
  if c = natPredName then [natPredName]
  else if c = natAddName then [natAddName]
  else if c = natSubName then [natPredName, natSubName]
  else if c = natMulName then [natAddName, natMulName]
  else if c = natPowName then [natAddName, natMulName, natPowName]
  else if c = natBeqName then [natBeqName]
  else if c = natBleName then [natBleName]
  else if c = natDivName then [natPredName, natSubName, natBleName, natDivName]
  else if c = natModName then [natPredName, natSubName, natBleName, natModName]
  else if c = natGcdName then [natBleName, natModName, natGcdName]
  else if c = natLandName then
    [natAddName, natMulName, natBleName, natDivName, natModName, natLandName]
  else if c = natLorName then
    [natAddName, natSubName, natMulName, natBleName, natDivName, natModName,
     natLorName]
  else if c = natXorName then
    [natAddName, natMulName, natBleName, natDivName, natModName, natXorName]
  else if c = natShiftLeftName then
    [natSubName, natMulName, natBleName, natShiftLeftName]
  else if c = natShiftRightName then
    [natSubName, natBleName, natDivName, natShiftRightName]
  else []

/-- The defining recurrence equations of a structural-Nat operation,
over constructor forms with free variables `d`, `d + 1` (the equation
sides are binder-free). -/
def natOpEquations (d : Nat) (c : Name) : List (Expr × Expr) :=
  let natTy : Expr := .const natName []
  let x : Expr := .fvar d natTy
  let y : Expr := .fvar (d + 1) natTy
  let z : Expr := .const natZeroName []
  let s : Expr → Expr := (.app (.const natSuccName []) ·)
  let ap1 : Name → Expr → Expr := fun n a => .app (.const n []) a
  let ap2 : Name → Expr → Expr → Expr := fun n a b =>
    .app (.app (.const n []) a) b
  let bT : Expr := .const boolTrueName []
  let bF : Expr := .const boolFalseName []
  if c = natPredName then
    [(ap1 c z, z), (ap1 c (s x), x)]
  else if c = natAddName then
    [(ap2 c x z, x), (ap2 c x (s y), s (ap2 c x y))]
  else if c = natSubName then
    [(ap2 c x z, x), (ap2 c x (s y), ap1 natPredName (ap2 c x y))]
  else if c = natMulName then
    [(ap2 c x z, z), (ap2 c x (s y), ap2 natAddName (ap2 c x y) x)]
  else if c = natPowName then
    [(ap2 c x z, s z), (ap2 c x (s y), ap2 natMulName (ap2 c x y) x)]
  else if c = natBeqName then
    [(ap2 c z z, bT), (ap2 c z (s y), bF), (ap2 c (s x) z, bF),
     (ap2 c (s x) (s y), ap2 c x y)]
  else if c = natBleName then
    [(ap2 c z y, bT), (ap2 c (s x) z, bF), (ap2 c (s x) (s y), ap2 c x y)]
  else []

/-- The reduct of op `c` on literal arguments (`pred` ignores the
second slot). -/
def natOpResult (c : Name) (a b : Nat) : Option Expr :=
  if c = natPredName then some (.lit (.natVal (a - 1)))
  else if c = natAddName then some (.lit (.natVal (a + b)))
  else if c = natSubName then some (.lit (.natVal (a - b)))
  else if c = natMulName then some (.lit (.natVal (a * b)))
  else if c = natPowName then
    -- the divergence audit's S2: official `reduce_pow` refuses exponents
    -- above `ReducePowMaxExp = 1 << 24` (`type_checker.cpp:616-627`) and
    -- lets `Nat.pow` unfold instead — the blow-up protection, mirrored
    if b > 16777216 then none else some (.lit (.natVal (a ^ b)))
  else if c = natDivName then some (.lit (.natVal (a / b)))
  else if c = natModName then some (.lit (.natVal (a % b)))
  else if c = natGcdName then some (.lit (.natVal (Nat.gcd a b)))
  else if c = natLandName then some (.lit (.natVal (Nat.land a b)))
  else if c = natLorName then some (.lit (.natVal (Nat.lor a b)))
  else if c = natXorName then some (.lit (.natVal (Nat.xor a b)))
  else if c = natShiftLeftName then
    some (.lit (.natVal (Nat.shiftLeft a b)))
  else if c = natShiftRightName then
    some (.lit (.natVal (Nat.shiftRight a b)))
  else if c = natBeqName then
    some (.const (if a = b then boolTrueName else boolFalseName) [])
  else if c = natBleName then
    some (.const (if a <= b then boolTrueName else boolFalseName) [])
  else none

/-- Stored-constant guards for op `c`: the `Nat` basis, every
dependency stored as a definition, and (for the `Bool`-valued ops and
the `ble`-guarded `div`/`mod`, whose semantic clauses mention the
`Bool` constructor values) the `Bool` constructors stored, level-free,
at the type `Bool` itself (their values must be members of `Bool`'s,
so that a recurrence `beq 0 0 = true` relates two members of one
type). -/
def natOpGuard (env : Env) (c : Name) : Bool :=
  natLitSupported env &&
  (natOpDeps c).all (fun n => match env.find? n with
    | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
    | _ => false) &&
  (if c = natBeqName || c = natBleName || natDivModNames.contains c then
    (match env.find? boolTrueName with
      | some ci => ci.toConstantVal.levelParams.isEmpty &&
          ci.toConstantVal.type == .const boolName []
      | none => false) &&
    (match env.find? boolFalseName with
      | some ci => ci.toConstantVal.levelParams.isEmpty &&
          ci.toConstantVal.type == .const boolName []
      | none => false)
   else true)

/-- The pin-certified WF-recursive `Nat` operations, as a *safety
net*: the preceding certified branches normally intercept literal
applications, so this list only fires when a capability is absent
(op not stored, or a dependency missing — a mismatching declaration
already declined at install); such a *literal application* is then
positively declined (arena exit 2) rather than ground unary through
the fuel recursion.  Declaring the functions themselves is
unaffected: only the reduction path declines. -/
def natOpWfNames : List Name :=
  [natDivName, natModName, natGcdName, natLandName, natLorName,
   natXorName, natShiftLeftName, natShiftRightName]

/-- Substitute the level-monomorphic constant `n` by `r` through an
application spine (the certification equations' self-references; the
equation sides are binder-free, so only `app` recurses). -/
def Expr.substConst0 (n : Name) (r : Expr) : Expr → Expr
  | .const c us => if c = n ∧ us = [] then r else .const c us
  | .app f a => .app (Expr.substConst0 n r f) (Expr.substConst0 n r a)
  | e => e

/-- Substitute the level-monomorphic constant `n` by the *closed* term
`r` everywhere, including under binders (the div/mod certificate
statements' and proofs' references to the pinned operation; `r` being
closed, no lifting is needed).  `fvar` annotations are not entered:
the substitution runs on closed input terms only. -/
def Expr.substConstAll (n : Name) (r : Expr) : Expr → Expr
  | .const c us => if c = n ∧ us = [] then r else .const c us
  | .app f a => .app (Expr.substConstAll n r f) (Expr.substConstAll n r a)
  | .lam ty b =>
    .lam (Expr.substConstAll n r ty) (Expr.substConstAll n r b)
  | .forallE ty b =>
    .forallE (Expr.substConstAll n r ty) (Expr.substConstAll n r b)
  | .letE ty v b =>
    .letE (Expr.substConstAll n r ty) (Expr.substConstAll n r v)
      (Expr.substConstAll n r b)
  | .proj s i e => .proj s i (Expr.substConstAll n r e)
  | e => e

/-- The pinned codomain of a structural-Nat operation: `Bool` (itself
stored level-monomorphically at type `Sort 1`) for the comparisons,
`Nat` otherwise. -/
def natOpCod (env : Env) (c : Name) (e : Expr) : Bool :=
  if c = natBeqName || c = natBleName then
    e == .const boolName [] &&
    (match env.find? boolName with
     | some ci => ci.toConstantVal.levelParams.isEmpty &&
         ci.toConstantVal.type == .sort (.succ .zero)
     | none => false)
  else e == .const natName []

/-- The pinned type of a certified `Nat` operation:
`Nat → Nat` for the unary `pred`, `Nat → Nat → Nat` for the arithmetic
operations, `Nat → Nat → Bool` for the comparisons.  The model reads
the operations' function-space memberships off this shape. -/
def natOpTyPinned (env : Env) (c : Name) (ty : Expr) : Bool :=
  if c = natPredName then
    match ty with
    | .forallE dom body =>
      dom == .const natName [] && natOpCod env c body
    | _ => false
  else
    match ty with
    | .forallE dom (.forallE dom2 body) =>
      dom == .const natName [] && dom2 == .const natName [] &&
      natOpCod env c body
    | _ => false

/-- Op `n` is stored as a level-monomorphic definition with the pinned
type. -/
def natOpStoredOk (env : Env) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo cv _ _) =>
    cv.levelParams.isEmpty && natOpTyPinned env n cv.type
  | _ => false

/-- Peel a `∀`-telescope along an argument list (the residual type of
a fully applied telescope). -/
def piResidual : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ b, a :: as => piResidual (b.instantiate1 a) as
  | _, _ :: _ => none

/-- Are all `nF` projection slots of `T` table entries — i.e. does
`T`'s projection table exist and cover them?  (Task #175 tower-flag:
a stored table always carries bodies, so "the entry exists" is the
whole test.) -/
def towerSlotsAll (env : Env) (T : Name) (nF : Nat) : Bool :=
  (List.range nF).all fun j => (env.findProj? T j).isSome

/-- The fabricated projections of a structure-eta spine: the
`.proj T j b` nodes (every slot of an η family the checker uses has a
table entry, `towerSlotsAll`; the node is what the table types and
reduces). -/
def etaProjs (T : Name) (b : Expr) (nF : Nat) : List Expr :=
  (List.range nF).map fun j => Expr.proj T j b

/-- The constructor shape official's `try_eta_struct_core` tests before
inferring anything (`type_checker.cpp:824-829`): the candidate's head is
a stored constructor applied to exactly its parameters and fields.
(`structEtaCertWith` re-reads the same head; this is the gate that
keeps the inferences behind it.) -/
def etaCtorShape (env : Env) (a : Expr) : Bool :=
  match a.getAppFn with
  | .const c _ =>
    match env.find? c with
    | some (.ctorInfo _ cnP cnF) => a.getAppArgs.length == cnP + cnF
    | _ => false
  | _ => false

/-- The eta-rescue fabrication's argument spine: the major's type's
arguments, then the major's projections (`etaProjs`). -/
def etaFabArgsE (T : Name) (targs : List Expr) (major : Expr) (nF : Nat) :
    List Expr :=
  targs ++ etaProjs T major nF

/-- **The telescope check of a spine** (task #342 L18): the
telescope's syntactic arity, nothing else.  It is applied to spines of
the subject (the projection fire, `projCert`; the recursor's own
telescope in `iotaRec`): where the redex is not the point, its spine
fits its head's telescope by the application slots of its own
invariant, and a reduction claims nothing of a redex that is the
point. -/
def teleArityOk (ty : Expr) (args : List Expr) : Bool :=
  (Expr.peelPis args.length ty).isSome

/-- Open the first `n` `∀`-binders at fresh free variables `0..n-1`
(each fvar's type is the binder domain, instantiated with the earlier
fvars).  Returns the fvars and the opened body. -/
def openPisAtFvars : Nat → Expr → Nat → Option (List Expr × Expr)
  | 0, e, _ => some ([], e)
  | n + 1, .forallE dom body, i =>
    let fv : Expr := .fvar i dom
    match openPisAtFvars n (body.instantiate1 fv) (i + 1) with
    | some (fvs, e) => some (fv :: fvs, e)
    | none => none
  | _ + 1, _, _ => none

/-- Core of `openPisAtFvarsF`: `acc` holds the already-created fvars,
innermost binder first.  Computes
`openPisAtFvars n (e.instantiateList acc) i` whenever `e` raw-strips
`n` `∀`-binders (`openPisAtFvarsFGo_sound`), `none` otherwise —
one `instantiateList` pass per domain instead of one whole-telescope
`instantiate1` pass per binder. -/
def openPisAtFvarsFGo (acc : List Expr) :
    Nat → Expr → Nat → Option (List Expr × Expr)
  | 0, e, _ => some ([], e.instantiateList acc)
  | n + 1, .forallE dom body, i =>
    let fv : Expr := .fvar i (dom.instantiateList acc)
    match openPisAtFvarsFGo (fv :: acc) n body (i + 1) with
    | some (fvs, e) => some (fv :: fvs, e)
    | none => none
  | _ + 1, _, _ => none

/-- One-pass `openPisAtFvars` (equal to it: `openPisAtFvarsF_eq`; the
fallback covers telescopes whose binders only appear after
substitution). -/
def openPisAtFvarsF (n : Nat) (e : Expr) (i : Nat) :
    Option (List Expr × Expr) :=
  match openPisAtFvarsFGo [] n e i with
  | some r => some r
  | none => openPisAtFvars n e i

/-- Does `bvar i` occur loose in `e`?  (Not through fvar type
annotations — the generated telescopes are fvar-free.) -/
def Expr.hasLooseBVar : Nat → Expr → Bool
  | i, .bvar j => i == j
  | _, .fvar .. => false
  | _, .sort _ => false
  | _, .const .. => false
  | _, .lit _ => false
  | i, .app f a => hasLooseBVar i f || hasLooseBVar i a
  | i, .lam ty b => hasLooseBVar i ty || hasLooseBVar (i + 1) b
  | i, .forallE ty b => hasLooseBVar i ty || hasLooseBVar (i + 1) b
  | i, .letE t v b =>
    hasLooseBVar i t || hasLooseBVar i v || hasLooseBVar (i + 1) b
  | i, .proj _ _ e => hasLooseBVar i e

/-- `hasLooseBVar` with the packed bound's cutoff (task #214, P4): a
node whose loose-bvar bound is at or below `i` has no `bvar i`, so the
walk stops there without descending, so `structUsedLater` calls touch
only the spine of a large telescope, never its shared instance towers.  Read as `hasLooseBVar`
by `Expr.hasLooseBVarB_eq` (`ConLeche/Verify/Inductives/DirectGen.lean`). -/
def Expr.hasLooseBVarB (i : Nat) (e : Expr) : Bool :=
  if e.bvarB ≤ i then false else
  match e with
  | .bvar j => i == j
  | .fvar .. => false
  | .sort _ => false
  | .const .. => false
  | .lit _ => false
  | .app f a => hasLooseBVarB i f || hasLooseBVarB i a
  | .lam ty b => hasLooseBVarB i ty || hasLooseBVarB (i + 1) b
  | .forallE ty b => hasLooseBVarB i ty || hasLooseBVarB (i + 1) b
  | .letE t v b =>
    hasLooseBVarB i t || hasLooseBVarB i v || hasLooseBVarB (i + 1) b
  | .proj _ _ e => hasLooseBVarB i e

/-! ### `hasLooseBVarB`, memoized (task #233)

The cutoff above stops the walk where the variable **cannot** occur.
It cannot stop it where a loose variable *above* `i` occurs but `i`
itself does not: `bvarB` is the bound of the largest loose index, so a
node holding `bvar 1` has `bvarB = 2` and the `bvarB ≤ 0` test fails at
every node of a shared tower whose answer is `false` — and with no
`true` to short-circuit the `||` on, each shared node is re-entered
once per path.  A user's stream showed 99.5 % of a run inside this one
function; the depth-60 fixture is `tests/e2e/tower_usedlater.ndjson`
(a three-field structure whose last field's type is a tower over the
FIRST field, asked about the SECOND).

The cutoff and the memo are complementary — this keeps both.  As with
`mentionsConst` below and `instantiate1` (`ConLeche/Kernel/ExprOps.lean`,
task #215), the memoized walk is swapped in by `@[csimp]`:
kernel-checked, no trust point, and the pure definition stays what
every proof consumes (`Expr.hasLooseBVarB_eq`,
`ConLeche/Verify/Inductives/DirectGen.lean`, is unchanged).  The memo
is keyed by the *node and the index* — the index shifts under binders,
so a node's answer is not a function of the node alone — and dropped
after each call. -/

/-- The memo's invariant: every recorded answer is the real one. -/
def LooseBVarMemoInv (memo : Std.HashMap (Expr × Nat) Bool) : Prop :=
  ∀ (k : Expr × Nat) (r : Bool), memo[k]? = some r → r = Expr.hasLooseBVarB k.2 k.1

theorem LooseBVarMemoInv.empty : LooseBVarMemoInv {} := by
  intro k r h; simp at h

theorem LooseBVarMemoInv.insert {memo : Std.HashMap (Expr × Nat) Bool}
    (hm : LooseBVarMemoInv memo) {e : Expr} {i : Nat} {r : Bool}
    (heq : r = Expr.hasLooseBVarB i e) :
    LooseBVarMemoInv (memo.insert (e, i) r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Record one answer for `(e, i)` in the memo the walk hands back.
Written with projections rather than a destructuring `let` so that the
correctness proof can `split` the walk's own matches. -/
@[inline] def Expr.hasLooseBVarBIns (e : Expr) (i : Nat)
    (r : Bool × Std.HashMap (Expr × Nat) Bool) : Bool × Std.HashMap (Expr × Nat) Bool :=
  (r.1, r.2.insert (e, i) r.1)

/-- Memoized `hasLooseBVarB`. -/
def Expr.hasLooseBVarBGo (memo : Std.HashMap (Expr × Nat) Bool) (i : Nat) (e : Expr) :
    Bool × Std.HashMap (Expr × Nat) Bool :=
  if e.bvarB ≤ i then (false, memo) else
  match e with
  | .bvar j => (i == j, memo)
  | .fvar .. => (false, memo)
  | .sort _ => (false, memo)
  | .const .. => (false, memo)
  | .lit _ => (false, memo)
  | e =>
    match memo[(e, i)]? with
    | some r => (r, memo)
    | none =>
      Expr.hasLooseBVarBIns e i <|
        match e with
        | .app f a =>
          match hasLooseBVarBGo memo i f with
          | (true, memo) => (true, memo)
          | (false, memo) => hasLooseBVarBGo memo i a
        | .lam ty b =>
          match hasLooseBVarBGo memo i ty with
          | (true, memo) => (true, memo)
          | (false, memo) => hasLooseBVarBGo memo (i + 1) b
        | .forallE ty b =>
          match hasLooseBVarBGo memo i ty with
          | (true, memo) => (true, memo)
          | (false, memo) => hasLooseBVarBGo memo (i + 1) b
        | .letE t v b =>
          match hasLooseBVarBGo memo i t with
          | (true, memo) => (true, memo)
          | (false, memo) =>
            match hasLooseBVarBGo memo i v with
            | (true, memo) => (true, memo)
            | (false, memo) => hasLooseBVarBGo memo (i + 1) b
        | .proj _ _ sub => hasLooseBVarBGo memo i sub
        | _ => (false, memo)

/-- **The memoized walk is `hasLooseBVarB`.** -/
theorem Expr.hasLooseBVarBGo_spec :
    ∀ (e : Expr) (i : Nat) (memo : Std.HashMap (Expr × Nat) Bool), LooseBVarMemoInv memo →
      (hasLooseBVarBGo memo i e).1 = Expr.hasLooseBVarB i e ∧
        LooseBVarMemoInv (hasLooseBVarBGo memo i e).2 := by
  intro e
  induction e with
  | bvar j =>
    intro i memo hm
    rw [hasLooseBVarBGo, Expr.hasLooseBVarB]
    split <;> exact ⟨rfl, hm⟩
  | fvar idx ty _ =>
    intro i memo hm
    rw [hasLooseBVarBGo, Expr.hasLooseBVarB]
    split <;> exact ⟨rfl, hm⟩
  | sort u =>
    intro i memo hm
    rw [hasLooseBVarBGo, Expr.hasLooseBVarB]
    split <;> exact ⟨rfl, hm⟩
  | const n us =>
    intro i memo hm
    rw [hasLooseBVarBGo, Expr.hasLooseBVarB]
    split <;> exact ⟨rfl, hm⟩
  | lit l =>
    intro i memo hm
    rw [hasLooseBVarBGo, Expr.hasLooseBVarB]
    split <;> exact ⟨rfl, hm⟩
  | app f a ihf iha =>
    intro i memo hm
    rw [hasLooseBVarBGo]
    split
    · rename_i hcut
      exact ⟨by rw [Expr.hasLooseBVarB, ite_eq_left hcut], hm⟩
    · rename_i hcut
      have hspec : Expr.hasLooseBVarB i (.app f a)
          = (Expr.hasLooseBVarB i f || Expr.hasLooseBVarB i a) := by
        rw [Expr.hasLooseBVarB, ite_eq_right hcut]
      split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ihf i memo hm
        simp only [hasLooseBVarBIns]
        split
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          exact ⟨by simp [hspec, ← h1], h2.insert (by simp [hspec, ← h1])⟩
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          obtain ⟨h3, h4⟩ := iha i memo₁ h2
          exact ⟨by simp [hspec, ← h1, h3], h4.insert (by simp [hspec, ← h1, h3])⟩
  | lam ty b iht ihb =>
    intro i memo hm
    rw [hasLooseBVarBGo]
    split
    · rename_i hcut
      exact ⟨by rw [Expr.hasLooseBVarB, ite_eq_left hcut], hm⟩
    · rename_i hcut
      have hspec : Expr.hasLooseBVarB i (.lam ty b)
          = (Expr.hasLooseBVarB i ty || Expr.hasLooseBVarB (i + 1) b) := by
        rw [Expr.hasLooseBVarB, ite_eq_right hcut]
      split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht i memo hm
        simp only [hasLooseBVarBIns]
        split
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          exact ⟨by simp [hspec, ← h1], h2.insert (by simp [hspec, ← h1])⟩
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          obtain ⟨h3, h4⟩ := ihb (i + 1) memo₁ h2
          exact ⟨by simp [hspec, ← h1, h3], h4.insert (by simp [hspec, ← h1, h3])⟩
  | forallE ty b iht ihb =>
    intro i memo hm
    rw [hasLooseBVarBGo]
    split
    · rename_i hcut
      exact ⟨by rw [Expr.hasLooseBVarB, ite_eq_left hcut], hm⟩
    · rename_i hcut
      have hspec : Expr.hasLooseBVarB i (.forallE ty b)
          = (Expr.hasLooseBVarB i ty || Expr.hasLooseBVarB (i + 1) b) := by
        rw [Expr.hasLooseBVarB, ite_eq_right hcut]
      split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht i memo hm
        simp only [hasLooseBVarBIns]
        split
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          exact ⟨by simp [hspec, ← h1], h2.insert (by simp [hspec, ← h1])⟩
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          obtain ⟨h3, h4⟩ := ihb (i + 1) memo₁ h2
          exact ⟨by simp [hspec, ← h1, h3], h4.insert (by simp [hspec, ← h1, h3])⟩
  | letE t v b iht ihv ihb =>
    intro i memo hm
    rw [hasLooseBVarBGo]
    split
    · rename_i hcut
      exact ⟨by rw [Expr.hasLooseBVarB, ite_eq_left hcut], hm⟩
    · rename_i hcut
      have hspec : Expr.hasLooseBVarB i (.letE t v b)
          = (Expr.hasLooseBVarB i t || Expr.hasLooseBVarB i v
              || Expr.hasLooseBVarB (i + 1) b) := by
        rw [Expr.hasLooseBVarB, ite_eq_right hcut]
      split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := iht i memo hm
        simp only [hasLooseBVarBIns]
        split
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          exact ⟨by simp [hspec, ← h1], h2.insert (by simp [hspec, ← h1])⟩
        · rename_i memo₁ heq
          rw [heq] at h1 h2
          obtain ⟨h3, h4⟩ := ihv i memo₁ h2
          split
          · rename_i memo₂ heq₂
            rw [heq₂] at h3 h4
            exact ⟨by simp [hspec, ← h1, ← h3], h4.insert (by simp [hspec, ← h1, ← h3])⟩
          · rename_i memo₂ heq₂
            rw [heq₂] at h3 h4
            obtain ⟨h5, h6⟩ := ihb (i + 1) memo₂ h4
            exact ⟨by simp [hspec, ← h1, ← h3, h5],
              h6.insert (by simp [hspec, ← h1, ← h3, h5])⟩
  | proj s j sub ih =>
    intro i memo hm
    rw [hasLooseBVarBGo]
    split
    · rename_i hcut
      exact ⟨by rw [Expr.hasLooseBVarB, ite_eq_left hcut], hm⟩
    · rename_i hcut
      have hspec : Expr.hasLooseBVarB i (.proj s j sub) = Expr.hasLooseBVarB i sub := by
        rw [Expr.hasLooseBVarB, ite_eq_right hcut]
      split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
      · obtain ⟨h1, h2⟩ := ih i memo hm
        simp only [hasLooseBVarBIns]
        exact ⟨by simp [hspec, h1], h2.insert (by simp [hspec, h1])⟩

/-- The executed `hasLooseBVarB` (one memoized DAG walk). -/
def Expr.hasLooseBVarBFast (i : Nat) (e : Expr) : Bool :=
  (Expr.hasLooseBVarBGo {} i e).1

@[csimp] theorem Expr.hasLooseBVarB_eq_hasLooseBVarBFast :
    @Expr.hasLooseBVarB = @Expr.hasLooseBVarBFast := by
  funext i e
  exact (hasLooseBVarBGo_spec e i {} LooseBVarMemoInv.empty).1.symm

/-- **Field `j` is used by a later field** — the official
`infer_proj`'s `has_loose_bvars(binding_body(r))` at step `j`: the
field's variable occurs in the constructor telescope's remainder after
binder `j` (a later field's domain; the result never mentions a
field). -/
def structUsedLater (cty : Expr) (nP j : Nat) : Bool :=
  match cty.stripPis (nP + j + 1) with
  | some (_, rest) => rest.hasLooseBVarB 0
  | none => false

/-- The rows of `projGuardRows` read off an opened constructor telescope
`fvs`: field `idx`, and every earlier field a later one uses. -/
def projGuardRowsAt (cty : Expr) (nP idx : Nat) (fvs : List Expr) : List (Nat × Expr) :=
  (List.range (idx + 1)).filterMap fun j =>
    if j = idx ∨ structUsedLater cty nP j = true then
      (fvs[nP + j]?).map fun x => (nP + j, x.fvarTypeD)
    else none

/-- **What a `.proj` use on a `Prop`-declared structure must show**
(official `infer_proj`, task #480): the domains, at the use's level
instantiation and at the constructor telescope's own variables, that
must be propositions — the projected field's, and that of every earlier
field a later field's type uses.  Each row is a depth and a term at that
depth.  `none` where the stored constructor does not bind what the entry
says (the use is a reject).  Computed where it is read; nothing about it is
stored. -/
def projGuardRows (find? : Name → Option ConstantInfo) (entry : ProjEntry)
    (us : List Level) : Option (List (Nat × Expr)) :=
  match find? entry.ctor with
  | some ci =>
    let cv := ci.toConstantVal
    match openPisAtFvars (entry.numParams + entry.idx + 1)
        (cv.type.instantiateLevelParams cv.levelParams us) 0 with
    | some (fvs, _) => some (projGuardRowsAt cv.type entry.numParams entry.idx fvs)
    | none => none
  | none => none

/-- **`And`'s projection slots, ready to fire**: the two
tower entries of `And` are stored and name the rule's constructor at the
major's parameter count.  The gate of `majorToCtor`'s `And` branch;
abstracted over the lookup so the indexed twin
(`FEnv.andRescueSlotsF`) shares the body. -/
def andRescueSlotsOf (findProj? : Name → Nat → Option ProjEntry)
    (ctor : Name) (nP : Nat) : Bool :=
  (List.range 2).all fun j =>
    match findProj? andName j with
    | some e => e.ctor == ctor && e.numParams == nP && e.numFields == 2
    | none => false

/-- `andRescueSlotsOf` at the plain environment. -/
def andRescueSlots (env : Env) (ctor : Name) (nP : Nat) : Bool :=
  andRescueSlotsOf env.findProj? ctor nP

/-- **The structure-η rescue's standing condition, at use**: the single
rule's constructor `ctor` (stored as `cvj`) is the η constructor of its
family `cvT`, which is structure-like (`IndCaps.eta`), and carries the family's
level parameters.  The rescue asks this where it has just looked all three up;
nothing about it is stored.

The level-parameter conjunct is what lets the rescue fabricate the
constructor application at the major type's levels without comparing
the two lists per call.  `And.intro` is left to `And`'s own rescue. -/
def etaRescueOk (ctor : Name) (cvj cvT : ConstantVal) (caps : IndCaps) : Bool :=
  caps.eta && caps.etaCtor == ctor && cvj.levelParams == cvT.levelParams && ctor != andIntroName

/-- What `etaRescueOk` says. -/
theorem etaRescueOk_inv {ctor : Name} {cvj cvT : ConstantVal} {caps : IndCaps}
    (h : etaRescueOk ctor cvj cvT caps = true) :
    caps.eta = true ∧ caps.etaCtor = ctor ∧ cvj.levelParams = cvT.levelParams := by
  simp only [etaRescueOk, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

/-- The level and constructor-parameter comparands a firing rule's
checks compare the major's constructor levels and parameters against:
for a `.plain` rule the constructor's levels link to the recursor's by
name and its parameters are the recursor's leading arguments; for a
`.nested` rule both are the stored instantiations (the class the
auxiliary recursor's type was generated from, `auxRuleFire`), at the
recursor's level instantiation and (for the parameters) instantiated at
the recursor's leading-argument spine (the stored pins live in the
`rP`-binder prefix context; index arguments never occur in them); a
`.levels` rule's levels are stored and its parameters a `.plain` rule's. -/
def recFireComparands (rl : RecRule) (cnP : Nat) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args : List Expr)
    (rP : Nat) : List Level × List Expr :=
  match rl.fire with
  | .nested lvls pins =>
    (lvls.map (Level.subst lps us),
     pins.map fun p => Expr.instSpine (args.take rP) (rP - 1)
       (p.instantiateLevelParams lps us))
  | .plain =>
    (cvjLps.map fun p => Level.subst lps us (.param p),
     args.take cnP)
  | .levels lvls =>
    (lvls.map (Level.subst lps us), args.take cnP)

/-- **The type of a `.proj` node at a tower-backed entry** (task #175
S1): the stored body `F_i[p⃗ ↦ bvars, f_j ↦ .proj T j (bvar 0)]`,
level-instantiated at the subject type's levels, with the subject
type's arguments and the subject substituted for its `numParams + 1`
loose variables in ONE traversal (`instantiateList`: `bvar 0` is the
subject, `bvar (numParams - k)` parameter `k`). -/
def ProjEntry.typeAt (entry : ProjEntry) (us : List Level) (targs : List Expr)
    (pe : Expr) : Expr :=
  (entry.body.instantiateLevelParams entry.levelParams us).instantiateList
    (pe :: targs.reverse)

end ConLeche
