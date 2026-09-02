import Setlec.Kernel.Env
import Setlec.Kernel.Level
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Basis

/-!
# The checker core, in open-recursion style

Every core function is written **once**, as a non-recursive *body*
parameterized over a record of the mutually recursive entry points
(`CoreFns`) and polymorphic in the monad.  All recursion is routed
through the record — bodies never call themselves, and the few helpers
that do recurse (`iotaCerts`, `defEqList`, `structEtaProjCerts`) do so
structurally on a list.  Fuel lives only in the *knots* that tie the
record: the pure knot (`Setlec.Kernel.TypeChecker`) instantiates the
bodies at `CheckM` and is the verification's subject; the memoized knot
(`Setlec.Kernel.TypeCheckerC`) instantiates them at a state monad
carrying the caches and is what the checker executes.  A refinement
bridge relates the two (see DESIGN.md).

The reduction loop follows the official kernel (`whnfCore` never
delta-unfolds; `whnf` iterates `whnfCore → reduceNat → unfold one
definition`), and definitional equality starts with the syntactic fast
path and tries proof irrelevance before structural congruence.
Inference re-checks the application argument and the λ-annotation: the
soundness claims re-derive their membership slots from those checks at
their own fuel.  The official kernel's *infer-only* mode is deferred
until the refinement bridge's fuel-determinism machinery lands
(DESIGN.md).

Verification: `Setlec.SetR.*` and `Setlec.TTVerify.*` (claims),
`Setlec.Verify.*` (inversions), both stated against the bodies with
hypotheses about the record and discharged by one induction at the
knot.
-/

namespace Setlec

inductive CheckError where
  | notImplemented (what : String)
  | invalid (msg : String)
  | internal (msg : String)
  deriving Repr

instance : ToString CheckError where
  toString
    | .notImplemented what => s!"not implemented yet: {what}"
    | .invalid msg => s!"invalid: {msg}"
    | .internal msg => s!"internal error: {msg}"

abbrev CheckM := Except CheckError

/-- One-level view of a term: the constructor with immediate children.
The genericization seam for interned representations (task #26): core
bodies destructure terms through `viewM`, which is `pure ∘ Expr.view`
here and a store read for an interned index type. -/
inductive ExprView (τ : Type) where
  | bvar (i : Nat)
  | fvar (idx : Nat) (name : Name) (type : τ)
  | sort (u : Level)
  | const (n : Name) (us : List Level)
  | app (f a : τ)
  | lam (n : Name) (type body : τ) (m : BinderMeta)
  | forallE (n : Name) (type body : τ) (m : BinderMeta)
  | letE (n : Name) (type value body : τ)
  | lit (l : Literal)
  | proj (structName : Name) (idx : Nat) (e : τ)

@[inline] def Expr.view : Expr → ExprView Expr
  | .bvar i => .bvar i
  | .fvar idx n ty => .fvar idx n ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app f a
  | .lam n ty b mb => .lam n ty b mb
  | .forallE n ty b mb => .forallE n ty b mb
  | .letE n ty v b => .letE n ty v b
  | .lit l => .lit l
  | .proj s i e => .proj s i e

/-- The record of mutually recursive core entry points.  `whnfCore`
computes a head normal form without delta; `whnf` is the full reduction
loop; `infer` is type inference;
`defeq` is definitional equality; `annotate` computes binder
annotations (and is the one place typing is checked). -/
structure CoreFns (m : Type → Type u) where
  whnfCore : Nat → Expr → m Expr
  whnf : Nat → Expr → m Expr
  infer : Nat → Expr → m Expr
  defeq : Nat → Expr → Expr → m Bool
  annotate : Nat → Expr → m Expr

section Bodies

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/- The three-mode setting (task #147): definitions below that mention
`mode` take it as their first explicit argument (after the monad
instances).  Only the seven TT-lane check sites branch on it, through
`CheckMode.ttChecks`; at `.ttModel` the checker is exactly the pre-#147
one, at `.setModel` (the default) the seven checks are skipped. -/
variable (mode : CheckMode)

/-- Lift a fuel-style partial result; `none` is an internal error. -/
def liftFueled (what : String) : Option α → m α
  | some a => pure a
  | none => throw (.internal s!"fuel exhausted: {what}")

/-- The model-side name of field `i`'s projection for `T`
(the documented public interface of the preprocessor's models). -/
def projModelName (T : Name) (i : Nat) : Name :=
  (T.str "_model").str ("proj_" ++ toString i)

/-- Is the expression headed by a stored constructor? -/
def isCtorApp (env : Env) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const c _ =>
    match env.find? c with
    | some (.ctorInfo _ _ _) => true
    | _ => false
  | _ => false

/-- Does the syntactic pi telescope end in a (normalized) `Prop`?
Used for the K capability (an inductive *proposition*) and to guard the
structure-eta rescue (the official kernel does not eta-rescue
propositional structures). -/
def piResultIsProp (e : Expr) : Bool :=
  match e.piResult with
  | .sort u => Level.isEquiv u .zero == some true
  | _ => false

/-- Is the result sort of a stored inductive's type, instantiated at
the given levels, provably nonzero (official `is_never_zero`)?  The
official kernel's structure rescue (`to_cnstr_when_structure`)
requires this of the major's type; the basis `PUnit` rescue mirrors
it (`Sort u` at a concrete level such as `Unit`'s `1` passes, the
parameter `u` itself does not). -/
def piResultNeverZero (lps : List Name) (us : List Level) (e : Expr) :
    Bool :=
  match e.piResult with
  | .sort u => (Level.subst lps us u).isNeverZero
  | _ => false

/-- Is this (whnf'd) type expression a unit-like inductive type — a
stored inductive whose recursor (under the `<ind>.rec` naming
convention) has no indices and a single zero-field rule?  All of its
inhabitants are then equal (in the model: the proof point; the
environment invariant supplies the fact for the stored constant). -/
def isUnitLikeTy (env : Env) : Expr → Bool
  | .const c _ =>
    (match env.find? c with
      | some (.indInfo _ _) => true
      | _ => false) &&
    (match env.find? (c.str "rec") with
      -- no indices: the major's position equals the rule prefix
      | some (.recInfo _ mI rP [r]) => mI == rP && r.nfields == 0
      | _ => false) &&
    -- native unit semantics: pinned basis blocks only (env-stored
    -- capability flags will replace this)
    reservedBasisNames.contains (c.str "rec")
  | _ => false

/-- Unfold the (application of a) definition or theorem at the head,
one step.  `none` when the head is not an unfoldable constant.
Theorems unfold like the reference kernels' delta step (official
`is_delta`: any constant with a value; theorems at hint `opaque`) —
needed e.g. when a recursor major is a theorem application whose value
reduces to a constructor (arena `subject-reduction-redex`). -/
def unfoldDefinition (env : Env) (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const n us =>
    match env.find? n with
    | some (.defnInfo cv value _) =>
      if us.length = cv.levelParams.length then
        some (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
          e.getAppArgs)
      else none
    | some (.thmInfo cv value) =>
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
    | some (.thmInfo cv _) => us.length == cv.levelParams.length
    | _ => false
  | _ => false

/-- The reducibility hint of the constant at the head of `e` (`opaque`
when the head is not a stored definition; in particular a theorem
unfolds at hint `opaque`, exactly the official kernel's
`constant_info::get_hints`). -/
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

/-- The stored `Nat.succ` declaration has the expected (annotated)
shape. -/
def natSuccOk : Option ConstantInfo → Bool
  | some (.ctorInfo cv _ _) =>
    cv.levelParams.isEmpty &&
    (match cv.type with
     | .forallE _ (.const c1 []) (.const c2 []) _mb =>
       c1 == natName && c2 == natName
     | _ => false)
  | _ => false

/-- Whether the environment supports `Nat` literals: `Nat`, `Nat.zero`
and `Nat.succ` are stored with exactly the expected kinds, level
parameters and (annotated) types.  Every literal code path is guarded
on this — the model interprets a literal by iterating the `Nat.succ`
value on the `Nat.zero` value, and the soundness proofs read the
declaration shapes off this guard. -/
def natLitSupported (env : Env) : Bool :=
  natIndOk (env.find? natName) && natZeroOk (env.find? natZeroName) &&
    natSuccOk (env.find? natSuccName)

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
  | .fvar _ _ ty => ty.constsResolve env
  | .app f a => f.constsResolve env && a.constsResolve env
  | .lam _ ty body _ | .forallE _ ty body _ =>
    ty.constsResolve env && body.constsResolve env
  | .letE _ ty val body =>
    ty.constsResolve env && val.constsResolve env && body.constsResolve env
  | .proj s _ e => (env.find? s).isSome && e.constsResolve env

/-- Convert a `Nat`-literal major premise to constructor form, one
layer; anything else passes through. -/
def litToCtorIfNat (env : Env) : Expr → Expr
  | .lit (.natVal n) =>
    if natLitSupported env then natLitToConstructor n else .lit (.natVal n)
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
`Nat` literal names: the guard `strLitSupported` checks that the stored
declarations have exactly the expected (annotated) types, which is what
the model's interpretation of a string literal reads its meaning off.
A string literal in the input while the guard fails is a positively
detected unsupported feature — annotation *declines* (exit 2). -/

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

/-- The stored `List` declaration has the expected (annotated) shape
`List.{p} : Type p → Type p`. -/
def listTyOk : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE _ (.sort u1) (.sort u2) _mb =>
         u1 == .succ (.param p) && u2 == .succ (.param p)
       | _ => false)
    | _ => false
  | none => false

/-- The stored `List.nil` declaration has the expected (annotated) shape
`List.nil.{p} : ∀ (α : Type p), List.{p} α`. -/
def listNilTyOk : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE _ (.sort u1) (.app (.const l1 us1) (.bvar 0)) _mb =>
         u1 == .succ (.param p) && l1 == listName && us1 == [.param p]
       | _ => false)
    | _ => false
  | none => false

/-- The stored `List.cons` declaration has the expected (annotated) shape
`List.cons.{p} : ∀ (α : Type p) (head : α) (tail : List.{p} α),
List.{p} α` (with the codomain-sort annotations the annotation pass
produces on that type). -/
def listConsTyOk : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE _ (.sort u1)
           (.forallE _ (.bvar 0)
             (.forallE _ (.app (.const l1 us1) (.bvar 1))
               (.app (.const l2 us2) (.bvar 2)) _mb3) _mb2) _mb1 =>
         u1 == .succ (.param p) && l1 == listName && l2 == listName &&
           us1 == [.param p] && us2 == [.param p]
       | _ => false)
    | _ => false
  | none => false

/-- The stored `Char.ofNat` declaration has the expected (annotated)
shape `Char.ofNat : Nat → Char`. -/
def charOfNatTyOk : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      (match ci.toConstantVal.type with
       | .forallE _ (.const c1 []) (.const c2 []) _mb =>
         c1 == natName && c2 == charName
       | _ => false)
  | none => false

/-- The stored `String.ofList` declaration has the expected (annotated)
shape `String.ofList : List.{0} Char → String`. -/
def stringOfListTyOk : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      (match ci.toConstantVal.type with
       | .forallE _ (.app (.const l1 us1) (.const c1 [])) (.const c2 []) _mb =>
         l1 == listName && us1 == [.zero] && c1 == charName &&
           c2 == stringName
       | _ => false)
  | none => false

/-- Whether the environment supports `String` literals: the `Nat`
literal guard plus `String`, `String.ofList`, `List`, `List.nil`,
`List.cons`, `Char` and `Char.ofNat` stored with exactly the expected
level parameters and (annotated) types.  Every string-literal code path
is guarded on this; the model interprets a string literal through the
values of these constants, and the soundness proofs read the
declaration shapes off this guard.  (The reference kernels only check
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
by its (annotated) definition value (`Expr.substConst0`): running it
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
def natLog2Name : Name := natName.str "log2"
def boolName : Name := .str .anonymous "Bool"
def boolTrueName : Name := boolName.str "true"
def boolFalseName : Name := boolName.str "false"

/-- The structural-Nat operations with a certified literal fast path. -/
def natOpNames : List Name :=
  [natPredName, natAddName, natSubName, natMulName, natPowName,
   natBeqName, natBleName]

/-- The WF-recursive operations with a *pinned-declaration* certified
fast path: at install, `checkDecl` compares the stream's definition
against a vendored pin of the toolchain's own (helper-unfolded)
definition by definitional equality, and then checks the pinned
`Nat.ble`-guarded characterization certificates
(`Setlec/Kernel/NatOpPins.lean`) like theorem declarations — without
installing them.  Presence in the store is therefore again the
capability: a stored operation under one of these names has passed pin
and certificates, or the install declined.  (The name is historic:
the family started with `Nat.div`/`Nat.mod` and now covers every
pin-certified WF-recursive kernel-accelerated `Nat` operation.) -/
def natDivModNames : List Name :=
  [natDivName, natModName, natGcdName, natLandName, natLorName,
   natXorName, natShiftLeftName, natShiftRightName, natLog2Name]

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
  else if c = natLog2Name then [natBleName, natDivName, natLog2Name]
  else []

/-- The defining recurrence equations of a structural-Nat operation,
over constructor forms with free variables `d`, `d + 1` (binder-free,
so the equation sides carry no annotations). -/
def natOpEquations (d : Nat) (c : Name) : List (Expr × Expr) :=
  let natTy : Expr := .const natName []
  let x : Expr := .fvar d (.str .anonymous "x") natTy
  let y : Expr := .fvar (d + 1) (.str .anonymous "y") natTy
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
  else if c = natPowName then some (.lit (.natVal (a ^ b)))
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
  else if c = natLog2Name then some (.lit (.natVal (Nat.log2 a)))
  else if c = natBeqName then
    some (.const (if a = b then boolTrueName else boolFalseName) [])
  else if c = natBleName then
    some (.const (if a <= b then boolTrueName else boolFalseName) [])
  else none

/-- Stored-constant guards for op `c`: the `Nat` basis, every
dependency stored as a definition, and (for the `Bool`-valued ops and
the `ble`-guarded `div`/`mod`, whose semantic clauses mention the
`Bool` constructor values) the `Bool` constructors stored. -/
def natOpGuard (env : Env) (c : Name) : Bool :=
  natLitSupported env &&
  (natOpDeps c).all (fun n => match env.find? n with
    | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
    | _ => false) &&
  (if c = natBeqName || c = natBleName || natDivModNames.contains c then
    (match env.find? boolTrueName with
      | some ci => ci.toConstantVal.levelParams.isEmpty
      | none => false) &&
    (match env.find? boolFalseName with
      | some ci => ci.toConstantVal.levelParams.isEmpty
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
   natXorName, natShiftLeftName, natShiftRightName, natLog2Name]

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
  | .lam nm ty b mb =>
    .lam nm (Expr.substConstAll n r ty) (Expr.substConstAll n r b) mb
  | .forallE nm ty b mb =>
    .forallE nm (Expr.substConstAll n r ty) (Expr.substConstAll n r b) mb
  | .letE nm ty v b =>
    .letE nm (Expr.substConstAll n r ty) (Expr.substConstAll n r v)
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

/-- The pinned type of a structural-Nat operation:
`Nat → Nat` for `pred`, `Nat → Nat → Nat` for the arithmetic
operations, `Nat → Nat → Bool` for the comparisons.  The model reads
the operations' function-space memberships off this shape. -/
def natOpTyPinned (env : Env) (c : Name) (ty : Expr) : Bool :=
  if c = natPredName || c = natLog2Name then
    match ty with
    | .forallE _ dom body _mb =>
      dom == .const natName [] && natOpCod env c body
    | _ => false
  else
    match ty with
    | .forallE _ dom (.forallE _ dom2 body _mb2) _mb =>
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

/-- Literal acceleration (the official kernel's `reduceNat`, run in the
`whnf` loop *before* delta-unfolding): pack `Nat.succ` applied to a
literal back into a literal.  Binary operations on literal arguments
are added with the verified fast-path capabilities (see DESIGN.md);
until then only the constructor packing reduces. -/
def reduceNat (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) :
    m (Option Expr) := do
  match e with
  | .app (.const c []) a =>
    if c = natSuccName ∧ natLitSupported env then
      -- the argument is reduced first (as for the operations below):
      -- literals reach `succ` wrapped in `OfNat`/instance towers, and a
      -- missed packing here defeats the binary fast paths downstream,
      -- which then delta-grind the `brecOn` below-tower unarily
      match rawNatLit? (← r.whnf depth a) with
      | some n => pure (some (.lit (.natVal (n + 1))))
      | none => pure none
    else if c = natPredName ∧ natOpGuard env c = true then
      match rawNatLit? (← r.whnf depth a) with
      | some n => pure (natOpResult c n 0)
      | none => pure none
    else if c = natLog2Name ∧ natOpGuard env c = true then
      match rawNatLit? (← r.whnf depth a) with
      | some n => pure (natOpResult c n 0)
      | none => pure none
    else if c = natLog2Name ∧ natLitSupported env then
      -- capless `log2` literal: positively decline (safety net; a
      -- mismatching declaration already declined at install)
      match rawNatLit? (← r.whnf depth a) with
      | some _ => throw (.notImplemented
          s!"native Nat computation on literals ({c})")
      | none => pure none
    else pure none
  | .app (.app (.const c []) a) b =>
    if (c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
        c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
        c = natDivName ∨ c = natModName ∨ c = natGcdName ∨
        c = natLandName ∨ c = natLorName ∨ c = natXorName ∨
        c = natShiftLeftName ∨ c = natShiftRightName) ∧
        natOpGuard env c = true then
      match rawNatLit? (← r.whnf depth a),
          rawNatLit? (← r.whnf depth b) with
      | some n₁, some n₂ => pure (natOpResult c n₁ n₂)
      | _, _ => pure none
    else if natOpWfNames.contains c ∧ natLitSupported env then
      match rawNatLit? (← r.whnf depth a),
          rawNatLit? (← r.whnf depth b) with
      | some _, some _ => throw (.notImplemented
          s!"native Nat computation on literals ({c})")
      | _, _ => pure none
    else pure none
  | _ => pure none

/-- Certify a spine against a recursor telescope: each argument's
inferred type is defeq to the corresponding (instantiated) domain.
This is what hands the soundness proof the memberships the iota
equations need, at every level assignment. -/
def iotaCerts (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → List Expr → m Bool
  | _, [] => pure true
  | .forallE _ ty body _, arg :: rest => do
    let ta ← r.infer depth arg
    if ← r.defeq depth ta ty then
      iotaCerts r env depth (body.instantiate1 arg) rest
    else pure false
  | _, _ :: _ => pure false

/-- Peel a `∀`-telescope along an argument list (the residual type of
a fully applied telescope). -/
def piResidual : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ _ b _, a :: as => piResidual (b.instantiate1 a) as
  | _, _ :: _ => none

/-- Pairwise definitional equality of two spines (used to check a
major's constructor parameters against the recursor's). -/
def defEqList (r : CoreFns m) (env : Env) (depth : Nat) :
    List Expr → List Expr → m Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then
      defEqList r env depth as bs
    else pure false
  | _, _ => pure false

/-- Proof irrelevance certification: both sides' types whnf to the
basis unit type (all of whose inhabitants are the proof point in the
model), or both sides' types' *sorts* are `Prop`.  In the model
everything inhabiting a proposition is the proof point, so any two such
terms are equal — no common-type check is needed: soundness holds
without it, and the annotation-first discipline (every subterm is
checked before definitional equality compares it; congruence compares
argument pairs only after the earlier arguments matched) makes a
heterogeneous comparison unreachable, so the official kernel's check is
implied (see DESIGN.md, design-review triage). -/
def proofIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  let ta ← r.infer depth a
  if isUnitLikeTy env (← r.whnf depth ta) then
    let tb ← r.infer depth b
    if isUnitLikeTy env (← r.whnf depth tb) then
      pure true
    else
      pure false
  else
    match ← r.whnf depth (← r.infer depth ta) with
    | .sort uT =>
      let okA ← liftFueled "level comparison" (Level.isEquiv uT .zero)
      let tb ← r.infer depth b
      match ← r.whnf depth (← r.infer depth tb) with
      | .sort vT =>
        let okB ← liftFueled "level comparison" (Level.isEquiv vT .zero)
        pure (okA && okB)
      | _ => pure false
    | _ => pure false

/-- Pair eta certification: `a` is a fully applied structure
constructor (a stored constructor that is the single rule of an
index-free recursor, under the `<ind>.rec` naming convention), `b`
inhabits the matching structure type at the same levels, and `a`'s
two fields are defeq to `b`'s projections.  In the model both sides
are then the pair of `b`'s components (or the proof point at the Prop
collapse); the environment invariant supplies the facts for the stored
constants.

Task #130's extra check — the pair type's two arguments certified
against the projection entry's telescope (`projParamCert`) — was a
TT-lane check, statically dead since #148 T7b (`CheckMode.ttChecks ≡
false`) and deleted with the rest of that code at task #161's de-gating
round A+B+C (item A, harvest site 23). -/
def pairEtaCert (_mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (a b : Expr) :
    m Bool := do
  match a with
  | .app (.app (.app (.app (.const c us) pα) pβ) s₁) s₂ =>
    match env.find? c with
    | some (.ctorInfo _cvm 2 2) => do
      let tb ← r.infer depth b
      match ← r.whnf depth tb with
      | .app (.app (.const c' us') A) B =>
        match env.find? c' with
        | some (.indInfo _ _) =>
          match env.find? (c'.str "rec") with
          | some (.recInfo _ mI rP [rr]) =>
            if rr.ctor = c ∧ rr.nfields = 2 ∧ mI = rP ∧
                reservedBasisNames.contains (c'.str "rec") = true then
              if ← liftFueled "level comparison"
                  (Level.isEquivList us us') then
                -- Certify the constructor's type arguments against the
                -- stuck side's (task #100: under the domain-relative
                -- collapse the model cannot recover the constructor
                -- spine's memberships from its value — an empty-domain
                -- chain collapses to the proof point — so the fields'
                -- memberships are transported from the stuck side's
                -- type, which these two checks identify)
                if ← r.defeq depth pα A then
                  if ← r.defeq depth pβ B then
                    if ← r.defeq depth s₁ (.proj c' 0 b) then
                      if ← r.defeq depth s₂ (.proj c' 1 b) then
                        pure true
                      else pure false
                    else pure false
                  else pure false
                else pure false
              else pure false
            else pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false
  | _ => pure false

/-- The per-projection telescope certificates of a structural eta
certification: for every field index, the installed projection
function's telescope is certified against the type's arguments and the
stuck side. -/
def structEtaProjCerts (r : CoreFns m) (env : Env) (depth : Nat)
    (T : Name) (us' : List Level) (targs : List Expr) (b : Expr)
    (lpsT : List Name) : List Nat → m Bool
  | [] => pure true
  | i :: rest => do
    match env.find? (projFnName T i) with
    | some (.recInfo cvp _ _ _) =>
      if cvp.levelParams = lpsT ∧
          (cvp.type.stripPis (targs.length + 1)).isSome = true then
        if ← iotaCerts r env depth
            (cvp.type.instantiateLevelParams cvp.levelParams us')
            (targs ++ [b]) then
          structEtaProjCerts r env depth T us' targs b lpsT rest
        else pure false
      else pure false
    | _ => pure false

/-- The structure-eta certificate against a *given* weak-head-normal
type of the stuck side (callers that already reduced it — the
stuck-major rescue — pass their own copy, so the certificate's facts
are in terms of that expression). -/
def structEtaCertWith (r : CoreFns m) (env : Env) (depth : Nat)
    (a b wtb : Expr) : m Bool := do
  match a.getAppFn with
  | .const c us =>
    match env.find? c with
    | some (.ctorInfo cvc cnP cnF) =>
      if a.getAppArgs.length = cnP + cnF then
        match wtb.getAppFn with
        | .const T us' =>
          match env.find? T with
          | some (.indInfo cvT caps) =>
            if caps.eta = true ∧ caps.etaCtor = c ∧
                caps.etaParams = cnP ∧ caps.etaFields = cnF ∧
                reservedBasisNames.contains T = false ∧
                reservedBasisNames.contains c = false ∧
                wtb.getAppArgs.length = cnP ∧
                us'.length = cvT.levelParams.length ∧
                cvc.levelParams = cvT.levelParams ∧
                (cvT.type.stripPis cnP).isSome = true then
              if ← liftFueled "level comparison"
                  (Level.isEquivList us us') then
                if ← iotaCerts r env depth
                    (cvT.type.instantiateLevelParams cvT.levelParams
                      us') wtb.getAppArgs then
                  if ← structEtaProjCerts r env depth T us'
                      wtb.getAppArgs b cvT.levelParams
                      (List.range cnF) then
                    if ← defEqList r env depth
                        (a.getAppArgs.take cnP) wtb.getAppArgs then
                      -- synthetic-spine certification (task #137): the
                      -- fabricated constructor application is certified
                      -- against the constructor's own telescope, here
                      -- rather than at the callers, so that both
                      -- consumers get it (`majorToCtor`'s eta rescue ran
                      -- it already, task #71; `defeq`'s `structEtaCert`
                      -- did not).  TT-lane check (task #147): skipped
                      -- unless `mode.ttChecks`.
                      if ← (if mode.ttChecks then
                          iotaCerts r env depth
                            (cvc.type.instantiateLevelParams
                              cvc.levelParams us)
                            (wtb.getAppArgs ++
                              (List.range cnF).map fun i =>
                                Expr.mkAppN (.const (projFnName T i) us')
                                  (wtb.getAppArgs ++ [b]))
                        else pure true) then
                        defEqList r env depth (a.getAppArgs.drop cnP)
                          ((List.range cnF).map fun i =>
                            Expr.mkAppN (.const (projFnName T i) us')
                              (wtb.getAppArgs ++ [b]))
                      else pure false
                    else pure false
                  else pure false
                else pure false
              else pure false
            else pure false
          | _ => pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Structural eta certification for a stored eta-capable structure:
`a` is a fully applied constructor of a structure whose recorded
capabilities include eta, `b` inhabits that structure type, the
constructor's parameters are the type's arguments, and every field is
the corresponding installed projection function applied to `b`.  The
type application is additionally certified against the type former's
telescope (the memberships the stored eta law consumes). -/
def structEtaCert (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  let tb ← r.infer depth b
  let wtb ← r.whnf depth tb
  structEtaCertWith mode r env depth a b wtb

/-- Unit-likeness certification: `a` and `b` inhabit the same stored
unit-like family (the types are definitionally equal and the type
application is certified against the family's telescope), so their
values coincide by the stored unit law. -/
def structUnitCert (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  let ta ← r.infer depth a
  let wta ← r.whnf depth ta
  match wta.getAppFn with
  | .const T us' =>
    match env.find? T with
    | some (.indInfo cvT caps) =>
      if caps.unitlike = true ∧
          reservedBasisNames.contains T = false ∧
          wta.getAppArgs.length = caps.unitParams ∧
          us'.length = cvT.levelParams.length ∧
          (cvT.type.stripPis caps.unitParams).isSome = true then
        let tb ← r.infer depth b
        let wtb ← r.whnf depth tb
        if ← r.defeq depth wta wtb then
          iotaCerts r env depth
            (cvT.type.instantiateLevelParams cvT.levelParams us')
            wta.getAppArgs
        else pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Eta certification for a one-sided λ against a stuck term `b`: `b`'s
type whnfs to a `∀` whose domain is defeq to the λ's, and the λ's body
is pointwise the application of `b`.  The λ is then `b`'s eta-expansion
(soundness: `SetTheory.lam_eta`). -/
def etaCert (mode : CheckMode) (r : CoreFns m) (_env : Env) (depth : Nat)
    (n₁ : Name) (ty₁ body₁ : Expr) (m₁ : BinderMeta) (b : Expr) :
    m Bool := do
  let tb ← r.infer depth b
  match ← r.whnf depth tb with
  | .forallE _ ty₂ _ m₂ =>
    -- Task #161: the λ's prop-ness annotation must agree with the
    -- product it η-expands (`lamR_eta`'s regime agreement) — checked
    -- LAST, like the defeq binder arms, so a mismatch fires only on
    -- an otherwise-successful η certification.  (This is the
    -- validated successor of the cod-agreement comparison task #100
    -- stage 6 deleted.)
    if ← r.defeq depth ty₂ ty₁ then
      unless ← r.defeq (depth + 1)
          (body₁.instantiate1 (.fvar depth n₁ ty₁))
          (.app b (.fvar depth n₁ ty₁)) do return false
      if mode.verified && !(m₁.pw.equiv m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (eta)")
      pure true
    else pure false
  | _ => pure false

/-- The fallback for structurally distinct stuck terms: pair eta in
either direction, structural eta in either direction, unit-likeness,
else proof irrelevance. -/
def stuckIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  if ← pairEtaCert mode r env depth a b then pure true
  else if ← pairEtaCert mode r env depth b a then pure true
  else if ← structEtaCert mode r env depth a b then pure true
  else if ← structEtaCert mode r env depth b a then pure true
  else if ← structUnitCert r env depth a b then pure true
  else proofIrrel r env depth a b

/-- The eta-rescue fabrication's argument spine: the reduced type's
arguments followed by the installed projection functions applied to
the stuck major.  Shared between the fabrication and its
synthetic-spine certificate in `majorToCtor`; a named helper keeps the
walked proof goals small. -/
def etaFabArgs (T : Name) (ust : List Level) (targs : List Expr)
    (major : Expr) (nF : Nat) : List Expr :=
  targs ++ (List.range nF).map fun j =>
    Expr.mkAppN (.const (projFnName T j) ust) (targs ++ [major])

/-- Stuck-major rescue (`to_cnstr_when_K` and `to_cnstr_when_structure`
in the official kernel): a recursor's major premise that does not whnf
to a constructor application may still be *replaced* by one.  For a
K-flagged inductive proposition the parameters-only application of the
single constructor is fabricated from the major's type and certified by
proof irrelevance (in the model both are the proof point); for an
eta-capable structure the constructor of the major's projections is
fabricated and certified by the structure-eta certificate (in the model
both are the tuple of the major's components).  An uncertified major
stays put — sound, the reduction simply stays stuck. -/
def majorToCtor (r : CoreFns m) (env : Env) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : Expr) : m Expr := do
  -- cheap syntactic gates before any inference: a rescue needs a
  -- single-rule recursor whose constructor's inductive is stored with
  -- the matching capability
  if isCtorApp env major then pure major else
  match rules with
  | [rl] =>
    match env.find? rl.ctor with
    | some (.ctorInfo cvj cnP cnF) =>
      match (cvj.type.piResult).getAppFn with
      | .const T _ =>
        match env.find? T with
        | some (.indInfo cvT caps) =>
          if caps.ruleK = true ∧ cnF = 0 then
            let tmaj ← r.whnf depth (← r.infer depth major)
            match tmaj.getAppFn with
            | .const T' ust =>
              if T' = T ∧ cvj.levelParams.length = ust.length then
                if cnP ≤ tmaj.getAppArgs.length ∧
                    (cvj.type.stripPis cnP).isSome = true then
                  let fab := Expr.mkAppN (.const rl.ctor ust)
                    (tmaj.getAppArgs.take cnP)
                  -- scope guard (cf. `annotateProjElim`): scoping of
                  -- the fabricated major is checked syntactically,
                  -- keeping its verification local
                  if fab.wscopedB depth && fab.looseBVarsBounded 0 &&
                      fab.fvarLeaves.all
                        (fun l => major.fvarLeaves.contains l) then
                    -- Synthetic-spine certification (task #71): a
                    -- fabricated constructor spine has no annotated
                    -- application chain for the gated fire-path
                    -- certificates to recover memberships from, so
                    -- the *ungated* telescope certificate runs here,
                    -- relocated from the fire path.
                    if ← iotaCerts r env depth
                        (cvj.type.instantiateLevelParams
                          cvj.levelParams ust)
                        (tmaj.getAppArgs.take cnP) then
                      -- The official `to_cnstr_when_K` type check on
                      -- the fabrication: the constructor
                      -- application's type must be defeq to the
                      -- major's (for `Eq` this is the endpoint
                      -- condition — `Eq.refl a : Eq a a` against the
                      -- major's `Eq a b` forces `a ≡ b`).  A
                      -- reference-kernel check, kept independently of
                      -- the per-fire iota certificates (during the
                      -- gated era of tasks #49/#71 it was load-bearing
                      -- on its own — arena bad/098_ruleKbad fires at
                      -- `Eq.rec.{3,3}`).  `proofIrrel` stays as the
                      -- soundness certificate (in the model both
                      -- sides are the proof point).
                      if ← r.defeq depth tmaj (← r.infer depth fab) then
                        if ← proofIrrel r env depth fab major then
                          pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
              -- a projection function's rescue would reduce to a
              -- no-op (its own reduct), looping the reduction: a
              -- stuck projection stays stuck
              Name.isProjFnShape recName = false then
            let tmaj ← r.whnf depth (← r.infer depth major)
            match tmaj.getAppFn with
            | .const T' ust =>
              -- The official kernel does not eta-rescue propositional
              -- structures (`to_cnstr_when_structure` requires the
              -- structure's result sort to be provably nonzero).  The
              -- test is the *instantiated* one (task #61): a static
              -- `piResultIsProp cvT.type = false` passes a parametric
              -- `Sort u` that a `Prop` instantiation collapses, which
              -- is exactly the case the guard exists for.
              if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
                  ust.length = cvT.levelParams.length ∧
                  piResultNeverZero cvT.levelParams ust cvT.type = true then
                if cvj.levelParams.length = ust.length ∧
                    (cvj.type.stripPis
                      (caps.etaParams + caps.etaFields)).isSome
                      = true then
                  let fab := Expr.mkAppN (.const caps.etaCtor ust)
                    (etaFabArgs T ust tmaj.getAppArgs major
                      caps.etaFields)
                  -- scope guard, as in the K branch
                  if fab.wscopedB depth && fab.looseBVarsBounded 0 &&
                      fab.fvarLeaves.all
                        (fun l => major.fvarLeaves.contains l) then
                    -- synthetic-spine certification, as in the K
                    -- branch (task #71)
                    if ← iotaCerts r env depth
                        (cvj.type.instantiateLevelParams
                          cvj.levelParams ust)
                        (etaFabArgs T ust tmaj.getAppArgs major
                          caps.etaFields) then
                      if ← structEtaCertWith mode r env depth fab major
                          tmaj then
                        pure fab
                      -- 0-field rescue for the pinned basis `PUnit`
                      -- (the generic certificate excludes reserved
                      -- names): the fabrication is the bare
                      -- constructor, certified by proof
                      -- irrelevance's unit-likeness branch; the
                      -- official rescue additionally requires the
                      -- instantiated result sort to be provably
                      -- nonzero
                      -- 0-field rescue: the instantiated non-Prop
                      -- test is already in the branch guard above
                      else if caps.etaFields = 0 ∧
                          cvj.levelParams.length = ust.length then
                        if ← proofIrrel r env depth fab major then
                          pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else pure major
        | _ => pure major
      | _ => pure major
    | _ => pure major
  | _ => pure major

/-- Convert a literal major premise to constructor form: a `Nat`
literal one layer (`litToCtorIfNat`); a `String` literal to its
*reduced* constructor form — the reference kernels re-reduce after
`strLitToConstructor` (lean4lean `Inductive/Reduce.lean`, nanoda
`str_lit_to_ctor_reducing`) since `String.ofList` is a definition, not
a constructor.  An unsupported literal passes through (stuck; sound,
and unreachable for annotated input). -/
def litMajorToCtor (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → m Expr
  | .lit (.strVal s) =>
    if strLitSupported env then r.whnf depth (strLitToConstructor s)
    else pure (.lit (.strVal s))
  | e => pure (litToCtorIfNat env e)

/-- Convert a string-literal projection scrutinee to its *reduced*
constructor form — the references' proj expansion site (official
`reduce_proj_core`, `type_checker.cpp:383-384`; lean4lean
`TypeChecker.lean` proj clause; nanoda `tc.rs` `reduce_proj`): the
expansion's head `String.ofList` is a definition, so the whnf grinds it
to the real `String.ofByteArray` constructor form.  Only `String`
literals — no reference touches other scrutinees here.  An unsupported
literal passes through (stuck; sound, and unreachable for annotated
input). -/
def projLitToCtor (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → m Expr
  | .lit (.strVal s) =>
    if strLitSupported env then r.whnf depth (strLitToConstructor s)
    else pure (.lit (.strVal s))
  | e => pure e

/-- The level and constructor-parameter comparands a firing rule's
checks compare the major's constructor levels and parameters against:
for a canonical (`.plain`) rule the constructor's levels link to the
recursor's by name and its parameters are the recursor's leading
arguments; for a certified nested (`.nested`) rule both are the stored
major-domain instantiations, at the recursor's level instantiation and
(for the parameters) instantiated at the recursor's leading-argument
spine (the stored pins live in the `rP`-binder prefix context — index
arguments never occur in them, by the shape certification).
(Junk for `.inert` rules — `iotaRec` declines before reading it.) -/
def recFireComparands (rl : RecRule) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args : List Expr)
    (rP : Nat) : List Level × List Expr :=
  match rl.fire with
  | .nested lvls pins =>
    (lvls.map (Level.subst lps us),
     pins.map fun p => Expr.instSpine (args.take rP) (rP - 1)
       (p.instantiateLevelParams lps us))
  | _ =>
    (cvjLps.map fun p => Level.subst lps us (.param p),
     args.take rl.ctorParams)

/-- One iota step: the expression is a stored recursor applied to
exactly its telescope (params, motives, minors, indices, major), the
major premise whnfs to a fully applied constructor with a matching
rule (a literal major converts to constructor form — see
`litMajorToCtor` —, a
stuck major may be rescued — see `majorToCtor`), and the spine is
certified against the recursor's own (pinned, annotated) type with
`iotaCerts` (per-slot infer+defeq; task #100 de-gating retired the
possibly-Prop annotation gate of tasks #49/#71 — unsound-to-model
under the domain-relative collapse, DESIGN.md).  The
result is the rule's rhs applied to the non-index prefix and the
constructor's fields; over-application is handled by the outer app
recursion. -/
def iotaRec (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) :
    m (Option Expr) := do
  match e.getAppFn with
  | .const c us =>
    match env.find? c with
    | some (.recInfo cv mI rP rules) =>
      let args := e.getAppArgs
      -- checker change #9: the recursor's level arity, guarded as
      -- `unfoldDefinition` guards it (`Core.lean:174`).  The official
      -- kernel tests this immediately before instantiating the rule's
      -- RHS (`src/kernel/inductive.h:105`, present since v4.0.0);
      -- lean4lean does the same (`Inductive/Reduce.lean:98`) and
      -- nanoda's `subst_expr_levels` asserts it.  Without it
      -- `rl.rhs.instantiateLevelParams cv.levelParams us` can leak a
      -- level parameter the subject never had -- refuted concretely
      -- at `Interp2/IotaArity.lean`.  Ungated: the reference has it
      -- unconditionally, so a mode gate would break parity.
      if args.length = mI + 1 ∧ us.length = cv.levelParams.length then
        let major₀ ← r.whnf depth (args.getD mI (.bvar 0))
        let major₁ ← litMajorToCtor r env depth major₀
        let major ← majorToCtor mode r env depth c rules major₁
        match major.getAppFn with
        | .const cj usj =>
          match env.find? cj with
          | some (.ctorInfo cvj _ _) =>
            match rules.find? (fun r' => r'.ctor == cj) with
            | some rl =>
              let margs := major.getAppArgs
              -- the constructor's counts are read off the stored rule
              -- (install-computed); the defensive spine-length check
              -- stays
              if margs.length = rl.ctorParams + rl.nfields then
               -- A matched *inert* rule is a positive detection of an
               -- unsupported feature: the redex demands firing an
               -- uncertified nested-auxiliary rule (e.g.
               -- `Syntax.rec_1` on an `Array.mk` major with the
               -- nested certification absent).  Staying silently
               -- stuck would surface as a spurious *reject*
               -- downstream (defeq failure in the app rule), so
               -- decline here instead.
               if rl.fire = .inert then
                 throw (.notImplemented
                   "iota reduction over a nested auxiliary recursor rule")
               else
               if (cv.type.stripPis (mI + 1)).isSome ∧
                  (cvj.type.stripPis (rl.ctorParams + rl.nfields)).isSome
                  then
                -- the constructor's levels and parameters must agree
                -- with the rule's comparands (canonical: the
                -- recursor's own instantiation and leading arguments;
                -- nested: the stored major-domain instantiations) —
                -- the firing mode was computed once at install
                -- (`Expr.recRulePlain` / the nested certification),
                -- never re-derived per fire
                if ← liftFueled "level comparison" (Level.isEquivList usj
                    (recFireComparands rl cv.levelParams us
                      cvj.levelParams args rP).1) then
                 if ← defEqList r env depth (margs.take rl.ctorParams)
                    (recFireComparands rl cv.levelParams us
                      cvj.levelParams args rP).2 then
                  if ← iotaCerts r env depth
                     (cv.type.instantiateLevelParams cv.levelParams us)
                     (args.take mI ++ [major]) then
                   if ← iotaCerts r env depth
                      (cvj.type.instantiateLevelParams cvj.levelParams usj)
                      margs then
                    -- the recursor's index arguments must match the
                    -- constructor's canonical index tuple (the residual
                    -- of its telescope, whose head must be the stored
                    -- family): the model's iota equation only speaks
                    -- about the canonical indices
                    match (cvj.type.instantiateLevelParams cvj.levelParams
                          usj).stripPis (rl.ctorParams + rl.nfields),
                        piResidual (cvj.type.instantiateLevelParams
                          cvj.levelParams usj) margs with
                    | some (_, cbody), some residual =>
                      match cbody.getAppFn with
                      | .const _ _ =>
                        if ← defEqList r env depth
                            (residual.getAppArgs.drop rl.ctorParams)
                            ((args.take mI).drop rP) then
                          pure (some (Expr.mkAppN
                            (rl.rhs.instantiateLevelParams cv.levelParams us)
                            (args.take rP ++ margs.drop rl.ctorParams)))
                        else pure none
                      | _ => pure none
                    | _, _ => pure none
                   else pure none
                  else pure none
                 else pure none
                else pure none
               else pure none
              else pure none
            | none => pure none
          | _ => pure none
        | _ => pure none
      else pure none
    | _ => pure none
  | _ => pure none

/-- Certification for a possibly-Prop structural projection
`proj_i (ctor p⃗ x⃗)` (the subject `e₂` is the whnf'd constructor
application): the projected argument and the subject are both typed.

Task #161 de-gating round A+B+C, item B1 (harvest site 18, list entry
P9).  The clause used to run six things: infer the field, infer *its*
type and whnf it to a sort, compare that sort with the entry's
instantiated `fieldSort`; then the same three for the subject against
`structSort`.  `projStepP_of_claims` (`SetR/Interp2/Step2/ProjRowsP.lean`)
destructures `projCert_inv` as `⟨…, -, -, -, -, hite, -, -, -⟩`: it
consumes **conjunct 5 only**, the subject's own `inferTypeCore` run.
The four sort legs — the two `infer`+`whnf`-to-a-sort runs and the two
`Level.isEquiv` comparisons — are inspected by nothing, and they cannot
become load-bearing later either: `projEntry_pins` (`SetR/ProjPins.lean`)
pins a `native` entry to one of the two basis pair entries, so
`fieldSort`/`structSort` are *concrete* and carry no information the
model does not already have.  They are deleted, and with them the two
`Level` arguments and the callers' `Level.subst`/`substLevelTreeM` of
the pinned sorts.

THE FIELD-INFER RUN STAYS (the ratified negative verdict of the harvest
list): it is not licensed by anything, it is simply not on the removal
list. -/
def projCert (r : CoreFns m) (_env : Env) (depth : Nat)
    (e₂ : Expr) (i : Nat) (nP : Nat) : m Bool := do
  let arg := e₂.getAppArgs.getD (nP + i) (.bvar 0)
  let _ta ← r.infer depth arg
  let _te ← r.infer depth e₂
  pure true

/-- The head-normalization body: beta (with the per-redex argument
certificate, unconditional since the task-#100 de-gating), iota (with
the stuck-major machinery) and the native basis pair projection — but
**no delta**; unfolding happens in the `whnf` loop.  Values (sorts,
binders, constants, literals) return themselves. -/
def whnfCoreBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e =>
    match e with
    | .sort u => pure (.sort u)
    | .fvar idx n ty => pure (.fvar idx n ty)
    | .forallE n ty body bi => pure (.forallE n ty body bi)
    | .lam n ty body mb => pure (.lam n ty body mb)
    | .const n us => pure (.const n us)
    | .lit l => pure (.lit l)
    | .app f a => do
      match ← r.whnfCore depth f with
      | .lam n ty body mb => do
        -- Certify the argument against the domain before reducing
        -- (the soundness proof needs `⟦a⟧ ∈ ⟦ty⟧` at every level
        -- assignment).  An uncertified redex stays stuck — sound, and
        -- unreachable for well-typed input.  Task #100 de-gating: the
        -- former possibly-Prop annotation gate (skip the certificate
        -- at a provably nonzero codomain sort) is unsound-to-model
        -- under the domain-relative collapse (DESIGN.md), so the
        -- certificate now runs unconditionally.
        let ta ← r.infer depth a
        if ← r.defeq depth ta ty then
          r.whnfCore depth (body.instantiate1 a)
        else pure (.app (.lam n ty body mb) a)
      | f' => do
        match ← iotaRec mode r env depth (.app f' a) with
        | some e'' => r.whnfCore depth e''
        | none => pure (.app f' a)
    | .proj sn i pe => do
      let e' ← r.whnf depth pe
      -- A string-literal scrutinee first expands to its reduced
      -- constructor form (`projLitToCtor`) — the references' proj
      -- expansion site.
      let e' ← projLitToCtor r env depth e'
      -- The structural rule `proj_i (ctor p⃗ x⃗) ↦ x_i`, driven by the
      -- projection table (never by basis names): a `native` entry for
      -- (structName, i) supplies the constructor, the counts, and the
      -- possibly-Prop level guard.
      match env.findProj? sn i with
      | some entry =>
        match e'.getAppFn with
        | .const c us =>
          let args := e'.getAppArgs
          if entry.native ∧ c = entry.ctor ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length then
            let arg := args.getD (entry.numParams + i) (.bvar 0)
            -- Certify the reduction: at Prop instances both the
            -- projected argument and the subject collapse to the
            -- proof point (see DESIGN.md on beta certification).
            -- Task #100 de-gating: the former nonzero-sort gate is
            -- unsound-to-model under the domain-relative collapse,
            -- so the certificate runs unconditionally.  Task #161
            -- item B1: the two sort legs and their `Level.subst`s are
            -- gone (see `projCert`).
            if ← projCert r env depth e' i entry.numParams then
              r.whnfCore depth arg
            else pure (.proj sn i e')
          else pure (.proj sn i e')
        | _ => pure (.proj sn i e')
      | none => pure (.proj sn i e')
    | .letE _ _ v b =>
      -- zeta: instantiate the body with the value on demand and
      -- continue (official kernel `whnf_core`, `case expr_kind::Let`;
      -- nanoda `whnf_no_unfolding_aux` `Let`; lean4lean `whnfCore'`
      -- `.letE`).  No local let environment is kept.
      r.whnfCore depth (b.instantiate1 v)
    | .bvar _ =>
      throw (.notImplemented "whnf beyond the supported fragment")

/-- Step budget of the `whnfCore` head-normalization loop (task #106).
Beta, iota, zeta and projection steps are *iteration*: the interned
`whnfCoreLoopI` runs them on this budget instead of charging each step
to the shared recursion-depth budget (and to the native stack).  The
`Expr`-level specification below stays chained — the refinement bridge
reproduces a loop run by the chained recursion *at some knot fuel*
(`Setlec/Verify/BetaSpine.lean`), so the specification and everything
above it are unchanged. -/
@[irreducible] def whnfCoreLoopFuel : Nat := 1000000

/-- Step budget of the `whnf` reduction loop (lean4lean's
`FuelConfig.whnf`, same value).  Literal-acceleration and delta steps
are *iteration*, not recursion: the official kernel's loop is a
`while (true)` and lean4lean's is a fixed-fuel local loop.  Task #106:
routing them through the knot instead charged every unfolding step to
the shared *recursion depth* budget (and to the native stack), so a
long-but-perfectly-ordinary unfolding chain exhausted `checkFuel`. -/
@[irreducible] def whnfLoopFuel : Nat := 100000

/-- One iteration of the reduction loop (the official kernel's `whnf`
body, lean4lean's `whnf'` loop body): head-normalize, try literal
acceleration, unfold one definition — and hand the reduct to the
loop's continuation `k`.  As everywhere in this module, the body never
calls itself: the continuation is abstracted exactly like the record
`r`, so every lemma about the body is proven once, with a hypothesis
about `k`, and the loop lemma is one induction on the budget. -/
def whnfStep (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) (e : Expr) : m Expr := do
  let e₁ ← r.whnfCore depth e
  match ← reduceNat r env depth e₁ with
  | some e₂ => k e₂
  | none =>
    match unfoldDefinition env e₁ with
    | some e₂ => k e₂
    | none => pure e₁

/-- The reduction loop: iterate `whnfStep` on its own step budget, so
the whole chain costs one knot level however many steps it takes. -/
def whnfLoop (r : CoreFns m) (env : Env) (depth : Nat) :
    Nat → Expr → m Expr
  | 0, _ => throw (.internal "fuel exhausted: whnf loop")
  | n + 1, e => whnfStep r env depth (whnfLoop r env depth n) e

/-- The reduction loop's body: run `whnfLoop` at its own step budget. -/
def whnfBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e => whnfLoop r env depth whnfLoopFuel e

/-- Ensure `e` (the type of some expression) is a sort, returning its
level. -/
def ensureSort (r : CoreFns m) (_env : Env) (depth : Nat) (e : Expr) :
    m Level := do
  match ← r.whnf depth e with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

/-- Destructure a term one level (see `ExprView`). -/
@[inline] def viewM (e : Expr) : m (ExprView Expr) := pure e.view

/-- The inference body — **infer-only**: the application rule's
argument check ran once, in the annotation pass, and is trusted here
(so speculative inference inside reduction cannot reject). -/
def inferBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e => do
    match ← viewM (m := m) e with
    | .sort u => pure (.sort (.succ u))
    | .fvar idx _ ty =>
      -- Scope check at the leaf of a traversal that happens anyway
      -- (O(1); never a fresh walk): a free variable must refer to an
      -- enclosing opened binder.  On raw (closed) input at depth 0 this
      -- rejects any `fvar` outright; internally the checker only opens
      -- variables below the ambient depth, so for disciplined calls the
      -- check always passes (and inference success implies
      -- well-scopedness, the base case of the cache discipline).
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | .const n us => do
      match env.find? n with
      | none => throw (.invalid s!"unknown constant {n}")
      | some ci =>
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {n}")
        pure (cv.type.instantiateLevelParams cv.levelParams us)
    | .lit (.natVal _) => do
      if natLitSupported env then pure (.const natName [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      -- a string literal types as `String` (the reference kernels'
      -- `Literal.typeName`); without the pinned support declarations
      -- this is a positively detected unsupported feature: decline
      if strLitSupported env then pure (.const stringName [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .forallE n ty body mb => do
      -- The ∀-formation rule, official-kernel style (task #100 stage 6):
      -- the codomain sort is *inferred* from the opened body.  Task
      -- #161: at the verified modes the node's prop-ness annotation is
      -- VALIDATED against the inferred codomain sort — `equiv` is
      -- complete for zero-ness agreement, and a mismatch is a decline
      -- (a positively detected annotation the checker cannot certify),
      -- never a reject.  The annotation is never read by reduction.
      match ← r.whnf depth (← r.infer depth ty) with
      | .sort u => do
        let v ← ensureSort r env (depth + 1)
          (← r.infer (depth + 1) (body.instantiate1 (.fvar depth n ty)))
        if mode.verified then
          unless (Level.zeronessOf v).equiv mb.pw do
            throw (.notImplemented "sort-annotation mismatch (forall-cod)")
        pure (.sort (.imax u v))
      | _ => throw (.invalid "expected a sort")
    | .lam n ty body mb => do
      -- The domain must be a type (and the model needs its
      -- interpretation defined), exactly as in the ∀ rule.
      match ← r.whnf depth (← r.infer depth ty) with
      | .sort _ => do
        let bt ← r.infer (depth + 1)
          (body.instantiate1 (.fvar depth n ty))
        -- The *codomain* sort, at the verified modes only (task #152,
        -- restoring the I6/I7 symmetry task #100 stage 6 broke): the
        -- ∀ clause's own `ensureSort` move, on the body's inferred
        -- type.  It is what the set lane's annotation pass needs —
        -- `HasSort (A :: Δ) B v` — and what no metatheorem supplies
        -- (`Setlec/SetR/DESIGN.md` findings A3, B5, A5: validity for
        -- `Infer` is refuted at the application clause, so the fact
        -- has to be computed).  The reference kernel's `infer_lambda`
        -- does not run it, so `.noModel` — the official-parity lane —
        -- does not either.
        --
        -- It fires once per λ **chain**, at the innermost binder (the
        -- `!body.isLam` guard).  At an outer binder the codomain is
        -- the inner λ's own `∀`-type, whose sort is `imax` of the
        -- inner domain's (checked at that binder) and the chain's
        -- (checked here) — so no fact is lost, and this is the
        -- granularity the interned telescope loop (task #72) can
        -- reproduce: it opens a whole λ-chain in bulk and never
        -- materializes the intermediate opened types.
        if mode.verified then
          match body.lamPw with
          | some pwI =>
            -- Task #161, the chain rule: an outer λ's codomain is the
            -- inner λ's own ∀-type, whose sort's zero-ness is the
            -- inner codomain's — datum equality with the neighbour,
            -- no inference (this dissolves the #152 chain guard's
            -- information loss: the per-node fact is now checked at
            -- every node, at O(1) each).
            unless mb.pw.equiv pwI do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-chain)")
          | none =>
            -- The innermost binder: the task-#152 codomain-sort
            -- computation, now also validating the node's annotation.
            let btt ← r.infer (depth + 1) bt
            let vb ← ensureSort r env (depth + 1) btt
            unless (Level.zeronessOf vb).equiv mb.pw do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-leaf)")
        pure (.forallE n ty (bt.abstract1 depth) mb)
      | _ => throw (.invalid "expected a sort")
    | .app f a => do
      let tf ← r.infer depth f
      match ← r.whnf depth tf with
      | .forallE _ ty body _mt => do
        -- Per-argument re-check (task #100 de-gating: the former
        -- possibly-Prop annotation gate of task #49 is unsound-to-model
        -- under the domain-relative collapse, so the certificate runs
        -- unconditionally; the soundness proof needs `⟦a⟧ ∈ ⟦ty⟧`).
        let ta ← r.infer depth a
        unless ← r.defeq depth ta ty do
          throw (.invalid "application type mismatch")
        pure (body.instantiate1 a)
      | _ => throw (.invalid "function expected")
    | .proj _sn i pe => do
      -- A `.proj` node is typed by its projection-table entry: the
      -- stored level-parametric type, instantiated at the subject
      -- type's levels and peeled along its arguments and the subject.
      -- Only `native` entries type bare nodes (fallback-shape
      -- projections are rewritten into eliminations at annotate time).
      let te ← r.whnf depth (← r.infer depth pe)
      match te.getAppFn with
      | .const T us =>
        match env.findProj? T i with
        | some entry =>
          if entry.native ∧ te.getAppArgs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            match piResidual
                (entry.ty.instantiateLevelParams entry.levelParams us)
                (te.getAppArgs ++ [pe]) with
            | some resTy => pure resTy
            | none => throw (.internal "malformed projection entry")
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | .letE _ ty v b => do
      -- The official kernel's `infer_let` check order (`!infer_only`):
      -- the annotation is a type, the value's inferred type matches it,
      -- then the body *with the value transparent* — nanoda's
      -- `infer_let` instantiates the body with the value and recurses
      -- (task #100 stage 6: these checks moved here from the deleted
      -- annotation pass).
      let _ ← ensureSort r env depth (← r.infer depth ty)
      let tv ← r.infer depth v
      unless ← r.defeq depth tv ty do
        throw (.invalid "let value type mismatch")
      r.infer depth (b.instantiate1 v)
    | .bvar _ =>
      throw (.notImplemented "inferType beyond the supported fragment")

/-- Levels-and-spine congruence for two applications of the same
stored constant — the lazy delta *same-head short-circuit* (the
official kernel's `try_eq_const_app`): before unfolding both sides of
`f as ≡ f bs`, try pairwise definitional equality of the levels and
the spine arguments.  A `false` verdict is never final — the caller
falls back to unfolding — so an inconclusive level comparison simply
answers `false` here. -/
def defeqSpine (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  match a.getAppFn with
  | .const n us =>
    match b.getAppFn with
    | .const n' us' =>
      if n = n' ∧ a.getAppArgs.length = b.getAppArgs.length then
        match Level.isEquivList us us' with
        | some true => defEqList r env depth a.getAppArgs b.getAppArgs
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- The definitional-equality body: syntactic fast path, head
normalization of both sides (**no delta** — `whnfCore`), proof
irrelevance (the official kernel's `is_def_eq_proof_irrel`, run after
`whnf_core` and before any delta), then the
*lazy delta* strategy of real kernels: literal acceleration first
(mirroring the `whnf` loop order), then — when a side's head is an
unfoldable definition — unfold lazily, guided by the reducibility
hints (unfold only the side with the greater hint; at equal hints try
the same-head congruence short-circuit, then unfold both).  Each
literal-acceleration and unfolding step is one **iteration of this
loop** (the reference kernels' `lazy_delta_reduction` loop; lean4lean
runs it on `FuelConfig.lazyDelta`), and every re-entry re-runs the
syntactic fast path and `whnfCore` (the official kernel's `whnf_core`
after each unfold).  Task #106: these steps used to recurse through
`r.defeq`, charging a delta chain to the shared *recursion depth*
budget one unit per step.  Only when neither head unfolds does
structural congruence with the stuck fallbacks decide.  The hints
steer *order only*: every branch below is an independently sound
reduction or comparison, so the verdict never depends on the hint
values. -/
def defeqStep (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → Expr → m Bool) (a b : Expr) : m Bool := do
    -- syntactic fast path (the references' most-hit branch)
    if a == b then pure true else
    let a' ← r.whnfCore depth a
    let b' ← r.whnfCore depth b
    if a' == b' then pure true else
    -- Proof irrelevance, hoisted before lazy delta exactly as in the
    -- official kernel (`is_def_eq_proof_irrel` runs after `whnf_core`
    -- and before `lazy_delta_reduction`): with theorem values
    -- delta-unfolding (task #66), leaving it in the stuck fallback
    -- would grind through proof bodies first (init-prelude probe:
    -- 227 G → recovered by the hoist).  The fallback's copy stays
    -- (memoized; reachable when a reduction step rewrites a side).
    if ← proofIrrel r env depth a' b' then pure true else
    -- Literal acceleration is guarded on *both* sides being free of
    -- free variables, mirroring the official kernel
    -- (`type_checker.cpp`, `lazy_delta_reduction`:
    -- `if ((!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce)`) and
    -- lean4lean (`TypeChecker.lean:782`).  Unguarded folding is a
    -- forbidden strategy superset (DESIGN.md, reduction-strategy
    -- ruling): on an *open* `Int32`/`Int64` arithmetic pair it whnfs
    -- an open argument and delta-grinds the `Nat.brecOn` tower toward
    -- `2^31`/`2^63` unary `succ` steps; guarded, such pairs fall
    -- through to the `sameRegular` spine congruence below (the
    -- official kernel's `is_def_eq_args`).  The whnf-loop `reduceNat`
    -- (`whnfBody`) stays unguarded — the official whnf loop is too.
    -- The `hasFvar` traversals cost no more than the `a' == b'`
    -- comparison already above (this Expr-level body is the
    -- specification; the executable interned twin reads an `O(1)`
    -- eager per-node fvar range instead).
    match ← (if !a'.hasFvar && !b'.hasFvar then
        reduceNat r env depth a' else pure none) with
    | some a₂ => k a₂ b'
    | none =>
    match ← (if !a'.hasFvar && !b'.hasFvar then
        reduceNat r env depth b' else pure none) with
    | some b₂ => k a' b₂
    | none =>
    -- Lazy delta, **decision before materialization** (the official
    -- kernel's `lazy_delta_reduction_step` reads a `delta_step` off
    -- the two heads and their hints and calls `unfold_definition`
    -- only inside the branch that consumes it; lean4lean's
    -- `isDefEqDelta` likewise).  The former spelling built *both*
    -- unfoldings in the match scrutinee before deciding which one it
    -- needed — pure waste on every one-sided step and on every
    -- short-circuited same-head step (measured at ~19 000 unfoldings
    -- per side on `Std.Time…toDays._proof_1`, task #106).  The
    -- `pure false` fallbacks are unreachable — `unfoldableHead env e`
    -- is `(unfoldDefinition env e).isSome` by construction — and
    -- sound (`false` is never a certificate).
    match unfoldableHead env a', unfoldableHead env b' with
    | true, false =>
      match unfoldDefinition env a' with
      | some a₂ => k a₂ b'
      | none => pure false
    | false, true =>
      match unfoldDefinition env b' with
      | some b₂ => k a' b₂
      | none => pure false
    | true, true =>
      let ha := headHint env a'
      let hb := headHint env b'
      if ReducibilityHint.lt hb ha then
        match unfoldDefinition env a' with
        | some a₂ => k a₂ b'
        | none => pure false
      else if ReducibilityHint.lt ha hb then
        match unfoldDefinition env b' with
        | some b₂ => k a' b₂
        | none => pure false
      else if ReducibilityHint.sameRegular ha hb && sameConstHeads a' b' then
        -- Same constant at equal *regular* hints: cheap congruence
        -- first — this short-circuit is where lazy delta wins on
        -- large proof terms, and (task #106) it now runs *before* any
        -- unfolding is built, as `try_eq_const_app` does.  The
        -- `sameRegular` guard mirrors the reference kernels (nanoda
        -- `try_eq_const_app`, the official kernel) exactly and is
        -- deliberate: at equal `abbrev` (or `opaque`) hints both
        -- sides unfold eagerly instead, because proof authors rely on
        -- abbrevs unfolding eagerly and a spine defeq attempt on
        -- abbrev-headed applications risks reduction bombs (spines
        -- only equal after reduction, retried at every congruence
        -- level).  Do not generalize this guard.
        if ← defeqSpine r env depth a' b' then pure true
        else
          match unfoldDefinition env a', unfoldDefinition env b' with
          | some a₂, some b₂ => k a₂ b₂
          | _, _ => pure false
      else
        match unfoldDefinition env a', unfoldDefinition env b' with
        | some a₂, some b₂ => k a₂ b₂
        | _, _ => pure false
    | false, false =>
    match a', b' with
    | .sort u, .sort v => liftFueled "level comparison" (Level.isEquiv u v)
    | .lit l₁, .lit l₂ => pure (l₁ == l₂)
    -- a packed literal against a constructor form: compare
    -- shape-directed (an unpack-and-retry would immediately repack in
    -- `reduceNat` and loop)
    | .lit (.natVal n), .const c us =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrel mode r env depth (.lit (.natVal n)) (.const c us)
    | .const c us, .lit (.natVal n) =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrel mode r env depth (.const c us) (.lit (.natVal n))
    | .lit (.natVal nn), .app f x =>
      match nn, f with
      | k + 1, .const c [] =>
        if c = natSuccName then r.defeq depth (.lit (.natVal k)) x
        else stuckIrrel mode r env depth (.lit (.natVal nn)) (.app f x)
      | _, _ => stuckIrrel mode r env depth (.lit (.natVal nn)) (.app f x)
    | .app f x, .lit (.natVal nn) =>
      match nn, f with
      | k + 1, .const c [] =>
        if c = natSuccName then r.defeq depth x (.lit (.natVal k))
        else stuckIrrel mode r env depth (.app f x) (.lit (.natVal nn))
      | _, _ => stuckIrrel mode r env depth (.app f x) (.lit (.natVal nn))
    -- a string literal against a unary `String.ofList` application:
    -- expand the literal to its constructor form and compare — the
    -- reference kernels' `tryStringLitExpansion` (lean4lean
    -- `TypeChecker.lean`, nanoda `try_string_lit_expansion`), which
    -- fires exactly when the other side's function part is the bare
    -- `String.ofList` constant
    | .lit (.strVal st), .app (.const cO usO) x =>
      if cO = stringOfListName ∧ usO = [] ∧ strLitSupported env then
        r.defeq depth (strLitToConstructor st) (.app (.const cO usO) x)
      else stuckIrrel mode r env depth (.lit (.strVal st)) (.app (.const cO usO) x)
    | .app (.const cO usO) x, .lit (.strVal st) =>
      if cO = stringOfListName ∧ usO = [] ∧ strLitSupported env then
        r.defeq depth (.app (.const cO usO) x) (strLitToConstructor st)
      else stuckIrrel mode r env depth (.app (.const cO usO) x) (.lit (.strVal st))
    | .fvar i n₁ ty₁, .fvar j n₂ ty₂ =>
      if i == j then pure true
      else stuckIrrel mode r env depth (.fvar i n₁ ty₁) (.fvar j n₂ ty₂)
    | .const n us, .const n' us' =>
      if n = n' then
        if ← liftFueled "level comparison" (Level.isEquivList us us') then
          pure true
        else stuckIrrel mode r env depth (.const n us) (.const n' us')
      else stuckIrrel mode r env depth (.const n us) (.const n' us')
    | .forallE n₁ ty₁ body₁ m₁, .forallE n₂ ty₂ body₂ m₂ => do
      -- Binder congruence.  Task #161: at the verified modes the two
      -- prop-ness annotations must agree (`equiv`, complete) for the
      -- two-regime interpretations to coincide (`piR_zero_agree`'s
      -- premise).  The comparison runs LAST — only a pair that is
      -- otherwise definitionally equal can reach it, so benign
      -- cert-fallthrough `false`s are untouched and a firing mismatch
      -- is exactly the cross-provenance coherence corner, declined
      -- loudly.  (The official kernel compares no annotations; the
      -- pre-#100 zero-ness comparison is back in validated clothing.)
      unless ← r.defeq depth ty₁ ty₂ do return false
      unless ← r.defeq (depth + 1)
          (body₁.instantiate1 (.fvar depth n₁ ty₁))
          (body₂.instantiate1 (.fvar depth n₂ ty₂)) do return false
      if mode.verified && !(m₁.pw.equiv m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-forall)")
      pure true
    | .lam n₁ ty₁ body₁ m₁, .lam n₂ ty₂ body₂ m₂ => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      unless ← r.defeq (depth + 1)
          (body₁.instantiate1 (.fvar depth n₁ ty₁))
          (body₂.instantiate1 (.fvar depth n₂ ty₂)) do return false
      if mode.verified && !(m₁.pw.equiv m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-lam)")
      pure true
    | .app f₁ a₁, .app f₂ a₂ => do
      -- Stuck applications: **spine-wise** congruence (the official
      -- kernel's `is_def_eq_app`, lean4lean's `isDefEqApp`, nanoda's
      -- `def_eq_app`): equal spine lengths, one head comparison, then
      -- the argument lists pairwise.  Task #106: the former spelling
      -- recursed `defeq` on the *partial* applications `f₁ ≡ f₂`, so
      -- a length-`n` spine re-entered the whole body `n` times —
      -- `n` syntactic fast paths, `n` `whnfCore` pairs, `n` proof
      -- irrelevance probes (two `infer`s each!) and `n` lazy delta
      -- decisions, at `n` levels of knot recursion.  No reference
      -- kernel does that, and nothing is lost: `whnfCore` already
      -- normalized the function parts, and the `unfoldableHead`
      -- guards above are read off the *head* constant, which the
      -- partial applications share.  Then the stuck fallbacks (proof
      -- irrelevance is additionally hoisted before lazy delta at the
      -- top of this body, as in the official kernel; the fallback
      -- copy here fires when a reduction step rewrote a side after
      -- the hoist ran).
      if (Expr.app f₁ a₁).getAppArgs.length =
          (Expr.app f₂ a₂).getAppArgs.length then
        if ← r.defeq depth (Expr.app f₁ a₁).getAppFn
            (Expr.app f₂ a₂).getAppFn then
          if ← defEqList r env depth (Expr.app f₁ a₁).getAppArgs
              (Expr.app f₂ a₂).getAppArgs then pure true
          else stuckIrrel mode r env depth (.app f₁ a₁) (.app f₂ a₂)
        else stuckIrrel mode r env depth (.app f₁ a₁) (.app f₂ a₂)
      else stuckIrrel mode r env depth (.app f₁ a₁) (.app f₂ a₂)
    | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => do
      -- Stuck projections: congruence, else the stuck fallbacks.
      if i₁ == i₂ then
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrel mode r env depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
      else stuckIrrel mode r env depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
    -- One-sided λ: eta, else the stuck fallbacks.
    | .lam n₁ ty₁ body₁ m₁, b₂ => do
      if ← etaCert mode r env depth n₁ ty₁ body₁ m₁ b₂ then pure true
      else stuckIrrel mode r env depth (.lam n₁ ty₁ body₁ m₁) b₂
    | a₁, .lam n₂ ty₂ body₂ m₂ => do
      if ← etaCert mode r env depth n₂ ty₂ body₂ m₂ a₁ then pure true
      else stuckIrrel mode r env depth a₁ (.lam n₂ ty₂ body₂ m₂)
    -- Distinct whnf-stuck head symbols: only the stuck fallbacks can
    -- equate them; `false` is always sound, and `whnf` has already
    -- thrown on unsupported heads, so no unimplemented case can hide
    -- here.
    | e₁, e₂ => stuckIrrel mode r env depth e₁ e₂

/-- The lazy-delta loop: iterate `defeqStep` on its own step budget. -/
def defeqLoop (r : CoreFns m) (env : Env) (depth : Nat) :
    Nat → Expr → Expr → m Bool
  | 0, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | fl + 1, a, b => defeqStep mode r env depth (defeqLoop r env depth fl) a b

/-- Step budget of the lazy-delta loop (lean4lean's
`FuelConfig.lazyDelta`, generously sized here because this loop also
absorbs the literal-acceleration re-entries lean4lean routes through
`isDefEqCore`).  Exhaustion is an internal error, never a verdict. -/
@[irreducible] def defeqLoopFuel : Nat := 100000

/-- The definitional-equality body: the lazy-delta loop at its own
step budget. -/
def defeqBody (r : CoreFns m) (env : Env) : Nat → Expr → Expr → m Bool :=
  fun depth a b => defeqLoop mode r env depth defeqLoopFuel a b

/-- Check that a (raw) type is a `Prop` by annotating it and inferring
its sort. -/
def isPropType (r : CoreFns m) (env : Env) (depth : Nat) (ty : Expr) :
    m Bool := do
  let ty' ← r.annotate depth ty
  let s ← ensureSort r env depth (← r.infer depth ty')
  liftFueled "level comparison" (Level.isEquiv s Level.zero)

/-- Walk a field telescope to the `i`-th binder and return its domain,
earlier binders instantiated with projections of `e'`, mirroring the
official kernel's projection rule: for a `Prop` structure every
*depended-on* skipped field must itself be a `Prop`. -/
def projFieldDom (r : CoreFns m) (env : Env) (depth : Nat)
    (structProp : Bool) (sn : Name) (e' : Expr) :
    Nat → Nat → Expr → m Expr
  | _, 0, .forallE _ dom _ _ => pure dom
  | j, k + 1, .forallE _ dom rest _ => do
    if rest.looseBVarsBounded 0 then
      projFieldDom r env depth structProp sn e' (j + 1) k rest
    else
      if structProp then
        unless ← isPropType r env depth dom do
          throw (.invalid
            "projection through a non-Prop field of a Prop structure")
      projFieldDom r env depth structProp sn e' (j + 1) k
        (rest.instantiate1 (.proj sn j e'))
  | _, _, _ => throw (.invalid "projection index out of range")

/-- Fallback for structures without an installed projection function
(Prop-valued structures whose projections only exist at certain level
instantiations, so per-declaration artifacts cannot cover them):
inline the recursor elimination `S.rec params motive minor e'`, with a
constant motive — the projected field's type, earlier fields replaced
by projections of `e'` — and the minor the constructor's field
telescope as `λ`s returning field `i`.  The parent's elimination
*shape* was checked once, at install, and stored as a template-kind
projection-table entry (`entry.native = false`); only the
per-instantiation pieces are (re)built here.  The rewrite is
annotated, so the ordinary rules re-check it; in particular the
kernel's Prop restriction (projections from a `Prop` structure must
land in `Prop`) surfaces as a type error when the stored recursor's
fixed motive sort cannot reach the field's. -/
def annotateProjRec (r : CoreFns m) (env : Env) (depth : Nat)
    (entry : ProjEntry) (i : Nat) (te e' : Expr) (us : List Level) :
    m Expr := do
  match env.find? entry.ctor with
  | some (.ctorInfo cvC _ cnF) =>
    let params := te.getAppArgs
    if params.length = entry.numParams then
      let ctorTy := cvC.type.instantiateLevelParams cvC.levelParams us
      match ctorTy.instPis params with
      | some tel =>
        let structProp ← isPropType r env depth te
        let fi ← projFieldDom r env depth structProp entry.structName e'
          0 i tel
        match Expr.pisToLams cnF tel (.bvar (cnF - 1 - i)) with
        | some minor =>
          -- the projected field's sort: the official Prop
          -- restriction, and the motive level for subsingleton
          -- eliminators
          let fi' ← r.annotate depth fi
          let sfi ← ensureSort r env depth (← r.infer depth fi')
          if structProp then
            unless ← liftFueled "level comparison"
                (Level.isEquiv sfi Level.zero) do
              throw (.invalid "non-Prop projection from a Prop structure")
          let uf := if entry.recExtraLevel then [sfi] else []
          let raw := Expr.mkAppN
            (.const (entry.structName.str "rec") (uf ++ us))
            (params ++ [.lam (.str .anonymous "t") te fi ⟨.default, .never⟩,
              minor, e'])
          if raw.wscopedB depth && raw.looseBVarsBounded 0 &&
              raw.fvarLeaves.all (fun l => e'.fvarLeaves.contains l) then
            r.annotate depth raw
          else throw (.notImplemented "projection elimination scoping")
        | none => throw (.invalid "projection index out of range")
      | none => throw (.invalid "projection index out of range")
    else throw (.notImplemented "projection parameter mismatch")
  | _ => throw (.notImplemented
      "projection constructor not stored")

/-- Rewrite a projection on a stored non-basis structure into its
installed projection function (a rules-carrying constant checked
against the structure's `_model.proj_i` at install) and annotate the
rewrite: the recursive annotation re-checks every node with the
ordinary rules, and the scope guard keeps the scaffolding inside the
annotated struct's free-variable leaves.  Structures without an
installed projection function fall back to `annotateProjRec`. -/
def annotateProjElim (r : CoreFns m) (env : Env) (depth : Nat) (sn : Name)
    (i : Nat) (te e' : Expr) : m Expr := do
  match te.getAppFn with
  | .const T us =>
    if T = sn then
      match env.find? (projFnName T i) with
      | some (.recInfo _ _ rP _) =>
        -- a projection function is a degenerate recursor: no motive,
        -- no minors, no indices, so its rule prefix is exactly the
        -- parameter count
        if te.getAppArgs.length = rP then
          let raw := Expr.mkAppN (.const (projFnName T i) us)
            (te.getAppArgs ++ [e'])
          if raw.wscopedB depth && raw.looseBVarsBounded 0 &&
              raw.fvarLeaves.all (fun l => e'.fvarLeaves.contains l) then
            r.annotate depth raw
          else throw (.notImplemented "projection elimination scoping")
        else throw (.notImplemented "projection parameter mismatch")
      | some (.projInfo entry) =>
        -- only template entries reach the fallback (native entries
        -- were dispatched by the annotate rule itself)
        if entry.native then
          throw (.internal "native projection entry reached the fallback")
        else annotateProjRec r env depth entry i te e' us
      | _ =>
        -- distinguish an out-of-range index on a projectable
        -- structure (its field 0 has an entry) from a shape without
        -- any projection support
        throw (if (env.find? (projFnName T 0)).isSome then
            CheckError.invalid "projection index out of range"
          else .notImplemented "projection on a non-structure-like type")
    else throw (.invalid "projection structure mismatch")
  | _ => throw (.notImplemented "projection on a non-structure type")

/-! ### The untrusted annotation writes (task #161 P5)

The pass is the existing normalizer: at the verified modes its ∀/λ
clauses *write* the `pw` datum the front door then *validates*.  The
write is untrusted by design — a wrong datum declines, never
unsoundness — and it is a no-op wherever the input already carries a
non-placeholder annotation (`pwWritten`): explicit input annotations
are judged by validation, never overwritten.  The parser's placeholder
for an absent `"pw"` field is `.never`, which is also a legitimate
value; the pass therefore recomputes over `.never` unconditionally
(harmless: a genuinely never-zero codomain recomputes to `.never`),
and the *only* input annotations preserved are the `ifAllZero` ones.
-/

/-- Is this datum a real (non-placeholder) input annotation? -/
@[inline] def pwWritten : PropWhen → Bool
  | .never => false
  | .ifAllZero _ => true

/-- The datum a rebuilt binder ends up with: the one threaded in from
the node below (the chain rule), unless it carries a real input
annotation — those are judged by validation, never overwritten. -/
def annotBinderMeta (pw? : Option PropWhen) (mb : BinderMeta) : BinderMeta :=
  match pw? with
  | some pw => if pwWritten mb.pw then mb else ⟨mb.bi, pw⟩
  | none => mb

/-- The ∀ node's datum: the zero-ness of the *codomain*'s sort, on the
already-annotated opened body — exactly the value `inferBody`'s ∀
clause validates against (`(forall-cod)`).

**The chain read (task #161 P5, proof-lane repair).**  A ∀ body that is
itself a ∀ reuses its inner neighbour's datum instead of inferring:
`zeronessOf (imax u v) = zeronessOf v`, so every node of a telescope
carries the *leaf* codomain sort's zero-ness.  This is the same rule
`annotPwLam` already applies through `lamPw`, and it is what makes the
spec pass pay **one** inference per ∀ telescope, as the design's
telescope-collapse paragraph claims — and what makes it agree with the
interned pass, which computes at the leaf and threads outward
(`annotateBindersOutI`).

Without it the spec inferred the whole inner telescope at every node,
so it *failed* on terms the interned pass accepts — e.g.
`∀ (x : Prop), ∀ (y : Foo), Prop` with `Foo` absent from the
environment: `annotate` never looks a constant up, but inferring the
inner ∀ node does.  See DESIGN.md, task #161 P5 proof-lane finding. -/
def annotPwPi (r : CoreFns m) (env : Env) (depth : Nat) (body' : Expr) :
    m PropWhen := do
  match body'.forallPw with
  | some pwI => pure pwI
  | none => do
    let v ← ensureSort r env depth (← r.infer depth body')
    pure (Level.zeronessOf v)

/-- The λ node's datum: the zero-ness of the sort of the *body's type*.
Mirrors `inferBody`'s λ clause exactly — a λ body reuses its inner
neighbour's datum (the chain rule, no inference), any other body pays
one leaf computation (`(lam-cod-leaf)`). -/
def annotPwLam (r : CoreFns m) (env : Env) (depth : Nat) (body' : Expr) :
    m PropWhen := do
  match body'.lamPw with
  | some pwI => pure pwI
  | none => do
    let bt ← r.infer depth body'
    let vb ← ensureSort r env depth (← r.infer depth bt)
    pure (Level.zeronessOf vb)

/-- The annotation body: compute the codomain-sort annotations of every
binder, bottom-up, by real inference on the opened (already annotated)
body.  This is the one place binder bodies — and the application rule —
are type-checked; `infer` afterwards trusts the annotations.  For a
`forallE` the annotation is the body's sort (so this also checks that
the body *is* a type — the ∀-formation rule); for a `lam` it is the
sort of the body's type. -/
def annotateBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e =>
    match e with
    | .bvar i => pure (.bvar i)
    | .fvar idx n ty =>
      -- Leaf scope check, as in `inferBody`: annotation is the pass raw
      -- input enters through, so a dangling free variable in the input
      -- is rejected here (depth 0: any `fvar` fails).
      if idx < depth then pure (.fvar idx n ty)
      else throw (.invalid "free variable out of scope")
    | .sort u => pure (.sort u)
    | .const n us => pure (.const n us)
    | .lit (.natVal n) => do
      -- a literal is well-formed exactly when its type's declarations
      -- are stored in the expected shape
      if natLitSupported env then pure (.lit (.natVal n))
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal s) => do
      -- as for `Nat` literals; the missing-support verdict is a
      -- decline (exit 2), the feature being positively detected
      if strLitSupported env then pure (.lit (.strVal s))
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .app f a => do
      -- structural (task #100 stage 6: the application rule's checks
      -- moved to the driver's inference sweep — `inferBody`'s app
      -- clause re-checks every argument unconditionally)
      let f' ← r.annotate depth f
      let a' ← r.annotate depth a
      pure (.app f' a')
    | .forallE n ty body mb => do
      -- structural (task #100 stage 6: no annotation to compute and no
      -- checks — the driver's inference sweep re-checks every binder
      -- body via the ∀/λ rules)
      let ty' ← r.annotate depth ty
      let body' ← r.annotate (depth + 1) (body.instantiate1 (.fvar depth n ty'))
      let pw ← if mode.verified && !pwWritten mb.pw then
          annotPwPi r env (depth + 1) body'
        else pure mb.pw
      pure (.forallE n ty' (body'.abstract1 depth) ⟨mb.bi, pw⟩)
    | .lam n ty body mb => do
      let ty' ← r.annotate depth ty
      let body' ← r.annotate (depth + 1) (body.instantiate1 (.fvar depth n ty'))
      let pw ← if mode.verified && !pwWritten mb.pw then
          annotPwLam r env (depth + 1) body'
        else pure mb.pw
      pure (.lam n ty' (body'.abstract1 depth) ⟨mb.bi, pw⟩)
    | .letE _ ty v b => do
      -- The body is annotated *with the value transparent* — nanoda's
      -- `infer_let` instantiates the body with the value and recurses
      -- (the official kernel gets the same transparency from valued
      -- let-fvars in its local context).  Setlec fvars carry no value,
      -- so the body is annotated as its zeta reduct; an opened opaque
      -- variable was tried and rejects real streams (elaborated `let`
      -- bodies rely on the value definitionally — see DESIGN.md).
      --
      -- Task #161 de-gating round A+B+C (item C2, harvest site 6): the
      -- official `infer_let` triple — `ensure_sort_core(infer(type))`,
      -- `infer(val)`, `is_def_eq(val_type, type)` — used to run *here*
      -- as well.  It is redundant: `inferBody`'s own `.letE` clause
      -- runs exactly those three checks on the same `letE` node during
      -- the driver's inference sweep, and nothing in the annotation
      -- pass's contract reads them.  The two `annotate` traversals stay
      -- — they are the pass itself (leaf scope checks, literal support
      -- verdicts), not a certificate.
      let _ ← r.annotate depth ty
      let _ ← r.annotate depth v
      r.annotate depth (b.instantiate1 v)
    | .proj sn i pe => do
      let e' ← r.annotate depth pe
      -- Run the projection rule (the one place it is checked; this
      -- establishes the semantic proj clause of `AnnotOk`).  A
      -- `native` table entry types the node directly (the display
      -- name is normalized to the type's head, so reduction's table
      -- lookup is complete on annotated terms); anything else goes
      -- through the rewrite/fallback dispatch.
      let te ← r.whnf depth (← r.infer depth e')
      match te.getAppFn with
      | .const T _ =>
        match env.findProj? T i with
        | some entry =>
          if entry.native then do
            unless te.getAppArgs.length = entry.numParams do
              throw (.invalid "projection parameter mismatch")
            pure (.proj T i e')
          else annotateProjElim r env depth sn i te e'
        | none => annotateProjElim r env depth sn i te e'
      | _ => annotateProjElim r env depth sn i te e'

end Bodies

/-- Tie the bodies together at a monad: the record whose entry points
are the bodies applied to the record one fuel level down.  Fuel is
*only* here — exhaustion is an internal error, never a verdict.  The
next level is constructed lazily, inside each entry point's closure
(constant work per call; an eager tower would cost `fuel` allocations
per instantiation). -/
def coreKnot {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (mode : CheckMode) (env : Env)
    (wrap : CoreFns m → CoreFns m) : Nat → CoreFns m
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate") }
  | fuel + 1 =>
    wrap
      { whnfCore := fun d e =>
          whnfCoreBody mode (coreKnot mode env wrap fuel) env d e
        whnf := fun d e => whnfBody (coreKnot mode env wrap fuel) env d e
        infer := fun d e =>
          inferBody mode (coreKnot mode env wrap fuel) env d e
        defeq := fun d a b =>
          defeqBody mode (coreKnot mode env wrap fuel) env d a b
        annotate := fun d e =>
          annotateBody mode (coreKnot mode env wrap fuel) env d e }

/-- The shared fuel for the checker core: bounds the recursion depth of
reduction, inference and definitional equality.  Exhaustion is an
internal error, never a verdict. -/
def checkFuel : Nat := 100000

end Setlec
