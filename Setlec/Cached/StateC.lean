import Setlec.Kernel.FEnv
import Setlec.Cached.ExprOpsC

/-!
# The cached-clone checker state and its operation wrappers

The `ExprC` counterpart of `IState` (`Setlec/Kernel/CoreI.lean`) and of
the monadic store-access layer above it.  Same cache set, same
lifetimes, same linear-update discipline (detach a component from the
state record before mutating it); the arena is gone, so the
"interning" wrappers become plain smart-constructor calls and the
node-view wrappers become field reads.

The environment index (`FEnv`) and every `FEnv`-based guard are
**reused verbatim** from the interned checker — they are
representation-free.  Only the store-based guards (`isCtorAppI`,
`isUnitLikeTyI`, `headHintI`, `unfoldableHeadI`, `sameConstHeadsI`,
`rawNatLitI?`) get `ExprC` twins here.

## Memo key discipline (the pilot's central decision)

Pointer identity is not available as a *key*, so the memo maps are
keyed on `ExprC` values with:

* `Hashable ExprC` = the cached hash field (`O(1)`, no traversal — the
  arena gets `O(1)` from the index instead);
* `BEq ExprC` = pointer identity, then the cached hashes, then
  structural descent.  Bucket comparisons therefore cost `O(1)` on
  the overwhelmingly common shared-subterm case (instantiation and
  abstraction return unchanged subterms *by reference*), and a hash
  mismatch rejects the rest without descending.

A hash-cons table was deliberately **not** added: it would reintroduce
the arena's central data structure, which is exactly what the pilot
exists to do without.  The `Level`-keyed and `Name`-keyed caches
(`lsimpC`, `eqvC`, `constTyAt`, …) are the one place where structural
hashing survives — see the pilot's assessment in DESIGN.md.
-/

namespace Setlec.Cached

open Setlec

/-! ## The vestigial store

The interned twins read the arena through a store value (`withStore
(fun st => st.getAppArgsI e)` &c.).  `ExprC` needs no store, but the
clone keeps the *shape* of every such call so that it mirrors its
interned original character for character — `CStore` is a unit type
whose "methods" are the corresponding `ExprC` operations, and
`withStore` is `pure`.  This is what makes the clone auditable against
`Setlec/Kernel/CoreI.lean` line by line. -/

/-- The vestigial store (a unit). -/
structure CStore where
  dummy : Unit := ()
  deriving Inhabited

namespace CStore

@[inline] def getNode (_ : CStore) (e : ExprC) : Option (ExprView ExprC) :=
  some e.view

@[inline] def getAppFnI (_ : CStore) (e : ExprC) : ExprC := ExprC.getAppFn e

@[inline] def getAppArgsI (_ : CStore) (e : ExprC) : List ExprC :=
  ExprC.getAppArgs e

@[inline] def wscopedBI (_ : CStore) (d : Nat) (e : ExprC) : Bool :=
  ExprC.wscopedB d e

@[inline] def looseBVarsBoundedI (_ : CStore) (k : Nat) (e : ExprC) : Bool :=
  ExprC.looseBVarsBounded k e

@[inline] def leafGuardI (_ : CStore) (fab base : ExprC) : Bool :=
  ExprC.leafGuard fab base

@[inline] def hasFvarI (_ : CStore) (e : ExprC) : Bool := e.hasFvar

@[inline] def stripPisBodyI (_ : CStore) (k : Nat) (e : ExprC) :
    Option ExprC := ExprC.stripPisBody k e

/-- Memo table for the zero-ness readout (structural `Level` keys). -/
abbrev PWMemo := Std.HashMap Level PropWhen

@[inline] def zeronessOfLIGo (_ : CStore) (memo : PWMemo) (u : Level) :
    PropWhen × PWMemo :=
  match memo[u]? with
  | some r => (r, memo)
  | none => let r := Level.zeronessOf u; (r, memo.insert u r)

end CStore

/-! ## Store-free guard twins -/

/-- `isUnitLikeTy` through the index, on a (whnf'd) `ExprC`. -/
def isUnitLikeTyC (fe : FEnv) (e : ExprC) : Bool :=
  match e with
  | .const cn _ .. =>
    -- task #161 item C1: the pinned-name test (see `isUnitLikeTy`)
    cn == punitName &&
    (match fe.find? punitName with
      | some (.indInfo _ _) => true
      | _ => false) &&
    (match fe.find? punitRecName with
      | some (.recInfo _ mI rP [r]) => mI == rP && r.nfields == 0
      | _ => false)
  | _ => false

/-- `isCtorApp` through the index. -/
def isCtorAppC (fe : FEnv) (e : ExprC) : Bool :=
  match ExprC.getAppFn e with
  | .const cn _ .. =>
    match fe.find? cn with
    | some (.ctorInfo _ _ _) => true
    | _ => false
  | _ => false

/-- `headHint` through the index. -/
def headHintC (fe : FEnv) (e : ExprC) : ReducibilityHint :=
  match ExprC.getAppFn e with
  | .const nm _ .. =>
    match fe.find? nm with
    | some (.defnInfo _ _ hint) => hint
    | _ => .opaque
  | _ => .opaque

/-- `unfoldableHead` through the index (the lazy-delta decision). -/
def unfoldableHeadC (fe : FEnv) (e : ExprC) : Bool :=
  match ExprC.getAppFn e with
  | .const nm us .. =>
    match fe.find? nm with
    | some (.defnInfo cv _ _) => us.length == cv.levelParams.length
    | some (.thmInfo cv _) => us.length == cv.levelParams.length
    | _ => false
  | _ => false

/-- `sameConstHeads` on `ExprC`. -/
def sameConstHeadsC (a b : ExprC) : Bool :=
  match a, b with
  | .app f₁ _ .., .app f₂ _ .. =>
    match ExprC.getAppFn f₁, ExprC.getAppFn f₂ with
    | .const n₁ _ .., .const n₂ _ .. => n₁ == n₂
    | _, _ => false
  | _, _ => false

/-- `rawNatLit?` on an `ExprC`. -/
def rawNatLitC? (e : ExprC) : Option Nat :=
  match e with
  | .lit (.natVal n) .. => some n
  | .const c [] .. => if c == natZeroName then some 0 else none
  | _ => none

/-! The store-shaped spellings the twins use (a `CStore` argument in
the interned original's position). -/

@[inline] def isUnitLikeTyI (fe : FEnv) (_ : CStore) (e : ExprC) : Bool :=
  isUnitLikeTyC fe e

@[inline] def isCtorAppI (fe : FEnv) (_ : CStore) (e : ExprC) : Bool :=
  isCtorAppC fe e

@[inline] def headHintI (fe : FEnv) (_ : CStore) (e : ExprC) :
    ReducibilityHint := headHintC fe e

@[inline] def unfoldableHeadI (fe : FEnv) (_ : CStore) (e : ExprC) : Bool :=
  unfoldableHeadC fe e

@[inline] def sameConstHeadsI (_ : CStore) (a b : ExprC) : Bool :=
  sameConstHeadsC a b

@[inline] def rawNatLitI? (_ : CStore) (e : ExprC) : Option Nat :=
  rawNatLitC? e

/-! ## The state -/

/-- One cached-environment entry: a stored constant's annotated type
and (for definitions/theorems/opaques) value converted to `ExprC`,
each tagged with the very `Expr` object it came from.  A use validates
the tag by pointer equality (`Expr.exprPtrBEq`, reused), so the
conversion of a stored constant is paid once per declaration instead
of once per delta step — the counterpart of `IState.ienv`. -/
structure CConstE where
  tyE : Expr
  ty : ExprC
  val : Option (Expr × ExprC) := none

/-- Per-declaration state: the converted-constant cache, the memo
caches for the five entry points, the lazy caches for
level-instantiated stored constants, the level-operation memos, and
the persistent bulk-instantiation memo (task #145).  Mirrors `IState`
field for field, minus the arena. -/
structure CState where
  ienv : Std.HashMap Name CConstE := {}
  constTyAt : Std.HashMap (Name × List Level) ExprC := {}
  constValAt : Std.HashMap (Name × List Level) ExprC := {}
  ruleRhsAt : Std.HashMap (Name × Name × List Level) ExprC := {}
  whnfCoreC : Std.HashMap ExprC ExprC := {}
  whnfC : Std.HashMap ExprC ExprC := {}
  inferC : Std.HashMap ExprC ExprC := {}
  /-- Memo of the *checking-mode* inference (`coreKnotFNC`, the
  `--no-model` cached parity lane, `Setlec/Cached/CoreNC.lean`), kept
  apart from `inferC` so a result derived in infer-only mode can never
  be served to a checking-mode query.  Unused — and always empty — on
  the certified path, which never builds `coreKnotFNC`; the
  counterpart of `IState.inferFC` (task #134/#147). -/
  inferFC : Std.HashMap ExprC ExprC := {}
  /-- **The io-grade inference memo** (task #170 / #172 B4): results of
  the certified knot's `inferIO` slot at the gated config
  (`cfg.ioGate`), kept apart from `inferC` per the task-#170 memo
  ruling — *"since caching has no access to semantic reasoning (yet)
  we need two memos, one with and one without the flag"* — because an
  io entry witnesses fewer checks than the full-infer claims consume.
  Its invariant is the io claims' weaker (premise-form) one
  (`CSOK.inferIOC`, `Verify/Cached/DiscC1.lean`).  Official's own
  layout: the C++ kernel keys its infer cache by `infer_only`.  At
  gate-off configs the slot shares `inferC` and this map stays
  empty. -/
  inferIOC : Std.HashMap ExprC ExprC := {}
  defeqC : Std.HashMap (ExprC × ExprC) Bool := {}
  annotC : Std.HashMap ExprC ExprC := {}
  lsimpC : Std.HashMap Level Level := {}
  lnzC : Std.HashMap Level Bool := {}
  eqvC : Std.HashMap (Level × Level) Bool := {}
  instC : Std.HashMap (ExprC × List ExprC × Nat) ExprC := {}

instance : Inhabited CState := ⟨{}⟩

/-- Entry bound for the persistent bulk-instantiation memo (the
interned checker's `instCCap`, reused unchanged). -/
def instCCapC : Nat := 32000000

/-- The cached-clone checker monad. -/
abbrev CheckCM := StateT CState CheckM

/-! ## Node access (pure; kept monadic so the clone mirrors the
interned twins call for call) -/

/-- Read a node's one-level view. -/
@[inline] def viewI (e : ExprC) : CheckCM (Option (ExprView ExprC)) :=
  pure (some e.view)

/-- Build one node. -/
@[inline] def internI (n : ExprView ExprC) : CheckCM ExprC :=
  pure (ExprC.ofView n)

/-- Convert a whole `Expr` (fabricated terms, stored instantiations).
The identity since task #172 B3a — one type — kept under the interned
twin's name so the two read the same. -/
@[inline] def internExprM (x : Expr) : CheckCM ExprC :=
  pure x

/-- Run a store query (the store is a unit here). -/
@[inline] def withStore {α : Type} (f : CStore → α) : CheckCM α :=
  pure (f default)

/-! Names and levels are plain trees in the clone, so the interned
checker's name/level interning and readback wrappers are identities —
kept under their original names so the twins read the same. -/

@[inline] def internNameM (n : Name) : CheckCM Name := pure n

@[inline] def readbackNM (n : Name) : CheckCM Name := pure n

@[inline] def beqNameM (i : Name) (nm : Name) : CheckCM Bool := pure (i == nm)

@[inline] def projFnIdxM (T : Name) (i : Nat) : CheckCM Name :=
  pure (projFnName T i)

@[inline] def internLM (u : Level) : CheckCM Level := pure u

@[inline] def viewLM (u : Level) : CheckCM (Option Level) := pure (some u)

@[inline] def readbackLevelM (u : Level) : CheckCM Level := pure u

@[inline] def readbackLevelsM (us : List Level) : CheckCM (List Level) :=
  pure us

/-- Peel fuel of the binder-telescope loops.  The interned loops use
the arena's node count (an upper bound on any binder chain in a
canonical arena); there is no such count here, so a constant beyond
any real chain serves — the fuel is *semantically transparent*: on
exhaustion the leaf phase hands the residual chain back to the knot,
which is exactly the chained specification's next step. -/
def peelFuel : Nat := 16777216

@[inline] def peelFuelM : CheckCM Nat := pure peelFuel

/-- The per-node loose-bvar bound — an `O(1)` field read. -/
@[inline] def bvarBoundM (e : ExprC) : CheckCM Nat := pure e.bvarB

/-! ## Syntactic operations (the `*M` wrappers) -/

/-- `Expr.instantiate1`; the identity — the same node, by reference —
when the target has no loose bvar at or above the cursor. -/
@[inline] def inst1M (e v : ExprC) (d : Nat := 0) : CheckCM ExprC :=
  pure (ExprC.instantiate1 e v d)

/-- Bulk instantiation with the persistent result memo (task #145),
keyed by the whole argument tuple exactly as `IState.instC`. -/
def instListM (e : ExprC) (vs : List ExprC) (d : Nat := 0) : CheckCM ExprC :=
  modifyGet fun s =>
    if e.bvarB ≤ d then (e, s)
    else
      match s.instC[(e, vs, d)]? with
      | some r => (r, s)
      | none =>
        let mp := s.instC
        let s := { s with instC := {} }
        let mp := if mp.size < instCCapC then mp else {}
        let r := ExprC.instantiateList e vs d
        (r, { s with instC := mp.insert (e, vs, d) r })

/-- Bulk instantiation on a reversed accumulator array (deliberately
not memoized, as in the interned checker). -/
@[inline] def instListRevM (e : ExprC) (vs : Array ExprC) (d : Nat := 0) :
    CheckCM ExprC :=
  pure (ExprC.instantiateRev e vs d)

@[inline] def abstract1M (e : ExprC) (d : Nat) : CheckCM ExprC :=
  pure (ExprC.abstract1 e d)

@[inline] def abstractRangeM (e : ExprC) (d k : Nat) : CheckCM ExprC :=
  pure (ExprC.abstractRange e d k)

@[inline] def mkAppNM (f : ExprC) (args : List ExprC) : CheckCM ExprC :=
  pure (ExprC.mkAppN f args)

@[inline] def instSpineM (args : List ExprC) (t : Nat) (e : ExprC) :
    CheckCM ExprC :=
  pure (ExprC.instSpine args t e)

@[inline] def piResidualM (e : ExprC) (args : List ExprC) :
    CheckCM (Option ExprC) :=
  pure (ExprC.piResidual e args)

@[inline] def pisToLamsM (k : Nat) (e body : ExprC) :
    CheckCM (Option ExprC) :=
  pure (ExprC.pisToLams k e body)

@[inline] def instLevelParamsM (ks : List Name) (us : List Level)
    (e : ExprC) : CheckCM ExprC :=
  pure (ExprC.instLevelParams ks us e)

/-! ## Level operations

Levels are plain trees here (there is no level arena), so the level
memos are keyed structurally — the one place the clone pays a
non-`O(1)` hash.  The *results* are cached exactly as in the interned
checker (`lsimpC`, `lnzC`, `eqvC`), so a decided comparison is never
recomputed. -/

@[inline] def substLM (ks : List Name) (us : List Level) (u : Level) :
    CheckCM Level :=
  pure (Level.subst ks us u)

@[inline] def substLevelTreeM (ks : List Name) (us : List Level)
    (l : Level) : CheckCM Level :=
  pure (Level.subst ks us l)

@[inline] def substLevelTreesM (ks : List Name) (us : List Level)
    (ls : List Level) : CheckCM (List Level) :=
  pure (ls.map (Level.subst ks us))

/-- `Level.simplify`, persistently memoized. -/
def simplifyLM (u : Level) : CheckCM Level :=
  modifyGet fun s =>
    match s.lsimpC[u]? with
    | some r => (r, s)
    | none =>
      let mp := s.lsimpC
      let s := { s with lsimpC := {} }
      let r := Level.simplify u
      (r, { s with lsimpC := mp.insert u r })

/-- `Level.isNonZero`, persistently memoized. -/
def isNonZeroLM (u : Level) : CheckCM Bool :=
  modifyGet fun s =>
    match s.lnzC[u]? with
    | some r => (r, s)
    | none =>
      let mp := s.lnzC
      let s := { s with lnzC := {} }
      let r := Level.isNonZero u
      (r, { s with lnzC := mp.insert u r })

/-- Level equivalence with a persistent result cache (the interned
`isEquivLM`, same shape: simplify both sides, compare, then the
`leqCore` cascade both ways). -/
def isEquivLM (l r : Level) : CheckCM (Option Bool) :=
  modifyGet fun s =>
    match s.eqvC[(l, r)]? with
    | some b => (some b, s)
    | none =>
      let mp := s.lsimpC
      let ec := s.eqvC
      let s := { s with lsimpC := {}, eqvC := {} }
      let (ls, mp) :=
        match mp[l]? with
        | some x => (x, mp)
        | none => let x := Level.simplify l; (x, mp.insert l x)
      let (rs, mp) :=
        match mp[r]? with
        | some x => (x, mp)
        | none => let x := Level.simplify r; (x, mp.insert r x)
      if ls == rs then
        (some true, { s with lsimpC := mp, eqvC := ec.insert (l, r) true })
      else
        match Level.leqCore Level.defaultFuel ls rs 0 with
        | some false =>
          (some false, { s with lsimpC := mp, eqvC := ec.insert (l, r) false })
        | some true =>
          match Level.leqCore Level.defaultFuel rs ls 0 with
          | some b =>
            (some b, { s with lsimpC := mp, eqvC := ec.insert (l, r) b })
          | none => (none, { s with lsimpC := mp, eqvC := ec })
        | none => (none, { s with lsimpC := mp, eqvC := ec })

/-- Pointwise `isEquivLM`. -/
def isEquivListLM : List Level → List Level → CheckCM (Option Bool)
  | [], [] => pure (some true)
  | l :: ls, r :: rs => do
    match ← isEquivLM l r with
    | none => pure none
    | some false => pure (some false)
    | some true => isEquivListLM ls rs
  | _, _ => pure (some false)

/-- The zero-ness datum of a level (task #161). -/
@[inline] def zeronessOfM (u : Level) : CheckCM PropWhen :=
  pure (Level.zeronessOf u)

/-! ## Lazy stored-constant conversions -/

/-- The `ExprC` of a stored constant's type: the cached entry when its
`Expr` tag validates by pointer equality, else a fresh conversion. -/
def storedTyIdxM (n : Name) (ty : Expr) : CheckCM ExprC := do
  let ent? : Option CConstE ← modifyGet fun s => (s.ienv[n]?, s)
  match ent? with
  | some ent =>
    if Expr.exprPtrBEq ent.tyE ty then pure ent.ty
    else internExprM ty
  | none => internExprM ty

/-- The `ExprC` of a stored definition/theorem value (see
`storedTyIdxM`). -/
def storedValIdxM (n : Name) (v : Expr) : CheckCM ExprC := do
  let ent? : Option CConstE ← modifyGet fun s => (s.ienv[n]?, s)
  match ent? with
  | some ⟨_, _, some (vE, vi)⟩ =>
    if Expr.exprPtrBEq vE v then pure vi
    else internExprM v
  | _ => internExprM v

/-- The level-instantiated *type* of the stored constant `n`. -/
def constTyAtM (fe : FEnv) (_nI : Name) (n : Name) (us : List Level) :
    CheckCM ExprC := do
  let hit? ← modifyGet fun s => (s.constTyAt[(n, us)]?, s)
  match hit? with
  | some i => pure i
  | none =>
    match fe.find? n with
    | some ci =>
      let cv := ci.toConstantVal
      let raw ← storedTyIdxM n cv.type
      let i ← instLevelParamsM cv.levelParams us raw
      modify fun s =>
        let mp := s.constTyAt
        let s := { s with constTyAt := ∅ }
        { s with constTyAt := mp.insert (n, us) i }
      pure i
    | none => throw (.internal "constTyAtM: unknown constant")

/-- The level-instantiated *value* of the stored definition `n`. -/
def constValAtM (fe : FEnv) (_nI : Name) (n : Name) (us : List Level) :
    CheckCM ExprC := do
  let hit? ← modifyGet fun s => (s.constValAt[(n, us)]?, s)
  match hit? with
  | some i => pure i
  | none =>
    match fe.find? n with
    | some (.defnInfo cv v _) =>
      let raw ← storedValIdxM n v
      let i ← instLevelParamsM cv.levelParams us raw
      modify fun s =>
        let mp := s.constValAt
        let s := { s with constValAt := ∅ }
        { s with constValAt := mp.insert (n, us) i }
      pure i
    | some (.thmInfo cv v) =>
      let raw ← storedValIdxM n v
      let i ← instLevelParamsM cv.levelParams us raw
      modify fun s =>
        let mp := s.constValAt
        let s := { s with constValAt := ∅ }
        { s with constValAt := mp.insert (n, us) i }
      pure i
    | _ => throw (.internal "constValAtM: not a stored definition")

/-- The level-instantiated right-hand side of the rule for constructor
`j` of the stored recursor `c`. -/
def ruleRhsAtM (fe : FEnv) (_cI _jI : Name) (c j : Name) (us : List Level) :
    CheckCM ExprC := do
  let hit? ← modifyGet fun s => (s.ruleRhsAt[(c, j, us)]?, s)
  match hit? with
  | some i => pure i
  | none =>
    match fe.find? c with
    | some (.recInfo cv _ _ rules) =>
      match rules.find? (fun r' => r'.ctor == j) with
      | some rl =>
        let raw ← internExprM rl.rhs
        let i ← instLevelParamsM cv.levelParams us raw
        modify fun s =>
          let mp := s.ruleRhsAt
          let s := { s with ruleRhsAt := ∅ }
          { s with ruleRhsAt := mp.insert (c, j, us) i }
        pure i
      | none => throw (.internal "ruleRhsAtM: no rule for constructor")
    | _ => throw (.internal "ruleRhsAtM: not a stored recursor")

/-- Drop the environment-dependent caches (an environment transition).
The environment-independent components — the converted-constant cache
`ienv` (self-certified by its `Expr` tags) and the level-operation
memos — survive, exactly as in `IState.flushed`. -/
def CState.flushed (s : CState) : CState :=
  { s with
      constTyAt := {}, constValAt := {}, ruleRhsAt := {},
      whnfCoreC := {}, whnfC := {}, inferC := {}, inferIOC := {},
      defeqC := {}, annotC := {}, instC := {} }

def flushC : CheckCM Unit := modify (·.flushed)


/-! ## The parsed-index driver's syntactic guards

`Expr.constsResolveF` as a memoized `ExprC` DAG walk (the counterpart
of `constsResolveFIGo`): the tree-walking `Expr` version is what makes
the `Expr`-typed driver quadratic — or worse — on shared declarations. -/

/-- Core of `constsResolveFC` (memo per call: the result depends on the
environment). -/
def constsResolveFCGo (fe : FEnv) (memo : Std.HashMap ExprC Bool)
    (e : ExprC) : Bool × Std.HashMap ExprC Bool :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap ExprC Bool :=
      match e with
      | .bvar .. | .sort .. => (true, memo)
      | .lit (.natVal _) .. =>
        ((fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
          (fe.find? natSuccName).isSome, memo)
      | .lit (.strVal _) .. =>
        ((fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
          (fe.find? natSuccName).isSome && (fe.find? stringName).isSome &&
          (fe.find? stringOfListName).isSome &&
          (fe.find? listName).isSome && (fe.find? listNilName).isSome &&
          (fe.find? listConsName).isSome && (fe.find? charName).isSome &&
          (fe.find? charOfNatName).isSome, memo)
      | .const nm _ .. => ((fe.find? nm).isSome, memo)
      | .fvar _ _ ty .. => constsResolveFCGo fe memo ty
      | .app f a .. =>
        let (rf, memo) := constsResolveFCGo fe memo f
        if rf then constsResolveFCGo fe memo a else (false, memo)
      | .lam _ ty body _ .. | .forallE _ ty body _ .. =>
        let (rt, memo) := constsResolveFCGo fe memo ty
        if rt then constsResolveFCGo fe memo body else (false, memo)
      | .letE _ ty val body .. =>
        let (rt, memo) := constsResolveFCGo fe memo ty
        if rt then
          let (rv, memo) := constsResolveFCGo fe memo val
          if rv then constsResolveFCGo fe memo body else (false, memo)
        else (false, memo)
      | .proj sn _ sub .. =>
        if (fe.find? sn).isSome then constsResolveFCGo fe memo sub
        else (false, memo)
    (r, memo.insert e r)

/-- `Expr.constsResolveF fe` on `ExprC` (one memoized DAG walk). -/
def constsResolveFC (fe : FEnv) (e : ExprC) : Bool :=
  (constsResolveFCGo fe {} e).1

@[inline] def CStore.constsResolveFI (_ : CStore) (fe : FEnv) (e : ExprC) :
    Bool := constsResolveFC fe e

@[inline] def CStore.allLevelParamsDefinedI (_ : CStore) (ps : List Name)
    (e : ExprC) : Bool := ExprC.allLevelParamsDefined ps e

/-- Record an accepted constant's converted type/value, tagged with the
very `Expr` objects pushed into the environment (the counterpart of
`recordIConst`). -/
def recordCConst (n : Name) (tyE : Expr) (ty : ExprC)
    (val : Option (Expr × ExprC)) : CheckCM Unit :=
  modify fun s =>
    let m := s.ienv
    let s := { s with ienv := {} }
    { s with ienv := m.insert n ⟨tyE, ty, val⟩ }

end Setlec.Cached
