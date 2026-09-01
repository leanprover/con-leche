import Setlec.Kernel.Core
import Setlec.Kernel.IExpr

/-!
# The interned checker core (task #26)

Hand-written interned twins of the core bodies (`Setlec/Kernel/Core.lean`),
operating on arena indices (`EIdx` into an `EStore`, `Setlec/Kernel/
IExpr.lean`) instead of `Expr` trees.  Equality of interned terms is index
comparison, memo keys are indices (`O(1)` hash/compare), and the syntactic
operations are DAG-memoized — nanoda's expression-pointer design.

The state (`IState`) carries the arena, the id-keyed memo caches for the
five entry points, and lazy interning caches for level-instantiated stored
constants; its lifetime is one top-level entry-point call (exactly the
lifetime of the Expr-level `KCache`, and of nanoda's per-`TypeChecker`
temporary dag), so the environment is fixed while any cache lives.

Environment lookups go through `FEnv`: the spec environment plus a name
index built once per entry call by folding the constant list from the back
(newest insert wins), so the index's lookup function *is* `Env.find?`
(`Setlec/Verify/IExprOps.lean`, `mkFEnv_find?`).

Every twin mirrors its `Core.lean` original clause by clause — same order
of record calls, same short-circuits; the only extra effects are node
views, interning, and the caches.  Faithfulness (a successful interned run
is reproduced by the pure fueled knot under the denotation) is proven in
`Setlec/Verify/SimI.lean` / `Setlec/Verify/DiscI*.lean`.

Linearity: every mutation of a state component detaches the component from
the state record before updating (`let mp := s.f; let s := { s with f := ∅ };
… mp.insert …`), so the backing stores are uniquely referenced at each
update — the `memoE` discipline of `Setlec/Kernel/TypeCheckerC.lean`.
-/

namespace Setlec

/-! ## The indexed environment -/

/-- The spec environment together with a name index whose lookup function
agrees with `Env.find?` (built once per top-level entry call).

Every index entry carries its **installation counter** — the number of
constants installed before it, i.e. its position counted from the bottom
of `env.consts` — and the environment carries a **visibility bound**,
`visibleBelow`: `find?` returns `none` for an entry whose counter is at
or above the bound, so a single `FEnv` value answers lookups against any
*prefix* of itself at `O(1)` (task #108; a field comparison on the entry
— never a filtered copy or a second environment value).  `visibleBelow`
doubles as the next counter to hand out, so on the ordinary
install-and-check path it is exactly `env.consts.length` and nothing is
ever hidden (`mkFEnv_find?`); lowering it to `k` is the prefix view of
the first `k` installed constants (`mkFEnv_find?_visibleBelow`,
`Setlec/Verify/EnvBound.lean`). -/
structure FEnv where
  env : Env
  idx : Std.HashMap Name (Nat × ConstantInfo)
  /-- Entries with counter `< visibleBelow` are visible; also the next
  counter `push` hands out. -/
  visibleBelow : Nat

/-- The index build, from the back: the newest (front) constant is
inserted last and wins, exactly as `List.find?` takes the first match —
so the agreement with `Env.find?` is unconditional (no freshness
assumption).  The `Nat` component is the running counter, so the build
stays linear (the tail's length is returned, not recomputed). -/
def mkFEnvGo : List ConstantInfo → Nat × Std.HashMap Name (Nat × ConstantInfo)
  | [] => (0, ∅)
  | ci :: cs =>
    let p := mkFEnvGo cs
    (p.1 + 1, p.2.insert ci.name (p.1, ci))

/-- Build the index of `env`, with nothing hidden (`visibleBelow` is the
constant count). -/
def mkFEnv (env : Env) : FEnv :=
  let p := mkFEnvGo env.consts
  ⟨env, p.2, p.1⟩

namespace FEnv

/-- Indexed lookup, bounded by the visibility counter (`= Env.find?` for
`mkFEnv`, which hides nothing). -/
def find? (fe : FEnv) (n : Name) : Option ConstantInfo :=
  match fe.idx[n]? with
  | some (c, ci) => if c < fe.visibleBelow then some ci else none
  | none => none

/-- Restrict the view to the first `k` installed constants (task #108).
`O(1)`: a field update on the single linearly-threaded index. -/
def restrictTo (fe : FEnv) (k : Nat) : FEnv :=
  { fe with visibleBelow := k }

/-- The index of the cons-extended environment (`mkFEnv_push`:
`FEnv.push (mkFEnv env) ci = mkFEnv ⟨ci :: env.consts⟩`, definitionally).
The new entry gets the next installation counter, and the visibility
bound advances with it — so a push is visible to everything checked
after it and to nothing checked before (task #108). -/
def push (fe : FEnv) (ci : ConstantInfo) : FEnv :=
  ⟨⟨ci :: fe.env.consts⟩, fe.idx.insert ci.name (fe.visibleBelow, ci),
   fe.visibleBelow + 1⟩

/-- Indexed projection-table lookup (`= Env.findProj?` for `mkFEnv`). -/
def findProj? (fe : FEnv) (T : Name) (i : Nat) : Option ProjEntry :=
  match fe.find? (projFnName T i) with
  | some (.projInfo e) => some e
  | _ => none

end FEnv

/-! ### Indexed guard twins (same result as the `Env` versions) -/

/-- `natLitSupported` through the index. -/
def natLitSupportedF (fe : FEnv) : Bool :=
  natIndOk (fe.find? natName) && natZeroOk (fe.find? natZeroName) &&
    natSuccOk (fe.find? natSuccName)

/-- `strLitSupported` through the index. -/
def strLitSupportedF (fe : FEnv) : Bool :=
  natLitSupportedF fe &&
    stringTyOk (fe.find? stringName) &&
    stringOfListTyOk (fe.find? stringOfListName) &&
    listTyOk (fe.find? listName) &&
    listNilTyOk (fe.find? listNilName) &&
    listConsTyOk (fe.find? listConsName) &&
    charTyOk (fe.find? charName) &&
    charOfNatTyOk (fe.find? charOfNatName)

/-- `natOpGuard` through the index. -/
def natOpGuardF (fe : FEnv) (c : Name) : Bool :=
  natLitSupportedF fe &&
  (natOpDeps c).all (fun n => match fe.find? n with
    | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
    | _ => false) &&
  (if c = natBeqName || c = natBleName || natDivModNames.contains c then
    (match fe.find? boolTrueName with
      | some ci => ci.toConstantVal.levelParams.isEmpty
      | none => false) &&
    (match fe.find? boolFalseName with
      | some ci => ci.toConstantVal.levelParams.isEmpty
      | none => false)
   else true)

/-- `isUnitLikeTy` through the index, on an interned (whnf'd) type. -/
def isUnitLikeTyI (fe : FEnv) (st : EStore) (e : EIdx) : Bool :=
  match st.getNode e with
  | some (.const c _) =>
    match st.readbackN c with
    | some cn =>
      (match fe.find? cn with
        | some (.indInfo _ _) => true
        | _ => false) &&
      (match fe.find? (cn.str "rec") with
        | some (.recInfo _ mI rP [r]) => mI == rP && r.nfields == 0
        | _ => false) &&
      reservedBasisNames.contains (cn.str "rec")
    | none => false
  | _ => false

/-- `isCtorApp` through the index. -/
def isCtorAppI (fe : FEnv) (st : EStore) (e : EIdx) : Bool :=
  match st.getNode (st.getAppFnI e) with
  | some (.const c _) =>
    match st.readbackN c with
    | some cn =>
      match fe.find? cn with
      | some (.ctorInfo _ _ _) => true
      | _ => false
    | none => false
  | _ => false

/-- `headHint` through the index. -/
def headHintI (fe : FEnv) (st : EStore) (e : EIdx) : ReducibilityHint :=
  match st.getNode (st.getAppFnI e) with
  | some (.const n _) =>
    match st.readbackN n with
    | some nm =>
      match fe.find? nm with
      | some (.defnInfo _ _ hint) => hint
      | _ => .opaque
    | none => .opaque
  | _ => .opaque

/-- `unfoldableHead` through the index: the lazy delta *decision*
(a pure store read), taken before any unfolding is materialized. -/
def unfoldableHeadI (fe : FEnv) (st : EStore) (e : EIdx) : Bool :=
  match st.getNode (st.getAppFnI e) with
  | some (.const n us) =>
    match st.readbackN n with
    | some nm =>
      match fe.find? nm with
      | some (.defnInfo cv _ _) => us.length == cv.levelParams.length
      | some (.thmInfo cv _) => us.length == cv.levelParams.length
      | _ => false
    | none => false
  | _ => false

/-- `sameConstHeads` on indices. -/
def sameConstHeadsI (st : EStore) (a b : EIdx) : Bool :=
  match st.getNode a, st.getNode b with
  | some (.app f₁ _), some (.app f₂ _) =>
    match st.getNode (st.getAppFnI f₁), st.getNode (st.getAppFnI f₂) with
    | some (.const n₁ _), some (.const n₂ _) => n₁ == n₂
    | _, _ => false
  | _, _ => false

/-- `rawNatLit?` on an index. -/
def rawNatLitI? (st : EStore) (e : EIdx) : Option Nat :=
  match st.getNode e with
  | some (.lit (.natVal n)) => some n
  | some (.const c []) => if st.beqNameI c natZeroName then some 0 else none
  | _ => none

/-- Interned counterpart of `Expr.constsResolveF` (`CheckerS`; same
clauses as `EStore.constsResolveIGo` with the lookups through the
index).  Memo per call: the result depends on the environment. -/
def constsResolveFIGo (st : EStore) (fe : FEnv)
    (memo : Std.HashMap EIdx Bool) (e : EIdx) : Bool × Std.HashMap EIdx Bool :=
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    match st.getNode e with
    | none => (false, memo)
    | some n =>
      let (r, memo) : Bool × Std.HashMap EIdx Bool :=
        match n with
        | .bvar _ | .sort _ => (true, memo)
        | .lit (.natVal _) =>
          ((fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
            (fe.find? natSuccName).isSome, memo)
        | .lit (.strVal _) =>
          ((fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
            (fe.find? natSuccName).isSome && (fe.find? stringName).isSome &&
            (fe.find? stringOfListName).isSome &&
            (fe.find? listName).isSome && (fe.find? listNilName).isSome &&
            (fe.find? listConsName).isSome && (fe.find? charName).isSome &&
            (fe.find? charOfNatName).isSome, memo)
        | .const n _ =>
          (match st.readbackN n with
           | some nm => (fe.find? nm).isSome
           | none => false, memo)
        | .fvar _ _ ty =>
          if _h : emlt ty e then constsResolveFIGo st fe memo ty
          else (false, memo)
        | .app f a =>
          if _h : emlt f e ∧ emlt a e then
            let (rf, memo) := constsResolveFIGo st fe memo f
            if rf then constsResolveFIGo st fe memo a else (false, memo)
          else (false, memo)
        | .lam _ ty body _ | .forallE _ ty body _ =>
          if _h : emlt ty e ∧ emlt body e then
            let (rt, memo) := constsResolveFIGo st fe memo ty
            if rt then constsResolveFIGo st fe memo body else (false, memo)
          else (false, memo)
        | .letE _ ty val body =>
          if _h : emlt ty e ∧ emlt val e ∧ emlt body e then
            let (rt, memo) := constsResolveFIGo st fe memo ty
            if rt then
              let (rv, memo) := constsResolveFIGo st fe memo val
              if rv then constsResolveFIGo st fe memo body else (false, memo)
            else (false, memo)
          else (false, memo)
        | .proj s _ sub =>
          if _h : emlt sub e then
            match st.readbackN s with
            | some sn =>
              if (fe.find? sn).isSome then constsResolveFIGo st fe memo sub
              else (false, memo)
            | none => (false, memo)
          else (false, memo)
      (r, memo.insert e r)
termination_by (etier e, epos e)
decreasing_by all_goals first | exact emlt_lex _h.1 | exact emlt_lex _h.2.1 | exact emlt_lex _h.2.2 | exact emlt_lex _h.2 | exact emlt_lex _h

/-- Interned `Expr.constsResolveF fe` (one memoized DAG walk). -/
def constsResolveFI (st : EStore) (fe : FEnv) (e : EIdx) : Bool :=
  (constsResolveFIGo st fe {} e).1

/-! ## The interned checker state and monad -/

/-- One interned-environment entry: the arena indices of a stored
constant's annotated type and (for definitions/theorems/opaques) value,
each *tagged with its own denotation* — the very `Expr` objects stored
in the environment.  The tags make the cache self-certifying: a use
first validates the tag against the current stored constant
(`exprPtrBEq` — the entry was created from the stored object itself, so
the pointer test succeeds without walking), so the invariant on the
cache ties indices to tags only and never mentions the environment
(it survives every flush and every environment transition). -/
structure IConstE where
  tyE : Expr
  ty : EIdx
  /-- value tag and index (definitions/theorems/opaques) -/
  val : Option (Expr × EIdx) := none

/-- Per-entry-call state: the arena, id-keyed memo caches for the five
entry points, lazy caches for level-instantiated stored constants
(type / definition value / recursor-rule right-hand side), keyed by name
and level-index instantiation, and the level-operation memo tables
(task #62: `lsimpC` for `simplifyLM`, `lnzC` for `isNonZeroLM`, `eqvC`
for `isEquivLM` — all environment-independent, keyed by level indices
alone: on a canonical arena a level index determines its denotation). -/
structure IState where
  store : EStore := .empty
  /-- The interned environment (task #78): per accepted constant, the
  arena indices of its stored annotated type/value, self-certified by
  denotation tags (`IConstE`).  Persists across declarations and every
  flush — the invariant never mentions the environment. -/
  ienv : Std.HashMap Name IConstE := {}
  constTyAt : Std.HashMap (NIdx × List LIdx) EIdx := {}
  constValAt : Std.HashMap (NIdx × List LIdx) EIdx := {}
  ruleRhsAt : Std.HashMap (NIdx × NIdx × List LIdx) EIdx := {}
  whnfCoreC : Std.HashMap EIdx EIdx := {}
  whnfC : Std.HashMap EIdx EIdx := {}
  inferC : Std.HashMap EIdx EIdx := {}
  /-- Memo of the *checking-mode* inference (`coreKnotF`, task #134),
  kept apart from `inferC` so a result derived in infer-only mode can
  never be served to a checking-mode query.  Unused — and always
  empty — on the default (fully certified) path, which never builds
  `coreKnotF`; see `Setlec/Kernel/CoreIO.lean`. -/
  inferFC : Std.HashMap EIdx EIdx := {}
  defeqC : Std.HashMap (EIdx × EIdx) Bool := {}
  annotC : Std.HashMap EIdx EIdx := {}
  lsimpC : EStore.LMemo := {}
  lnzC : Std.HashMap LIdx Bool := {}
  eqvC : Std.HashMap (LIdx × LIdx) Bool := {}
  /-- Persistent memo of bulk instantiation at the `instListM` sites
  (task #145), keyed by the *whole argument tuple* of the pure
  operation — target index, value-index list, cursor — so the entry is
  a fact about `instantiateListI` alone and mentions no ambient
  binder depth (the `#31` depth-free discipline; at every call site
  the cursor is the default `0`).  Bounded by `instCCap` and flushed
  with the entry-point memos. -/
  instC : Std.HashMap (EIdx × List EIdx × Nat) EIdx := {}

instance : Inhabited IState := ⟨{}⟩

/-- Entry bound for the persistent bulk-instantiation memo `instC`
(task #145).  The memo is unbounded in principle — it accumulates one
entry per distinct `(target, values, cursor)` triple until the next
flush — and its space cost is real: the `Std.Time` cone probe paid
+26.6 % peak RSS for −6.0 % instructions.  Flushes come at environment
transitions, so a *single* declaration is the only shape that can grow
it without bound; this cap is the guard against that shape and nothing
else.

Measured peaks (certified lane): `init-prelude` **8 934** entries, a
40 % Mathlib prefix **115 802**, and the `Std.Time` cone — a
stress stream that needs twice the shipped `checkFuel` to finish at
all — **18 318 022**, all of the last in one flush epoch, for 13.6 GB
peak RSS.  The cap is set above that worst case on purpose: the
measured configuration must be the one that ships, so the guard binds
only *past* the most pathological stream on record.  At roughly 170
bytes an entry it bounds the memo's own footprint at some 5 GB.

On overflow the table is dropped whole — a fresh memo, no eviction
policy: past this size the run is already pathological and the only
property worth keeping is the bound. -/
def instCCap : Nat := 32000000

/-- The interned checker monad. -/
abbrev CheckIM := StateT IState CheckM

/-! ### Store access (linear discipline: detach before update) -/

/-- Read a node (no store change). -/
@[inline] def viewI (e : EIdx) : CheckIM (Option ENode) :=
  (fun s => s.store.getNode e) <$> get

/-- Run a read-only store query.

`@[noinline]` is load-bearing: inlined, this is the pure application
`f s.store`, and the compiler *sinks* such applications past later
calls when the result is not used until after them (e.g. computing
`getAppArgsI` only after an `r.infer` that could throw).  The sunk
form keeps the projected `EStore` alive — at RC 2 — across the whole
nested call, so every arena mutation inside copies the shared tables
(whole-arena copy-on-write strikes, ~35 % of the init-prelude probe
before this attribute).  As an opaque call that threads the state,
it cannot be reordered, and the projection lives and dies inside. -/
@[noinline] def withStore {α : Type} (f : EStore → α) : CheckIM α :=
  (fun s => f s.store) <$> get

/-- Intern one node. -/
def internI (n : ENode) : CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (i, store) := store.intern n
    (i, { s with store := store })

/-- Intern a whole `Expr` (used for small fabricated terms and for
stored-constant instantiations entering the arena). -/
def internExprM (x : Expr) : CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (i, store) := store.internExpr x
    (i, { s with store := store })

/-- Intern one name node (task #88). -/
def internNM (n : NNode) : CheckIM NIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (i, store) := store.internN n
    (i, { s with store := store })

/-- Intern a whole `Name` (task #88). -/
def internNameM (n : Name) : CheckIM NIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (i, store) := store.internName n
    (i, { s with store := store })

/-- Read an interned name back as a `Name` tree (an internal error when
the index is dangling — never on validated stores). -/
def readbackNM (i : NIdx) : CheckIM Name := do
  match ← withStore (·.readbackN i) with
  | some n => pure n
  | none => throw (.internal "interned name readback failed")

/-- Alloc-free fixed-name test through the store (task #88). -/
@[inline] def beqNameM (i : NIdx) (nm : Name) : CheckIM Bool :=
  withStore (fun st => st.beqNameI i nm)

/-- The interned `projFnName T i` (`(T.proj).i` as name nodes;
task #88). -/
def projFnIdxM (T : NIdx) (i : Nat) : CheckIM NIdx := do
  let p ← internNM (.str T "proj")
  internNM (.num p i)

/-- The per-node loose-bvar bound — an `O(1)` read of the eager
derived-field array (tasks #72/#87). -/
def bvarBoundM (e : EIdx) : CheckIM Nat :=
  withStore (fun st => st.bvarBoundD e)

/-- Memoized interned `Expr.instantiate1`; the identity — same index —
when the target has no loose bvar at or above the cursor (task #72's
scope shortcut, an `O(1)` eager-array read since task #87; on a
canonical arena the traversal would rebuild the same index node by
node). -/
def inst1M (e v : EIdx) (d : Nat := 0) : CheckIM EIdx :=
  modifyGet fun s =>
    if s.store.bvarBoundD e ≤ d then (e, s)
    else
      let store := s.store
      let s := { s with store := EStore.empty }
      let (r', store) := store.instantiate1I e v d
      (r', { s with store := store })

/-- Memoized interned `Expr.instantiateList` (bulk instantiation,
task #50); identity shortcut as in `inst1M` (task #72).

Task #145: beyond the shortcut and the per-call node memo inside
`instantiateListI`, the *result* is memoized across calls in
`IState.instC`.  The eight `instListM` sites are the recursor-argument
certificate walk (`iotaCertsIAux`) and the two β-peels, which re-enter
the same `(binder telescope, argument prefix)` pair once per argument;
persisting the result collapses that quadratic re-instantiation
(−6.0 % instructions on the `Std.Time` cone, −19.6 % on a 40 %
Mathlib prefix, both certified).  The sibling `instListRevM` is
deliberately *not* memoized: it serves the binder loops and the
application spines, which are faithful to the reference kernels'
`instantiateRev` discipline and were measured to lose on one lane
while costing a further +26 % RSS. -/
def instListM (e : EIdx) (vs : List EIdx) (d : Nat := 0) :
    CheckIM EIdx :=
  modifyGet fun s =>
    if s.store.bvarBoundD e ≤ d then (e, s)
    else
      match s.instC[(e, vs, d)]? with
      | some r => (r, s)
      | none =>
        -- linear discipline (task #64): detach arena *and* memo before
        -- the update, so neither is shared while `instantiateListI`
        -- mutates the arena
        let store := s.store
        let mp := s.instC
        let s := { s with store := EStore.empty, instC := {} }
        let mp := if mp.size < instCCap then mp else {}
        let (r', store) := store.instantiateListI e vs d
        (r', { s with store := store, instC := mp.insert (e, vs, d) r' })

/-- Memoized interned bulk instantiation on a reversed accumulator
array — innermost binder **last**, the binder loops' push order
(lean4lean's `instantiateRev` discipline, task #97); identity shortcut
as in `instListM`.  Task #145 unpicked the former definitional
identity with `instListM e vs.toList.reverse d`: this sibling is *not*
memoized (measured: no win here, and a further +26 % peak RSS), so the
identification survives only as the shared spec —
`instantiateRevI_eq` — and `instListRevM_eff`
(`Setlec/Verify/SimI.lean`) repeats the raw proof. -/
def instListRevM (e : EIdx) (vs : Array EIdx) (d : Nat := 0) :
    CheckIM EIdx :=
  modifyGet fun s =>
    if s.store.bvarBoundD e ≤ d then (e, s)
    else
      let store := s.store
      let s := { s with store := EStore.empty }
      let (r', store) := store.instantiateRevI e vs d
      (r', { s with store := store })

/-- Memoized interned `Expr.abstract1`. -/
def abstract1M (e : EIdx) (d : Nat) : CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.abstract1I e d
    (r, { s with store := store })

/-- Memoized interned `Expr.abstractRange` (bulk abstraction,
task #72); the identity — same index — when the target has no fvar at
or above the range base (task #86's fvar-range shortcut, an `O(1)`
eager-array read since task #87, mirroring `inst1M`). -/
def abstractRangeM (e : EIdx) (d k : Nat) : CheckIM EIdx :=
  modifyGet fun s =>
    if s.store.fvarRangeD e ≤ d then (e, s)
    else
      let store := s.store
      let s := { s with store := EStore.empty }
      let (r', store) := store.abstractRangeI e d k 0
      (r', { s with store := store })

/-- Interned `Expr.mkAppN`. -/
def mkAppNM (f : EIdx) (args : List EIdx) : CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.mkAppNI f args
    (r, { s with store := store })

/-- Interned `Expr.instSpine` (per-node bound shortcut through the
eager derived-field array, tasks #84/#87). -/
def instSpineM (args : List EIdx) (t : Nat) (e : EIdx) :
    CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r', store) := store.instSpineI args t e
    (r', { s with store := store })

/-- Interned `Expr.piResidual`/`Expr.instPis` (per-node bound
shortcut as in `instSpineM`, tasks #84/#87). -/
def piResidualM (e : EIdx) (args : List EIdx) :
    CheckIM (Option EIdx) :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r', store) := store.piResidualI e args
    (r', { s with store := store })

/-- Interned `Expr.pisToLams`. -/
def pisToLamsM (k : Nat) (e body : EIdx) : CheckIM (Option EIdx) :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.pisToLamsI k e body
    (r, { s with store := store })

/-! ### Interned level operations (task #62) -/

/-- Read a level node (no store change). -/
@[inline] def viewLM (u : LIdx) : CheckIM (Option LNode) :=
  (fun s => s.store.lnodes[u]?) <$> get

/-- Intern one level node. -/
def internLM (n : LNode) : CheckIM LIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (i, store) := store.internL n
    (i, { s with store := store })

/-- Interned `Level.subst` on a level index (fresh per-call memo). -/
def substLM (ks : List Name) (us : List LIdx) (u : LIdx) :
    CheckIM LIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.substLI ks us u
    (r, { s with store := store })

/-- Interned `Level.subst` applied to a stored level *tree*. -/
def substLevelTreeM (ks : List Name) (us : List LIdx) (l : Level) :
    CheckIM LIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.internLevelSubst ks us l
    (r, { s with store := store })

/-- Interned `Level.subst` over a list of stored level trees
(the spec side is a pure `List.map`). -/
def substLevelTreesM (ks : List Name) (us : List LIdx)
    (ls : List Level) : CheckIM (List LIdx) :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (rs, store) := store.internLevelSubsts ks us ls
    (rs, { s with store := store })

/-- Interned `Level.simplify` (persistently memoized: the memo is keyed
by level index alone, so it survives across calls). -/
def simplifyLM (u : LIdx) : CheckIM LIdx :=
  modifyGet fun s =>
    let store := s.store
    let memo := s.lsimpC
    let s := { s with store := EStore.empty, lsimpC := {} }
    let (r, store, memo) := store.simplifyLIGo memo u
    (r, { s with store := store, lsimpC := memo })

/-- Interned `Level.isNonZero` (persistently memoized). -/
def isNonZeroLM (u : LIdx) : CheckIM Bool :=
  modifyGet fun s =>
    let memo := s.lnzC
    let s := { s with lnzC := {} }
    let (r, memo) := s.store.isNonZeroLIGo memo u
    (r, { s with lnzC := memo })

/-- Interned `Expr.instantiateLevelParams` (interned replacement
levels; fresh per-call memos). -/
def instLevelParamsM (ks : List Name) (us : List LIdx)
    (e : EIdx) : CheckIM EIdx :=
  modifyGet fun s =>
    let store := s.store
    let s := { s with store := EStore.empty }
    let (r, store) := store.instantiateLevelParamsI ks us e
    (r, { s with store := store })

/-- Monadic level equivalence: simplify both sides on the arena
(persistent memo — repeat subterms are free), read the *small*
simplified levels back and run the spec `Level.leqCore` on the
transient trees (the `byCases` cascades allocate transient trees like
the `Expr`-level checker did, instead of interning every intermediate
level), with a persistent *result* cache (`eqvC`): on a canonical
arena the pair of indices determines the pair of levels, so a decided
equivalence never needs recomputing. -/
@[inline] def isEquivLM (l r : LIdx) : CheckIM (Option Bool) :=
  modifyGet fun s =>
    match s.eqvC[(l, r)]? with
    | some b => (some b, s)
    | none =>
      let store := s.store
      let memo := s.lsimpC
      let ec := s.eqvC
      let s := { s with store := EStore.empty, lsimpC := {}, eqvC := {} }
      let (ls, store, memo) := store.simplifyLIGo memo l
      let (rs, store, memo) := store.simplifyLIGo memo r
      if ls == rs then
        (some true, { s with store := store, lsimpC := memo,
                             eqvC := ec.insert (l, r) true })
      else
      match store.readbackL ls, store.readbackL rs with
      | some la, some ra =>
        match Level.leqCore Level.defaultFuel la ra 0 with
        | some false =>
          (some false, { s with store := store, lsimpC := memo,
                                eqvC := ec.insert (l, r) false })
        | some true =>
          match Level.leqCore Level.defaultFuel ra la 0 with
          | some b =>
            (some b, { s with store := store, lsimpC := memo,
                              eqvC := ec.insert (l, r) b })
          | none =>
            (none, { s with store := store, lsimpC := memo, eqvC := ec })
        | none =>
          (none, { s with store := store, lsimpC := memo, eqvC := ec })
      | _, _ =>
        (none, { s with store := store, lsimpC := memo, eqvC := ec })

/-- Pointwise `isEquivLM` (each pair through the result cache). -/
def isEquivListLM : List LIdx → List LIdx → CheckIM (Option Bool)
  | [], [] => pure (some true)
  | l :: ls, r :: rs => do
    match ← isEquivLM l r with
    | none => pure none
    | some false => pure (some false)
    | some true => isEquivListLM ls rs
  | _, _ => pure (some false)


/-- Read a level index back as a `Level` tree (an internal error when
the index is dangling — never on the bridge invariant). -/
def readbackLevelM (u : LIdx) : CheckIM Level := do
  match ← withStore (·.readbackL u) with
  | some l => pure l
  | none => throw (.internal "interned level readback failed")

/-- Read a list of level indices back (structural recursion). -/
def readbackLevelsM : List LIdx → CheckIM (List Level)
  | [] => pure []
  | u :: us => do
    let l ← readbackLevelM u
    let ls ← readbackLevelsM us
    pure (l :: ls)

/-! ### Lazy interned stored-constant instantiations -/

/-- The interned index of a stored constant's type: the interned-
environment entry when its denotation tag validates (a pointer test —
the entry was created from the very object stored in the environment),
else a fresh tree interning (basis pins and budget-bounded members). -/
def storedTyIdxM (n : Name) (ty : Expr) : CheckIM EIdx := do
  let ent? : Option IConstE ← modifyGet fun s => (s.ienv[n]?, s)
  match ent? with
  | some ent =>
    if EStore.exprPtrBEq ent.tyE ty then pure ent.ty
    else internExprM ty
  | none => internExprM ty

/-- The interned index of a stored definition/theorem value (see
`storedTyIdxM`). -/
def storedValIdxM (n : Name) (v : Expr) : CheckIM EIdx := do
  let ent? : Option IConstE ← modifyGet fun s => (s.ienv[n]?, s)
  match ent? with
  | some ⟨_, _, some (vE, vi)⟩ =>
    if EStore.exprPtrBEq vE v then pure vi
    else internExprM v
  | _ => internExprM v

/-- The interned level-instantiated *type* of the stored constant `n`
(cached by `(n, us)`; the constant must be stored — callers have already
matched the lookup). -/
def constTyAtM (fe : FEnv) (nI : NIdx) (n : Name) (us : List LIdx) :
    CheckIM EIdx := do
  let hit? ← modifyGet fun s => (s.constTyAt[(nI, us)]?, s)
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
        { s with constTyAt := mp.insert (nI, us) i }
      pure i
    | none => throw (.internal "constTyAtM: unknown constant")

/-- The interned level-instantiated *value* of the stored definition `n`
(cached by `(n, us)`). -/
def constValAtM (fe : FEnv) (nI : NIdx) (n : Name) (us : List LIdx) :
    CheckIM EIdx := do
  let hit? ← modifyGet fun s => (s.constValAt[(nI, us)]?, s)
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
        { s with constValAt := mp.insert (nI, us) i }
      pure i
    | some (.thmInfo cv v) =>
      let raw ← storedValIdxM n v
      let i ← instLevelParamsM cv.levelParams us raw
      modify fun s =>
        let mp := s.constValAt
        let s := { s with constValAt := ∅ }
        { s with constValAt := mp.insert (nI, us) i }
      pure i
    | _ => throw (.internal "constValAtM: not a stored definition")

/-- The interned level-instantiated right-hand side of the rule for
constructor `j` of the stored recursor `c` (cached by `(c, j, us)`). -/
def ruleRhsAtM (fe : FEnv) (cI jI : NIdx) (c j : Name)
    (us : List LIdx) : CheckIM EIdx := do
  let hit? ← modifyGet fun s => (s.ruleRhsAt[(cI, jI, us)]?, s)
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
          { s with ruleRhsAt := mp.insert (cI, jI, us) i }
        pure i
      | none => throw (.internal "ruleRhsAtM: no rule for constructor")
    | _ => throw (.internal "ruleRhsAtM: not a stored recursor")

/-! ## The interned core record and helper twins -/

/-- The record of mutually recursive interned entry points. -/
structure CoreFnsI where
  whnfCore : Nat → EIdx → CheckIM EIdx
  whnf : Nat → EIdx → CheckIM EIdx
  infer : Nat → EIdx → CheckIM EIdx
  defeq : Nat → EIdx → EIdx → CheckIM Bool
  annotate : Nat → EIdx → CheckIM EIdx

/-- Twin of `unfoldDefinition` (monadic: the unfolded value is interned
through the `(name, levels)` cache).  Like the spec, theorem values
unfold too. -/
def unfoldDefinitionI (fe : FEnv) (e : EIdx) : CheckIM (Option EIdx) := do
  match ← withStore (fun st => st.getNode (st.getAppFnI e)) with
  | some (.const n us) => do
    let nm ← readbackNM n
    match fe.find? nm with
    | some (.defnInfo cv _ _) =>
      if us.length = cv.levelParams.length then do
        let v ← constValAtM fe n nm us
        let args ← withStore (·.getAppArgsI e)
        let r ← mkAppNM v args
        pure (some r)
      else pure none
    | some (.thmInfo cv _) =>
      if us.length = cv.levelParams.length then do
        let v ← constValAtM fe n nm us
        let args ← withStore (·.getAppArgsI e)
        let r ← mkAppNM v args
        pure (some r)
      else pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `litToCtorIfNat`. -/
def litToCtorIfNatI (fe : FEnv) (e : EIdx) : CheckIM EIdx := do
  match ← viewI e with
  | some (.lit (.natVal n)) =>
    if natLitSupportedF fe then internExprM (natLitToConstructor n)
    else pure e
  | _ => pure e

/-- Twin of `reduceNat`. -/
def reduceNatI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : EIdx) :
    CheckIM (Option EIdx) := do
  match ← viewI e with
  | some (.app f₁ b) =>
    match ← viewI f₁ with
    | some (.const c us) =>
      match us with
      | _ :: _ => pure none
      | [] => do
        let cn ← readbackNM c
        if cn = natSuccName ∧ natLitSupportedF fe then do
          let w ← r.whnf depth b
          match ← withStore (rawNatLitI? · w) with
          | some n => do
            let r ← internExprM (.lit (.natVal (n + 1)))
            pure (some r)
          | none => pure none
        else if cn = natPredName ∧ natOpGuardF fe cn = true then do
          let w ← r.whnf depth b
          match ← withStore (rawNatLitI? · w) with
          | some n =>
            match natOpResult cn n 0 with
            | some x => do
              let r ← internExprM x
              pure (some r)
            | none => pure none
          | none => pure none
        else if cn = natLog2Name ∧ natOpGuardF fe cn = true then do
          let w ← r.whnf depth b
          match ← withStore (rawNatLitI? · w) with
          | some n =>
            match natOpResult cn n 0 with
            | some x => do
              let r ← internExprM x
              pure (some r)
            | none => pure none
          | none => pure none
        else if cn = natLog2Name ∧ natLitSupportedF fe then do
          let w ← r.whnf depth b
          match ← withStore (rawNatLitI? · w) with
          | some _ => throw (.notImplemented
              s!"native Nat computation on literals ({cn})")
          | none => pure none
        else pure none
    | some (.app f₂ a) =>
      match ← viewI f₂ with
      | some (.const c us) =>
        match us with
        | _ :: _ => pure none
        | [] => do
          let cn ← readbackNM c
          if (cn = natAddName ∨ cn = natSubName ∨ cn = natMulName ∨
              cn = natPowName ∨ cn = natBeqName ∨ cn = natBleName ∨
              cn = natDivName ∨ cn = natModName ∨ cn = natGcdName ∨
              cn = natLandName ∨ cn = natLorName ∨ cn = natXorName ∨
              cn = natShiftLeftName ∨ cn = natShiftRightName) ∧
              natOpGuardF fe cn = true then do
            let w₁ ← r.whnf depth a
            let w₂ ← r.whnf depth b
            match ← withStore (rawNatLitI? · w₁),
                ← withStore (rawNatLitI? · w₂) with
            | some n₁, some n₂ =>
              match natOpResult cn n₁ n₂ with
              | some x => do
              let r ← internExprM x
              pure (some r)
              | none => pure none
            | _, _ => pure none
          else if natOpWfNames.contains cn ∧ natLitSupportedF fe then do
            let w₁ ← r.whnf depth a
            let w₂ ← r.whnf depth b
            match ← withStore (rawNatLitI? · w₁),
                ← withStore (rawNatLitI? · w₂) with
            | some _, some _ => throw (.notImplemented
                s!"native Nat computation on literals ({cn})")
            | _, _ => pure none
          else pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `iotaCerts`, bulk form (task #50): peel the raw telescope
while accumulating the certified arguments, substituting only each
binder's *domain* (small) instead of copying the whole residual
telescope per argument.  A raw `bvar` body (whose substitution could
expose further `∀`-binders — the fold semantics) substitutes the
accumulator and re-enters. -/
def iotaCertsIAux (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    EIdx → List EIdx → List EIdx → CheckIM Bool
  | _, _, [] => pure true
  | ty, acc, arg :: rest => do
    match ← viewI ty with
    | some (.forallE _ dom body _) => do
      let dom' ← instListM dom acc
      let ta ← r.infer depth arg
      if ← r.defeq depth ta dom' then
        iotaCertsIAux r fe depth body (arg :: acc) rest
      else pure false
    | some (.bvar _) =>
      match acc with
      | [] => pure false
      | _ :: _ => do
        let ty' ← instListM ty acc
        iotaCertsIAux r fe depth ty' [] (arg :: rest)
    | _ => pure false
termination_by _ acc args => (args.length, acc.length)
decreasing_by
  · apply Prod.Lex.left; simp
  · apply Prod.Lex.right' <;> simp

/-- Twin of `iotaCerts` (certify a spine against a recursor telescope);
the bulk-instantiating accumulator loop at the empty accumulator. -/
def iotaCertsI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (ty : EIdx) (args : List EIdx) : CheckIM Bool :=
  iotaCertsIAux r fe depth ty [] args

/-- Twin of `defEqList`. -/
def defEqListI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    List EIdx → List EIdx → CheckIM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then
      defEqListI r fe depth as bs
    else pure false
  | _, _ => pure false

/-- Twin of `defeqSpine`. -/
def defeqSpineI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  match ← withStore (fun st => st.getNode (st.getAppFnI a)) with
  | some (.const n us) =>
    match ← withStore (fun st => st.getNode (st.getAppFnI b)) with
    | some (.const n' us') => do
      let aargs ← withStore (·.getAppArgsI a)
      let bargs ← withStore (·.getAppArgsI b)
      if n = n' ∧ aargs.length = bargs.length then
        match ← isEquivListLM us us' with
        | some true => defEqListI r fe depth aargs bargs
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `proofIrrel`. -/
def proofIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  let ta ← r.infer depth a
  let wta ← r.whnf depth ta
  if ← withStore (fun st => isUnitLikeTyI fe st wta) then do
    let tb ← r.infer depth b
    let wtb ← r.whnf depth tb
    if ← withStore (fun st => isUnitLikeTyI fe st wtb) then
      pure true
    else
      pure false
  else do
    let tta ← r.infer depth ta
    let wtta ← r.whnf depth tta
    match ← viewI wtta with
    | some (.sort uT) => do
      let z ← internLM .zero
      let okA ← liftFueled "level comparison" (← isEquivLM uT z)
      let tb ← r.infer depth b
      let ttb ← r.infer depth tb
      let wttb ← r.whnf depth ttb
      match ← viewI wttb with
      | some (.sort vT) => do
        let z ← internLM .zero
        let okB ← liftFueled "level comparison" (← isEquivLM vT z)
        pure (okA && okB)
      | _ => pure false
    | _ => pure false

/-- Twin of `projParamCert` (task #129).  The pinned projection type
`pty` is the caller's — the same interned expression `piResidual`
peels, and the same one `constTyAtM` caches for the η certificate
below (task #130) — so this adds a telescope walk and no lookup. -/
def projParamCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (pty : EIdx) (params : List EIdx) : CheckIM Bool :=
  iotaCertsI r fe depth pty params

/- Task #147: functions below that mention `mode` take the
three-mode setting as their first explicit argument; only the seven
TT-lane check sites branch on it (`CheckMode.ttChecks`). -/
variable (mode : CheckMode)

/-- Twin of `pairEtaCert`. -/
def pairEtaCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  match ← viewI a with
  | some (.app f₄ s₂) =>
    match ← viewI f₄ with
    | some (.app f₃ s₁) =>
      match ← viewI f₃ with
      | some (.app f₂ pβ) =>
        match ← viewI f₂ with
        | some (.app f₁ pα) =>
          match ← viewI f₁ with
          | some (.const c us) => do
            let cn ← readbackNM c
            match fe.find? cn with
            | some (.ctorInfo _cvm 2 2) => do
              let tb ← r.infer depth b
              let wtb ← r.whnf depth tb
              match ← viewI wtb with
              | some (.app g₂ B) =>
                match ← viewI g₂ with
                | some (.app g₁ A) =>
                  match ← viewI g₁ with
                  | some (.const c' us') => do
                    let c'n ← readbackNM c'
                    match fe.find? c'n with
                    | some (.indInfo _ _) =>
                      match fe.find? (c'n.str "rec") with
                      | some (.recInfo _ mI rP [rr]) =>
                        if rr.ctor = cn ∧ rr.nfields = 2 ∧ mI = rP ∧
                            reservedBasisNames.contains (c'n.str "rec")
                              = true then do
                          if ← liftFueled "level comparison"
                              (← isEquivListLM us us') then do
                            if ← r.defeq depth pα A then do
                              if ← r.defeq depth pβ B then do
                                let p₀ ← internI (.proj c' 0 b)
                                if ← r.defeq depth s₁ p₀ then do
                                  let p₁ ← internI (.proj c' 1 b)
                                  if ← r.defeq depth s₂ p₁ then do
                                    -- Task #130: certify the pair
                                    -- type's parameters against the
                                    -- projection entry's telescope
                                    -- (twin of `pairEtaCert`'s call).
                                    -- TT-lane check (task #147):
                                    -- skipped unless `mode.ttChecks`.
                                    if mode.ttChecks then
                                      match fe.findProj? c'n 0 with
                                      | some _ => do
                                        let pf ← projFnIdxM c' 0
                                        let pty ← constTyAtM fe pf
                                          (projFnName c'n 0) us'
                                        projParamCertI r fe depth pty
                                          [A, B]
                                      | none => pure false
                                    else pure true
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
            | _ => pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false
  | _ => pure false

/-- The interned projection-application spine
`[proj_0 targs b, …]` (structural recursion; the spec side is a pure
`List.map`). -/
def projAppsI (T : NIdx) (us' : List LIdx) (targs : List EIdx)
    (b : EIdx) : List Nat → CheckIM (List EIdx)
  | [] => pure []
  | i :: rest => do
    let pf ← projFnIdxM T i
    let h ← internI (.const pf us')
    let r ← mkAppNM h (targs ++ [b])
    let rs ← projAppsI T us' targs b rest
    pure (r :: rs)

/-- Twin of `structEtaProjCerts`. -/
def structEtaProjCertsI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (TI : NIdx) (T : Name) (us' : List LIdx) (targs : List EIdx)
    (b : EIdx)
    (lpsT : List Name) : List Nat → CheckIM Bool
  | [] => pure true
  | i :: rest => do
    match fe.find? (projFnName T i) with
    | some (.recInfo cvp _ _ _) =>
      if cvp.levelParams = lpsT ∧
          (cvp.type.stripPis (targs.length + 1)).isSome = true then do
        let pf ← projFnIdxM TI i
        let pty ← constTyAtM fe pf (projFnName T i) us'
        if ← iotaCertsI r fe depth pty (targs ++ [b]) then
          structEtaProjCertsI r fe depth TI T us' targs b lpsT rest
        else pure false
      else pure false
    | _ => pure false

/-- Twin of `structEtaCertWith`. -/
def structEtaCertWithI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b wtb : EIdx) : CheckIM Bool := do
  match ← withStore (fun st => st.getNode (st.getAppFnI a)) with
  | some (.const c us) => do
    let cn ← readbackNM c
    match fe.find? cn with
    | some (.ctorInfo cvc cnP cnF) => do
      let aargs ← withStore (·.getAppArgsI a)
      if aargs.length = cnP + cnF then
        match ← withStore (fun st => st.getNode (st.getAppFnI wtb)) with
        | some (.const T us') => do
          let Tn ← readbackNM T
          match fe.find? Tn with
          | some (.indInfo cvT caps) => do
            let targs ← withStore (·.getAppArgsI wtb)
            if caps.eta = true ∧ caps.etaCtor = cn ∧
                caps.etaParams = cnP ∧ caps.etaFields = cnF ∧
                reservedBasisNames.contains Tn = false ∧
                reservedBasisNames.contains cn = false ∧
                targs.length = cnP ∧
                us'.length = cvT.levelParams.length ∧
                cvc.levelParams = cvT.levelParams ∧
                (cvT.type.stripPis cnP).isSome = true then do
              if ← liftFueled "level comparison"
                  (← isEquivListLM us us') then do
                let tyT ← constTyAtM fe T Tn us'
                if ← iotaCertsI r fe depth tyT targs then do
                  if ← structEtaProjCertsI r fe depth T Tn us'
                      targs b cvT.levelParams (List.range cnF) then do
                    if ← defEqListI r fe depth (aargs.take cnP) targs then do
                      let projs ← projAppsI T us' targs b (List.range cnF)
                      -- synthetic-spine certification (task #137): the
                      -- fabricated constructor application
                      -- `c targs (proj_i … b)` is certified against the
                      -- constructor's own telescope, here rather than at
                      -- the callers, so that BOTH consumers get it —
                      -- `majorToCtorI`'s eta rescue ran it already
                      -- (task #71), `defeq`'s `structEtaCertI` did not.
                      -- TT-lane check (task #147): skipped unless
                      -- `mode.ttChecks`.
                      if ← (if mode.ttChecks then do
                          let tyCtor ← constTyAtM fe c cn us
                          iotaCertsI r fe depth tyCtor (targs ++ projs)
                        else pure true) then
                        defEqListI r fe depth (aargs.drop cnP) projs
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

/-- Twin of `structEtaCert`. -/
def structEtaCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  let tb ← r.infer depth b
  let wtb ← r.whnf depth tb
  structEtaCertWithI mode r fe depth a b wtb

/-- Twin of `structUnitCert`. -/
def structUnitCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  let ta ← r.infer depth a
  let wta ← r.whnf depth ta
  match ← withStore (fun st => st.getNode (st.getAppFnI wta)) with
  | some (.const T us') => do
    let Tn ← readbackNM T
    match fe.find? Tn with
    | some (.indInfo cvT caps) => do
      let targs ← withStore (·.getAppArgsI wta)
      if caps.unitlike = true ∧
          reservedBasisNames.contains Tn = false ∧
          targs.length = caps.unitParams ∧
          us'.length = cvT.levelParams.length ∧
          (cvT.type.stripPis caps.unitParams).isSome = true then do
        let tb ← r.infer depth b
        let wtb ← r.whnf depth tb
        if ← r.defeq depth wta wtb then do
          let tyT ← constTyAtM fe T Tn us'
          iotaCertsI r fe depth tyT targs
        else pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `etaCert` (the λ's pieces come pre-destructured, as in the
spec). -/
def etaCertI (r : CoreFnsI) (_fe : FEnv) (depth : Nat)
    (n₁ : NIdx) (ty₁ body₁ : EIdx) (m₁ : IBinderMeta) (b : EIdx) :
    CheckIM Bool := do
  let tb ← r.infer depth b
  let wtb ← r.whnf depth tb
  match ← viewI wtb with
  | some (.forallE _ ty₂ _ m₂) => do
    -- prop-ness agreement checked LAST (task #161); see `etaCert`
    if ← r.defeq depth ty₂ ty₁ then do
      let fv ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv
      let ba ← internI (.app b fv)
      unless ← r.defeq (depth + 1) b₁ ba do return false
      if mode.verified && !(m₁.pw.equiv m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (eta)")
      pure true
    else pure false
  | _ => pure false

/-- Twin of `stuckIrrel`. -/
def stuckIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  if ← pairEtaCertI mode r fe depth a b then pure true
  else if ← pairEtaCertI mode r fe depth b a then pure true
  else if ← structEtaCertI mode r fe depth a b then pure true
  else if ← structEtaCertI mode r fe depth b a then pure true
  else if ← structUnitCertI r fe depth a b then pure true
  else proofIrrelI r fe depth a b

/-- Twin of `majorToCtor`. -/
def majorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : EIdx) :
    CheckIM EIdx := do
  if ← withStore (fun st => isCtorAppI fe st major) then pure major else
  match rules with
  | [rl] =>
    match fe.find? rl.ctor with
    | some (.ctorInfo cvj cnP cnF) =>
      match (cvj.type.piResult).getAppFn with
      | .const T _ =>
        match fe.find? T with
        | some (.indInfo cvT caps) =>
          if caps.ruleK = true ∧ cnF = 0 then do
            let tmaj₀ ← r.infer depth major
            let tmaj ← r.whnf depth tmaj₀
            match ← withStore (fun st => st.getNode (st.getAppFnI tmaj)) with
            | some (.const T' ust) =>
              if (← beqNameM T' T) ∧ cvj.levelParams.length = ust.length then do
                let margs ← withStore (·.getAppArgsI tmaj)
                if cnP ≤ margs.length ∧
                    (cvj.type.stripPis cnP).isSome = true then do
                  let ctorI ← internNameM rl.ctor
                  let h ← internI (.const ctorI ust)
                  let fab ← mkAppNM h (margs.take cnP)
                  if ← withStore (fun st => st.wscopedBI depth fab &&
                      st.looseBVarsBoundedI 0 fab &&
                      st.leafGuardI fab major) then do
                    -- synthetic-spine certification (task #71): a
                    -- fabricated constructor spine keeps the ungated
                    -- telescope certificate, relocated here from the
                    -- fire path
                    let tyCtor ← constTyAtM fe ctorI rl.ctor ust
                    if ← iotaCertsI r fe depth tyCtor
                        (margs.take cnP) then do
                      -- official `to_cnstr_when_K` fabrication type
                      -- check (load-bearing with the major-slot
                      -- certificate gated at nonzero motives, tasks
                      -- #49/#71; arena bad/098_ruleKbad);
                      -- `proofIrrelI` stays as the soundness
                      -- certificate
                      let tfab ← r.infer depth fab
                      if ← r.defeq depth tmaj tfab then
                        if ← proofIrrelI r fe depth fab major then
                          pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
              Name.isProjFnShape recName = false then do
            let tmaj₀ ← r.infer depth major
            let tmaj ← r.whnf depth tmaj₀
            match ← withStore (fun st => st.getNode (st.getAppFnI tmaj)) with
            | some (.const T' ust) => do
              let margs ← withStore (·.getAppArgsI tmaj)
              let ustL ← readbackLevelsM ust
              -- instantiated non-Prop guard, as in the spec body
              -- `majorToCtor` (task #61)
              if (← beqNameM T' T) ∧ margs.length = caps.etaParams ∧
                  ust.length = cvT.levelParams.length ∧
                  piResultNeverZero cvT.levelParams ustL cvT.type = true then do
                if cvj.levelParams.length = ust.length ∧
                    (cvj.type.stripPis
                      (caps.etaParams + caps.etaFields)).isSome
                      = true then do
                  let TI ← internNameM T
                  let projs ← projAppsI TI ust margs major
                    (List.range caps.etaFields)
                  let ctorI ← internNameM caps.etaCtor
                  let h ← internI (.const ctorI ust)
                  let fab ← mkAppNM h (margs ++ projs)
                  if ← withStore (fun st => st.wscopedBI depth fab &&
                      st.looseBVarsBoundedI 0 fab &&
                      st.leafGuardI fab major) then do
                    -- synthetic-spine certification, as in the K
                    -- branch (task #71)
                    let tyCtor ← constTyAtM fe ctorI rl.ctor ust
                    if ← iotaCertsI r fe depth tyCtor
                        (margs ++ projs) then do
                      if ← structEtaCertWithI mode r fe depth fab major
                          tmaj then
                        pure fab
                      else if caps.etaFields = 0 ∧
                          cvj.levelParams.length = ust.length then
                        if ← proofIrrelI r fe depth fab major then
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

/-- Twin of `litMajorToCtor`. -/
def litMajorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : EIdx) :
    CheckIM EIdx := do
  match ← viewI e with
  | some (.lit (.strVal s)) =>
    if strLitSupportedF fe then do
      let x ← internExprM (strLitToConstructor s)
      r.whnf depth x
    else pure e
  | _ => litToCtorIfNatI fe e

/-- Twin of `projLitToCtor`. -/
def projLitToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : EIdx) :
    CheckIM EIdx := do
  match ← viewI e with
  | some (.lit (.strVal s)) =>
    if strLitSupportedF fe then do
      let x ← internExprM (strLitToConstructor s)
      r.whnf depth x
    else pure e
  | _ => pure e

/-- The interned nested-rule pin instantiations (structural recursion;
the spec side is `(recFireComparands …).2`'s `List.map`). -/
def pinArgsI (lps : List Name) (us : List LIdx) (args : List EIdx)
    (t : Nat) : List Expr → CheckIM (List EIdx)
  | [] => pure []
  | p :: ps => do
    let praw ← internExprM p
    let pi ← instLevelParamsM lps us praw
    let r ← instSpineM args t pi
    let rs ← pinArgsI lps us args t ps
    pure (r :: rs)

/-- Twin of `iotaRec`. -/
def iotaRecI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : EIdx) :
    CheckIM (Option EIdx) := do
  match ← withStore (fun st => st.getNode (st.getAppFnI e)) with
  | some (.const c us) => do
    let cn ← readbackNM c
    match fe.find? cn with
    | some (.recInfo cv mI rP rules) => do
      let args ← withStore (·.getAppArgsI e)
      -- checker change #9 (twin of `Core.lean`'s `iotaRec`): guard the
      -- recursor's level arity before the rule's RHS is instantiated.
      if args.length = mI + 1 ∧ us.length = cv.levelParams.length then do
        let bvar0 ← internI (.bvar 0)
        let major₀ ← r.whnf depth (args.getD mI bvar0)
        let major₁ ← litMajorToCtorI r fe depth major₀
        let major ← majorToCtorI mode r fe depth cn rules major₁
        match ← withStore (fun st => st.getNode (st.getAppFnI major)) with
        | some (.const cj usj) => do
          let cjn ← readbackNM cj
          match fe.find? cjn with
          | some (.ctorInfo cvj _ _) =>
            match rules.find? (fun r' => r'.ctor == cjn) with
            | some rl => do
              let margs ← withStore (·.getAppArgsI major)
              if margs.length = rl.ctorParams + rl.nfields then
               if rl.fire = .inert then
                 throw (.notImplemented
                   "iota reduction over a nested auxiliary recursor rule")
               else
               if (cv.type.stripPis (mI + 1)).isSome ∧
                  (cvj.type.stripPis (rl.ctorParams + rl.nfields)).isSome
                  then do
                -- the comparands (canonical: recursor's levels/args;
                -- nested: the stored major-domain instantiations)
                let cmpLvls : List LIdx ←
                  match rl.fire with
                  | .nested lvls _ => substLevelTreesM cv.levelParams us lvls
                  | _ =>
                    substLevelTreesM cv.levelParams us
                      (cvj.levelParams.map Level.param)
                let cmpArgs : List EIdx ←
                  match rl.fire with
                  | .nested _ pins =>
                    pinArgsI cv.levelParams us (args.take rP) (rP - 1) pins
                  | _ => pure (args.take rl.ctorParams)
                if ← liftFueled "level comparison"
                    (← isEquivListLM usj cmpLvls) then do
                 if ← defEqListI r fe depth (margs.take rl.ctorParams)
                    cmpArgs then do
                  let tyRec ← constTyAtM fe c cn us
                  if ← iotaCertsI r fe depth tyRec
                     (args.take mI ++ [major]) then do
                   let tyCtor ← constTyAtM fe cj cjn usj
                   if ← iotaCertsI r fe depth tyCtor margs then do
                    match ← withStore (fun st =>
                          st.stripPisBodyI (rl.ctorParams + rl.nfields)
                            tyCtor),
                        ← piResidualM tyCtor margs with
                    | some cbody, some residual =>
                      match ← withStore (fun st =>
                          st.getNode (st.getAppFnI cbody)) with
                      | some (.const _ _) => do
                        let resArgs ← withStore (·.getAppArgsI residual)
                        if ← defEqListI r fe depth
                            (resArgs.drop rl.ctorParams)
                            ((args.take mI).drop rP) then do
                          let rhs ← ruleRhsAtM fe c cj cn cjn us
                          let red ← mkAppNM rhs
                            (args.take rP ++ margs.drop rl.ctorParams)
                          pure (some red)
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

/-- Twin of `projCert`. -/
def projCertI (r : CoreFnsI) (_fe : FEnv) (depth : Nat)
    (e₂ : EIdx) (i : Nat) (fieldLvl structLvl : LIdx) (nP : Nat) :
    CheckIM Bool := do
  let bvar0 ← internI (.bvar 0)
  let args ← withStore (·.getAppArgsI e₂)
  let arg := args.getD (nP + i) bvar0
  let ta ← r.infer depth arg
  let tta ← r.infer depth ta
  let wtta ← r.whnf depth tta
  match ← viewI wtta with
  | some (.sort uT) => do
    let okT ← liftFueled "level comparison" (← isEquivLM uT fieldLvl)
    let te ← r.infer depth e₂
    let tte ← r.infer depth te
    let wtte ← r.whnf depth tte
    match ← viewI wtte with
    | some (.sort wT) => do
      let okW ← liftFueled "level comparison"
        (← isEquivLM wT structLvl)
      pure (okT && okW)
    | _ => pure false
  | _ => pure false

/-- Twin of `projTeleCert` (task #126). -/
def projTeleCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (cI : NIdx) (c : Name) (us : List LIdx) (args : List EIdx) :
    CheckIM Bool := do
  match fe.find? c with
  | some (.ctorInfo _ _ _) => do
    let tyCtor ← constTyAtM fe cI c us
    iotaCertsI r fe depth tyCtor args
  | _ => pure false

mutual

/-- Bulk-beta argument loop (task #50): consume the whole application
spine against the whnf'd head `v`.  A lambda head enters the peel loop
(first binder inline, which keeps the argument count decreasing);
other heads try iota with one more argument and otherwise accumulate a
stuck application — exactly the per-level `whnfCoreBody` app clauses,
but with the chained per-argument `instantiate1` of the beta path
replaced by one bulk substitution per peeled group
(`Setlec/Verify/BetaSpine.lean` proves the identification).  The
head-normalization loop's continuation `k` is threaded through
(task #106). -/
def whnfAppI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : EIdx → CheckIM EIdx) :
    EIdx → List EIdx → CheckIM EIdx
  | v, [] => pure v
  | v, a :: rest => do
    match ← viewI v with
    | some (.lam _ ty body _mb) => do
        let ta ← r.infer depth a
        if ← r.defeq depth ta ty then
          betaPeelI r fe depth k body [a] rest
        else do
          let fa ← internI (.app v a)
          mkAppNM fa rest
    | _ => do
      let fa ← internI (.app v a)
      match ← iotaRecI mode r fe depth fa with
      | some e'' => do
        let v' ← k e''
        whnfAppI r fe depth k v' rest
      | none => whnfAppI r fe depth k fa rest
termination_by _ args => (args.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Peel loop of `whnfAppI`: `t` is the raw (unsubstituted) lambda body
after the binders consumed so far, `acc` their arguments (innermost
first).  Each binder's argument certificate (unconditional since the
task-#100 de-gating) substitutes only the *domain*; the body is
substituted once, when peeling stops. -/
def betaPeelI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : EIdx → CheckIM EIdx) :
    EIdx → List EIdx → List EIdx → CheckIM EIdx
  | t, acc, [] => do
    let e' ← instListM t acc
    k e'
  | t, acc, a :: rest => do
    match ← viewI t with
    | some (.lam _ ty body _mb) => do
        let ty' ← instListM ty acc
        let ta ← r.infer depth a
        if ← r.defeq depth ta ty' then
          betaPeelI r fe depth k body (a :: acc) rest
        else do
          let f' ← instListM t acc
          let fa ← internI (.app f' a)
          mkAppNM fa rest
    | _ => do
      let e' ← instListM t acc
      let v ← k e'
      whnfAppI r fe depth k v (a :: rest)
termination_by _ _acc args => (args.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

/-- Twin of `whnfCoreStep`: one head-normalization step (beta, iota,
zeta, projection) with the loop's continuation `k` abstracted, in the
open-recursion style of the whole module.  Only the spine head's
normalization stays a knot call (genuine nesting, bounded by the
term's depth); every *reduction* step is iteration, so a chain no
longer charges the shared recursion-depth budget one unit per step
(task #106 — that is what made the `Nat.brecOn` grind of
`Std.Time…toDays._proof_1` exhaust `checkFuel`). -/
def whnfCoreStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : EIdx → CheckIM EIdx) (e : EIdx) : CheckIM EIdx := do
    match ← viewI e with
    | some (.sort _) | some (.fvar ..) | some (.forallE ..)
    | some (.lam ..) | some (.const ..) | some (.lit _) => pure e
    | some (.app _ _) => do
      -- Bulk beta (task #50): normalize the spine head once and run the
      -- argument loop over the whole spine, batching consecutive
      -- lambda binders into one substitution.
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let v ← r.whnfCore depth h
      whnfAppI mode r fe depth k v args
    | some (.proj sn i pe) => do
      let e' ← r.whnf depth pe
      let e' ← projLitToCtorI r fe depth e'
      let snn ← readbackNM sn
      match fe.findProj? snn i with
      | some entry =>
        match ← withStore (fun st => st.getNode (st.getAppFnI e')) with
        | some (.const c us) => do
          let args ← withStore (·.getAppArgsI e')
          if entry.native ∧ (← beqNameM c entry.ctor) ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length then do
            let mx ← substLevelTreeM entry.levelParams us
              entry.structSort
            let bvar0 ← internI (.bvar 0)
            let arg := args.getD (entry.numParams + i) bvar0
            -- task #100 de-gating: the certificate runs
            -- unconditionally (the former nonzero-sort gate is
            -- unsound-to-model under the domain-relative collapse)
            let fl ← substLevelTreeM entry.levelParams us entry.fieldSort
            if ← projCertI r fe depth e' i fl
                mx entry.numParams then
              -- task #126: the constructor-telescope certification.
              -- TT-lane check (task #147): skipped unless
              -- `mode.ttChecks`.
              if ← (if mode.ttChecks then
                  projTeleCertI r fe depth c entry.ctor us args
                else pure true) then
                k arg
              else internI (.proj sn i e')
            else internI (.proj sn i e')
          else internI (.proj sn i e')
        | _ => internI (.proj sn i e')
      | none => internI (.proj sn i e')
    | some (.letE _ _ v b) => do
      -- zeta on demand (official `whnf_core` Let case); `inst1M` is the
      -- sharing-preserving arena substitution
      let e' ← inst1M b v
      k e'
    | some (.bvar _) =>
      throw (.notImplemented "whnf beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- Twin of `whnfCoreLoop`: iterate `whnfCoreStepI` on its own step
budget. -/
def whnfCoreLoopI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → EIdx → CheckIM EIdx
  | 0, _ => throw (.internal "fuel exhausted: whnfCore loop")
  | n + 1, e =>
    whnfCoreStepI mode r fe depth (whnfCoreLoopI r fe depth n) e

/-- Twin of `whnfCoreBody`: the head-normalization loop at its own step
budget. -/
def whnfCoreBodyI (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → CheckIM EIdx :=
  fun depth e => whnfCoreLoopI mode r fe depth whnfCoreLoopFuel e

/-- Application-inference spine loop (task #50): walk the raw
Π-telescope against the arguments with deferred substitution — each
argument's certificate substitutes only its *domain*; the codomain is
substituted once per peeled group.  A non-syntactic telescope step
substitutes and normalizes, exactly like the chained `inferBody`
recursion (`Setlec/Verify/BetaSpine.lean` proves the
identification). -/
def inferSpineI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    EIdx → Array EIdx → List EIdx → CheckIM EIdx
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ← viewI ty with
    | some (.forallE _ dom body _mt) => do
      -- per-argument re-check (task #100 de-gating: the former
      -- possibly-Prop gate of task #49 is unsound-to-model under the
      -- domain-relative collapse; the certificate runs
      -- unconditionally, as in the spec body `inferBody`)
      let dom' ← instListRevM dom acc
      let ta ← r.infer depth a
      unless ← r.defeq depth ta dom' do
        throw (.invalid "application type mismatch")
      inferSpineI r fe depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← r.whnf depth ty'
      match ← viewI w with
      | some (.forallE _ dom body _mt) => do
        let ta ← r.infer depth a
        unless ← r.defeq depth ta dom do
          throw (.invalid "application type mismatch")
        inferSpineI r fe depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- Twin of `whnfStep`. -/
def whnfStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : EIdx → CheckIM EIdx) (e : EIdx) : CheckIM EIdx := do
  let e₁ ← r.whnfCore depth e
  match ← reduceNatI r fe depth e₁ with
  | some e₂ => k e₂
  | none =>
    match ← unfoldDefinitionI fe e₁ with
    | some e₂ => k e₂
    | none => pure e₁

/-- Twin of `whnfLoop`. -/
def whnfLoopI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → EIdx → CheckIM EIdx
  | 0, _ => throw (.internal "fuel exhausted: whnf loop")
  | n + 1, e => whnfStepI r fe depth (whnfLoopI r fe depth n) e

/-- Twin of `whnfBody`. -/
def whnfBodyI (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → CheckIM EIdx :=
  fun depth e => whnfLoopI r fe depth whnfLoopFuel e

/-- Twin of `ensureSort` (returns the level; no readback needed). -/
def ensureSortI (r : CoreFnsI) (depth : Nat) (e : EIdx) : CheckIM LIdx := do
  let w ← r.whnf depth e
  match ← viewI w with
  | some (.sort u) => pure u
  | _ => throw (.invalid "expected a sort")

/-! ### Binder-telescope loops (task #72)

The official-kernel discipline (lean4lean's `inferLambda`/`inferForall`
loops): peel a whole binder telescope accumulating opened free
variables, substituting only each binder's *domain* on the way in
(domains are small; `instListM` against the accumulator), infer or
annotate the leaf once on the bulk-opened body, then rebuild with one
`abstractRange` per domain and one over the leaf.  Each loop replays
exactly the per-binder checks of the chained recursion, in order; the
value-level identification with the chained spec bodies is
`Setlec/Verify/BinderLoop.lean` (the `DiscI` walks relate the interned
loops to their pure mirrors, and `_sound_body` theorems reproduce a
mirror run in the original one-binder-at-a-time body at some fuel).
The peel fuel (arena size, an upper bound for any chain in a canonical
arena) is semantically transparent: on exhaustion the leaf phase hands
the residual binder chain back to the knot, which is exactly the
chained spec's next step. -/

/-- Stack entry of `inferLamsI`: binder name, opened domain and binder
meta. -/
abbrev InferLamEntry := NIdx × EIdx × IBinderMeta

/-- Rebuild loop of `inferLamsI`: fold the stack (innermost binder
first, `j` its binder level relative to the ambient depth `d`).  The
intermediate `∀`-node inferences of the chained body are
value-determined by the peel phase's domain sorts and the leaf phase's
body-type sort and cannot fail (task #100 stage 6: the per-level
λ-annotation re-check is gone with the stored annotations). -/
def inferLamsOutI (d : Nat) :
    List InferLamEntry → Nat → EIdx → PropWhen → CheckIM EIdx
  | [], _j, cur, _prevPw => pure cur
  | (n, tyo, mb) :: rest, j, cur, prevPw => do
    -- Task #161, the chain rule (see `inferBody`'s `.lam` clause): a
    -- node's prop-ness annotation must agree with its inner
    -- neighbour's (the innermost step compares the entry with itself
    -- — vacuously true).
    if mode.verified && !(mb.pw.equiv prevPw) then
      throw (.notImplemented "sort-annotation mismatch (lam-cod-chain)")
    let tyAbs ← abstractRangeM tyo d j
    let node ← internI (.forallE n tyAbs cur mb)
    inferLamsOutI d rest (j - 1) node mb.pw

/-- Leaf phase of `inferLamsI`: bulk-open the residual body, infer it,
then rebuild outward.

Task #152: at the verified modes the chain's body type is
sort-checked here — the spec's codomain check (`inferBody`'s `.lam`
clause), which fires at the innermost binder of a λ-chain, i.e.
exactly when the peel stops on a non-λ residual.  The guard is the
same one the spec uses, on the same term. -/
def inferLamsLeafI (r : CoreFnsI) (d : Nat) (t : EIdx) (k : Nat)
    (fvs : Array EIdx) (stk : List InferLamEntry) : CheckIM EIdx := do
  let ob ← instListRevM t fvs
  let bt ← r.infer (d + k) ob
  match ← viewI t with
  | some (.lam ..) => pure ()
  | _ =>
    if mode.verified then
      let btt ← r.infer (d + k) bt
      let wbtt ← r.whnf (d + k) btt
      match ← viewI wbtt with
      | some (.sort vb) =>
        -- Task #161: validate the innermost binder's prop-ness
        -- annotation against the chain's body-type sort — the leaf
        -- half of the spec's `.lam` clause check.
        match stk with
        | (_, _, mb₀) :: _ => do
          let pv ← withStore fun st => (st.zeronessOfLIGo {} vb).1
          unless pv.equiv mb₀.pw do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-leaf)")
        | [] => pure ()
      | _ => throw (.invalid "expected a sort")
  let cur ← abstractRangeM bt d k
  -- The fold's initial neighbour: a λ residual (the fuel-exhausted
  -- path) supplies its own annotation — the head entry's chain check
  -- then compares against it, exactly as the spec's per-node clause
  -- does; a non-λ residual makes the head entry's step vacuous (its
  -- codomain fact is the leaf check above).
  let prevPw ← do
    match ← viewI t with
    | some (.lam _ _ _ mbT) => pure mbT.pw
    | _ =>
      pure (match stk with
        | (_, _, mb₀) :: _ => mb₀.pw
        | [] => .never)
  inferLamsOutI mode d stk (k - 1) cur prevPw

/-- λ-telescope inference loop (task #72; used by `inferBodyI`'s and
`inferBodyNC`'s lam cases): peel the raw λ-chain, checking each opened
domain to be a type on the way in.  `k` counts the opened binders
(`≥ 1`: the caller peels the first binder inline), `fvs` their free
variables innermost-first. -/
def inferLamsI (r : CoreFnsI) (d : Nat) :
    Nat → EIdx → Nat → Array EIdx → List InferLamEntry → CheckIM EIdx
  | fuel + 1, t, k, fvs, stk => do
    match ← viewI t with
    | some (.lam n ty body mb) => do
      let tyo ← instListRevM ty fvs
      let tty ← r.infer (d + k) tyo
      let wtty ← r.whnf (d + k) tty
      match ← viewI wtty with
      | some (.sort _) => do
        let fv ← internI (.fvar (d + k) n tyo)
        inferLamsI r d fuel body (k + 1) (fvs.push fv)
          ((n, tyo, mb) :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferLamsLeafI mode r d t k fvs stk
  | 0, t, k, fvs, stk => inferLamsLeafI mode r d t k fvs stk

/-- Rebuild loop of `inferPisI`: fold the accumulated domain sorts by
`imax`, innermost binder first — exactly the chained `∀`-rule's result
value. -/
def inferPisOutI : List (LIdx × PropWhen) → LIdx → EStore.PWMemo → CheckIM LIdx
  | [], v, _memo => pure v
  | (u, pw) :: rest, v, memo => do
    -- Task #161: validate the node's prop-ness annotation against its
    -- inferred codomain sort (`v` is exactly the spec `∀`-clause's
    -- `v` at this node); the readout is memoized across the fold.
    let (pv, memo) ← withStore fun st => st.zeronessOfLIGo memo v
    if mode.verified && !(pv.equiv pw) then
      throw (.notImplemented "sort-annotation mismatch (forall-cod)")
    let v' ← internLM (.imax u v)
    inferPisOutI rest v' memo

/-- Leaf phase of `inferPisI`: bulk-open the residual body, infer its
sort, then fold the domain sorts outward. -/
def inferPisLeafI (r : CoreFnsI) (d : Nat) (t : EIdx) (k : Nat)
    (fvs : Array EIdx) (stk : List (LIdx × PropWhen)) : CheckIM EIdx := do
  let ob ← instListRevM t fvs
  let bt ← r.infer (d + k) ob
  let wbt ← r.whnf (d + k) bt
  match ← viewI wbt with
  | some (.sort v) => do
    let iv ← inferPisOutI mode stk v ({} : EStore.PWMemo)
    internI (.sort iv)
  | _ => throw (.invalid "expected a sort")

/-- ∀-telescope inference loop (task #100 stage 6: the `∀`-rule infers
its codomain sort — the stored annotation is not read): peel the raw
∀-chain, checking each opened domain to be a type on the way in and
accumulating its sort, infer the bulk-opened leaf's sort once, and
fold `imax` outward. -/
def inferPisI (r : CoreFnsI) (d : Nat) :
    Nat → EIdx → Nat → Array EIdx → List (LIdx × PropWhen) →
      CheckIM EIdx
  | fuel + 1, t, k, fvs, stk => do
    match ← viewI t with
    | some (.forallE n ty body mb) => do
      let tyo ← instListRevM ty fvs
      let tty ← r.infer (d + k) tyo
      let wtty ← r.whnf (d + k) tty
      match ← viewI wtty with
      | some (.sort u) => do
        let fv ← internI (.fvar (d + k) n tyo)
        inferPisI r d fuel body (k + 1) (fvs.push fv)
          ((u, mb.pw) :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferPisLeafI mode r d t k fvs stk
  | 0, t, k, fvs, stk => inferPisLeafI mode r d t k fvs stk

/-- Twin of `inferBody`. -/
def inferBodyI (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → CheckIM EIdx :=
  fun depth e => do
    match ← viewI e with
    | some (.sort u) => do
      let su ← internLM (.succ u)
      internI (.sort su)
    | some (.fvar idx _ ty) =>
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | some (.const n us) => do
      let nm ← readbackNM n
      match fe.find? nm with
      | none => throw (.invalid s!"unknown constant {nm}")
      | some ci =>
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {nm}")
        constTyAtM fe n nm us
    | some (.lit (.natVal _)) => do
      if natLitSupportedF fe then do
        let ni ← internNameM natName
        internI (.const ni [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | some (.lit (.strVal _)) => do
      if strLitSupportedF fe then do
        let si ← internNameM stringName
        internI (.const si [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | some (.forallE n ty body mb) => do
      -- Binder-telescope loop (task #72 discipline; the codomain sort
      -- is inferred; task #161: each node's prop-ness annotation is
      -- validated against it in the rebuild fold).
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match ← viewI wtty with
      | some (.sort u) => do
        let fv ← internI (.fvar depth n ty)
        let fuel ← withStore (·.nodes.size)
        inferPisI mode r depth fuel body 1 #[fv] [(u, mb.pw)]
      | _ => throw (.invalid "expected a sort")
    | some (.lam n ty body mb) => do
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match ← viewI wtty with
      | some (.sort _) => do
        -- Binder-telescope loop (task #72): peel the whole λ-chain,
        -- open in bulk, rebuild with `abstractRange`.
        let fv ← internI (.fvar depth n ty)
        let fuel ← withStore (·.nodes.size)
        inferLamsI mode r depth fuel body 1 #[fv] [(n, ty, mb)]
      | _ => throw (.invalid "expected a sort")
    | some (.app _ _) => do
      -- Bulk telescope consumption (task #50): infer the spine head
      -- once and walk its Π-telescope against the whole spine.
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let tf ← r.infer depth h
      inferSpineI r fe depth tf #[] args
    | some (.proj _sn i pe) => do
      let tpe ← r.infer depth pe
      let te ← r.whnf depth tpe
      match ← withStore (fun st => st.getNode (st.getAppFnI te)) with
      | some (.const T us) => do
        let Tn ← readbackNM T
        match fe.findProj? Tn i with
        | some entry => do
          let targs ← withStore (·.getAppArgsI te)
          if entry.native ∧ targs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            let pf ← projFnIdxM T i
            let pty ← constTyAtM fe pf (projFnName Tn i) us
            -- Task #129: certify the type former's parameters against
            -- the entry's own telescope (twin of `projParamCert`).
            -- TT-lane check (task #147): skipped unless
            -- `mode.ttChecks`.
            unless ← (if mode.ttChecks then
                projParamCertI r fe depth pty targs
              else pure true) do
              throw (.invalid "projection parameter type mismatch")
            match ← piResidualM pty (targs ++ [pe]) with
            | some resTy => pure resTy
            | none => throw (.internal "malformed projection entry")
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | some (.letE _ ty v b) => do
      -- The official kernel's `infer_let` check order (`!infer_only`):
      -- the annotation is a type, the value's inferred type matches it,
      -- then the body with the value transparent (nanoda `infer_let`;
      -- task #100 stage 6: the checks moved here from the deleted
      -- annotation pass).
      let _ ← ensureSortI r depth (← r.infer depth ty)
      let tv ← r.infer depth v
      unless ← r.defeq depth tv ty do
        throw (.invalid "let value type mismatch")
      let e' ← inst1M b v
      r.infer depth e'
    | some (.bvar _) =>
      throw (.notImplemented "inferType beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- Twin of `defeqStep`. -/
def defeqStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : EIdx → EIdx → CheckIM Bool) (a b : EIdx) : CheckIM Bool := do
    if a == b then pure true else
    let a' ← r.whnfCore depth a
    let b' ← r.whnfCore depth b
    if a' == b' then pure true else
    -- proof irrelevance hoisted before lazy delta, as in the spec
    -- (and the official kernel)
    if ← proofIrrelI r fe depth a' b' then pure true else
    -- Literal folding only when both sides are fvar-free, mirroring
    -- the official kernel (`type_checker.cpp`, `lazy_delta_reduction`)
    -- and lean4lean (`TypeChecker.lean:782`); see `defeqBody` for the
    -- full rationale.  `hasFvarI` is an `O(1)` read of the eager
    -- per-node fvar-range array.
    let fold ← withStore fun st => !st.hasFvarI a' && !st.hasFvarI b'
    match ← (if fold then reduceNatI r fe depth a' else pure none) with
    | some a₂ => k a₂ b'
    | none =>
    match ← (if fold then reduceNatI r fe depth b' else pure none) with
    | some b₂ => k a' b₂
    | none =>
    -- lazy delta, decision before materialization; see `defeqBody`
    match ← withStore (fun st => unfoldableHeadI fe st a'),
        ← withStore (fun st => unfoldableHeadI fe st b') with
    | true, false =>
      match ← unfoldDefinitionI fe a' with
      | some a₂ => k a₂ b'
      | none => pure false
    | false, true =>
      match ← unfoldDefinitionI fe b' with
      | some b₂ => k a' b₂
      | none => pure false
    | true, true => do
      let ha ← withStore (fun st => headHintI fe st a')
      let hb ← withStore (fun st => headHintI fe st b')
      if ReducibilityHint.lt hb ha then
        match ← unfoldDefinitionI fe a' with
        | some a₂ => k a₂ b'
        | none => pure false
      else if ReducibilityHint.lt ha hb then
        match ← unfoldDefinitionI fe b' with
        | some b₂ => k a' b₂
        | none => pure false
      else if ReducibilityHint.sameRegular ha hb &&
          (← withStore (sameConstHeadsI · a' b')) then do
        if ← defeqSpineI r fe depth a' b' then pure true
        else
          match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
          | some a₂, some b₂ => k a₂ b₂
          | _, _ => pure false
      else
        match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
        | some a₂, some b₂ => k a₂ b₂
        | _, _ => pure false
    | false, false =>
    match ← viewI a', ← viewI b' with
    | some (.sort u), some (.sort v) => do
      liftFueled "level comparison" (← isEquivLM u v)
    | some (.lit l₁), some (.lit l₂) => pure (l₁ == l₂)
    | some (.lit (.natVal n)), some (.const c us) =>
      if (← beqNameM c natZeroName) ∧ us = [] then pure (n == 0)
      else stuckIrrelI mode r fe depth a' b'
    | some (.const c us), some (.lit (.natVal n)) =>
      if (← beqNameM c natZeroName) ∧ us = [] then pure (n == 0)
      else stuckIrrelI mode r fe depth a' b'
    | some (.lit (.natVal nn)), some (.app f x) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if ← beqNameM c natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth kl x
        else stuckIrrelI mode r fe depth a' b'
      | _, _ => stuckIrrelI mode r fe depth a' b'
    | some (.app f x), some (.lit (.natVal nn)) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if ← beqNameM c natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth x kl
        else stuckIrrelI mode r fe depth a' b'
      | _, _ => stuckIrrelI mode r fe depth a' b'
    | some (.lit (.strVal s)), some (.app fO _x) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if (← beqNameM cO stringOfListName) ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← internExprM (strLitToConstructor s)
          r.defeq depth sc b'
        else stuckIrrelI mode r fe depth a' b'
      | _ => stuckIrrelI mode r fe depth a' b'
    | some (.app fO _x), some (.lit (.strVal s)) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if (← beqNameM cO stringOfListName) ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← internExprM (strLitToConstructor s)
          r.defeq depth a' sc
        else stuckIrrelI mode r fe depth a' b'
      | _ => stuckIrrelI mode r fe depth a' b'
    | some (.fvar i _ _), some (.fvar j _ _) =>
      if i == j then pure true
      else stuckIrrelI mode r fe depth a' b'
    | some (.const n us), some (.const n' us') =>
      if n = n' then do
        if ← liftFueled "level comparison" (← isEquivListLM us us') then
          pure true
        else stuckIrrelI mode r fe depth a' b'
      else stuckIrrelI mode r fe depth a' b'
    | some (.forallE n₁ ty₁ body₁ m₁), some (.forallE n₂ ty₂ body₂ m₂) => do
      -- prop-ness agreement checked LAST (task #161); see `defeqBody`
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv₁ ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv₁
      let fv₂ ← internI (.fvar depth n₂ ty₂)
      let b₂ ← inst1M body₂ fv₂
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      if mode.verified && !(m₁.pw.equiv m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-forall)")
      pure true
    | some (.lam n₁ ty₁ body₁ m₁), some (.lam n₂ ty₂ body₂ m₂) => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv₁ ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv₁
      let fv₂ ← internI (.fvar depth n₂ ty₂)
      let b₂ ← inst1M body₂ fv₂
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      if mode.verified && !(m₁.pw.equiv m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-lam)")
      pure true
    | some (.app _f₁ _a₁), some (.app _f₂ _a₂) => do
      -- spine-wise congruence, as in the spec body `defeqBody`
      -- (official `is_def_eq_app`)
      let as₁ ← withStore (·.getAppArgsI a')
      let as₂ ← withStore (·.getAppArgsI b')
      if as₁.length = as₂.length then do
        let h₁ ← withStore (fun st => st.getAppFnI a')
        let h₂ ← withStore (fun st => st.getAppFnI b')
        if ← r.defeq depth h₁ h₂ then do
          if ← defEqListI r fe depth as₁ as₂ then pure true
          else stuckIrrelI mode r fe depth a' b'
        else stuckIrrelI mode r fe depth a' b'
      else stuckIrrelI mode r fe depth a' b'
    | some (.proj _s₁ i₁ e₁), some (.proj _s₂ i₂ e₂) => do
      if i₁ == i₂ then do
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrelI mode r fe depth a' b'
      else stuckIrrelI mode r fe depth a' b'
    | some (.lam n₁ ty₁ body₁ m₁), _ => do
      if ← etaCertI mode r fe depth n₁ ty₁ body₁ m₁ b' then pure true
      else stuckIrrelI mode r fe depth a' b'
    | _, some (.lam n₂ ty₂ body₂ m₂) => do
      if ← etaCertI mode r fe depth n₂ ty₂ body₂ m₂ a' then pure true
      else stuckIrrelI mode r fe depth a' b'
    | some _, some _ => stuckIrrelI mode r fe depth a' b'
    | _, _ => throw (.internal "interned node missing")

/-- Twin of `defeqLoop`. -/
def defeqLoopI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → EIdx → EIdx → CheckIM Bool
  | 0, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | fl + 1, a, b =>
    defeqStepI mode r fe depth (defeqLoopI r fe depth fl) a b

/-- Twin of `defeqBody`. -/
def defeqBodyI (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → EIdx → CheckIM Bool :=
  fun depth a b => defeqLoopI mode r fe depth defeqLoopFuel a b

/-- Twin of `isPropType`. -/
def isPropTypeI (r : CoreFnsI) (_fe : FEnv) (depth : Nat) (ty : EIdx) :
    CheckIM Bool := do
  let ty' ← r.annotate depth ty
  let tty ← r.infer depth ty'
  let s ← ensureSortI r depth tty
  let z ← internLM .zero
  liftFueled "level comparison" (← isEquivLM s z)

/-- Twin of `projFieldDom`. -/
def projFieldDomI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (structProp : Bool) (sn : NIdx) (e' : EIdx) :
    Nat → Nat → EIdx → CheckIM EIdx
  | _j, 0, tel => do
    match ← viewI tel with
    | some (.forallE _ dom _ _) => pure dom
    | _ => throw (.invalid "projection index out of range")
  | j, k + 1, tel => do
    match ← viewI tel with
    | some (.forallE _ dom rest _) => do
      if ← withStore (fun st => st.looseBVarsBoundedI 0 rest) then
        projFieldDomI r fe depth structProp sn e' (j + 1) k rest
      else do
        if structProp then do
          unless ← isPropTypeI r fe depth dom do
            throw (.invalid
              "projection through a non-Prop field of a Prop structure")
        let pj ← internI (.proj sn j e')
        let rest' ← inst1M rest pj
        projFieldDomI r fe depth structProp sn e' (j + 1) k rest'
    | _ => throw (.invalid "projection index out of range")

/-- Twin of `annotateProjRec`. -/
def annotateProjRecI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (entry : ProjEntry) (i : Nat) (te e' : EIdx) (us : List LIdx) :
    CheckIM EIdx := do
  match fe.find? entry.ctor with
  | some (.ctorInfo _cvC _ cnF) => do
    let params ← withStore (·.getAppArgsI te)
    if params.length = entry.numParams then do
      let ctorI ← internNameM entry.ctor
      let ctorTy ← constTyAtM fe ctorI entry.ctor us
      match ← piResidualM ctorTy params with
      | some tel => do
        let structProp ← isPropTypeI r fe depth te
        let snI ← internNameM entry.structName
        let fi ← projFieldDomI r fe depth structProp snI e'
          0 i tel
        let fieldBvar ← internI (.bvar (cnF - 1 - i))
        match ← pisToLamsM cnF tel fieldBvar with
        | some minor => do
          let fi' ← r.annotate depth fi
          let tfi ← r.infer depth fi'
          let sfi ← ensureSortI r depth tfi
          if structProp then do
            let z ← internLM .zero
            unless ← liftFueled "level comparison"
                (← isEquivLM sfi z) do
              throw (.invalid "non-Prop projection from a Prop structure")
          let uf := if entry.recExtraLevel then [sfi] else []
          let recI ← internNameM (entry.structName.str "rec")
          let recC ← internI (.const recI (uf ++ us))
          let tI ← internNameM (.str .anonymous "t")
          let motive ← internI
            (.lam tI te fi ⟨.default, .never⟩)
          let raw ← mkAppNM recC (params ++ [motive, minor, e'])
          if ← withStore (fun st => st.wscopedBI depth raw &&
              st.looseBVarsBoundedI 0 raw &&
              st.leafGuardI raw e') then
            r.annotate depth raw
          else throw (.notImplemented "projection elimination scoping")
        | none => throw (.invalid "projection index out of range")
      | none => throw (.invalid "projection index out of range")
    else throw (.notImplemented "projection parameter mismatch")
  | _ => throw (.notImplemented
      "projection constructor not stored")

/-- Twin of `annotateProjElim`. -/
def annotateProjElimI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (sn : NIdx)
    (i : Nat) (te e' : EIdx) : CheckIM EIdx := do
  match ← withStore (fun st => st.getNode (st.getAppFnI te)) with
  | some (.const T us) => do
    let Tn ← readbackNM T
    if T = sn then
      match fe.find? (projFnName Tn i) with
      | some (.recInfo _ _ rP _) => do
        let targs ← withStore (·.getAppArgsI te)
        if targs.length = rP then do
          let pf ← projFnIdxM T i
          let h ← internI (.const pf us)
          let raw ← mkAppNM h (targs ++ [e'])
          if ← withStore (fun st => st.wscopedBI depth raw &&
              st.looseBVarsBoundedI 0 raw &&
              st.leafGuardI raw e') then
            r.annotate depth raw
          else throw (.notImplemented "projection elimination scoping")
        else throw (.notImplemented "projection parameter mismatch")
      | some (.projInfo entry) =>
        if entry.native then
          throw (.internal "native projection entry reached the fallback")
        else annotateProjRecI r fe depth entry i te e' us
      | _ =>
        throw (if (fe.find? (projFnName Tn 0)).isSome then
            CheckError.invalid "projection index out of range"
          else .notImplemented "projection on a non-structure-like type")
    else throw (.invalid "projection structure mismatch")
  | _ => throw (.notImplemented "projection on a non-structure type")

/-! ### Annotation binder-telescope loops (task #72; see the
`inferLamsI` block comment) -/

/-- Stack entry of the annotation loops: binder name, annotated opened
domain, binder info. -/
abbrev AnnotBinderEntry := NIdx × EIdx × IBinderMeta

/-- Rebuild loop of the annotation binder-telescope loops: fold the
stack (innermost binder first, `j` its binder level), rebuilding one
binder node per entry.

Task #161 P5 — the untrusted write: `pw?` is the telescope's datum,
computed once in the leaf phase and shared by every node of the
telescope (`zeronessOf (imax u v) = zeronessOf v` makes every ∀ node's
codomain-sort zero-ness the leaf's; the λ chain rule makes every λ
node's datum the innermost one's).  `none` = no write (unverified
mode).  A node whose input datum is a real annotation (`pwWritten`) is
left alone — validation judges it. -/
def annotateBindersOutI (mk : NIdx → EIdx → EIdx → IBinderMeta → ENode)
    (d : Nat) (pw? : Option PropWhen) :
    List AnnotBinderEntry → Nat → EIdx → CheckIM EIdx
  | [], _j, cur => pure cur
  | (n, ty', mb) :: rest, j, cur => do
    let tyAbs ← abstractRangeM ty' d j
    let mb : IBinderMeta :=
      match pw? with
      | some pw => if pwWritten mb.pw then mb else ⟨mb.bi, pw⟩
      | none => mb
    let node ← internI (mk n tyAbs cur mb)
    annotateBindersOutI mk d pw? rest (j - 1) node

/-- Leaf phase of `annotatePisI`: bulk-open and annotate the residual
body, then rebuild outward. -/
def annotatePisLeafI (r : CoreFnsI) (d : Nat) (t : EIdx) (k : Nat)
    (fvs : Array EIdx) (stk : List AnnotBinderEntry) : CheckIM EIdx := do
  let to ← instListRevM t fvs
  let leaf' ← r.annotate (d + k) to
  -- Task #161 P5: the telescope's datum — the leaf codomain sort's
  -- zero-ness, shared by every node (`zeronessOf (imax u v) =
  -- zeronessOf v`).  One inference per telescope, memo-shared with the
  -- front-door sweep that validates it.
  let pw? ← if mode.verified then do
      let bt ← r.infer (d + k) leaf'
      let wbt ← r.whnf (d + k) bt
      match ← viewI wbt with
      | some (.sort v) => do
        let pv ← withStore fun st => (st.zeronessOfLIGo {} v).1
        pure (some pv)
      | _ => throw (.invalid "expected a sort")
    else pure none
  let cur ← abstractRangeM leaf' d k
  annotateBindersOutI (fun n ty b mb => .forallE n ty b mb) d pw?
    stk (k - 1) cur

/-- ∀-telescope annotation loop (task #72; `annotateBodyI`'s forallE
case): peel the raw ∀-chain, annotating each opened domain on the way
in.  `k ≥ 1` counts the opened binders (first binder peeled inline by
the caller), `fvs` their free variables innermost-first. -/
def annotatePisI (r : CoreFnsI) (d : Nat) :
    Nat → EIdx → Nat → Array EIdx → List AnnotBinderEntry → CheckIM EIdx
  | fuel + 1, t, k, fvs, stk => do
    match ← viewI t with
    | some (.forallE n ty body mb) => do
      let tyo ← instListRevM ty fvs
      let ty' ← r.annotate (d + k) tyo
      let fv ← internI (.fvar (d + k) n ty')
      annotatePisI r d fuel body (k + 1) (fvs.push fv)
        ((n, ty', mb) :: stk)
    | _ => annotatePisLeafI mode r d t k fvs stk
  | 0, t, k, fvs, stk => annotatePisLeafI mode r d t k fvs stk

/-- Leaf phase of `annotateLamsI` (as `annotatePisLeafI`, rebuilding
λ-nodes). -/
def annotateLamsLeafI (r : CoreFnsI) (d : Nat) (t : EIdx) (k : Nat)
    (fvs : Array EIdx) (stk : List AnnotBinderEntry) : CheckIM EIdx := do
  let to ← instListRevM t fvs
  let leaf' ← r.annotate (d + k) to
  -- Task #161 P5: the chain's datum — the zero-ness of the sort of the
  -- innermost body's TYPE; every λ node of the chain shares it (the
  -- `(lam-cod-chain)` rule).  A λ residual (the fuel path) supplies its
  -- own already-written datum, exactly as `inferLamsLeafI` reads it.
  let pw? ← if mode.verified then do
      match ← viewI leaf' with
      | some (.lam _ _ _ mbT) => pure (some mbT.pw)
      | _ => do
        let bt ← r.infer (d + k) leaf'
        let btt ← r.infer (d + k) bt
        let wbtt ← r.whnf (d + k) btt
        match ← viewI wbtt with
        | some (.sort vb) => do
          let pv ← withStore fun st => (st.zeronessOfLIGo {} vb).1
          pure (some pv)
        | _ => throw (.invalid "expected a sort")
    else pure none
  let cur ← abstractRangeM leaf' d k
  annotateBindersOutI (fun n ty b mb => .lam n ty b mb) d pw?
    stk (k - 1) cur

/-- λ-telescope annotation loop (task #72; `annotateBodyI`'s lam
case). -/
def annotateLamsI (r : CoreFnsI) (d : Nat) :
    Nat → EIdx → Nat → Array EIdx → List AnnotBinderEntry → CheckIM EIdx
  | fuel + 1, t, k, fvs, stk => do
    match ← viewI t with
    | some (.lam n ty body mb) => do
      let tyo ← instListRevM ty fvs
      let ty' ← r.annotate (d + k) tyo
      let fv ← internI (.fvar (d + k) n ty')
      annotateLamsI r d fuel body (k + 1) (fvs.push fv)
        ((n, ty', mb) :: stk)
    | _ => annotateLamsLeafI mode r d t k fvs stk
  | 0, t, k, fvs, stk => annotateLamsLeafI mode r d t k fvs stk

/-- Twin of `annotateBody`. -/
def annotateBodyI (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → CheckIM EIdx :=
  fun depth e => do
    match ← viewI e with
    | some (.bvar _) => pure e
    | some (.fvar idx _ _) =>
      if idx < depth then pure e
      else throw (.invalid "free variable out of scope")
    | some (.sort _) => pure e
    | some (.const ..) => pure e
    | some (.lit (.natVal _)) => do
      if natLitSupportedF fe then pure e
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | some (.lit (.strVal _)) => do
      if strLitSupportedF fe then pure e
      else throw (.notImplemented
        "string literals before the String support declarations")
    | some (.app f a) => do
      -- structural (task #100 stage 6: the application checks moved to
      -- the driver's inference sweep)
      let f' ← r.annotate depth f
      let a' ← r.annotate depth a
      internI (.app f' a')
    | some (.forallE n ty body mb) => do
      -- Binder-telescope loop (task #72): peel the whole ∀-chain,
      -- open in bulk, rebuild with `abstractRange`.
      let ty' ← r.annotate depth ty
      let fv ← internI (.fvar depth n ty')
      let fuel ← withStore (·.nodes.size)
      annotatePisI mode r depth fuel body 1 #[fv] [(n, ty', mb)]
    | some (.lam n ty body mb) => do
      -- The λ-loop is chain-identical only on bvar-closed nodes (the
      -- chained tails re-open exactly what they closed); disciplined
      -- inputs always are, and the cached bound decides in O(1).
      if (← bvarBoundM e) = 0 then do
        let ty' ← r.annotate depth ty
        let fv ← internI (.fvar depth n ty')
        let fuel ← withStore (·.nodes.size)
        annotateLamsI mode r depth fuel body 1 #[fv] [(n, ty', mb)]
      else do
        let ty' ← r.annotate depth ty
        let fv ← internI (.fvar depth n ty')
        let ob ← inst1M body fv
        let body' ← r.annotate (depth + 1) ob
        let bAbs ← abstract1M body' depth
        -- task #161 P5: the single-binder write (the λ-loop's rule at
        -- a chain of length one; see `annotateLamsLeafI`)
        let pw ← if mode.verified && !pwWritten mb.pw then do
            match ← viewI body' with
            | some (.lam _ _ _ mbI) => pure mbI.pw
            | _ => do
              let bt ← r.infer (depth + 1) body'
              let btt ← r.infer (depth + 1) bt
              let wbtt ← r.whnf (depth + 1) btt
              match ← viewI wbtt with
              | some (.sort vb) =>
                withStore fun st => (st.zeronessOfLIGo {} vb).1
              | _ => throw (.invalid "expected a sort")
          else pure mb.pw
        internI (.lam n ty' bAbs ⟨mb.bi, pw⟩)
    | some (.letE _ ty v b) => do
      -- official `infer_let` check order (see the spec body): the
      -- annotation is a type, the value's inferred type matches it,
      -- then the body with the value transparent (zeta at annotate;
      -- `inst1M` keeps the substitution sharing-preserving)
      let ty' ← r.annotate depth ty
      let tty ← r.infer depth ty'
      let _ ← ensureSortI r depth tty
      let v' ← r.annotate depth v
      let tv ← r.infer depth v'
      unless ← r.defeq depth tv ty' do
        throw (.invalid "let value type mismatch")
      let ob ← inst1M b v
      r.annotate depth ob
    | some (.proj sn i pe) => do
      let e' ← r.annotate depth pe
      let tpe ← r.infer depth e'
      let te ← r.whnf depth tpe
      match ← withStore (fun st => st.getNode (st.getAppFnI te)) with
      | some (.const T _) => do
        let Tn ← readbackNM T
        match fe.findProj? Tn i with
        | some entry =>
          if entry.native then do
            let targs ← withStore (·.getAppArgsI te)
            unless targs.length = entry.numParams do
              throw (.invalid "projection parameter mismatch")
            internI (.proj T i e')
          else annotateProjElimI r fe depth sn i te e'
        | none => annotateProjElimI r fe depth sn i te e'
      | _ => annotateProjElimI r fe depth sn i te e'
    | none => throw (.internal "interned node missing")

/-! ## The interned memoized knot -/

/-- Memoize a unary interned entry point under its index (`O(1)` key). -/
def memoEI (get' : IState → Std.HashMap EIdx EIdx)
    (set' : IState → Std.HashMap EIdx EIdx → IState)
    (f : Nat → EIdx → CheckIM EIdx) : Nat → EIdx → CheckIM EIdx :=
  fun d e => do
    match (get' (← get))[e]? with
    | some r => pure r
    | none =>
      let r ← f d e
      modify fun st =>
          let mp := get' st
        let st := set' st ∅
        set' st (mp.insert e r)
      pure r

/-- Memoize the interned definitional-equality entry point under the
index pair. -/
def memoBI (f : Nat → EIdx → EIdx → CheckIM Bool) :
    Nat → EIdx → EIdx → CheckIM Bool :=
  fun d a b => do
    match (← get).defeqC[(a, b)]? with
    | some r => pure r
    | none =>
      let r ← f d a b
      modify fun st =>
        let mp := st.defeqC
        let st := { st with defeqC := ∅ }
        { st with defeqC := mp.insert (a, b) r }
      pure r

/-- Tie the interned bodies at the memoizing state monad (fuel only
here, as in `coreKnot`; levels built lazily). -/
def coreKnotI (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate") }
  | fuel + 1 =>
    { whnfCore := memoEI (·.whnfCoreC)
        (fun st mp => { st with whnfCoreC := mp })
        (fun d e => whnfCoreBodyI mode (coreKnotI fe fuel) fe d e)
      whnf := memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
        (fun d e => whnfBodyI (coreKnotI fe fuel) fe d e)
      infer := memoEI (·.inferC) (fun st mp => { st with inferC := mp })
        (fun d e => inferBodyI mode (coreKnotI fe fuel) fe d e)
      defeq := memoBI
        (fun d a b => defeqBodyI mode (coreKnotI fe fuel) fe d a b)
      annotate := memoEI (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI mode (coreKnotI fe fuel) fe d e) }

/-! ## Entry runners

Each entry interns its argument into a fresh arena, runs the interned
knot, and reads the result back (`readbackI`, memoized so the rebuilt
tree shares subterms in memory).  State lifetime = one entry call,
exactly like the Expr-level `KCache`.  The `CheckerOps` record over
these lives in `Setlec/Kernel/Checker.lean`. -/

/-- Run a unary interned entry point on an `Expr`. -/
def runEntryE (env : Env)
    (pick : CoreFnsI → Nat → EIdx → CheckIM EIdx)
    (d : Nat) (e : Expr) : CheckM Expr := do
  let fe := mkFEnv env
  let (i, store) := EStore.empty.internExpr e
  let (j, s) ← (pick (coreKnotI mode fe checkFuel) d i).run { store := store }
  match s.store.readbackI j with
  | some v => pure v
  | none => throw (.internal "interned readback failed")

/-- Run the interned definitional-equality entry on two `Expr`s. -/
def runEntryB (env : Env) (d : Nat) (a b : Expr) : CheckM Bool := do
  let fe := mkFEnv env
  let (i, store) := EStore.empty.internExpr a
  let (j, store) := store.internExpr b
  ((coreKnotI mode fe checkFuel).defeq d i j).run' { store := store }

/-- Run the interned sort-ensuring entry on an `Expr`. -/
def runEntryS (env : Env) (d : Nat) (e : Expr) : CheckM Level := do
  let fe := mkFEnv env
  let (i, store) := EStore.empty.internExpr e
  let (u, s) ←
    (ensureSortI (coreKnotI mode fe checkFuel) d i).run { store := store }
  match s.store.readbackL u with
  | some l => pure l
  | none => throw (.internal "interned level readback failed")

end Setlec
