module

public import ConLeche.Cached.ExprNodes
public import ConLeche.Kernel.Core

@[expose] public section

/-!
# The cached syntactic operations on `Expr`

The **executed** counterparts of the arena operations in
`ConLeche/Kernel/IExpr.lean` — same clauses, same memo discipline, same
cutoffs; the mechanism differs only in where the derived data lives (a
field of the node instead of a parallel array indexed by the node's
arena position) and in how a rebuilt node is obtained (allocation
instead of a cons-table probe).

Two structural consequences of dropping the arena, both load-bearing
for the pilot's numbers:

* every traversal memo is keyed on `Expr` itself (`O(1)` hashing off
  the cached field, pointer-first equality), so shared sub-DAGs are
  still visited once — a `Std.HashMap Expr α` replaces the arena's
  `Std.HashMap EIdx α` one for one;
* a cutoff (`bvarB ≤ d`, `fvarB ≤ d`, `!hasLP`) returns the node
  **itself**, so the result shares memory with the input and later
  pointer comparisons on it are `O(1)` — the analogue of the arena
  returning the same index.

## The memo discipline of the substitution walks (task #177)

The retired arena's memo key was an `EIdx` — a scalar.  This tier's is
a *constructed* key, so the probe costs allocations, and profiling put
`instantiate*Go`/`abstract*Go` plus their `Std.DHashMap` spec sites at
roughly half of every `--trusted` run.  Three shape rules cut that,
and each is a property of the walks alone (the values are unchanged —
`ConLeche/Verify/Cached/OpsC.lean` proves each walk equal to its
`ConLeche.Expr` counterpart exactly as before):

1. **The key is built once per node.**  `let key := …` is shared by the
   probe and the insert, instead of the same tuple being allocated for
   each.
2. **The bulk key carries no live prefix.**  `k` is invariant over the
   life of a table (see `MemoNL`), so it moved from the key into the
   memo *invariant* (`MemoLInv ws k memo`), and the `bvar` arm's
   re-entry — the one place `k` shrinks — runs under a fresh table.
3. **Only compound nodes are memoized.**  The memo probe and insert sit
   inside the `app`/`lam`/`forallE`/`letE`/`proj` arms; a node with no
   children to descend into is answered on the spot.  This matters most
   for the loose `bvar`s, which the cutoff lets through by
   construction and which are the most numerous nodes a substitution
   touches — recording a one-word answer under a two-word key was pure
   loss.  It is why the arms carry the probe rather than the head of
   the function.
-/

namespace ConLeche.Expr

/-! ## Spines -/

/-- Prepend the spine arguments of `e` to `acc` (outermost last). -/
def getAppArgsAccC : Expr → List Expr → List Expr
  | .app f a .., acc => getAppArgsAccC f (a :: acc)
  | _, acc => acc

/-- The arguments of an application spine, outermost last. -/
@[inline] def getAppArgsC (e : Expr) : List Expr := getAppArgsAccC e []

/-! ## Instantiation -/

/-- Memo table for cursored node→node traversals. -/
abbrev MemoN := Std.HashMap (Expr × Nat) Expr

/-- Memo table for the bulk traversals (node, cursor).

**The live prefix `k` is not part of the key.**  It is constant for the
whole life of one table: the only place `k` changes is the `bvar` arm's
re-entry at a replacement, and that re-entry runs under a *fresh*
table.  Dropping it halves the key — `(Expr × Nat × Nat)` is two
`Prod` allocations per probe, `(Expr × Nat)` is one. -/
abbrev MemoNL := Std.HashMap (Expr × Nat) Expr

/-- Core of `instantiate1C` (nodes whose cached bound is at or below the
cursor are returned unchanged; compound nodes are memoized, atoms are
answered in place — see this module's memo discipline). -/
def instantiate1GoC (v : Expr) (memo : MemoN) (e : Expr) (d : Nat) :
    Expr × MemoN :=
  if e.bvarB ≤ d then (e, memo) else
  match e with
  | .bvar i .. =>
    (if i = d then v else if i > d then Expr.mkBvar (i - 1) else e, memo)
  | .fvar .. | .sort .. | .const .. | .lit .. => (e, memo)
  | .app f a .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (f', memo) := instantiate1GoC v memo f d
      let (a', memo) := instantiate1GoC v memo a d
      let r := mkApp f' a'
      (r, memo.insert key r)
  | .lam ty body m .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := instantiate1GoC v memo ty d
      let (b', memo) := instantiate1GoC v memo body (d + 1)
      let r := mkLam ty' b' m
      (r, memo.insert key r)
  | .forallE ty body m .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := instantiate1GoC v memo ty d
      let (b', memo) := instantiate1GoC v memo body (d + 1)
      let r := mkForallE ty' b' m
      (r, memo.insert key r)
  | .letE ty val body .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := instantiate1GoC v memo ty d
      let (v', memo) := instantiate1GoC v memo val d
      let (b', memo) := instantiate1GoC v memo body (d + 1)
      let r := mkLetE ty' v' b'
      (r, memo.insert key r)
  | .proj sn i sub .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (s', memo) := instantiate1GoC v memo sub d
      let r := mkProj sn i s'
      (r, memo.insert key r)

/-! ### `instantiate1LiftC` (task #214, P4)

The capture-avoiding substitution `Expr.instantiate1Lift` — the one
substitution on the direct install's executed path with no memoised
twin: `structProjBodies` runs it once per field over the constructor
telescope, turning a DAG-shared field type into an unshared tree each
time.  The twin has the `bvarB` cutoff (a node bounded at or below the
cursor is returned unchanged), a BUDGETED plain descent first (4096
nodes, allocation-free of any memo table — the memo would be a tax on
the small terms that are the common case, cf. the +33 % an
unconditional instantiate memo cost on init-prelude), and the memoised
descent only past the budget.  `instantiate1LiftC_spec`
(`ConLeche/Verify/Cached/OpsC.lean`) reads it as `Expr.instantiate1Lift`. -/

/-- The budgeted descent: the plain rebuild on a node budget, `none`
when it runs out (nothing built is kept). -/
def instantiate1LiftBC (v : Expr) (fuel : Nat) (e : Expr) (d : Nat) : Option Expr × Nat :=
  if e.bvarB ≤ d then (some e, fuel) else
  match fuel, e with
  | _, .bvar i .. =>
    (some (if i = d then Expr.liftLooseBVars d 0 v else if i > d then Expr.mkBvar (i - 1) else e),
      fuel)
  | _, .fvar .. | _, .sort .. | _, .const .. | _, .lit .. => (some e, fuel)
  | 0, _ => (none, 0)
  | fuel + 1, .app f a .. =>
    match instantiate1LiftBC v fuel f d with
    | (some f', fuel) =>
      match instantiate1LiftBC v fuel a d with
      | (some a', fuel) => (some (mkApp f' a'), fuel)
      | r => r
    | r => r
  | fuel + 1, .lam ty body m .. =>
    match instantiate1LiftBC v fuel ty d with
    | (some ty', fuel) =>
      match instantiate1LiftBC v fuel body (d + 1) with
      | (some b', fuel) => (some (mkLam ty' b' m), fuel)
      | r => r
    | r => r
  | fuel + 1, .forallE ty body m .. =>
    match instantiate1LiftBC v fuel ty d with
    | (some ty', fuel) =>
      match instantiate1LiftBC v fuel body (d + 1) with
      | (some b', fuel) => (some (mkForallE ty' b' m), fuel)
      | r => r
    | r => r
  | fuel + 1, .letE ty val body .. =>
    match instantiate1LiftBC v fuel ty d with
    | (some ty', fuel) =>
      match instantiate1LiftBC v fuel val d with
      | (some v', fuel) =>
        match instantiate1LiftBC v fuel body (d + 1) with
        | (some b', fuel) => (some (mkLetE ty' v' b'), fuel)
        | r => r
      | r => r
    | r => r
  | fuel + 1, .proj sn i sub .. =>
    match instantiate1LiftBC v fuel sub d with
    | (some s', fuel) => (some (mkProj sn i s'), fuel)
    | r => r

/-- The memoised descent, in `instantiate1GoC`'s shape. -/
def instantiate1LiftGoC (v : Expr) (memo : MemoN) (e : Expr) (d : Nat) :
    Expr × MemoN :=
  if e.bvarB ≤ d then (e, memo) else
  match e with
  | .bvar i .. =>
    (if i = d then Expr.liftLooseBVars d 0 v else if i > d then Expr.mkBvar (i - 1) else e, memo)
  | .fvar .. | .sort .. | .const .. | .lit .. => (e, memo)
  | .app f a .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (f', memo) := instantiate1LiftGoC v memo f d
      let (a', memo) := instantiate1LiftGoC v memo a d
      let r := mkApp f' a'
      (r, memo.insert key r)
  | .lam ty body m .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := instantiate1LiftGoC v memo ty d
      let (b', memo) := instantiate1LiftGoC v memo body (d + 1)
      let r := mkLam ty' b' m
      (r, memo.insert key r)
  | .forallE ty body m .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := instantiate1LiftGoC v memo ty d
      let (b', memo) := instantiate1LiftGoC v memo body (d + 1)
      let r := mkForallE ty' b' m
      (r, memo.insert key r)
  | .letE ty val body .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := instantiate1LiftGoC v memo ty d
      let (v', memo) := instantiate1LiftGoC v memo val d
      let (b', memo) := instantiate1LiftGoC v memo body (d + 1)
      let r := mkLetE ty' v' b'
      (r, memo.insert key r)
  | .proj sn i sub .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (s', memo) := instantiate1LiftGoC v memo sub d
      let r := mkProj sn i s'
      (r, memo.insert key r)

/-- The cached `Expr.instantiate1Lift`: the cutoff, the budgeted plain
descent, the memoised one past the budget. -/
def instantiate1LiftC (e v : Expr) (d : Nat := 0) : Expr :=
  if e.bvarB ≤ d then e else
  match instantiate1LiftBC v 4096 e d with
  | (some r, _) => r
  | (none, _) => (instantiate1LiftGoC v {} e d).1

/-! ### The budgeted plain descent (task #313)

Every substitution walk below runs in two stages: a PLAIN rebuild on
a node budget first — no memo table, no key allocation, no bucket
probe — and the memoised walk above only when the budget runs out,
from scratch.  The budget is a fuel threaded through the result pair:
a compound node needs at least two units and hands one fewer to its
children, a leaf hands its fuel back unchanged, and a returned fuel of
`0` means the descent was abandoned (the `Expr` beside it is then
meaningless).  The invariant that makes `0` an unambiguous signal: a
completed descent always returns fuel `≥ 1`, because every child of a
node that proceeds receives `≥ 1` and a leaf returns what it received.
So the result carries no `Option` — one `Prod` per node, which the
compiler's reset/reuse recycles up the spine — and the wrapper reads
success off the scalar.

Why a budget rather than a memo always: the memo's whole cost — the
`(Expr × Nat)` key, the bucket cons cell, the rehash from an
eight-bucket table at every β — is paid per node whether or not any
node is shared, and the day-one profile put it at 7 % of `init-full`
and 38 % of `app-lam`.  What the plain descent gives up is sharing: a
subterm reached twice under the cursor is rebuilt twice, and the
copies are distinct objects downstream — every later memo probe on
them is a structural `beq` instead of a pointer hit, and every later
walk visits both.  The budget bounds that loss to `walkBudget` rebuilt
nodes per walk, and a walk that exceeds it is RESTARTED under the memo
rather than continued: the alternative (switching to the memo
mid-walk, which keeps the plain part) was measured and lost — it
keeps the duplicated prefix, and on `app-lam` that compounds to 7×
at a 32 768 budget where the restart costs 0.6 % — see the task #313
record (DESIGN.md), which also holds the budget sweep the value below
comes from: a LARGE budget loses on every sharing-heavy stream.  The
restarted walk begins on a table pre-sized to the budget, since the
term is by then known to be at least that large. -/

/-- Node budget of the plain descent before a memo table is built. -/
def walkBudget : Nat := 256

/-- The memo table a walk restarts on after its budget ran out:
pre-sized to the budget. -/
@[inline] def memoAfterBudget : MemoN :=
  Std.HashMap.emptyWithCapacity walkBudget

/-- The budgeted plain descent of `instantiate1C` (see the section
docstring for the fuel convention). -/
def instantiate1BC (v : Expr) (fuel : Nat) (e : Expr) (d : Nat) : Expr × Nat :=
  if e.bvarB ≤ d then (e, fuel) else
  match e with
  | .bvar i .. =>
    (if i = d then v else if i > d then Expr.mkBvar (i - 1) else e, fuel)
  | .fvar .. | .sort .. | .const .. | .lit .. => (e, fuel)
  | .app f a .. =>
    if fuel < 2 then (e, 0) else
    let (f', fuel) := instantiate1BC v (fuel - 1) f d
    if fuel = 0 then (e, 0) else
    let (a', fuel) := instantiate1BC v fuel a d
    if fuel = 0 then (e, 0) else (mkApp f' a', fuel)
  | .lam ty body m .. =>
    if fuel < 2 then (e, 0) else
    let (ty', fuel) := instantiate1BC v (fuel - 1) ty d
    if fuel = 0 then (e, 0) else
    let (b', fuel) := instantiate1BC v fuel body (d + 1)
    if fuel = 0 then (e, 0) else (mkLam ty' b' m, fuel)
  | .forallE ty body m .. =>
    if fuel < 2 then (e, 0) else
    let (ty', fuel) := instantiate1BC v (fuel - 1) ty d
    if fuel = 0 then (e, 0) else
    let (b', fuel) := instantiate1BC v fuel body (d + 1)
    if fuel = 0 then (e, 0) else (mkForallE ty' b' m, fuel)
  | .letE ty val body .. =>
    if fuel < 2 then (e, 0) else
    let (ty', fuel) := instantiate1BC v (fuel - 1) ty d
    if fuel = 0 then (e, 0) else
    let (v', fuel) := instantiate1BC v fuel val d
    if fuel = 0 then (e, 0) else
    let (b', fuel) := instantiate1BC v fuel body (d + 1)
    if fuel = 0 then (e, 0) else (mkLetE ty' v' b', fuel)
  | .proj sn i sub .. =>
    if fuel < 2 then (e, 0) else
    let (s', fuel) := instantiate1BC v (fuel - 1) sub d
    if fuel = 0 then (e, 0) else (mkProj sn i s', fuel)

/-- The cached `Expr.instantiate1`: the cutoff, the budgeted plain
descent, the memoised walk past the budget. -/
def instantiate1C (e v : Expr) (d : Nat := 0) : Expr :=
  if e.bvarB ≤ d then e else
  let (r, fuel) := instantiate1BC v walkBudget e d
  if fuel ≠ 0 then r else (instantiate1GoC v memoAfterBudget e d).1

/-- Core of `instantiateListC` (task #50): `vs` innermost binder first,
`k` the live prefix length.

Not structural (the `bvar` arm re-enters at the replacement with the
shorter prefix `i - d`), so it carries the arena twin's lexicographic
measure `(k, sizeOf e)`: the subterm calls keep `k`, the `bvar` call
decreases it.  The prefix test is written as a dependent `if` — as in
`instantiateListIGo` — only to put `i - d < k` in scope for that
obligation; `dite` on the same `Decidable Nat.lt` instance compiles to
the same code as the `ite` did.

The re-entry runs under a **fresh** memo (that is what keeps `k` out of
the key, see `MemoNL`) and is guarded: a replacement that is closed at
the cursor, or a zero-length residual prefix, is its own instantiation,
so the common case — the checker substitutes `fvar`s — allocates no
table at all. -/
def instantiateListGoC (vs : Array Expr) (memo : MemoNL)
    (e : Expr) (k : Nat) (d : Nat) : Expr × MemoNL :=
  if k = 0 then (e, memo)
  else if e.bvarB ≤ d then (e, memo)
  else
    match e with
    | .bvar i .. =>
      if i < d then (e, memo)
      else if _h : i - d < k then
        if h : i - d < vs.size then
          let w := vs[i - d]
          if i - d = 0 || w.bvarB ≤ d then (w, memo)
          else ((instantiateListGoC vs {} w (i - d) d).1, memo)
        else (e, memo)
      else (Expr.mkBvar (i - k), memo)
    | .fvar .. | .sort .. | .const .. | .lit .. => (e, memo)
    | .app f a .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (f', memo) := instantiateListGoC vs memo f k d
        let (a', memo) := instantiateListGoC vs memo a k d
        let r := mkApp f' a'
        (r, memo.insert key r)
    | .lam ty body m .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateListGoC vs memo ty k d
        let (b', memo) := instantiateListGoC vs memo body k (d + 1)
        let r := mkLam ty' b' m
        (r, memo.insert key r)
    | .forallE ty body m .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateListGoC vs memo ty k d
        let (b', memo) := instantiateListGoC vs memo body k (d + 1)
        let r := mkForallE ty' b' m
        (r, memo.insert key r)
    | .letE ty val body .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateListGoC vs memo ty k d
        let (v', memo) := instantiateListGoC vs memo val k d
        let (b', memo) := instantiateListGoC vs memo body k (d + 1)
        let r := mkLetE ty' v' b'
        (r, memo.insert key r)
    | .proj sn i sub .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (s', memo) := instantiateListGoC vs memo sub k d
        let r := mkProj sn i s'
        (r, memo.insert key r)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

/-- The budgeted plain descent of `instantiateListC` (task #313; the
fuel convention of `instantiate1BC`).  The `bvar` arm's re-entry at a
replacement continues on the same fuel — it is one walk's budget. -/
def instantiateListBC (vs : Array Expr) (fuel : Nat)
    (e : Expr) (k : Nat) (d : Nat) : Expr × Nat :=
  if k = 0 then (e, fuel)
  else if e.bvarB ≤ d then (e, fuel)
  else
    match e with
    | .bvar i .. =>
      if i < d then (e, fuel)
      else if _h : i - d < k then
        if h : i - d < vs.size then
          let w := vs[i - d]
          if i - d = 0 || w.bvarB ≤ d then (w, fuel)
          else instantiateListBC vs fuel w (i - d) d
        else (e, fuel)
      else (Expr.mkBvar (i - k), fuel)
    | .fvar .. | .sort .. | .const .. | .lit .. => (e, fuel)
    | .app f a .. =>
      if fuel < 2 then (e, 0) else
      let (f', fuel) := instantiateListBC vs (fuel - 1) f k d
      if fuel = 0 then (e, 0) else
      let (a', fuel) := instantiateListBC vs fuel a k d
      if fuel = 0 then (e, 0) else (mkApp f' a', fuel)
    | .lam ty body m .. =>
      if fuel < 2 then (e, 0) else
      let (ty', fuel) := instantiateListBC vs (fuel - 1) ty k d
      if fuel = 0 then (e, 0) else
      let (b', fuel) := instantiateListBC vs fuel body k (d + 1)
      if fuel = 0 then (e, 0) else (mkLam ty' b' m, fuel)
    | .forallE ty body m .. =>
      if fuel < 2 then (e, 0) else
      let (ty', fuel) := instantiateListBC vs (fuel - 1) ty k d
      if fuel = 0 then (e, 0) else
      let (b', fuel) := instantiateListBC vs fuel body k (d + 1)
      if fuel = 0 then (e, 0) else (mkForallE ty' b' m, fuel)
    | .letE ty val body .. =>
      if fuel < 2 then (e, 0) else
      let (ty', fuel) := instantiateListBC vs (fuel - 1) ty k d
      if fuel = 0 then (e, 0) else
      let (v', fuel) := instantiateListBC vs fuel val k d
      if fuel = 0 then (e, 0) else
      let (b', fuel) := instantiateListBC vs fuel body k (d + 1)
      if fuel = 0 then (e, 0) else (mkLetE ty' v' b', fuel)
    | .proj sn i sub .. =>
      if fuel < 2 then (e, 0) else
      let (s', fuel) := instantiateListBC vs (fuel - 1) sub k d
      if fuel = 0 then (e, 0) else (mkProj sn i s', fuel)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

/-- The cached `Expr.instantiateList` (bulk): the budgeted plain
descent, the memoised DAG pass past the budget. -/
def instantiateListC (e : Expr) (vs : List Expr) (d : Nat := 0) : Expr :=
  match vs with
  | [] => e
  | _ :: _ =>
    let a := vs.toArray
    let (r, fuel) := instantiateListBC a walkBudget e a.size d
    if fuel ≠ 0 then r else (instantiateListGoC a memoAfterBudget e a.size d).1

/-- Core of `instantiateRev`: as `instantiateListGoC`, but the
replacement array holds the innermost binder **last** (the binder
loops' push order — lean4lean's `instantiateRev`).  Same
`(k, sizeOf e)` measure, same dependent prefix test. -/
def instantiateRevGo (vs : Array Expr) (memo : MemoNL)
    (e : Expr) (k : Nat) (d : Nat) : Expr × MemoNL :=
  if k = 0 then (e, memo)
  else if e.bvarB ≤ d then (e, memo)
  else
    match e with
    | .bvar i .. =>
      if i < d then (e, memo)
      else if _h : i - d < k then
        if h : i - d < vs.size then
          let w := vs[vs.size - 1 - (i - d)]'(by omega)
          if i - d = 0 || w.bvarB ≤ d then (w, memo)
          else ((instantiateRevGo vs {} w (i - d) d).1, memo)
        else (e, memo)
      else (Expr.mkBvar (i - k), memo)
    | .fvar .. | .sort .. | .const .. | .lit .. => (e, memo)
    | .app f a .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (f', memo) := instantiateRevGo vs memo f k d
        let (a', memo) := instantiateRevGo vs memo a k d
        let r := mkApp f' a'
        (r, memo.insert key r)
    | .lam ty body m .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateRevGo vs memo ty k d
        let (b', memo) := instantiateRevGo vs memo body k (d + 1)
        let r := mkLam ty' b' m
        (r, memo.insert key r)
    | .forallE ty body m .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateRevGo vs memo ty k d
        let (b', memo) := instantiateRevGo vs memo body k (d + 1)
        let r := mkForallE ty' b' m
        (r, memo.insert key r)
    | .letE ty val body .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateRevGo vs memo ty k d
        let (v', memo) := instantiateRevGo vs memo val k d
        let (b', memo) := instantiateRevGo vs memo body k (d + 1)
        let r := mkLetE ty' v' b'
        (r, memo.insert key r)
    | .proj sn i sub .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (s', memo) := instantiateRevGo vs memo sub k d
        let r := mkProj sn i s'
        (r, memo.insert key r)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

/-- The budgeted plain descent of `instantiateRev` (task #313; as
`instantiateListBC` on the reversed array). -/
def instantiateRevBC (vs : Array Expr) (fuel : Nat)
    (e : Expr) (k : Nat) (d : Nat) : Expr × Nat :=
  if k = 0 then (e, fuel)
  else if e.bvarB ≤ d then (e, fuel)
  else
    match e with
    | .bvar i .. =>
      if i < d then (e, fuel)
      else if _h : i - d < k then
        if h : i - d < vs.size then
          let w := vs[vs.size - 1 - (i - d)]'(by omega)
          if i - d = 0 || w.bvarB ≤ d then (w, fuel)
          else instantiateRevBC vs fuel w (i - d) d
        else (e, fuel)
      else (Expr.mkBvar (i - k), fuel)
    | .fvar .. | .sort .. | .const .. | .lit .. => (e, fuel)
    | .app f a .. =>
      if fuel < 2 then (e, 0) else
      let (f', fuel) := instantiateRevBC vs (fuel - 1) f k d
      if fuel = 0 then (e, 0) else
      let (a', fuel) := instantiateRevBC vs fuel a k d
      if fuel = 0 then (e, 0) else (mkApp f' a', fuel)
    | .lam ty body m .. =>
      if fuel < 2 then (e, 0) else
      let (ty', fuel) := instantiateRevBC vs (fuel - 1) ty k d
      if fuel = 0 then (e, 0) else
      let (b', fuel) := instantiateRevBC vs fuel body k (d + 1)
      if fuel = 0 then (e, 0) else (mkLam ty' b' m, fuel)
    | .forallE ty body m .. =>
      if fuel < 2 then (e, 0) else
      let (ty', fuel) := instantiateRevBC vs (fuel - 1) ty k d
      if fuel = 0 then (e, 0) else
      let (b', fuel) := instantiateRevBC vs fuel body k (d + 1)
      if fuel = 0 then (e, 0) else (mkForallE ty' b' m, fuel)
    | .letE ty val body .. =>
      if fuel < 2 then (e, 0) else
      let (ty', fuel) := instantiateRevBC vs (fuel - 1) ty k d
      if fuel = 0 then (e, 0) else
      let (v', fuel) := instantiateRevBC vs fuel val k d
      if fuel = 0 then (e, 0) else
      let (b', fuel) := instantiateRevBC vs fuel body k (d + 1)
      if fuel = 0 then (e, 0) else (mkLetE ty' v' b', fuel)
    | .proj sn i sub .. =>
      if fuel < 2 then (e, 0) else
      let (s', fuel) := instantiateRevBC vs (fuel - 1) sub k d
      if fuel = 0 then (e, 0) else (mkProj sn i s', fuel)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

/-- Bulk instantiation on a reversed accumulator array: the budgeted
plain descent, the memoised pass past the budget. -/
def instantiateRev (e : Expr) (vs : Array Expr) (d : Nat := 0) : Expr :=
  if vs.size = 0 then e
  else if e.bvarB ≤ d then e
  else
    let (r, fuel) := instantiateRevBC vs walkBudget e vs.size d
    if fuel ≠ 0 then r else (instantiateRevGo vs memoAfterBudget e vs.size d).1

/-! ## Abstraction -/

/-- Core of `abstract1C` (`d` is the abstracted fvar's level, `k` the
binder cursor; compound nodes are memoized, the `fvar` leaf is answered
in place).

**Documented deviation from the arena twin** (`abstract1IGo`, which has
no such cutoff): a node whose cached fvar range is at or below `d`
cannot contain `fvar d`, so it is returned unchanged.  A rebuild here
allocates, so returning the node itself is what keeps the walk
idempotent on the shared subterms.  Same value either way. -/
def abstract1GoC (d : Nat) (memo : MemoN) (e : Expr) (k : Nat) :
    Expr × MemoN :=
  if e.fvarB ≤ d then (e, memo) else
  match e with
  | .fvar idx .. => (if idx = d then Expr.mkBvar k else e, memo)
  | .bvar .. | .sort .. | .const .. | .lit .. => (e, memo)
  | .app f a .. =>
    let key := (e, k)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (f', memo) := abstract1GoC d memo f k
      let (a', memo) := abstract1GoC d memo a k
      let r := mkApp f' a'
      (r, memo.insert key r)
  | .lam ty body m .. =>
    let key := (e, k)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstract1GoC d memo ty k
      let (b', memo) := abstract1GoC d memo body (k + 1)
      let r := mkLam ty' b' m
      (r, memo.insert key r)
  | .forallE ty body m .. =>
    let key := (e, k)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstract1GoC d memo ty k
      let (b', memo) := abstract1GoC d memo body (k + 1)
      let r := mkForallE ty' b' m
      (r, memo.insert key r)
  | .letE ty val body .. =>
    let key := (e, k)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstract1GoC d memo ty k
      let (v', memo) := abstract1GoC d memo val k
      let (b', memo) := abstract1GoC d memo body (k + 1)
      let r := mkLetE ty' v' b'
      (r, memo.insert key r)
  | .proj sn i sub .. =>
    let key := (e, k)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (s', memo) := abstract1GoC d memo sub k
      let r := mkProj sn i s'
      (r, memo.insert key r)

/-- The budgeted plain descent of `abstract1C` (task #313; the fuel
convention of `instantiate1BC`). -/
def abstract1BC (d : Nat) (fuel : Nat) (e : Expr) (k : Nat) : Expr × Nat :=
  if e.fvarB ≤ d then (e, fuel) else
  match e with
  | .fvar idx .. => (if idx = d then Expr.mkBvar k else e, fuel)
  | .bvar .. | .sort .. | .const .. | .lit .. => (e, fuel)
  | .app f a .. =>
    if fuel < 2 then (e, 0) else
    let (f', fuel) := abstract1BC d (fuel - 1) f k
    if fuel = 0 then (e, 0) else
    let (a', fuel) := abstract1BC d fuel a k
    if fuel = 0 then (e, 0) else (mkApp f' a', fuel)
  | .lam ty body m .. =>
    if fuel < 2 then (e, 0) else
    let (ty', fuel) := abstract1BC d (fuel - 1) ty k
    if fuel = 0 then (e, 0) else
    let (b', fuel) := abstract1BC d fuel body (k + 1)
    if fuel = 0 then (e, 0) else (mkLam ty' b' m, fuel)
  | .forallE ty body m .. =>
    if fuel < 2 then (e, 0) else
    let (ty', fuel) := abstract1BC d (fuel - 1) ty k
    if fuel = 0 then (e, 0) else
    let (b', fuel) := abstract1BC d fuel body (k + 1)
    if fuel = 0 then (e, 0) else (mkForallE ty' b' m, fuel)
  | .letE ty val body .. =>
    if fuel < 2 then (e, 0) else
    let (ty', fuel) := abstract1BC d (fuel - 1) ty k
    if fuel = 0 then (e, 0) else
    let (v', fuel) := abstract1BC d fuel val k
    if fuel = 0 then (e, 0) else
    let (b', fuel) := abstract1BC d fuel body (k + 1)
    if fuel = 0 then (e, 0) else (mkLetE ty' v' b', fuel)
  | .proj sn i sub .. =>
    if fuel < 2 then (e, 0) else
    let (s', fuel) := abstract1BC d (fuel - 1) sub k
    if fuel = 0 then (e, 0) else (mkProj sn i s', fuel)

/-- The cached `Expr.abstract1`: the cutoff, the budgeted plain
descent, the memoised walk past the budget. -/
def abstract1C (e : Expr) (d : Nat) (k : Nat := 0) : Expr :=
  if e.fvarB ≤ d then e else
  let (r, fuel) := abstract1BC d walkBudget e k
  if fuel ≠ 0 then r else (abstract1GoC d memoAfterBudget e k).1

/-- Core of `abstractRangeC` (bulk abstraction, task #72; same memo
discipline as `abstract1GoC`). -/
def abstractRangeGoC (d k : Nat) (memo : MemoN) (e : Expr) (c : Nat) :
    Expr × MemoN :=
  if e.fvarB ≤ d then (e, memo) else
  match e with
  | .fvar idx .. =>
    (if d ≤ idx ∧ idx < d + k then Expr.mkBvar (c + (d + k - 1 - idx)) else e, memo)
  | .bvar .. | .sort .. | .const .. | .lit .. => (e, memo)
  | .app f a .. =>
    let key := (e, c)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (f', memo) := abstractRangeGoC d k memo f c
      let (a', memo) := abstractRangeGoC d k memo a c
      let r := mkApp f' a'
      (r, memo.insert key r)
  | .lam ty body m .. =>
    let key := (e, c)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstractRangeGoC d k memo ty c
      let (b', memo) := abstractRangeGoC d k memo body (c + 1)
      let r := mkLam ty' b' m
      (r, memo.insert key r)
  | .forallE ty body m .. =>
    let key := (e, c)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstractRangeGoC d k memo ty c
      let (b', memo) := abstractRangeGoC d k memo body (c + 1)
      let r := mkForallE ty' b' m
      (r, memo.insert key r)
  | .letE ty val body .. =>
    let key := (e, c)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstractRangeGoC d k memo ty c
      let (v', memo) := abstractRangeGoC d k memo val c
      let (b', memo) := abstractRangeGoC d k memo body (c + 1)
      let r := mkLetE ty' v' b'
      (r, memo.insert key r)
  | .proj sn i sub .. =>
    let key := (e, c)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (s', memo) := abstractRangeGoC d k memo sub c
      let r := mkProj sn i s'
      (r, memo.insert key r)

/-- The budgeted plain descent of `abstractRangeC` (task #313; the
fuel convention of `instantiate1BC`). -/
def abstractRangeBC (d k : Nat) (fuel : Nat) (e : Expr) (c : Nat) : Expr × Nat :=
  if e.fvarB ≤ d then (e, fuel) else
  match e with
  | .fvar idx .. =>
    (if d ≤ idx ∧ idx < d + k then Expr.mkBvar (c + (d + k - 1 - idx)) else e, fuel)
  | .bvar .. | .sort .. | .const .. | .lit .. => (e, fuel)
  | .app f a .. =>
    if fuel < 2 then (e, 0) else
    let (f', fuel) := abstractRangeBC d k (fuel - 1) f c
    if fuel = 0 then (e, 0) else
    let (a', fuel) := abstractRangeBC d k fuel a c
    if fuel = 0 then (e, 0) else (mkApp f' a', fuel)
  | .lam ty body m .. =>
    if fuel < 2 then (e, 0) else
    let (ty', fuel) := abstractRangeBC d k (fuel - 1) ty c
    if fuel = 0 then (e, 0) else
    let (b', fuel) := abstractRangeBC d k fuel body (c + 1)
    if fuel = 0 then (e, 0) else (mkLam ty' b' m, fuel)
  | .forallE ty body m .. =>
    if fuel < 2 then (e, 0) else
    let (ty', fuel) := abstractRangeBC d k (fuel - 1) ty c
    if fuel = 0 then (e, 0) else
    let (b', fuel) := abstractRangeBC d k fuel body (c + 1)
    if fuel = 0 then (e, 0) else (mkForallE ty' b' m, fuel)
  | .letE ty val body .. =>
    if fuel < 2 then (e, 0) else
    let (ty', fuel) := abstractRangeBC d k (fuel - 1) ty c
    if fuel = 0 then (e, 0) else
    let (v', fuel) := abstractRangeBC d k fuel val c
    if fuel = 0 then (e, 0) else
    let (b', fuel) := abstractRangeBC d k fuel body (c + 1)
    if fuel = 0 then (e, 0) else (mkLetE ty' v' b', fuel)
  | .proj sn i sub .. =>
    if fuel < 2 then (e, 0) else
    let (s', fuel) := abstractRangeBC d k (fuel - 1) sub c
    if fuel = 0 then (e, 0) else (mkProj sn i s', fuel)

/-- The cached `Expr.abstractRange` (`k = 0` is the identity and skips
the traversal, as in the arena): the cutoff, the budgeted plain
descent, the memoised walk past the budget. -/
def abstractRangeC (e : Expr) (d k : Nat) (c : Nat := 0) : Expr :=
  match k with
  | 0 => e
  | _ + 1 =>
    if e.fvarB ≤ d then e else
    let (r, fuel) := abstractRangeBC d k walkBudget e c
    if fuel ≠ 0 then r else (abstractRangeGoC d k memoAfterBudget e c).1

/-! ## Level instantiation -/

/-- Memo table for cursor-free node→node traversals. -/
abbrev Memo0 := Std.HashMap Expr Expr

/-- Core of `instantiateLevelParams` (memoized; nodes without a level
parameter are returned unchanged — the arena's `eparamBs` cutoff). -/
def instLevelParamsGo (ks : List Name) (us : List Level)
    (memo : Memo0) (e : Expr) : Expr × Memo0 :=
  if !e.hasLP then (e, memo) else
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Expr × Memo0 :=
      match e with
      | .bvar .. | .lit .. => (e, memo)
      | .sort u .. => (mkSort (Level.subst ks us u), memo)
      | .const n vs .. => (mkConst n (vs.map (Level.subst ks us)), memo)
      | .fvar idx ty .. =>
        let (t, memo) := instLevelParamsGo ks us memo ty
        (mkFVar idx t, memo)
      | .app f a .. =>
        let (f', memo) := instLevelParamsGo ks us memo f
        let (a', memo) := instLevelParamsGo ks us memo a
        (mkApp f' a', memo)
      | .lam ty body m .. =>
        let (ty', memo) := instLevelParamsGo ks us memo ty
        let (b', memo) := instLevelParamsGo ks us memo body
        (mkLam ty' b' ⟨Level.substPW ks us m.pw⟩, memo)
      | .forallE ty body m .. =>
        let (ty', memo) := instLevelParamsGo ks us memo ty
        let (b', memo) := instLevelParamsGo ks us memo body
        (mkForallE ty' b' ⟨Level.substPW ks us m.pw⟩, memo)
      | .letE ty val body .. =>
        let (ty', memo) := instLevelParamsGo ks us memo ty
        let (v', memo) := instLevelParamsGo ks us memo val
        let (b', memo) := instLevelParamsGo ks us memo body
        (mkLetE ty' v' b', memo)
      | .proj s i sub .. =>
        let (s', memo) := instLevelParamsGo ks us memo sub
        (mkProj s i s', memo)
    (r, memo.insert e r)

/-- The cached `Expr.instantiateLevelParams`. -/
def instLevelParams (ks : List Name) (us : List Level) (e : Expr) : Expr :=
  if !e.hasLP then e else (instLevelParamsGo ks us {} e).1

/-- The cached `ProjEntry.typeAt`: the same two instantiations through
the memoized, **sharing-preserving** `instLevelParams` and
`instantiateListC` (`ProjEntry.typeAtI_eq`, `ConLeche/Verify/Cached/
OpsC.lean`, is the equation).

The executable `.proj` inference clause used to call the spec's
`ProjEntry.typeAt` directly — legitimate as a *value* (`Expr = Expr`)
but not as a *computation*: `Expr.instantiateList` is the unmemoized
tree walk, and its `bvar` arm re-traverses the replacement (`vs[j - d]`
under `vs.take (j - d)`), so every occurrence of the subject and of
every parameter in the field type came back as a fresh **tree copy**
of a term that was a DAG.  On a projection chain over a Mathlib
carrier (`(Classical.choice …).ColimitCocone.0.Cocone.0.CommRingCat.0`)
the copies nest, and at `AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`
(subject tree 3.9 · 10⁸ nodes on a 3 106-node DAG) the copy alone is
the out-of-memory — DESIGN.md "The affine frontier". -/
def _root_.ConLeche.ProjEntry.typeAtI (entry : ProjEntry) (us : List Level)
    (targs : List Expr) (pe : Expr) : Expr :=
  instantiateListC (instLevelParams entry.levelParams us entry.body)
    (pe :: targs.reverse)

/-! ## Scope queries -/

/-- Core of `wscopedBC` (memoized; `fvar` annotations are descended,
so the cached fvar range does not decide it). -/
def wscopedBGoC (memo : Std.HashMap (Expr × Nat) Bool) (d : Nat)
    (e : Expr) : Bool × Std.HashMap (Expr × Nat) Bool :=
  if e.fvarB == 0 then (true, memo) else
  match memo[(e, d)]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap (Expr × Nat) Bool :=
      match e with
      | .bvar .. | .sort .. | .const .. | .lit .. => (true, memo)
      | .fvar idx ty .. =>
        if idx < d then wscopedBGoC memo idx ty else (false, memo)
      | .app f a .. =>
        let (rf, memo) := wscopedBGoC memo d f
        if rf then wscopedBGoC memo d a else (false, memo)
      | .lam ty body _ .. | .forallE ty body _ .. =>
        let (rt, memo) := wscopedBGoC memo d ty
        if rt then wscopedBGoC memo d body else (false, memo)
      | .letE ty val body .. =>
        let (rt, memo) := wscopedBGoC memo d ty
        if rt then
          let (rv, memo) := wscopedBGoC memo d val
          if rv then wscopedBGoC memo d body else (false, memo)
        else (false, memo)
      | .proj _ _ sub .. => wscopedBGoC memo d sub
    (r, memo.insert (e, d) r)

/-- The cached `Expr.wscopedB d` (one memoized DAG walk). -/
def wscopedBC (d : Nat) (e : Expr) : Bool := (wscopedBGoC {} d e).1

/-- Core of `fvarLeavesC` (memoized set accumulation). -/
def fvarLeavesGoC (acc : List (Nat × Expr))
    (seen : Std.HashMap Expr Unit) (e : Expr) :
    List (Nat × Expr) × Std.HashMap Expr Unit :=
  if e.fvarB == 0 then (acc, seen) else
  match seen[e]? with
  | some _ => (acc, seen)
  | none =>
    let seen := seen.insert e ()
    match e with
    | .bvar .. | .sort .. | .const .. | .lit .. => (acc, seen)
    | .fvar idx ty .. => fvarLeavesGoC ((idx, ty) :: acc) seen ty
    | .app f a .. =>
      let (acc, seen) := fvarLeavesGoC acc seen f
      fvarLeavesGoC acc seen a
    | .lam ty body _ .. | .forallE ty body _ .. =>
      let (acc, seen) := fvarLeavesGoC acc seen ty
      fvarLeavesGoC acc seen body
    | .letE ty val body .. =>
      let (acc, seen) := fvarLeavesGoC acc seen ty
      let (acc, seen) := fvarLeavesGoC acc seen val
      fvarLeavesGoC acc seen body
    | .proj _ _ sub .. => fvarLeavesGoC acc seen sub

/-- The reachable `fvar` leaves (hereditarily through annotations). -/
def fvarLeavesC (e : Expr) : List (Nat × Expr) :=
  (fvarLeavesGoC [] {} e).1

/-- Is `(idx, ty)` in the base leaf list?  Compares the annotation
with `Expr.beq` (pointer-first). -/
def leafMem : List (Nat × Expr) → Nat → Expr → Bool
  | [], _, _ => false
  | (i, t) :: rest, idx, ty =>
    (i == idx && t == ty) || leafMem rest idx ty

/-- Core of the fabrication-side leaf-subset test (task #86). -/
def leavesSubGo (bl : List (Nat × Expr))
    (memo : Std.HashMap Expr Bool) (e : Expr) :
    Bool × Std.HashMap Expr Bool :=
  if e.fvarB == 0 then (true, memo) else
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap Expr Bool :=
      match e with
      | .bvar .. | .sort .. | .const .. | .lit .. => (true, memo)
      | .fvar idx ty .. =>
        if leafMem bl idx ty then leavesSubGo bl memo ty else (false, memo)
      | .app f a .. =>
        let (rf, memo) := leavesSubGo bl memo f
        if rf then leavesSubGo bl memo a else (false, memo)
      | .lam ty body _ .. | .forallE ty body _ .. =>
        let (rt, memo) := leavesSubGo bl memo ty
        if rt then leavesSubGo bl memo body else (false, memo)
      | .letE ty val body .. =>
        let (rt, memo) := leavesSubGo bl memo ty
        if rt then
          let (rv, memo) := leavesSubGo bl memo val
          if rv then leavesSubGo bl memo body else (false, memo)
        else (false, memo)
      | .proj _ _ sub .. => leavesSubGo bl memo sub
    (r, memo.insert e r)

/-- The fabrication leaf guard: every `fvar` leaf of `fab` is one of
`base` (short-circuits on `fvar`-free fabrications, `O(1)` off the
cached range). -/
def leafGuard (fab base : Expr) : Bool :=
  !fab.hasFvar || (leavesSubGo (fvarLeavesC base) {} fab).1

/-! ## Telescope operations -/

/-- The `instantiate1C` chain of `Expr.instSpine`. -/
def instSpineChainC : List Expr → Nat → Expr → Expr
  | [], _, e => e
  | a :: as, t, e => instSpineChainC as (t - 1) (instantiate1C e a t)

/-- The cached `Expr.instSpine` (bulk when the spine spans the
telescope context, the chain otherwise). -/
def instSpineC (args : List Expr) (t : Nat) (e : Expr) : Expr :=
  if args.length = t + 1 then instantiateListC e args.reverse 0
  else instSpineChainC args t e

/-- Core of `piResidual` (bulk form, task #50).

Not structural: the `bvar` arm re-enters on the same argument list with
the accumulator flushed.  Measure `(as.length, acc.length)` — the
`forallE` arm consumes an argument, the `bvar` arm keeps the arguments
and empties a nonempty accumulator. -/
def piResidualAcc : List Expr → Expr → List Expr → Option Expr
  | acc, e, [] => some (instantiateListC e acc 0)
  | acc, e, a :: as =>
    match e with
    | .forallE _ b _ .. => piResidualAcc (a :: acc) b as
    | .bvar .. =>
      match acc with
      | [] => none
      | _ :: _ => piResidualAcc [] (instantiateListC e acc 0) (a :: as)
    | _ => none
termination_by acc _ as => (as.length, acc.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; simp +arith +decide)
    | (apply Prod.Lex.left; simp +arith +decide)

@[inherit_doc piResidualAcc]
def piResidual (e : Expr) (args : List Expr) : Option Expr :=
  piResidualAcc [] e args

/-! ## Level-parameter definedness (the parsed-index driver's guard) -/

/-- Core of `allLevelParamsDefinedC` (memoized; nodes without a level
parameter are `true` without traversal — the `hasLP` cutoff). -/
def allLevelParamsDefinedGoC (params : List Name)
    (memo : Std.HashMap Expr Bool) (e : Expr) :
    Bool × Std.HashMap Expr Bool :=
  if !e.hasLP then (true, memo) else
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap Expr Bool :=
      match e with
      | .bvar .. | .lit .. => (true, memo)
      | .sort u .. => (Level.allParamsDefined params u, memo)
      | .const _ us .. => (us.all (Level.allParamsDefined params), memo)
      | .fvar _ ty .. => allLevelParamsDefinedGoC params memo ty
      | .app f a .. =>
        let (rf, memo) := allLevelParamsDefinedGoC params memo f
        if rf then allLevelParamsDefinedGoC params memo a else (false, memo)
      | .lam ty body m .. | .forallE ty body m .. =>
        let (rt, memo) := allLevelParamsDefinedGoC params memo ty
        if rt then
          let (rb, memo) := allLevelParamsDefinedGoC params memo body
          (rb && m.pw.paramsDefined params, memo)
        else (false, memo)
      | .letE ty val body .. =>
        let (rt, memo) := allLevelParamsDefinedGoC params memo ty
        if rt then
          let (rv, memo) := allLevelParamsDefinedGoC params memo val
          if rv then allLevelParamsDefinedGoC params memo body
          else (false, memo)
        else (false, memo)
      | .proj _ _ sub .. => allLevelParamsDefinedGoC params memo sub
    (r, memo.insert e r)

/-- The cached `Expr.allLevelParamsDefined params` (one memoized DAG
walk). -/
def allLevelParamsDefinedC (params : List Name) (e : Expr) : Bool :=
  (allLevelParamsDefinedGoC params {} e).1

end ConLeche.Expr
