import Setlec.Cached.ExprC
import Setlec.Kernel.Core

/-!
# Syntactic operations on `ExprC`

The `ExprC` counterparts of the arena operations in
`Setlec/Kernel/IExpr.lean` — same clauses, same memo discipline, same
cutoffs; the mechanism differs only in where the derived data lives (a
field of the node instead of a parallel array indexed by the node's
arena position) and in how a rebuilt node is obtained (allocation
instead of a cons-table probe).

Two structural consequences of dropping the arena, both load-bearing
for the pilot's numbers:

* every traversal memo is keyed on `ExprC` itself (`O(1)` hashing off
  the cached field, pointer-first equality), so shared sub-DAGs are
  still visited once — a `Std.HashMap ExprC α` replaces the arena's
  `Std.HashMap EIdx α` one for one;
* a cutoff (`bvarB ≤ d`, `fvarB ≤ d`, `!hasLP`) returns the node
  **itself**, so the result shares memory with the input and later
  pointer comparisons on it are `O(1)` — the analogue of the arena
  returning the same index.

## The memo discipline of the substitution walks (task #177)

The arena's memo key was an `EIdx` — a scalar.  The clone's is a
*constructed* key, so the probe costs allocations, and profiling put
`instantiate*Go`/`abstract*Go` plus their `Std.DHashMap` spec sites at
roughly half of every `--no-model` run.  Three shape rules cut that,
and each is a property of the walks alone (the values are unchanged —
`Setlec/Verify/Cached/OpsC.lean` proves each walk equal to its
`Setlec.Expr` counterpart exactly as before):

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

namespace Setlec.Cached

open Setlec

namespace ExprC

/-! ## The one-level view -/

/-- The one-level view of a node (`Setlec.ExprView`, the
representation-generic destructuring seam of the core bodies). -/
@[inline] def view : ExprC → ExprView ExprC
  | .bvar i .. => .bvar i
  | .fvar idx n ty .. => .fvar idx n ty
  | .sort u .. => .sort u
  | .const n us .. => .const n us
  | .app f a .. => .app f a
  | .lam n ty b m .. => .lam n ty b m
  | .forallE n ty b m .. => .forallE n ty b m
  | .letE n ty v b .. => .letE n ty v b
  | .lit l .. => .lit l
  | .proj s i e .. => .proj s i e

/-- Build a node from a one-level view (the smart constructors). -/
@[inline] def ofView : ExprView ExprC → ExprC
  | .bvar i => mkBVar i
  | .fvar idx n ty => mkFVar idx n ty
  | .sort u => mkSort u
  | .const n us => mkConst n us
  | .app f a => mkApp f a
  | .lam n ty b m => mkLam n ty b m
  | .forallE n ty b m => mkForallE n ty b m
  | .letE n ty v b => mkLetE n ty v b
  | .lit l => mkLit l
  | .proj s i e => mkProj s i e

/-! ## Spines -/

/-- The head of an application spine. -/
def getAppFn : ExprC → ExprC
  | .app f _ .. => getAppFn f
  | e => e

/-- Prepend the spine arguments of `e` to `acc` (outermost last). -/
def getAppArgsAcc : ExprC → List ExprC → List ExprC
  | .app f a .., acc => getAppArgsAcc f (a :: acc)
  | _, acc => acc

/-- The arguments of an application spine, outermost last. -/
@[inline] def getAppArgs (e : ExprC) : List ExprC := getAppArgsAcc e []

/-- Apply to a list of arguments. -/
def mkAppN (f : ExprC) : List ExprC → ExprC
  | [] => f
  | a :: as => mkAppN (mkApp f a) as

/-! ## Instantiation -/

/-- Memo table for cursored node→node traversals. -/
abbrev MemoN := Std.HashMap (ExprC × Nat) ExprC

/-- Memo table for the bulk traversals (node, cursor).

**The live prefix `k` is not part of the key.**  It is constant for the
whole life of one table: the only place `k` changes is the `bvar` arm's
re-entry at a replacement, and that re-entry runs under a *fresh*
table.  Dropping it halves the key — `(ExprC × Nat × Nat)` is two
`Prod` allocations per probe, `(ExprC × Nat)` is one. -/
abbrev MemoNL := Std.HashMap (ExprC × Nat) ExprC

/-- Core of `instantiate1` (nodes whose cached bound is at or below the
cursor are returned unchanged; compound nodes are memoized, atoms are
answered in place — see this module's memo discipline). -/
def instantiate1Go (v : ExprC) (memo : MemoN) (e : ExprC) (d : Nat) :
    ExprC × MemoN :=
  if e.bvarB ≤ d then (e, memo) else
  match e with
  | .bvar i .. =>
    (if i = d then v else if i > d then mkBVar (i - 1) else e, memo)
  | .fvar .. | .sort .. | .const .. | .lit .. => (e, memo)
  | .app f a .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (f', memo) := instantiate1Go v memo f d
      let (a', memo) := instantiate1Go v memo a d
      let r := mkApp f' a'
      (r, memo.insert key r)
  | .lam n ty body m .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := instantiate1Go v memo ty d
      let (b', memo) := instantiate1Go v memo body (d + 1)
      let r := mkLam n ty' b' m
      (r, memo.insert key r)
  | .forallE n ty body m .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := instantiate1Go v memo ty d
      let (b', memo) := instantiate1Go v memo body (d + 1)
      let r := mkForallE n ty' b' m
      (r, memo.insert key r)
  | .letE n ty val body .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := instantiate1Go v memo ty d
      let (v', memo) := instantiate1Go v memo val d
      let (b', memo) := instantiate1Go v memo body (d + 1)
      let r := mkLetE n ty' v' b'
      (r, memo.insert key r)
  | .proj sn i sub .. =>
    let key := (e, d)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (s', memo) := instantiate1Go v memo sub d
      let r := mkProj sn i s'
      (r, memo.insert key r)

/-- `Expr.instantiate1` on `ExprC` (fresh per-call memo). -/
def instantiate1 (e v : ExprC) (d : Nat := 0) : ExprC :=
  if e.bvarB ≤ d then e else (instantiate1Go v {} e d).1

/-- Core of `instantiateList` (task #50): `vs` innermost binder first,
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
def instantiateListGo (vs : Array ExprC) (memo : MemoNL)
    (e : ExprC) (k : Nat) (d : Nat) : ExprC × MemoNL :=
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
          else ((instantiateListGo vs {} w (i - d) d).1, memo)
        else (e, memo)
      else (mkBVar (i - k), memo)
    | .fvar .. | .sort .. | .const .. | .lit .. => (e, memo)
    | .app f a .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (f', memo) := instantiateListGo vs memo f k d
        let (a', memo) := instantiateListGo vs memo a k d
        let r := mkApp f' a'
        (r, memo.insert key r)
    | .lam n ty body m .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateListGo vs memo ty k d
        let (b', memo) := instantiateListGo vs memo body k (d + 1)
        let r := mkLam n ty' b' m
        (r, memo.insert key r)
    | .forallE n ty body m .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateListGo vs memo ty k d
        let (b', memo) := instantiateListGo vs memo body k (d + 1)
        let r := mkForallE n ty' b' m
        (r, memo.insert key r)
    | .letE n ty val body .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateListGo vs memo ty k d
        let (v', memo) := instantiateListGo vs memo val k d
        let (b', memo) := instantiateListGo vs memo body k (d + 1)
        let r := mkLetE n ty' v' b'
        (r, memo.insert key r)
    | .proj sn i sub .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (s', memo) := instantiateListGo vs memo sub k d
        let r := mkProj sn i s'
        (r, memo.insert key r)
termination_by (k, sizeOf e)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp +arith +decide)

/-- `Expr.instantiateList` on `ExprC` (bulk, one memoized DAG pass). -/
def instantiateList (e : ExprC) (vs : List ExprC) (d : Nat := 0) : ExprC :=
  match vs with
  | [] => e
  | _ :: _ =>
    let a := vs.toArray
    (instantiateListGo a {} e a.size d).1

/-- Core of `instantiateRev`: as `instantiateListGo`, but the
replacement array holds the innermost binder **last** (the binder
loops' push order — lean4lean's `instantiateRev`).  Same
`(k, sizeOf e)` measure, same dependent prefix test. -/
def instantiateRevGo (vs : Array ExprC) (memo : MemoNL)
    (e : ExprC) (k : Nat) (d : Nat) : ExprC × MemoNL :=
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
      else (mkBVar (i - k), memo)
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
    | .lam n ty body m .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateRevGo vs memo ty k d
        let (b', memo) := instantiateRevGo vs memo body k (d + 1)
        let r := mkLam n ty' b' m
        (r, memo.insert key r)
    | .forallE n ty body m .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateRevGo vs memo ty k d
        let (b', memo) := instantiateRevGo vs memo body k (d + 1)
        let r := mkForallE n ty' b' m
        (r, memo.insert key r)
    | .letE n ty val body .. =>
      let key := (e, d)
      match memo[key]? with
      | some r => (r, memo)
      | none =>
        let (ty', memo) := instantiateRevGo vs memo ty k d
        let (v', memo) := instantiateRevGo vs memo val k d
        let (b', memo) := instantiateRevGo vs memo body k (d + 1)
        let r := mkLetE n ty' v' b'
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

/-- Bulk instantiation on a reversed accumulator array. -/
def instantiateRev (e : ExprC) (vs : Array ExprC) (d : Nat := 0) : ExprC :=
  if vs.size = 0 then e
  else if e.bvarB ≤ d then e
  else (instantiateRevGo vs {} e vs.size d).1

/-! ## Abstraction -/

/-- Core of `abstract1` (`d` is the abstracted fvar's level, `k` the
binder cursor; compound nodes are memoized, the `fvar` leaf is answered
in place).

**Documented deviation from the arena twin** (`abstract1IGo`, which has
no such cutoff): a node whose cached fvar range is at or below `d`
cannot contain `fvar d`, so it is returned unchanged.  The arena does
not need the cutoff — its rebuild re-interns to the *same index* — but
the clone's rebuild allocates, so returning the node itself is how the
computed-field representation recovers the arena's idempotence.  Same
value either way. -/
def abstract1Go (d : Nat) (memo : MemoN) (e : ExprC) (k : Nat) :
    ExprC × MemoN :=
  if e.fvarB ≤ d then (e, memo) else
  match e with
  | .fvar idx .. => (if idx = d then mkBVar k else e, memo)
  | .bvar .. | .sort .. | .const .. | .lit .. => (e, memo)
  | .app f a .. =>
    let key := (e, k)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (f', memo) := abstract1Go d memo f k
      let (a', memo) := abstract1Go d memo a k
      let r := mkApp f' a'
      (r, memo.insert key r)
  | .lam n ty body m .. =>
    let key := (e, k)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstract1Go d memo ty k
      let (b', memo) := abstract1Go d memo body (k + 1)
      let r := mkLam n ty' b' m
      (r, memo.insert key r)
  | .forallE n ty body m .. =>
    let key := (e, k)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstract1Go d memo ty k
      let (b', memo) := abstract1Go d memo body (k + 1)
      let r := mkForallE n ty' b' m
      (r, memo.insert key r)
  | .letE n ty val body .. =>
    let key := (e, k)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstract1Go d memo ty k
      let (v', memo) := abstract1Go d memo val k
      let (b', memo) := abstract1Go d memo body (k + 1)
      let r := mkLetE n ty' v' b'
      (r, memo.insert key r)
  | .proj sn i sub .. =>
    let key := (e, k)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (s', memo) := abstract1Go d memo sub k
      let r := mkProj sn i s'
      (r, memo.insert key r)

/-- `Expr.abstract1` on `ExprC`. -/
def abstract1 (e : ExprC) (d : Nat) (k : Nat := 0) : ExprC :=
  if e.fvarB ≤ d then e else (abstract1Go d {} e k).1

/-- Core of `abstractRange` (bulk abstraction, task #72; same memo
discipline as `abstract1Go`). -/
def abstractRangeGo (d k : Nat) (memo : MemoN) (e : ExprC) (c : Nat) :
    ExprC × MemoN :=
  if e.fvarB ≤ d then (e, memo) else
  match e with
  | .fvar idx .. =>
    (if d ≤ idx ∧ idx < d + k then mkBVar (c + (d + k - 1 - idx)) else e, memo)
  | .bvar .. | .sort .. | .const .. | .lit .. => (e, memo)
  | .app f a .. =>
    let key := (e, c)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (f', memo) := abstractRangeGo d k memo f c
      let (a', memo) := abstractRangeGo d k memo a c
      let r := mkApp f' a'
      (r, memo.insert key r)
  | .lam n ty body m .. =>
    let key := (e, c)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstractRangeGo d k memo ty c
      let (b', memo) := abstractRangeGo d k memo body (c + 1)
      let r := mkLam n ty' b' m
      (r, memo.insert key r)
  | .forallE n ty body m .. =>
    let key := (e, c)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstractRangeGo d k memo ty c
      let (b', memo) := abstractRangeGo d k memo body (c + 1)
      let r := mkForallE n ty' b' m
      (r, memo.insert key r)
  | .letE n ty val body .. =>
    let key := (e, c)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (ty', memo) := abstractRangeGo d k memo ty c
      let (v', memo) := abstractRangeGo d k memo val c
      let (b', memo) := abstractRangeGo d k memo body (c + 1)
      let r := mkLetE n ty' v' b'
      (r, memo.insert key r)
  | .proj sn i sub .. =>
    let key := (e, c)
    match memo[key]? with
    | some r => (r, memo)
    | none =>
      let (s', memo) := abstractRangeGo d k memo sub c
      let r := mkProj sn i s'
      (r, memo.insert key r)

/-- `Expr.abstractRange` on `ExprC` (`k = 0` is the identity and skips
the traversal, as in the arena). -/
def abstractRange (e : ExprC) (d k : Nat) (c : Nat := 0) : ExprC :=
  match k with
  | 0 => e
  | _ + 1 => if e.fvarB ≤ d then e else (abstractRangeGo d k {} e c).1

/-! ## Level instantiation -/

/-- Memo table for cursor-free node→node traversals. -/
abbrev Memo0 := Std.HashMap ExprC ExprC

/-- Core of `instantiateLevelParams` (memoized; nodes without a level
parameter are returned unchanged — the arena's `eparamBs` cutoff). -/
def instLevelParamsGo (ks : List Name) (us : List Level)
    (memo : Memo0) (e : ExprC) : ExprC × Memo0 :=
  if !e.hasLP then (e, memo) else
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : ExprC × Memo0 :=
      match e with
      | .bvar .. | .lit .. => (e, memo)
      | .sort u .. => (mkSort (Level.subst ks us u), memo)
      | .const n vs .. => (mkConst n (vs.map (Level.subst ks us)), memo)
      | .fvar idx n ty .. =>
        let (t, memo) := instLevelParamsGo ks us memo ty
        (mkFVar idx n t, memo)
      | .app f a .. =>
        let (f', memo) := instLevelParamsGo ks us memo f
        let (a', memo) := instLevelParamsGo ks us memo a
        (mkApp f' a', memo)
      | .lam n ty body m .. =>
        let (ty', memo) := instLevelParamsGo ks us memo ty
        let (b', memo) := instLevelParamsGo ks us memo body
        (mkLam n ty' b' ⟨m.bi, Level.substPW ks us m.pw⟩, memo)
      | .forallE n ty body m .. =>
        let (ty', memo) := instLevelParamsGo ks us memo ty
        let (b', memo) := instLevelParamsGo ks us memo body
        (mkForallE n ty' b' ⟨m.bi, Level.substPW ks us m.pw⟩, memo)
      | .letE n ty val body .. =>
        let (ty', memo) := instLevelParamsGo ks us memo ty
        let (v', memo) := instLevelParamsGo ks us memo val
        let (b', memo) := instLevelParamsGo ks us memo body
        (mkLetE n ty' v' b', memo)
      | .proj s i sub .. =>
        let (s', memo) := instLevelParamsGo ks us memo sub
        (mkProj s i s', memo)
    (r, memo.insert e r)

/-- `Expr.instantiateLevelParams` on `ExprC`. -/
def instLevelParams (ks : List Name) (us : List Level) (e : ExprC) : ExprC :=
  if !e.hasLP then e else (instLevelParamsGo ks us {} e).1

/-! ## Scope queries -/

/-- `Expr.looseBVarsBounded k` — `O(1)`: the cached bound is *exact*
(the least such `k`). -/
@[inline] def looseBVarsBounded (k : Nat) (e : ExprC) : Bool := e.bvarB ≤ k

/-- Core of `wscopedB` (memoized; `fvar` annotations are descended,
so the cached fvar range does not decide it). -/
def wscopedBGo (memo : Std.HashMap (ExprC × Nat) Bool) (d : Nat)
    (e : ExprC) : Bool × Std.HashMap (ExprC × Nat) Bool :=
  if e.fvarB == 0 then (true, memo) else
  match memo[(e, d)]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap (ExprC × Nat) Bool :=
      match e with
      | .bvar .. | .sort .. | .const .. | .lit .. => (true, memo)
      | .fvar idx _ ty .. =>
        if idx < d then wscopedBGo memo idx ty else (false, memo)
      | .app f a .. =>
        let (rf, memo) := wscopedBGo memo d f
        if rf then wscopedBGo memo d a else (false, memo)
      | .lam _ ty body _ .. | .forallE _ ty body _ .. =>
        let (rt, memo) := wscopedBGo memo d ty
        if rt then wscopedBGo memo d body else (false, memo)
      | .letE _ ty val body .. =>
        let (rt, memo) := wscopedBGo memo d ty
        if rt then
          let (rv, memo) := wscopedBGo memo d val
          if rv then wscopedBGo memo d body else (false, memo)
        else (false, memo)
      | .proj _ _ sub .. => wscopedBGo memo d sub
    (r, memo.insert (e, d) r)

/-- `Expr.wscopedB d` on `ExprC` (one memoized DAG walk). -/
def wscopedB (d : Nat) (e : ExprC) : Bool := (wscopedBGo {} d e).1

/-- Core of `fvarLeaves` (memoized set accumulation). -/
def fvarLeavesGo (acc : List (Nat × Name × ExprC))
    (seen : Std.HashMap ExprC Unit) (e : ExprC) :
    List (Nat × Name × ExprC) × Std.HashMap ExprC Unit :=
  if e.fvarB == 0 then (acc, seen) else
  match seen[e]? with
  | some _ => (acc, seen)
  | none =>
    let seen := seen.insert e ()
    match e with
    | .bvar .. | .sort .. | .const .. | .lit .. => (acc, seen)
    | .fvar idx n ty .. => fvarLeavesGo ((idx, n, ty) :: acc) seen ty
    | .app f a .. =>
      let (acc, seen) := fvarLeavesGo acc seen f
      fvarLeavesGo acc seen a
    | .lam _ ty body _ .. | .forallE _ ty body _ .. =>
      let (acc, seen) := fvarLeavesGo acc seen ty
      fvarLeavesGo acc seen body
    | .letE _ ty val body .. =>
      let (acc, seen) := fvarLeavesGo acc seen ty
      let (acc, seen) := fvarLeavesGo acc seen val
      fvarLeavesGo acc seen body
    | .proj _ _ sub .. => fvarLeavesGo acc seen sub

/-- The reachable `fvar` leaves (hereditarily through annotations). -/
def fvarLeaves (e : ExprC) : List (Nat × Name × ExprC) :=
  (fvarLeavesGo [] {} e).1

/-- Is `(idx, n, ty)` in the base leaf list?  Compares the annotation
with `ExprC.beq` (pointer-first). -/
def leafMem : List (Nat × Name × ExprC) → Nat → Name → ExprC → Bool
  | [], _, _, _ => false
  | (i, n, t) :: rest, idx, nm, ty =>
    (i == idx && n == nm && t == ty) || leafMem rest idx nm ty

/-- Core of the fabrication-side leaf-subset test (task #86). -/
def leavesSubGo (bl : List (Nat × Name × ExprC))
    (memo : Std.HashMap ExprC Bool) (e : ExprC) :
    Bool × Std.HashMap ExprC Bool :=
  if e.fvarB == 0 then (true, memo) else
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap ExprC Bool :=
      match e with
      | .bvar .. | .sort .. | .const .. | .lit .. => (true, memo)
      | .fvar idx nm ty .. =>
        if leafMem bl idx nm ty then leavesSubGo bl memo ty else (false, memo)
      | .app f a .. =>
        let (rf, memo) := leavesSubGo bl memo f
        if rf then leavesSubGo bl memo a else (false, memo)
      | .lam _ ty body _ .. | .forallE _ ty body _ .. =>
        let (rt, memo) := leavesSubGo bl memo ty
        if rt then leavesSubGo bl memo body else (false, memo)
      | .letE _ ty val body .. =>
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
def leafGuard (fab base : ExprC) : Bool :=
  !fab.hasFvar || (leavesSubGo (fvarLeaves base) {} fab).1

/-! ## Telescope operations -/

/-- The body after `k` leading `∀`-binders. -/
def stripPisBody : Nat → ExprC → Option ExprC
  | 0, e => some e
  | k + 1, e =>
    match e with
    | .forallE _ _ b _ .. => stripPisBody k b
    | _ => none

/-- The `instantiate1` chain of `Expr.instSpine`. -/
def instSpineChain : List ExprC → Nat → ExprC → ExprC
  | [], _, e => e
  | a :: as, t, e => instSpineChain as (t - 1) (instantiate1 e a t)

/-- `Expr.instSpine` on `ExprC` (bulk when the spine spans the
telescope context, the chain otherwise). -/
def instSpine (args : List ExprC) (t : Nat) (e : ExprC) : ExprC :=
  if args.length = t + 1 then instantiateList e args.reverse 0
  else instSpineChain args t e

/-- Core of `piResidual` (bulk form, task #50).

Not structural: the `bvar` arm re-enters on the same argument list with
the accumulator flushed.  Measure `(as.length, acc.length)` — the
`forallE` arm consumes an argument, the `bvar` arm keeps the arguments
and empties a nonempty accumulator. -/
def piResidualAcc : List ExprC → ExprC → List ExprC → Option ExprC
  | acc, e, [] => some (instantiateList e acc 0)
  | acc, e, a :: as =>
    match e with
    | .forallE _ _ b _ .. => piResidualAcc (a :: acc) b as
    | .bvar .. =>
      match acc with
      | [] => none
      | _ :: _ => piResidualAcc [] (instantiateList e acc 0) (a :: as)
    | _ => none
termination_by acc _ as => (as.length, acc.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; simp +arith +decide)
    | (apply Prod.Lex.left; simp +arith +decide)

@[inherit_doc piResidualAcc]
def piResidual (e : ExprC) (args : List ExprC) : Option ExprC :=
  piResidualAcc [] e args

/-- `Expr.pisToLams` on `ExprC`. -/
def pisToLams : Nat → ExprC → ExprC → Option ExprC
  | 0, _, body => some body
  | k + 1, e, body =>
    match e with
    | .forallE n ty rest mb .. =>
      match pisToLams k rest body with
      | some b => some (mkLam n ty b ⟨mb.bi, .never⟩)
      | none => none
    | _ => none

/-! ## Level-parameter definedness (the parsed-index driver's guard) -/

/-- Core of `allLevelParamsDefined` (memoized; nodes without a level
parameter are `true` without traversal — the `hasLP` cutoff). -/
def allLevelParamsDefinedGo (params : List Name)
    (memo : Std.HashMap ExprC Bool) (e : ExprC) :
    Bool × Std.HashMap ExprC Bool :=
  if !e.hasLP then (true, memo) else
  match memo[e]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : Bool × Std.HashMap ExprC Bool :=
      match e with
      | .bvar .. | .lit .. => (true, memo)
      | .sort u .. => (Level.allParamsDefined params u, memo)
      | .const _ us .. => (us.all (Level.allParamsDefined params), memo)
      | .fvar _ _ ty .. => allLevelParamsDefinedGo params memo ty
      | .app f a .. =>
        let (rf, memo) := allLevelParamsDefinedGo params memo f
        if rf then allLevelParamsDefinedGo params memo a else (false, memo)
      | .lam _ ty body m .. | .forallE _ ty body m .. =>
        let (rt, memo) := allLevelParamsDefinedGo params memo ty
        if rt then
          let (rb, memo) := allLevelParamsDefinedGo params memo body
          (rb && m.pw.paramsDefined params, memo)
        else (false, memo)
      | .letE _ ty val body .. =>
        let (rt, memo) := allLevelParamsDefinedGo params memo ty
        if rt then
          let (rv, memo) := allLevelParamsDefinedGo params memo val
          if rv then allLevelParamsDefinedGo params memo body
          else (false, memo)
        else (false, memo)
      | .proj _ _ sub .. => allLevelParamsDefinedGo params memo sub
    (r, memo.insert e r)

/-- `Expr.allLevelParamsDefined params` on `ExprC` (one memoized DAG
walk). -/
def allLevelParamsDefined (params : List Name) (e : ExprC) : Bool :=
  (allLevelParamsDefinedGo params {} e).1

end ExprC

end Setlec.Cached
