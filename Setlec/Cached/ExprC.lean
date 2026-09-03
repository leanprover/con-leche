import Std.Data.HashMap
import Setlec.Kernel.Expr
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Level

/-!
# `ExprC`: expressions with computed per-node fields (performance pilot)

The pilot's term representation (see DESIGN.md, "The cached-clone
pilot"): a plain inductive expression type — no arena, no interning
table, no indices — in which **every constructor carries a block of
derived data computed once, at construction time**:

* `h`  — the node's hash (`UInt64`), so hashing a term for a memo
  lookup is a field read instead of a (bounded or unbounded)
  traversal;
* `bb` — the loose-bvar *bound*: the least `k` with
  `looseBVarsBounded k` (the arena's `bvarBs`, task #87 / nanoda's
  `num_loose_bvars`).  Instantiation at or above the bound is the
  identity;
* `fb` — the fvar *range*: max fvar index + 1 (`0` = fvar-free; `fvar`
  type annotations are not descended, matching the abstraction
  traversals — the arena's `fvarBs`).  Abstraction at or above the
  range is the identity;
* `lp` — has-level-param (the arena's `eparamBs`; the official
  kernel's `has_univ_param`).  Level instantiation on a node without
  it is the identity.

The recurrences are *exactly* the arena's (`ENode.bvarBoundOf`,
`ENode.fvarRangeOf`, `ENode.hasLParamOf` in `Setlec/Kernel/IExpr.lean`)
so the two checkers take the same cutoffs at the same places; only the
mechanism differs (a field of the node vs. a parallel array indexed by
the node's arena position).

Equality (`ExprC.beq`) is the official kernel's: pointer equality
first, then the cached hashes, then structural descent.  Together with
the `O(1)` `Hashable` instance this is what makes `Std.HashMap ExprC α`
a viable memo key without a hash-consing table — the pilot's central
claim.  Terms are shared *naturally*, by Lean's own structure sharing:
the smart constructors return their children by reference, so the
result of an instantiation shares every unchanged subterm with its
input, and the pointer test then decides equality of those subterms in
O(1) exactly as an index comparison does.

This module is implementation-only and unverified — the pilot is a
measurement instrument (like the NbE and sortSpec pilots), not part of
the verified checker.
-/

namespace Setlec.Cached

open Setlec

/-- Does the level mention a parameter (the arena's `lparamBs`, the
official kernel's `level.has_param`)?  There is no interned level
table here, so this is an `O(|u|)` walk — paid once per `.sort`/
`.const` node construction, never per memo touch. -/
def levelHasParam : Level → Bool
  | .zero => false
  | .param _ => true
  | .succ u => levelHasParam u
  | .max u v | .imax u v => levelHasParam u || levelHasParam v

/-- `levelHasParam` over a `const` node's level arguments. -/
def levelsHaveParam : List Level → Bool
  | [] => false
  | u :: us => levelHasParam u || levelsHaveParam us

/-- Depth-bounded level hash — the existing `Level.hashB` budget of
`Setlec.Expr`'s own hash (a hash may ignore structure; `BEq` stays
full).  Keeping it bounded is what makes `mkSort`/`mkConst` `O(1)`
in the level's size. -/
@[inline] def levelHash (u : Level) : UInt64 := Level.hashB 4 u

/-- `levelHash` folded over a level list. -/
def levelsHash : List Level → UInt64
  | [] => 13
  | u :: us => mixHash (levelHash u) (levelsHash us)

/-- Expressions with computed per-node fields.  The constructors carry
the same payload as `Setlec.Expr`, plus the four derived fields
(`h` hash, `bb` loose-bvar bound, `fb` fvar range, `lp`
has-level-param) — always the *last* explicit arguments, so patterns
read `.app f a ..` and construction goes through the smart
constructors below (`mkApp` &c.), never through the raw constructor. -/
inductive ExprC where
  | bvar (i : Nat) (h : UInt64) (bb fb : Nat) (lp : Bool)
  | fvar (idx : Nat) (name : Name) (type : ExprC)
      (h : UInt64) (bb fb : Nat) (lp : Bool)
  | sort (u : Level) (h : UInt64) (bb fb : Nat) (lp : Bool)
  | const (n : Name) (us : List Level) (h : UInt64) (bb fb : Nat) (lp : Bool)
  | app (f a : ExprC) (h : UInt64) (bb fb : Nat) (lp : Bool)
  | lam (n : Name) (type body : ExprC) (m : BinderMeta)
      (h : UInt64) (bb fb : Nat) (lp : Bool)
  | forallE (n : Name) (type body : ExprC) (m : BinderMeta)
      (h : UInt64) (bb fb : Nat) (lp : Bool)
  | letE (n : Name) (type value body : ExprC)
      (h : UInt64) (bb fb : Nat) (lp : Bool)
  | lit (l : Literal) (h : UInt64) (bb fb : Nat) (lp : Bool)
  | proj (structName : Name) (idx : Nat) (e : ExprC)
      (h : UInt64) (bb fb : Nat) (lp : Bool)
  deriving Inhabited, Repr

namespace ExprC

/-! ## The derived-field readers (all `O(1)`) -/

/-- The node's cached hash. -/
@[inline] def hash : ExprC → UInt64
  | .bvar _ h _ _ _ | .fvar _ _ _ h _ _ _ | .sort _ h _ _ _
  | .const _ _ h _ _ _ | .app _ _ h _ _ _ | .lam _ _ _ _ h _ _ _
  | .forallE _ _ _ _ h _ _ _ | .letE _ _ _ _ h _ _ _ | .lit _ h _ _ _
  | .proj _ _ _ h _ _ _ => h

/-- The node's cached loose-bvar bound (least `k` with
`looseBVarsBounded k`). -/
@[inline] def bvarB : ExprC → Nat
  | .bvar _ _ b _ _ | .fvar _ _ _ _ b _ _ | .sort _ _ b _ _
  | .const _ _ _ b _ _ | .app _ _ _ b _ _ | .lam _ _ _ _ _ b _ _
  | .forallE _ _ _ _ _ b _ _ | .letE _ _ _ _ _ b _ _ | .lit _ _ b _ _
  | .proj _ _ _ _ b _ _ => b

/-- The node's cached fvar range (max fvar index + 1; `0` = fvar-free). -/
@[inline] def fvarB : ExprC → Nat
  | .bvar _ _ _ f _ | .fvar _ _ _ _ _ f _ | .sort _ _ _ f _
  | .const _ _ _ _ f _ | .app _ _ _ _ f _ | .lam _ _ _ _ _ _ f _
  | .forallE _ _ _ _ _ _ f _ | .letE _ _ _ _ _ _ f _ | .lit _ _ _ f _
  | .proj _ _ _ _ _ f _ => f

/-- The node's cached has-level-param flag. -/
@[inline] def hasLP : ExprC → Bool
  | .bvar _ _ _ _ p | .fvar _ _ _ _ _ _ p | .sort _ _ _ _ p
  | .const _ _ _ _ _ p | .app _ _ _ _ _ p | .lam _ _ _ _ _ _ _ p
  | .forallE _ _ _ _ _ _ _ p | .letE _ _ _ _ _ _ _ p | .lit _ _ _ _ p
  | .proj _ _ _ _ _ _ p => p

/-- The node's cached fvar flag (`fvarB ≠ 0`; the arena's `hasFvarI`). -/
@[inline] def hasFvar (e : ExprC) : Bool := e.fvarB != 0

instance : Hashable ExprC := ⟨ExprC.hash⟩

/-! ## Smart constructors

Each computes the four derived fields from its children's — `O(1)`,
exactly the arena's intern-time recurrences. -/

@[inline] def mkBVar (i : Nat) : ExprC :=
  .bvar i (mixHash 3 (Hashable.hash i)) (i + 1) 0 false

@[inline] def mkFVar (idx : Nat) (n : Name) (ty : ExprC) : ExprC :=
  .fvar idx n ty
    (mixHash 5 (mixHash (Hashable.hash idx)
      (mixHash (Hashable.hash n) ty.hash)))
    0 (idx + 1) ty.hasLP

@[inline] def mkSort (u : Level) : ExprC :=
  .sort u (mixHash 7 (levelHash u)) 0 0 (levelHasParam u)

@[inline] def mkConst (n : Name) (us : List Level) : ExprC :=
  .const n us (mixHash 11 (mixHash (Hashable.hash n) (levelsHash us)))
    0 0 (levelsHaveParam us)

@[inline] def mkApp (f a : ExprC) : ExprC :=
  .app f a (mixHash 17 (mixHash f.hash a.hash))
    (max f.bvarB a.bvarB) (max f.fvarB a.fvarB) (f.hasLP || a.hasLP)

@[inline] def mkLam (n : Name) (ty body : ExprC) (m : BinderMeta) : ExprC :=
  .lam n ty body m
    (mixHash 19 (mixHash (Hashable.hash n)
      (mixHash ty.hash (mixHash body.hash (Hashable.hash m)))))
    (max ty.bvarB (body.bvarB - 1)) (max ty.fvarB body.fvarB)
    (ty.hasLP || body.hasLP || m.pw.hasParams)

@[inline] def mkForallE (n : Name) (ty body : ExprC) (m : BinderMeta) :
    ExprC :=
  .forallE n ty body m
    (mixHash 23 (mixHash (Hashable.hash n)
      (mixHash ty.hash (mixHash body.hash (Hashable.hash m)))))
    (max ty.bvarB (body.bvarB - 1)) (max ty.fvarB body.fvarB)
    (ty.hasLP || body.hasLP || m.pw.hasParams)

@[inline] def mkLetE (n : Name) (ty val body : ExprC) : ExprC :=
  .letE n ty val body
    (mixHash 29 (mixHash (Hashable.hash n)
      (mixHash ty.hash (mixHash val.hash body.hash))))
    (max (max ty.bvarB val.bvarB) (body.bvarB - 1))
    (max (max ty.fvarB val.fvarB) body.fvarB)
    (ty.hasLP || val.hasLP || body.hasLP)

@[inline] def mkLit (l : Literal) : ExprC :=
  .lit l (mixHash 31 (Hashable.hash l)) 0 0 false

@[inline] def mkProj (s : Name) (i : Nat) (e : ExprC) : ExprC :=
  .proj s i e
    (mixHash 37 (mixHash (Hashable.hash s) (mixHash (Hashable.hash i) e.hash)))
    e.bvarB e.fvarB e.hasLP

/-! ## Equality

The official kernel's `is_equal`: pointer identity, then the cached
hashes (a cheap reject — a hash mismatch *is* an inequality), then
structural descent.  Since instantiation and abstraction return
unchanged subterms **by reference**, the pointer test decides most
comparisons in `O(1)`, which is the arena's index comparison in a
different mechanism. -/

/-- Structural equality, the specification: the cached hash fields are
compared at **every** node, then the payload structurally.  The hash
test is part of the spec (not just of the fast path) because the
executed descents (`beqB`, `beqGo`) reject on hash mismatch at every
level — with it, the `implemented_by` claim is faithful on all inputs,
not only on field-correct ones, and the hash conjunct is what makes
`LawfulHashable ExprC` a *theorem* (task #163; the memo-map lemmas
need it).  On field-correct terms (`WFc`, see
`Setlec/Verify/Cached/Erase.lean`) the hash test is redundant and
`beqSpec` decides equality of the erasures exactly. -/
def beqSpec (a b : ExprC) : Bool :=
  a.hash == b.hash &&
  match a, b with
  | .bvar i .., .bvar j .. => i == j
  | .fvar i n t .., .fvar j m u .. => i == j && n == m && beqSpec t u
  | .sort u .., .sort v .. => u == v
  | .const n us .., .const m vs .. => n == m && us == vs
  | .app f a .., .app g b .. => beqSpec f g && beqSpec a b
  | .lam n t b m .., .lam n' t' b' m' .. =>
    n == n' && m == m' && beqSpec t t' && beqSpec b b'
  | .forallE n t b m .., .forallE n' t' b' m' .. =>
    n == n' && m == m' && beqSpec t t' && beqSpec b b'
  | .letE n t v b .., .letE n' t' v' b' .. =>
    n == n' && beqSpec t t' && beqSpec v v' && beqSpec b b'
  | .lit l .., .lit l' .. => l == l'
  | .proj s i e .., .proj s' i' e' .. => s == s' && i == i' && beqSpec e e'
  | _, _ => false

/-- The executed equality: pointer test, hash test, then a **memoized**
structural descent.

The memo (keyed by the pair of addresses, storing the decided answer)
is what keeps equality `O(DAG)` rather than `O(tree)`.  It is not
optional at this representation: hash-consing identifies structurally
equal terms *however they arose*, so the arena never compares two
distinct-but-equal DAGs; the clone does exactly that whenever a
reduction rebuilds a term the arena would have collapsed, and without
the memo `good/perf/app-lam` (24 k arena nodes, ~10^1160 unshared
tree) is unreachable.  Pointer identity and the hash test still carry
the overwhelming majority of comparisons; the memo is allocated only
on the descent. -/
unsafe def beqGo (memo : Std.HashMap (USize × USize) Bool) (a b : ExprC) :
    Bool × Std.HashMap (USize × USize) Bool :=
  let pa := ptrAddrUnsafe a
  let pb := ptrAddrUnsafe b
  if pa == pb then (true, memo)
  else if a.hash != b.hash then (false, memo)
  else
    match memo[(pa, pb)]? with
    | some r => (r, memo)
    | none =>
      let and2 := fun (memo : Std.HashMap (USize × USize) Bool)
          (x y : ExprC) (z w : ExprC) =>
        let (r₁, memo) := beqGo memo x y
        if r₁ then beqGo memo z w else (false, memo)
      let (r, memo) : Bool × Std.HashMap (USize × USize) Bool :=
        match a, b with
        | .bvar i .., .bvar j .. => (i == j, memo)
        | .fvar i n t .., .fvar j m u .. =>
          if i == j && n == m then beqGo memo t u else (false, memo)
        | .sort u .., .sort v .. => (u == v, memo)
        | .const n us .., .const m vs .. => (n == m && us == vs, memo)
        | .app f x .., .app g y .. => and2 memo f g x y
        | .lam n t b m .., .lam n' t' b' m' .. =>
          if n == n' && m == m' then and2 memo t t' b b' else (false, memo)
        | .forallE n t b m .., .forallE n' t' b' m' .. =>
          if n == n' && m == m' then and2 memo t t' b b' else (false, memo)
        | .letE n t v b .., .letE n' t' v' b' .. =>
          if n == n' then
            let (r₁, memo) := beqGo memo t t'
            if r₁ then and2 memo v v' b b' else (false, memo)
          else (false, memo)
        | .lit l .., .lit l' .. => (l == l', memo)
        | .proj s i e .., .proj s' i' e' .. =>
          if s == s' && i == i' then beqGo memo e e' else (false, memo)
        | _, _ => (false, memo)
      (r, memo.insert (pa, pb) r)

/-- Node budget of the allocation-free descent before the memoized one
takes over.  Almost every comparison the checker makes is decided by
the pointer test, the hash test, or a handful of nodes; paying for a
memo table there was measured at +33 % instructions on `init-prelude`.
Beyond the budget the term is big enough that `O(tree)` is the real
risk, and the memoized descent is restarted from scratch. -/
def beqBudget : Nat := 4096

/-- Allocation-free structural descent on a node budget: `none` when
the budget runs out (the caller retries under the memo). -/
unsafe def beqB (fuel : Nat) (a b : ExprC) : Option Bool × Nat :=
  if ptrAddrUnsafe a == ptrAddrUnsafe b then (some true, fuel)
  else if a.hash != b.hash then (some false, fuel)
  else
    match fuel with
    | 0 => (none, 0)
    | fuel + 1 =>
      let and2 := fun (fuel : Nat) (x y z w : ExprC) =>
        match beqB fuel x y with
        | (some true, fuel) => beqB fuel z w
        | r => r
      match a, b with
      | .bvar i .., .bvar j .. => (some (i == j), fuel)
      | .fvar i n t .., .fvar j m u .. =>
        if i == j && n == m then beqB fuel t u else (some false, fuel)
      | .sort u .., .sort v .. => (some (u == v), fuel)
      | .const n us .., .const m vs .. => (some (n == m && us == vs), fuel)
      | .app f x .., .app g y .. => and2 fuel f g x y
      | .lam n t b m .., .lam n' t' b' m' .. =>
        if n == n' && m == m' then and2 fuel t t' b b' else (some false, fuel)
      | .forallE n t b m .., .forallE n' t' b' m' .. =>
        if n == n' && m == m' then and2 fuel t t' b b' else (some false, fuel)
      | .letE n t v b .., .letE n' t' v' b' .. =>
        if n == n' then
          match beqB fuel t t' with
          | (some true, fuel) => and2 fuel v v' b b'
          | r => r
        else (some false, fuel)
      | .lit l .., .lit l' .. => (some (l == l'), fuel)
      | .proj s i e .., .proj s' i' e' .. =>
        if s == s' && i == i' then beqB fuel e e' else (some false, fuel)
      | _, _ => (some false, fuel)

/-- The executed equality (see `beqGo`).

**TRUST POINT** (task #163; one of exactly two `implemented_by`
escapes the verified cached variant rests on).  The pure spec is
`beqSpec`; the acceleration is faithful to it given two facts about
the runtime: (a) *pointer equality implies structural equality* —
Lean objects are immutable, so two references to one address are one
value (the pointer short-circuits here and in `beqB`/`beqGo`, and the
address-pair memo keys, all rest on this); (b) *the address-keyed memo
entries stay valid for the life of one comparison* — both roots are
live for the whole call, so every keyed subobject is reachable and
the collector, which never moves objects, cannot reuse a keyed
address.  The verification (`Setlec/Verify/Cached/*`) consumes only
`beq`'s pure definition and never this function. -/
unsafe def beqFast (a b : ExprC) : Bool :=
  if ptrAddrUnsafe a == ptrAddrUnsafe b then true
  else if a.hash != b.hash then false
  else
    match (beqB beqBudget a b).1 with
    | some r => r
    | none => (beqGo {} a b).1

@[implemented_by beqFast]
def beq (a b : ExprC) : Bool := beqSpec a b

instance : BEq ExprC := ⟨ExprC.beq⟩

/-! ## The `Expr` boundary

The declaration checker above `CheckerOps` is `Expr`-typed (it is
shared verbatim with the production checker — the pilot replaces the
*core*, nothing above it), so each entry-point call converts its
arguments in and its result out.  This is the exact counterpart of the
interned checker's `internExprM` / `readbackI` at the same seam:

* `ofExpr` converts bottom-up under a **pointer-keyed** memo, so the
  input's structure sharing is carried across the boundary intact
  (`Expr` values reaching the core come from the parse arena's
  memoized readback and from the environment, both pointer-shared
  DAGs).  This is load-bearing, not an optimization: `EStore.internExpr`
  is a plain tree walk that nevertheless *recovers* full sharing,
  because hash-consing maps every structurally equal node to one
  index.  The clone has no cons table, so if the conversion did not
  preserve sharing the DAG would arrive as a tree — measured: the
  `dag_tower` e2e fixture does not terminate that way, while the
  interned checker takes it in stride.  The pointer memo is the
  computed-field representation's answer, and it is exactly what the
  official kernel does at the same kind of seam;
* `toExpr` is memoized on `ExprC` keys (`O(1)` hashing, pointer-fast
  equality), so a shared sub-DAG is rebuilt once and the resulting
  `Expr` is shared — the counterpart of the memoized `readbackI`. -/

/-- Structural conversion, the specification (no sharing memo). -/
def ofExprSpec : Expr → ExprC
  | .bvar i => mkBVar i
  | .fvar idx n ty => mkFVar idx n (ofExprSpec ty)
  | .sort u => mkSort u
  | .const n us => mkConst n us
  | .app f a => mkApp (ofExprSpec f) (ofExprSpec a)
  | .lam n ty b m => mkLam n (ofExprSpec ty) (ofExprSpec b) m
  | .forallE n ty b m => mkForallE n (ofExprSpec ty) (ofExprSpec b) m
  | .letE n ty v b => mkLetE n (ofExprSpec ty) (ofExprSpec v) (ofExprSpec b)
  | .lit l => mkLit l
  | .proj s i e => mkProj s i (ofExprSpec e)

/-- Convert an `Expr` into an `ExprC`, computing the derived fields
bottom-up.

**The former second trust point is DELETED** (user ruling, 2026-09-03):
this used to carry `@[implemented_by ofExprFast]` — a pointer-address
memo preserving the input's sharing — because the pilot converted
materialized `Expr` trees at the `CheckerOps` seam on the hot path.
The shipped cached pipeline no longer does: declaration terms enter as
`ExprC` through the index-memoized `ofStore` conversion of the parse
arena (`Setlec/Cached/ParsedC.lean`) and are served from the `ienv`
record thereafter (`recordCConst`/`storedTyIdxM`/`storedValIdxM`), so
the only remaining callers convert **frontend-budgeted** trees — axiom
and inductive-block member types and rule right-hand sides at their
first `(name, levels)` instantiation, fabricated terms, and the
`--core=cached` Expr-boundary pilot driver (explicitly unverified and
un-swept, whose per-entry conversion is now the pure tree walk: a
sharing-heavy stress term such as `dag_tower` is out of that pilot's
reach by design — use `cached-parsed`).  The pure walk is the
definition; there is nothing left to trust. -/
def ofExpr (e : Expr) : ExprC := ofExprSpec e

/-- Core of `toExpr`: a memoized readback (shared subterms are rebuilt
once and share the resulting `Expr` in memory).  Structurally
recursive, hence **not** a trust point: `toExpr_eq`
(`Setlec/Verify/Cached/Erase.lean`) proves the readback equal to the
structural erasure outright — a memo hit's key is `beq`-equal to the
query, and `beq`-equal terms have equal erasures. -/
def toExprGo (memo : Std.HashMap ExprC Expr) (e : ExprC) :
    Expr × Std.HashMap ExprC Expr :=
  match memo[e]? with
  | some x => (x, memo)
  | none =>
    let (r, memo) : Expr × Std.HashMap ExprC Expr :=
      match e with
      | .bvar i .. => (.bvar i, memo)
      | .fvar idx n ty .. =>
        let (t, memo) := toExprGo memo ty
        (.fvar idx n t, memo)
      | .sort u .. => (.sort u, memo)
      | .const n us .. => (.const n us, memo)
      | .app f a .. =>
        let (f', memo) := toExprGo memo f
        let (a', memo) := toExprGo memo a
        (.app f' a', memo)
      | .lam n ty b m .. =>
        let (t, memo) := toExprGo memo ty
        let (b', memo) := toExprGo memo b
        (.lam n t b' m, memo)
      | .forallE n ty b m .. =>
        let (t, memo) := toExprGo memo ty
        let (b', memo) := toExprGo memo b
        (.forallE n t b' m, memo)
      | .letE n ty v b .. =>
        let (t, memo) := toExprGo memo ty
        let (v', memo) := toExprGo memo v
        let (b', memo) := toExprGo memo b
        (.letE n t v' b', memo)
      | .lit l .. => (.lit l, memo)
      | .proj s i sub .. =>
        let (s', memo) := toExprGo memo sub
        (.proj s i s', memo)
    (r, memo.insert e r)

/-- Read an `ExprC` back as an `Expr` (memoized DAG walk). -/
def toExpr (e : ExprC) : Expr := (toExprGo {} e).1

end ExprC

/-! ## The one-level view

`Setlec.ExprView` (defined in `Setlec/Kernel/Core.lean`) is the
representation-generic one-level view the core bodies destructure
through; `ExprC` instantiates it with no allocation on the read side. -/

end Setlec.Cached
