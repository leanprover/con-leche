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

/-- Structural equality, the specification (no shortcuts). -/
def beqSpec : ExprC → ExprC → Bool
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

@[inherit_doc beqGo]
unsafe def beqFast (a b : ExprC) : Bool :=
  if ptrAddrUnsafe a == ptrAddrUnsafe b then true
  else if a.hash != b.hash then false
  else (beqGo {} a b).1

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

/-- Core of the executed conversion: bottom-up under a pointer-address
memo.  Sound because the root stays reachable for the whole traversal,
so every subterm whose address is a key is alive (Lean's collector
never moves objects). -/
unsafe def ofExprGo (memo : Std.HashMap USize ExprC) (e : Expr) :
    ExprC × Std.HashMap USize ExprC :=
  let k := ptrAddrUnsafe e
  match memo[k]? with
  | some r => (r, memo)
  | none =>
    let (r, memo) : ExprC × Std.HashMap USize ExprC :=
      match e with
      | .bvar i => (mkBVar i, memo)
      | .fvar idx n ty =>
        let (t, memo) := ofExprGo memo ty
        (mkFVar idx n t, memo)
      | .sort u => (mkSort u, memo)
      | .const n us => (mkConst n us, memo)
      | .app f a =>
        let (f', memo) := ofExprGo memo f
        let (a', memo) := ofExprGo memo a
        (mkApp f' a', memo)
      | .lam n ty b m =>
        let (t, memo) := ofExprGo memo ty
        let (b', memo) := ofExprGo memo b
        (mkLam n t b' m, memo)
      | .forallE n ty b m =>
        let (t, memo) := ofExprGo memo ty
        let (b', memo) := ofExprGo memo b
        (mkForallE n t b' m, memo)
      | .letE n ty v b =>
        let (t, memo) := ofExprGo memo ty
        let (v', memo) := ofExprGo memo v
        let (b', memo) := ofExprGo memo b
        (mkLetE n t v' b', memo)
      | .lit l => (mkLit l, memo)
      | .proj s i sub =>
        let (s', memo) := ofExprGo memo sub
        (mkProj s i s', memo)
    (r, memo.insert k r)

@[inherit_doc ofExprSpec]
unsafe def ofExprFast (e : Expr) : ExprC := (ofExprGo {} e).1

/-- Convert an `Expr` into an `ExprC`, computing the derived fields
bottom-up and preserving the input's structure sharing. -/
@[implemented_by ofExprFast]
def ofExpr (e : Expr) : ExprC := ofExprSpec e

/-- Core of `toExpr`: a memoized readback (shared subterms are rebuilt
once and share the resulting `Expr` in memory). -/
partial def toExprGo (memo : Std.HashMap ExprC Expr) (e : ExprC) :
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
