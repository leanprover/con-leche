module

public import Std.Data.HashMap

/-!
# Kernel expressions

The checker's own term representation, mirroring Lean's kernel expressions.
We deliberately do not reuse `Lean.Expr`: our own inductive has no cached
metadata, which keeps the verification story clean.

Design decisions (see DESIGN.md):
* Free variables (`fvar`) follow nanoda's representation: a de Bruijn *level*
  together with the variable's type (and binder name, for error messages).
  The type is part of the variable's identity, so a local context is implicit
  in every open term.  Input terms coming from declarations are closed and
  use only `bvar` (de Bruijn *indices*).
* No metavariables, no `mdata`: those never reach a kernel.
-/

@[expose] public section

namespace Setlec

/-- Hierarchical names, same shape as `Lean.Name` but without the cached hash,
so that it is a plain inductive datatype convenient for verification. -/
inductive Name where
  | anonymous
  | str (pre : Name) (s : String)
  | num (pre : Name) (n : Nat)
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Name

/-- Conversion from `Lean.Name` (dropping macro scopes is the caller's duty). -/
def ofLeanName : Lean.Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (ofLeanName p) s
  | .num p n => .num (ofLeanName p) n

protected def toString : Name → String
  | .anonymous => "[anonymous]"
  | .str .anonymous s => s
  | .str p s => p.toString ++ "." ++ s
  | .num .anonymous n => toString n
  | .num p n => p.toString ++ "." ++ toString n

instance : ToString Name := ⟨Name.toString⟩

end Name

/-- Universe levels, mirroring `Lean.Level` without metavariables. -/
inductive Level where
  | zero
  | succ (u : Level)
  | max (u v : Level)
  | imax (u v : Level)
  | param (n : Name)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Binder annotations. Irrelevant to checking; kept for round-tripping and
error messages. -/
inductive BinderInfo where
  | default
  | implicit
  | strictImplicit
  | instImplicit
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- PROBE (agent/pw-bitmask): the zero-ness datum of a binder's codomain
sort as a **flat positional bitmask** over the *current declaration's*
level-parameter list — bit `i` set = "the `i`-th level parameter must
be zero"; `always = 0` (zero at every valuation); `never = all ones`
(nonzero at every valuation — distinct from every satisfiable set as
long as the declaration has at most 63 parameters, which the checker
must decline above).  An `abbrev` for `UInt64`, so a `BinderMeta` holds
it as an inline scalar: no heap object, no list cells, and `=`/`==`/
`hash` all decide zero-ness agreement outright (the free datum's
containment test `equiv` and the `ZeroSet` canonical form collapse to
word equality).  The former free datum `never | ifAllZero (ps : List
Name)` and its laws are in the task-#161 design record. -/
abbrev PropWhen := UInt64

namespace PropWhen

/-- Nonzero at every valuation: all ones. -/
def never : PropWhen := 0xFFFFFFFFFFFFFFFF

/-- Zero at every valuation: the empty condition. -/
def always : PropWhen := 0

/-- The number of level parameters a declaration may have: above this
the mask's `never` value would coincide with a satisfiable set. -/
def maxParams : Nat := 63

/-- Position `i`'s singleton condition. -/
@[inline] def bit (i : Nat) : PropWhen := (1 : UInt64) <<< i.toUInt64

/-- Does the datum hold at a positional valuation — is the codomain
sort zero there?  (Spec only: the kernel never evaluates this.) -/
def holds (ψ : Nat → Nat) (pw : PropWhen) : Bool :=
  pw != never && (List.range 64).all fun i => (pw &&& bit i) == 0 || ψ i == 0

/-- Is the datum `never` — the graph regime everywhere. -/
@[inline] def isNever (pw : PropWhen) : Bool := pw == never

/-- Does the datum mention any level parameter — is `Level.substPW`
ever non-trivial on it? -/
@[inline] def hasParams (pw : PropWhen) : Bool := pw != never && pw != always

/-- Are all positions of the datum below `n` (the declaration's
parameter count)?  `never` is defined everywhere. -/
@[inline] def paramsDefined (n : Nat) (pw : PropWhen) : Bool :=
  pw == never || (pw >>> n.toUInt64) == 0

/-- Intersection of two zero-ness predicates (the `max` rule: a `max`
is zero iff both sides are): union of the conditions; `never` (all
ones) absorbs. -/
@[inline] def inter (a b : PropWhen) : PropWhen := a ||| b

/-- Substitute each position of the datum by a whole datum and intersect
— the monadic bind: the union of `ms[i]` over the set bits `i`; a
position beyond `ms` (an undefined parameter) is `never`.  Identity
(`ms[i] = bit i`) and composition are unconditional bit algebra. -/
def bindZ (ms : List PropWhen) (pw : PropWhen) : PropWhen :=
  if pw == never then never else go ms pw
where
  go : List PropWhen → UInt64 → PropWhen
  | [], w => if w == 0 then always else never
  | m :: rest, w =>
    if w == 0 then always
    else
      let here := if (w &&& 1) == 1 then m else always
      if here == never then never else here ||| go rest (w >>> 1)

/-- Zero-ness agreement at every valuation: word equality. -/
@[inline] def equiv (a b : PropWhen) : Bool := a == b

end PropWhen

/-- Metadata carried by a binder (`forallE`, `lam`): the display
`BinderInfo` and the codomain prop-ness annotation `pw` (task #161 —
the validated-annotation design; one datum per binder, written by the
untrusted annotate pass or the input stream and *validated* by the
checker; the reduction rules never read it).  Unannotated input
defaults to `.never` at the parser — a definite, validatable claim. -/
structure BinderMeta where
  bi : BinderInfo
  pw : PropWhen
  deriving DecidableEq, Repr, Hashable

instance : Inhabited BinderMeta := ⟨⟨.default, .never⟩⟩

/-- Literals. -/
inductive Literal where
  | natVal (n : Nat)
  | strVal (s : String)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- Depth-bounded `Level` hash (towers from universe arithmetic can be
deep; the memo maps only need *some* function of the value). -/
def Level.hashB : Nat → Level → UInt64
  | 0, _ => 511
  | _ + 1, .zero => 1
  | n + 1, .succ u => mixHash 3 (Level.hashB n u)
  | n + 1, .max u v => mixHash 5 (mixHash (Level.hashB n u) (Level.hashB n v))
  | n + 1, .imax u v => mixHash 7 (mixHash (Level.hashB n u) (Level.hashB n v))
  | _ + 1, .param p => mixHash 11 (hash p)

/-- Does the level mention a parameter (the official kernel's
`level.has_param`)?  There is no interned level table here, so this is
an `O(|u|)` walk — paid once per `.sort`/`.const` node construction,
never per memo touch. -/
def levelHasParam : Level → Bool
  | .zero => false
  | .param _ => true
  | .succ u => levelHasParam u
  | .max u v | .imax u v => levelHasParam u || levelHasParam v

/-- `levelHasParam` over a `const` node's level arguments. -/
def levelsHaveParam : List Level → Bool
  | [] => false
  | u :: us => levelHasParam u || levelsHaveParam us

/-- Depth-bounded level hash (a hash may ignore structure; `BEq` stays
full).  Keeping it bounded is what makes a `.sort`/`.const` node's
`hash` field `O(1)` in the level's size. -/
@[inline] def levelHash (u : Level) : UInt64 := Level.hashB 4 u

/-- `levelHash` folded over a level list. -/
def levelsHash : List Level → UInt64
  | [] => 13
  | u :: us => mixHash (levelHash u) (levelsHash us)

/-- Kernel expressions.

`fvar idx name type`: an opened variable, identified by its de Bruijn level
`idx` *and* its type; the binder `name` is display-only.  Closed input terms
contain no `fvar`s.

## The computed fields (task #172 B3a)

Every node carries a block of derived data, **computed once at
construction time** by Lean's `@[computed_field]` feature — exactly
`Lean.Expr`'s own arrangement:

* `hash`  — the node's hash, so hashing a term for a memo lookup is a
  field read instead of a traversal;
* `bvarB` — the loose-bvar *bound*: the least `k` with
  `looseBVarsBounded k` (`Expr.bvarBound` is the same recurrence
  spelled as an ordinary function; `bvarB_eq` proves them equal).
  Instantiation at or above the bound is the identity;
* `fvarB` — the fvar *range*: max fvar index + 1 (`0` = fvar-free;
  `fvar` type annotations are not descended, matching the abstraction
  traversals — `Expr.fvarRange`).  Abstraction at or above the range
  is the identity;
* `hasLP` — has-level-param (`Expr.hasLevelParam`; the official
  kernel's `has_univ_param`).  Level instantiation on a node without
  it is the identity.

Logically each field is an ordinary recursive function — the
constructors take no extra arguments, patterns are unaffected, and
`(Expr.app f a).bvarB = max f.bvarB a.bvarB` is `rfl`.  The *storage*
is the compiler's: `Lean/Elab/ComputedFields.lean:33` — *"This file
implements the computed fields feature by simulating it via
`implemented_by`."*  That is a named trust escape; it is enumerated,
with the user ruling that adopted it, in the trust census in
`Setlec/Cached/ExprC.lean`'s module docstring. -/
inductive Expr where
  | bvar (i : Nat)
  | fvar (idx : Nat) (name : Name) (type : Expr)
  | sort (u : Level)
  | const (n : Name) (us : List Level)
  | app (f a : Expr)
  | lam (n : Name) (type body : Expr) (m : BinderMeta)
  | forallE (n : Name) (type body : Expr) (m : BinderMeta)
  | letE (n : Name) (type value body : Expr)
  | lit (l : Literal)
  | proj (structName : Name) (idx : Nat) (e : Expr)
with
  /-- The node's hash (`O(1)`; display-only payload is included, which a
  hash may do — `DecidableEq` remains full structural equality). -/
  @[computed_field] hash : Expr → UInt64
    | .bvar i => mixHash 3 (Hashable.hash i)
    | .fvar idx n ty =>
      mixHash 5 (mixHash (Hashable.hash idx)
        (mixHash (Hashable.hash n) ty.hash))
    | .sort u => mixHash 7 (levelHash u)
    | .const n us => mixHash 11 (mixHash (Hashable.hash n) (levelsHash us))
    | .app f a => mixHash 17 (mixHash f.hash a.hash)
    | .lam n ty b m =>
      mixHash 19 (mixHash (Hashable.hash n)
        (mixHash ty.hash (mixHash b.hash (Hashable.hash m))))
    | .forallE n ty b m =>
      mixHash 23 (mixHash (Hashable.hash n)
        (mixHash ty.hash (mixHash b.hash (Hashable.hash m))))
    | .letE n ty v b =>
      mixHash 29 (mixHash (Hashable.hash n)
        (mixHash ty.hash (mixHash v.hash b.hash)))
    | .lit l => mixHash 31 (Hashable.hash l)
    | .proj s i e =>
      mixHash 37 (mixHash (Hashable.hash s) (mixHash (Hashable.hash i) e.hash))
  /-- The loose-bvar bound: the least `k` with `looseBVarsBounded k`. -/
  @[computed_field] bvarB : Expr → Nat
    | .bvar i => i + 1
    | .fvar _ _ _ | .sort _ | .const _ _ | .lit _ => 0
    | .app f a => max f.bvarB a.bvarB
    | .lam _ ty b _ | .forallE _ ty b _ => max ty.bvarB (b.bvarB - 1)
    | .letE _ ty v b => max (max ty.bvarB v.bvarB) (b.bvarB - 1)
    | .proj _ _ e => e.bvarB
  /-- The fvar range: max fvar index + 1 (`0` = fvar-free). -/
  @[computed_field] fvarB : Expr → Nat
    | .fvar idx _ _ => idx + 1
    | .bvar _ | .sort _ | .const _ _ | .lit _ => 0
    | .app f a => max f.fvarB a.fvarB
    | .lam _ ty b _ | .forallE _ ty b _ => max ty.fvarB b.fvarB
    | .letE _ ty v b => max (max ty.fvarB v.fvarB) b.fvarB
    | .proj _ _ e => e.fvarB
  /-- Has-level-param: is level instantiation ever non-trivial here? -/
  @[computed_field] hasLP : Expr → Bool
    | .bvar _ | .lit _ => false
    | .sort u => levelHasParam u
    | .const _ us => levelsHaveParam us
    | .fvar _ _ ty => ty.hasLP
    | .app f a => f.hasLP || a.hasLP
    | .lam _ ty b m | .forallE _ ty b m =>
      ty.hasLP || b.hasLP || m.pw.hasParams
    | .letE _ ty v b => ty.hasLP || v.hasLP || b.hasLP
    | .proj _ _ e => e.hasLP
deriving DecidableEq, Repr, Inhabited

/-- Hashing is the computed field: `O(1)`, no traversal.  (Before task
#172 B3a this was a *node-budgeted* walk, `Expr.hashB`, because the
pure representation had nowhere to put a hash; the budget is now only
inside `levelHash`.) -/
instance : Hashable Expr := ⟨Expr.hash⟩

namespace Expr

/-! ## Equality

The official kernel's `is_equal`: pointer identity, then the computed
hashes (a cheap reject — a hash mismatch *is* an inequality), then
structural descent.  Since instantiation and abstraction return
unchanged subterms **by reference**, the pointer test decides most
comparisons in `O(1)`, which is the arena's index comparison in a
different mechanism.

**The specification is plain decidable equality** (task #172 B3a).  It
used to be `beqSpec`, a hash-checking descent, because the hash was a
*stored* datum that could disagree with the term: the spec had to
compare it so that the `implemented_by` claim stayed faithful on
field-incorrect inputs.  Under `@[computed_field]` there are no
field-incorrect inputs — `a.hash` is a function of `a` — so the hash
test is an implementation detail of the fast path again, and
`beq = decide (a = b)` is defeq to the `BEq` instance any type gets
from its `DecidableEq`. -/

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
unsafe def beqGo (memo : Std.HashMap (USize × USize) Bool) (a b : Expr) :
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
          (x y : Expr) (z w : Expr) =>
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
unsafe def beqB (fuel : Nat) (a b : Expr) : Option Bool × Nat :=
  if ptrAddrUnsafe a == ptrAddrUnsafe b then (some true, fuel)
  else if a.hash != b.hash then (some false, fuel)
  else
    match fuel with
    | 0 => (none, 0)
    | fuel + 1 =>
      let and2 := fun (fuel : Nat) (x y z w : Expr) =>
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

**TRUST POINT** (task #163; the first of the **two** escapes the
verified cached variant rests on — see the census in this module's
header docstring).  The pure spec is *decidable equality*, and under
computed fields the hash test needs no side condition (`a.hash` is a
function of `a`, so a hash mismatch is an inequality outright — task
#172 B3a shrank this argument exactly as B2 predicted).  What is left
to trust is two facts about the runtime: (a) *pointer equality implies structural equality* —
Lean objects are immutable, so two references to one address are one
value (the pointer short-circuits here and in `beqB`/`beqGo`, and the
address-pair memo keys, all rest on this); (b) *the address-keyed memo
entries stay valid for the life of one comparison* — both roots are
live for the whole call, so every keyed subobject is reachable and
the collector, which never moves objects, cannot reuse a keyed
address.  The verification (`Setlec/Verify/Cached/*`) consumes only
`beq`'s pure definition and never this function. -/
unsafe def beqFast (a b : Expr) : Bool :=
  if ptrAddrUnsafe a == ptrAddrUnsafe b then true
  else if a.hash != b.hash then false
  else
    match (beqB beqBudget a b).1 with
    | some r => r
    | none => (beqGo {} a b).1

/-- The executed structural equality.  Definitionally `decide (a = b)`,
hence definitionally the `BEq` any `DecidableEq` type has; the
`implemented_by` above replaces it by the accelerated descent. -/
@[implemented_by beqFast]
def beq (a b : Expr) : Bool := decide (a = b)

instance : BEq Expr := ⟨Expr.beq⟩

/-- `beq` is lawful — it *is* `decide (· = ·)`. -/
instance : LawfulBEq Expr where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq, Expr.beq]

end Expr

end Setlec
