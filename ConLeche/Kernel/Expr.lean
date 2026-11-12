module

public import ConLeche.Kernel.Name
public import ConLeche.Kernel.Exclusive
/- `withPtrEq` is `public` but not `@[expose]`, and its whole point here
is that it is *definitionally* `k ()` — which is what `Expr.beqMemo_eq`
proves.  `import all` makes that body visible **in this module only**;
that theorem is the public relay, so no importer needs it, and the
executed `Expr.beq` stays the plain `decide (· = ·)` that the kernel
can still reduce. -/
import all Init.Util

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

namespace ConLeche

/-- Universe levels, mirroring `Lean.Level` without metavariables —
including the cached hash, which `Lean.Level` also keeps in a
`@[computed_field]` (`data`, `Lean/Level.lean`) and the C++ kernel in
the level's packed data word (`level::hash()`).  As for `Name`, the
field is a function of the value and no statement sees it. -/
inductive Level where
  | zero
  | succ (u : Level)
  | max (u v : Level)
  | imax (u v : Level)
  | param (n : Name)
with
  /-- The cached hash of a level. -/
  @[computed_field] hashData : Level → UInt64
    | .zero => 1
    | .succ u => mixHash 3 u.hashData
    | .max u v => mixHash 5 (mixHash u.hashData v.hashData)
    | .imax u v => mixHash 7 (mixHash u.hashData v.hashData)
    | .param n => mixHash 11 (hash n)
deriving Repr, Inhabited

/-- Hashing a level is an `O(1)` field read (the memo maps keyed by
`Level` — `lsimpC`, `lnzC`, `eqvC` — probe with this). -/
instance : Hashable Level := ⟨Level.hashData⟩

/-- The specification of level equality: the structural decision. -/
def Level.decEq : (a b : Level) → Decidable (a = b)
  | .zero, .zero => isTrue rfl
  | .succ u, .succ v =>
    match Level.decEq u v with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun e => h (Level.succ.inj e))
  | .max u v, .max u' v' =>
    match Level.decEq u u', Level.decEq v v' with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (fun e => h (Level.max.inj e).1)
    | _, isFalse h' => isFalse (fun e => h' (Level.max.inj e).2)
  | .imax u v, .imax u' v' =>
    match Level.decEq u u', Level.decEq v v' with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (fun e => h (Level.imax.inj e).1)
    | _, isFalse h' => isFalse (fun e => h' (Level.imax.inj e).2)
  | .param n, .param m =>
    if h : n = m then isTrue (by rw [h])
    else isFalse (fun e => h (Level.param.inj e))
  | .zero, .succ .. | .zero, .max .. | .zero, .imax .. | .zero, .param ..
  | .succ .., .zero | .succ .., .max .. | .succ .., .imax .. | .succ .., .param ..
  | .max .., .zero | .max .., .succ .. | .max .., .imax .. | .max .., .param ..
  | .imax .., .zero | .imax .., .succ .. | .imax .., .max .. | .imax .., .param ..
  | .param .., .zero | .param .., .succ .. | .param .., .max .. | .param .., .imax .. =>
    isFalse (fun e => Level.noConfusion e)

/-- Level equality in the official kernel's shape (task #176 P2, at
every level since task #551): the **pointer** and the cached **hash**
before the structural step, at every node — `level.cpp:125` is `kind` →
`hash` → `is_eqp` → structural.  The children start over with the
pointer, the parameter with `Name.decEqPtr`. -/
def Level.decEqPtr (a b : Level) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ =>
    if hh : a.hashData = b.hashData then
      match a, b with
      | .zero, .zero => isTrue rfl
      | .succ u, .succ v =>
        match Level.decEqPtr u v with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (fun e => h (Level.succ.inj e))
      | .max u v, .max u' v' =>
        match Level.decEqPtr u u' with
        | isFalse h => isFalse (fun e => h (Level.max.inj e).1)
        | isTrue h =>
          match Level.decEqPtr v v' with
          | isTrue h' => isTrue (by rw [h, h'])
          | isFalse h' => isFalse (fun e => h' (Level.max.inj e).2)
      | .imax u v, .imax u' v' =>
        match Level.decEqPtr u u' with
        | isFalse h => isFalse (fun e => h (Level.imax.inj e).1)
        | isTrue h =>
          match Level.decEqPtr v v' with
          | isTrue h' => isTrue (by rw [h, h'])
          | isFalse h' => isFalse (fun e => h' (Level.imax.inj e).2)
      | .param n, .param m =>
        if h : n = m then isTrue (by rw [h])
        else isFalse (fun e => h (Level.param.inj e))
      | .zero, .succ .. | .zero, .max .. | .zero, .imax .. | .zero, .param ..
      | .succ .., .zero | .succ .., .max .. | .succ .., .imax .. | .succ .., .param ..
      | .max .., .zero | .max .., .succ .. | .max .., .imax .. | .max .., .param ..
      | .imax .., .zero | .imax .., .succ .. | .imax .., .max .. | .imax .., .param ..
      | .param .., .zero | .param .., .succ .. | .param .., .max .. | .param .., .imax .. =>
        isFalse (fun e => Level.noConfusion e)
    else isFalse (fun e => hh (by rw [e]))

/-- The `Level` twin of `Name.decEq_eq_decEqPtr`: `@[csimp]`, not
`@[implemented_by]`, on `Decidable`'s subsingleton property. -/
@[csimp] theorem Level.decEq_eq_decEqPtr : @Level.decEq = @Level.decEqPtr := by
  funext a b; exact Subsingleton.elim _ _

/-- Every level equality runs `Level.decEqPtr`. -/
instance : DecidableEq Level := Level.decEq

/-- The executed level equality: definitionally `decide (a = b)`. -/
def Level.beq (a b : Level) : Bool := decide (a = b)

instance : BEq Level := ⟨Level.beq⟩

/-- `Level.beq` is lawful — it *is* `decide (· = ·)`. -/
instance : LawfulBEq Level where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq, Level.beq]

/-- Literals. -/
inductive Literal where
  | natVal (n : Nat)
  | strVal (s : String)
  deriving Repr, Inhabited, Hashable

/-- The specification of literal equality: the structural decision. -/
def Literal.decEq : (a b : Literal) → Decidable (a = b)
  | .natVal n, .natVal m =>
    if h : n = m then isTrue (by rw [h]) else isFalse (fun e => h (Literal.natVal.inj e))
  | .strVal s, .strVal t =>
    if h : s = t then isTrue (by rw [h]) else isFalse (fun e => h (Literal.strVal.inj e))
  | .natVal _, .strVal _ | .strVal _, .natVal _ => isFalse (fun e => Literal.noConfusion e)

/-- Literal equality, pointer first (task #551): the `Literal` object,
then the number or string object, then the value.  `Nat.decEq` on two
big numbers is a GMP comparison with no pointer test (`lean_nat_eq`), so
the value's pointer is tested here; `lean_string_eq` tests it itself.
The hash comes before all this, one level up: an `Expr.lit` pair reaches
the literal comparison only past the nodes' computed words, which hold
the literal's hash (`Expr.beqMemo`, `enterBeq`).  A memo hit on a
literal that was found again in a new node is then one pointer test,
not a walk over the number's words. -/
@[inline] def Literal.decEqPtr (a b : Literal) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ =>
    match a, b with
    | .natVal n, .natVal m =>
      match withPtrEqDecEq n m (fun _ => Nat.decEq n m) with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (fun e => h (Literal.natVal.inj e))
    | .strVal s, .strVal t =>
      if h : s = t then isTrue (by rw [h]) else isFalse (fun e => h (Literal.strVal.inj e))
    | .natVal _, .strVal _ | .strVal _, .natVal _ => isFalse (fun e => Literal.noConfusion e)

/-- The `Literal` twin of `Name.decEq_eq_decEqPtr`. -/
@[csimp] theorem Literal.decEq_eq_decEqPtr : @Literal.decEq = @Literal.decEqPtr := by
  funext a b; exact Subsingleton.elim _ _

/-- Every literal equality runs `Literal.decEqPtr`. -/
instance : DecidableEq Literal := Literal.decEq

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

/-- A level's hash: the cached `@[computed_field]`, so a `.sort`/`.const`
node's `hash` field is `O(1)` in the level's size *and* exact. -/
@[inline] def levelHash (u : Level) : UInt64 := u.hashData

/-- `levelHash` folded over a level list. -/
def levelsHash : List Level → UInt64
  | [] => 13
  | u :: us => mixHash (levelHash u) (levelsHash us)

/-! ## The packed node word (task #167)

`Lean.Expr` stores its derived data in one `UInt64` (`Lean.Expr.Data`:
a 32-bit hash, a 20-bit `looseBVarRange`, flags).  `ConLeche.Expr` does
the same, with one `@[computed_field] data : Expr → UInt64` whose
layout is

| bits | field | width |
|---|---|---|
| 63…32 | `hash` | 32 |
| 31 | *reserved* (always 0) | 1 |
| 30…16 | `bvarB`, the loose-bvar bound | 15 |
| 15…1 | `fvarB`, the fvar range | 15 |
| 0 | `hasLP` | 1 |

The two ranges **saturate** at `satRange = 2^15 - 1`: a node whose
bound would not fit stores `satRange`, which reads as "*at least*
`satRange`".  Saturation is a *representation* decision and costs
nothing logically — `Expr.bvarB`/`Expr.fvarB` remain the exact
functions `Expr.bvarBound`/`Expr.fvarRange` (`bvarB_eq`, `fvarB_eq`),
because the accessors fall back to a memoized exact walk on the
saturated branch.  What saturation costs is *performance*, and only
on terms that saturate: the `O(1)` field read becomes an `O(DAG)`
walk.  Measured maxima on the real streams — `init-full` 213,
`grind-ring-5` 488, `app-lam` (the deepest artificial workload) 4000 —
leave the branch unreached with 8× headroom.

The packing is written with **arithmetic**, not bitwise, operators
(`* 65536` for a shift, `/ 65536 % 32768` for a field read): the code
LLVM emits is the same shift-and-mask, and every roundtrip lemma
below is then `omega` after `UInt64.toNat`. -/

/-- Saturation value of the two 15-bit range fields: a stored
`satRange` reads as "at least `satRange`". -/
def satRange : Nat := 32767

/-- Assemble the packed word from a 32-bit hash, two 15-bit ranges and
the level-param flag.  Sums, not `|||`: the fields are disjoint, so
addition *is* the bitwise join, and the arithmetic form is what makes
the roundtrip lemmas `omega`-provable. -/
@[inline] def packData (h b f : UInt64) (lp : Bool) : UInt64 :=
  h * 4294967296 + b * 65536 + f * 2 + (if lp then 1 else 0)

/-- Hash field of a packed word (bits 63…32). -/
@[inline] def hashOfData (w : UInt64) : UInt64 := w / 4294967296

/-- Loose-bvar-bound field of a packed word (bits 30…16). -/
@[inline] def bvarOfData (w : UInt64) : UInt64 := w / 65536 % 32768

/-- Fvar-range field of a packed word (bits 15…1). -/
@[inline] def fvarOfData (w : UInt64) : UInt64 := w / 2 % 32768

/-- Has-level-param field of a packed word (bit 0). -/
@[inline] def lpOfData (w : UInt64) : Bool := w % 2 == 1

/-- Truncate a mixed hash to the packed word's 32 bits. -/
@[inline] def hash32 (w : UInt64) : UInt64 := w % 4294967296

/-- A leaf's range field: `n + 1`, saturating. -/
@[inline] def satSucc (n : Nat) : UInt64 := UInt64.ofNat (min (n + 1) satRange)

/-- A binder's range field: the body's bound less one, saturating
(a saturated body keeps a saturated bound — the stored value means
"at least", and subtracting from it would under-approximate). -/
@[inline] def satPred (x : UInt64) : UInt64 :=
  if x == 32767 then 32767 else if x == 0 then 0 else x - 1

/-! ### The packing roundtrip -/

theorem bvarOfData_lt (w : UInt64) : (bvarOfData w).toNat < 32768 := by
  simp [bvarOfData, UInt64.toNat_mod]; omega

theorem fvarOfData_lt (w : UInt64) : (fvarOfData w).toNat < 32768 := by
  simp [fvarOfData, UInt64.toNat_mod]; omega

theorem satSucc_lt (n : Nat) : (satSucc n).toNat < 32768 := by
  simp [satSucc, satRange]; omega

/-- `UInt64.max` transports to `Nat.max` through `toNat`. -/
theorem toNat_max (a b : UInt64) : (max a b).toNat = max a.toNat b.toNat := by
  simp only [Max.max]
  split <;> rename_i h <;> simp_all [UInt64.le_iff_toNat_le] <;> omega

/-- Predecessor on a `UInt64` known to be nonzero. -/
theorem toNat_sub_one {x : UInt64} (h : x.toNat ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  have hs := UInt64.toNat_lt_size x
  simp only [UInt64.size] at hs
  simp only [UInt64.toNat_sub, UInt64.toNat_one]
  omega

theorem satPred_lt {x : UInt64} (hx : x.toNat < 32768) :
    (satPred x).toNat < 32768 := by
  unfold satPred
  split
  · decide
  · split
    · decide
    · rename_i h₁ h₂
      have hne : x.toNat ≠ 0 := by
        simpa [← UInt64.toNat_inj] using h₂
      rw [toNat_sub_one hne]
      omega

theorem max_lt_32768 {a b : UInt64} (ha : a.toNat < 32768)
    (hb : b.toNat < 32768) : (max a b).toNat < 32768 := by
  rw [toNat_max]; omega

theorem bvarOfData_pack (h b f : UInt64) (lp : Bool)
    (hb : b.toNat < 32768) (hf : f.toNat < 32768) :
    bvarOfData (packData h b f lp) = b := by
  apply UInt64.toNat_inj.mp
  cases lp <;>
  · simp [bvarOfData, packData, UInt64.toNat_add, UInt64.toNat_mul,
      UInt64.toNat_div, UInt64.toNat_mod]
    omega

theorem fvarOfData_pack (h b f : UInt64) (lp : Bool)
    (_hb : b.toNat < 32768) (hf : f.toNat < 32768) :
    fvarOfData (packData h b f lp) = f := by
  apply UInt64.toNat_inj.mp
  cases lp <;>
  · simp [fvarOfData, packData, UInt64.toNat_add, UInt64.toNat_mul,
      UInt64.toNat_div, UInt64.toNat_mod]
    omega

theorem lpOfData_pack (h b f : UInt64) (lp : Bool)
    (_hb : b.toNat < 32768) (_hf : f.toNat < 32768) :
    lpOfData (packData h b f lp) = lp := by
  cases lp <;>
  · simp [lpOfData, packData, ← UInt64.toNat_inj, UInt64.toNat_add,
      UInt64.toNat_mul, UInt64.toNat_mod]
    omega

/-- Kernel expressions.

`fvar idx type`: an opened variable, identified by its de Bruijn level
`idx` *and* its type.  Closed input terms contain no `fvar`s.

## No display data (task #205, user ruling)

The official kernel's `is_equal` and `hash` ignore binder names and
`BinderInfo`s (`expr_eq_fn.cpp:52, :100-103`).  Task #203 first made
every term the checker holds carry them at one normal form; the user's
ruling on that — *"if we don't keep the names we should drop the
fields!"* — is why `lam`/`forallE`/`letE` carry no binder name,
`fvar` no display name and `lam`/`forallE` carry no `BinderInfo` (nor
any other binder metadata, task #342): there is nothing α-irrelevant
in a node, so structural `=`/`==` and the packed `hash` ARE
α-equivalence, with nothing to normalise and nothing a fabricated term
could get wrong.  The frontend still *validates* a stream's `name` and
`binderInfo` fields (a malformed record is malformed) and drops them
(`ConLeche/Frontend/ExportC.lean`); the pin
builder's `pi "a"`/`piI "α"` keep the `Init.Prelude` spelling as a
reader-facing argument (`ConLeche/Kernel/Basis/Builder.lean`).  Error
messages never printed a binder name; positions (de Bruijn level,
constant name) are what they carry.

## The computed field (task #172 B3a; packed at task #167)

Every node carries a block of derived data, **computed once at
construction time** by Lean's `@[computed_field]` feature — exactly
`Lean.Expr`'s own arrangement, down to the packing:

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

**One word holds all four** (`data`, the layout table above
`satRange`), which is where the node's memory goes: four separate
fields cost a `UInt64`, two boxed `Nat` pointers and a `Bool`; one
word costs eight bytes.  `bvarB` and `fvarB` *saturate* at
`satRange`; the accessors stay **exact** by falling back, on the
saturated branch alone, to a memoized walk (`bvarBoundMemo`,
`fvarRangeMemo` in `Kernel/ExprOps.lean`).  So no lemma anywhere
weakens and no invariant is threaded: saturation buys memory and
costs performance, and only on terms that saturate.

The *storage* is the compiler's: `Lean/Elab/ComputedFields.lean:33` —
*"This file implements the computed fields feature by simulating it
via `implemented_by`."*  That is a named trust escape; it is
enumerated, with the user ruling that adopted it, in the trust census
in `ConLeche/Cached/ExprNodes.lean`'s module docstring. -/
inductive Expr where
  | bvar (i : Nat)
  | fvar (idx : Nat) (type : Expr)
  | sort (u : Level)
  | const (n : Name) (us : List Level)
  | app (f a : Expr)
  | lam (type body : Expr)
  | forallE (type body : Expr)
  | letE (type value body : Expr)
  | lit (l : Literal)
  | proj (structName : Name) (idx : Nat) (e : Expr)
with
  /-- The packed derived-data word: `hash` (32) ǀ reserved (1) ǀ
  `bvarB` (15, saturating) ǀ `fvarB` (15, saturating) ǀ `hasLP` (1). -/
  @[computed_field] data : Expr → UInt64
    | .bvar i =>
      packData (hash32 (mixHash 3 (Hashable.hash i))) (satSucc i) 0 false
    | .fvar idx ty =>
      packData (hash32 (mixHash 5 (mixHash (Hashable.hash idx)
          (hashOfData ty.data))))
        0 (satSucc idx) (lpOfData ty.data)
    | .sort u =>
      packData (hash32 (mixHash 7 (levelHash u))) 0 0 (levelHasParam u)
    | .const n us =>
      packData (hash32 (mixHash 11 (mixHash (Hashable.hash n)
          (levelsHash us)))) 0 0 (levelsHaveParam us)
    | .app f a =>
      packData (hash32 (mixHash 17
          (mixHash (hashOfData f.data) (hashOfData a.data))))
        (max (bvarOfData f.data) (bvarOfData a.data))
        (max (fvarOfData f.data) (fvarOfData a.data))
        (lpOfData f.data || lpOfData a.data)
    | .lam ty b =>
      packData (hash32 (mixHash 19
          (mixHash (hashOfData ty.data)
            (hashOfData b.data))))
        (max (bvarOfData ty.data) (satPred (bvarOfData b.data)))
        (max (fvarOfData ty.data) (fvarOfData b.data))
        (lpOfData ty.data || lpOfData b.data)
    | .forallE ty b =>
      packData (hash32 (mixHash 23
          (mixHash (hashOfData ty.data)
            (hashOfData b.data))))
        (max (bvarOfData ty.data) (satPred (bvarOfData b.data)))
        (max (fvarOfData ty.data) (fvarOfData b.data))
        (lpOfData ty.data || lpOfData b.data)
    | .letE ty v b =>
      packData (hash32 (mixHash 29
          (mixHash (hashOfData ty.data)
            (mixHash (hashOfData v.data) (hashOfData b.data)))))
        (max (max (bvarOfData ty.data) (bvarOfData v.data))
          (satPred (bvarOfData b.data)))
        (max (max (fvarOfData ty.data) (fvarOfData v.data))
          (fvarOfData b.data))
        (lpOfData ty.data || lpOfData v.data || lpOfData b.data)
    | .lit l => packData (hash32 (mixHash 31 (Hashable.hash l))) 0 0 false
    | .proj s i e =>
      packData (hash32 (mixHash 37 (mixHash (Hashable.hash s)
          (mixHash (Hashable.hash i) (hashOfData e.data)))))
        (bvarOfData e.data) (fvarOfData e.data) (lpOfData e.data)
deriving Repr, Inhabited

/-! ## The packed word's accessors

`hash` and `hasLP` are exact bit reads.  `bvarBRaw`/`fvarBRaw` are the
*saturating* reads: below `satRange` they are the exact bound
(`bvarBRaw_exact` in `Kernel/ExprOps.lean`, `fvarBRaw_exact` in
`Verify/Cached/Erase.lean`); at
`satRange` they mean "at least that", and `Expr.bvarB`/`Expr.fvarB`
(`Kernel/ExprOps.lean`) recover exactness there with a memoized
walk. -/

namespace Expr

/-- The node's 32-bit hash (`O(1)`).  The recurrence reads exactly
what `is_equal` in the official kernel reads (`expr_eq_fn.cpp`); there
is no display data in a node (task #205), so hashing and
`DecidableEq` are α-equivalence outright. -/
@[inline] def hash (e : Expr) : UInt64 := hashOfData e.data

/-- Has-level-param: is level instantiation ever non-trivial here?
One bit, so this read is *exact*. -/
@[inline] def hasLP (e : Expr) : Bool := lpOfData e.data

/-- The stored loose-bvar bound, saturating at `satRange`. -/
@[inline] def bvarBRaw (e : Expr) : Nat := (bvarOfData e.data).toNat

/-- The stored fvar range, saturating at `satRange`. -/
@[inline] def fvarBRaw (e : Expr) : Nat := (fvarOfData e.data).toNat

end Expr

/-- Hashing is the computed field: `O(1)`, no traversal; no hash in
the tree is budgeted. -/
instance : Hashable Expr := ⟨Expr.hash⟩

namespace Expr

/-! ### The stored ranges, constructor by constructor

Each equation is the packed word's recurrence read back through the
roundtrip lemmas; together they are what the exactness induction in
`Verify/Cached/Erase.lean` runs on. -/

theorem bvarBRaw_lt (e : Expr) : e.bvarBRaw < 32768 := bvarOfData_lt _

theorem fvarBRaw_lt (e : Expr) : e.fvarBRaw < 32768 := fvarOfData_lt _

private theorem toNat_satSucc (n : Nat) :
    (satSucc n).toNat = min (n + 1) satRange := by
  simp [satSucc, satRange]
  omega

private theorem toNat_satPred {x : UInt64} (_hx : x.toNat < 32768) :
    (satPred x).toNat = if x.toNat = satRange then satRange else x.toNat - 1 := by
  by_cases hs : x.toNat = satRange
  · have : x = 32767 := by rw [← UInt64.toNat_inj]; simpa [satRange] using hs
    simp [satPred, this, satRange]
  · have hne : x ≠ 32767 := by
      rw [Ne, ← UInt64.toNat_inj]; simpa [satRange] using hs
    by_cases hz : x.toNat = 0
    · have : x = 0 := by rw [← UInt64.toNat_inj]; simpa using hz
      simp [satPred, this, satRange]
    · have hz' : x ≠ 0 := by rw [Ne, ← UInt64.toNat_inj]; simpa using hz
      simp only [satPred, beq_iff_eq, hne, hz', ↓reduceIte, hs,
        toNat_sub_one hz]

@[simp] theorem bvarBRaw_bvar (i : Nat) :
    (Expr.bvar i).bvarBRaw = min (i + 1) satRange := by
  show (bvarOfData (packData _ (satSucc i) 0 false)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (satSucc_lt i) (by decide), toNat_satSucc]

@[simp] theorem bvarBRaw_fvar (idx : Nat) (ty : Expr) :
    (Expr.fvar idx ty).bvarBRaw = 0 := by
  show (bvarOfData (packData _ 0 (satSucc idx) _)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (by decide) (satSucc_lt idx)]; rfl

@[simp] theorem bvarBRaw_sort (u : Level) : (Expr.sort u).bvarBRaw = 0 := by
  show (bvarOfData (packData _ 0 0 _)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem bvarBRaw_const (n : Name) (us : List Level) :
    (Expr.const n us).bvarBRaw = 0 := by
  show (bvarOfData (packData _ 0 0 _)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem bvarBRaw_lit (l : Literal) : (Expr.lit l).bvarBRaw = 0 := by
  show (bvarOfData (packData _ 0 0 _)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem bvarBRaw_app (f a : Expr) :
    (Expr.app f a).bvarBRaw = max f.bvarBRaw a.bvarBRaw := by
  show (bvarOfData (packData _ (max _ _) (max _ _) _)).toNat = _
  rw [bvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max]
  rfl

@[simp] theorem bvarBRaw_lam (ty b : Expr) :
    (Expr.lam ty b).bvarBRaw =
      max ty.bvarBRaw
        (if b.bvarBRaw = satRange then satRange else b.bvarBRaw - 1) := by
  show (bvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [bvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max,
    toNat_satPred (bvarOfData_lt _)]
  rfl

@[simp] theorem bvarBRaw_forallE (ty b : Expr) :
    (Expr.forallE ty b).bvarBRaw =
      max ty.bvarBRaw
        (if b.bvarBRaw = satRange then satRange else b.bvarBRaw - 1) := by
  show (bvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [bvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max,
    toNat_satPred (bvarOfData_lt _)]
  rfl

@[simp] theorem bvarBRaw_letE (ty v b : Expr) :
    (Expr.letE ty v b).bvarBRaw =
      max (max ty.bvarBRaw v.bvarBRaw)
        (if b.bvarBRaw = satRange then satRange else b.bvarBRaw - 1) := by
  show (bvarOfData (packData _ (max (max _ _) (satPred _)) (max (max _ _) _)
    _)).toNat = _
  rw [bvarOfData_pack _ _ _ _
    (max_lt_32768 (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
      (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))
      (fvarOfData_lt _)), toNat_max, toNat_max,
    toNat_satPred (bvarOfData_lt _)]
  rfl

@[simp] theorem bvarBRaw_proj (s : Name) (i : Nat) (e : Expr) :
    (Expr.proj s i e).bvarBRaw = e.bvarBRaw := by
  show (bvarOfData (packData _ _ _ _)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (bvarOfData_lt _) (fvarOfData_lt _)]
  rfl

@[simp] theorem fvarBRaw_bvar (i : Nat) : (Expr.bvar i).fvarBRaw = 0 := by
  show (fvarOfData (packData _ (satSucc i) 0 false)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (satSucc_lt i) (by decide)]; rfl

@[simp] theorem fvarBRaw_fvar (idx : Nat) (ty : Expr) :
    (Expr.fvar idx ty).fvarBRaw = min (idx + 1) satRange := by
  show (fvarOfData (packData _ 0 (satSucc idx) _)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (by decide) (satSucc_lt idx), toNat_satSucc]

@[simp] theorem fvarBRaw_sort (u : Level) : (Expr.sort u).fvarBRaw = 0 := by
  show (fvarOfData (packData _ 0 0 _)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem fvarBRaw_const (n : Name) (us : List Level) :
    (Expr.const n us).fvarBRaw = 0 := by
  show (fvarOfData (packData _ 0 0 _)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem fvarBRaw_lit (l : Literal) : (Expr.lit l).fvarBRaw = 0 := by
  show (fvarOfData (packData _ 0 0 _)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (by decide) (by decide)]; rfl

@[simp] theorem fvarBRaw_app (f a : Expr) :
    (Expr.app f a).fvarBRaw = max f.fvarBRaw a.fvarBRaw := by
  show (fvarOfData (packData _ (max _ _) (max _ _) _)).toNat = _
  rw [fvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max]
  rfl

@[simp] theorem fvarBRaw_lam (ty b : Expr) :
    (Expr.lam ty b).fvarBRaw = max ty.fvarBRaw b.fvarBRaw := by
  show (fvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [fvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max]
  rfl

@[simp] theorem fvarBRaw_forallE (ty b : Expr) :
    (Expr.forallE ty b).fvarBRaw = max ty.fvarBRaw b.fvarBRaw := by
  show (fvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [fvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max]
  rfl

@[simp] theorem fvarBRaw_letE (ty v b : Expr) :
    (Expr.letE ty v b).fvarBRaw =
      max (max ty.fvarBRaw v.fvarBRaw) b.fvarBRaw := by
  show (fvarOfData (packData _ (max (max _ _) (satPred _)) (max (max _ _) _)
    _)).toNat = _
  rw [fvarOfData_pack _ _ _ _
    (max_lt_32768 (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
      (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))
      (fvarOfData_lt _)), toNat_max, toNat_max]
  rfl

@[simp] theorem fvarBRaw_proj (s : Name) (i : Nat) (e : Expr) :
    (Expr.proj s i e).fvarBRaw = e.fvarBRaw := by
  show (fvarOfData (packData _ _ _ _)).toNat = _
  rw [fvarOfData_pack _ _ _ _ (bvarOfData_lt _) (fvarOfData_lt _)]
  rfl

/-! ### The has-level-param bit, constructor by constructor -/

@[simp] theorem hasLP_bvar (i : Nat) : (Expr.bvar i).hasLP = false := by
  show lpOfData (packData _ (satSucc i) 0 false) = _
  rw [lpOfData_pack _ _ _ _ (satSucc_lt i) (by decide)]

@[simp] theorem hasLP_fvar (idx : Nat) (ty : Expr) :
    (Expr.fvar idx ty).hasLP = ty.hasLP := by
  show lpOfData (packData _ 0 (satSucc idx) _) = _
  rw [lpOfData_pack _ _ _ _ (by decide) (satSucc_lt idx)]; rfl

@[simp] theorem hasLP_sort (u : Level) :
    (Expr.sort u).hasLP = levelHasParam u := by
  show lpOfData (packData _ 0 0 _) = _
  rw [lpOfData_pack _ _ _ _ (by decide) (by decide)]

@[simp] theorem hasLP_const (n : Name) (us : List Level) :
    (Expr.const n us).hasLP = levelsHaveParam us := by
  show lpOfData (packData _ 0 0 _) = _
  rw [lpOfData_pack _ _ _ _ (by decide) (by decide)]

@[simp] theorem hasLP_lit (l : Literal) : (Expr.lit l).hasLP = false := by
  show lpOfData (packData _ 0 0 _) = _
  rw [lpOfData_pack _ _ _ _ (by decide) (by decide)]

@[simp] theorem hasLP_app (f a : Expr) :
    (Expr.app f a).hasLP = (f.hasLP || a.hasLP) := by
  show lpOfData (packData _ (max _ _) (max _ _) _) = _
  rw [lpOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))]
  rfl

@[simp] theorem hasLP_lam (ty b : Expr) :
    (Expr.lam ty b).hasLP = (ty.hasLP || b.hasLP) := by
  show lpOfData (packData _ (max _ (satPred _)) (max _ _) _) = _
  rw [lpOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))]
  rfl

@[simp] theorem hasLP_forallE (ty b : Expr) :
    (Expr.forallE ty b).hasLP =
      (ty.hasLP || b.hasLP) := by
  show lpOfData (packData _ (max _ (satPred _)) (max _ _) _) = _
  rw [lpOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))]
  rfl

@[simp] theorem hasLP_letE (ty v b : Expr) :
    (Expr.letE ty v b).hasLP = (ty.hasLP || v.hasLP || b.hasLP) := by
  show lpOfData (packData _ (max (max _ _) (satPred _)) (max (max _ _) _)
    _) = _
  rw [lpOfData_pack _ _ _ _
    (max_lt_32768 (max_lt_32768 (bvarOfData_lt _) (bvarOfData_lt _))
      (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))
      (fvarOfData_lt _))]
  rfl

@[simp] theorem hasLP_proj (s : Name) (i : Nat) (e : Expr) :
    (Expr.proj s i e).hasLP = e.hasLP := by
  show lpOfData (packData _ _ _ _) = _
  rw [lpOfData_pack _ _ _ _ (bvarOfData_lt _) (fvarOfData_lt _)]
  rfl

/-! ## Equality

The official kernel's `is_equal`: pointer identity, then the computed
hashes (a cheap reject — a hash mismatch *is* an inequality), then
structural descent.  Since instantiation and abstraction return
unchanged subterms **by reference**, the pointer test decides most
comparisons in `O(1)`, which is the arena's index comparison in a
different mechanism.

**The specification is plain decidable equality**, `beq a b =
decide (a = b)`, and the executed function is **proved** equal to it
(`beqMemo_eq`) and substituted by `@[csimp]`; the structural
`DecidableEq` instance (`Expr.decEq`) is substituted by the decision
read off it (`decEqPtr`, `decEq_eq_decEqPtr`) — the same arrangement
as `Name.decEq`/`Level.decEq`/`Literal.decEq`, with no `implemented_by` and nothing
`unsafe` anywhere on the path.  The two runtime facts a pointer test
rests on — an address names one immutable object, so pointer-equal
means equal — enter only through `Init.Util`'s `withPtrEq` and
`withPtrAddr`, whose *pure* definitions (`k ()`, `k 0`) are what the
theorem is about; the compiler's substitution of the real address is
its own contract, justified by the side conditions those functions
demand and this file discharges.

The descent is **memoised** on the DAG so that it is `O(DAG)` rather
than `O(tree)`: hash-consing identifies structurally equal terms
however they arose, so the arena never compares two
distinct-but-equal DAGs, while a reduction that rebuilds a term the
arena would have collapsed does exactly that.  The memo is
*verified*, not trusted:

* an entry is the **pair of objects** a completed descent proved
  equal, together with the proof (`EqPair`), so the map's value type
  carries the invariant and no lemma about the map is needed;
* a probe finds a candidate by the address pair (`beqKey`) and then
  checks the candidate **by identity** (`withPtrEqDecEq` on each
  side), which is where the `a = b` behind a hit comes from.  At
  runtime the identity test is the pointer test: the stored objects
  are held by the memo, so their addresses stay theirs for the life
  of the comparison and an address match *is* an identity match.  The
  structural fallback that `withPtrEqDecEq` requires exists for the
  pure model and is never reached by compiled code;
* the memo is passed through a quotient (`Squash`) that identifies
  all its states, so the result of the descent is a *subsingleton*
  (a `Decidable (a = b)` beside an unobservable state) — which is
  exactly the side condition `withPtrAddr` asks of a continuation
  that reads an address.  The compiler erases the quotient; the
  runtime map is the raw hash map.

The pure model, in which every address is `0`, is a slow but correct
structural equality: every branch of the descent returns
`Decidable (a = b)` for its own `a`, `b`, so the equation holds by
construction and the proof of `beqMemo_eq` is three lines. -/

/-- `true` for the nodes whose comparison recurses.  The memo is
consulted and written **only** at these: a `bvar`, `sort`, `const` or
`lit` pair is decided without a descent, so an entry for it can never
save a walk and every one of them costs a probe, a bucket cons cell
and, at the end of the call, its `lean_dec_ref`.  Leaves are the
majority of the nodes of a real term. -/
@[inline] def beqRecursive : Expr → Bool
  | .fvar .. | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => true
  | _ => false

/-- Is the expression an application?  The spine test of `beqGoX`. -/
@[inline] def beqIsApp : Expr → Bool
  | .app .. => true
  | _ => false

/-- A memo entry: the pair of objects a completed descent proved
equal, the addresses the descent saw them at, and the proof.  The
proof is erased; the addresses are the probe's cheap filter; the
objects are what the probe verifies against (`probeHit`) — and
holding them is what keeps their addresses theirs. -/
structure EqPair where
  fst : Expr
  snd : Expr
  pa : USize
  pb : USize
  eq : fst = snd

/-- The default a probe reads on a miss: no object has address `0`,
so its filter never passes at runtime. -/
def EqPair.dflt : EqPair := ⟨.bvar 0, .bvar 0, 0, 0, rfl⟩

/-- The memo: keyed on the packed address pair (`beqKey`). -/
abbrev BeqMap := Std.HashMap Nat EqPair

/-- The memo key of a pair of addresses, packed into ONE small `Nat`:
a `Nat × Nat` key would be a `Prod` cell allocated on every probe and
every write, while a `Nat` below `2^62` is a tagged scalar and costs
nothing.  The packing need not be injective — the probe verifies the
stored pair itself — so a collision between distinct pairs costs an
entry, never an answer. -/
@[inline] def beqKey (pa pb : USize) : Nat :=
  ((pa ^^^ (pb * 0x9E3779B97F4A7C15)) &&& 0x3FFFFFFFFFFFFFFF).toNat

/-- `withPtrAddr` into a subsingleton: its side condition — the
continuation's result does not depend on the address — is then
`Subsingleton.elim`. -/
@[inline] def withAddr {α : Type u} {β : Type v} [Subsingleton β] (a : α)
    (k : USize → β) : β :=
  withPtrAddr a k (fun _ _ => Subsingleton.elim _ _)

/-- **The specification of expression equality**: the structural
decision, the one the kernel, `by decide` and `#guard` reduce (the
instance below).  No `deriving DecidableEq` (task #554): compiled code
runs `decEqPtr` in its place (`decEq_eq_decEqPtr`), and the only
compiled reference to this body is `ptrDecStruct`'s pure-model fallback,
which compiled code never reaches. -/
def decEq : (a b : Expr) → Decidable (a = b)
  | .bvar x0, .bvar y0 =>
    if h0 : x0 = y0 then
      isTrue (by subst h0; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .fvar x0 x1, .fvar y0 y1 =>
    if h0 : x0 = y0 then
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .sort x0, .sort y0 =>
    if h0 : x0 = y0 then
      isTrue (by subst h0; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .const x0 x1, .const y0 y1 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        isTrue (by subst h0; subst h1; rfl)
      else isFalse (fun e => h1 (by injection e <;> assumption))
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .app x0 x1, .app y0 y1 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .lam x0 x1, .lam y0 y1 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .forallE x0 x1, .forallE y0 y1 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        isTrue (by subst h0; subst h1; rfl)
  | .letE x0 x1 x2, .letE y0 y1 y2 =>
    match decEq x0 y0 with
    | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
    | isTrue h0 =>
      match decEq x1 y1 with
      | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
      | isTrue h1 =>
        match decEq x2 y2 with
        | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
        | isTrue h2 =>
          isTrue (by subst h0; subst h1; subst h2; rfl)
  | .lit x0, .lit y0 =>
    if h0 : x0 = y0 then
      isTrue (by subst h0; rfl)
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .proj x0 x1 x2, .proj y0 y1 y2 =>
    if h0 : x0 = y0 then
      if h1 : x1 = y1 then
        match decEq x2 y2 with
        | isFalse h => isFalse (fun e => h (by injection e <;> assumption))
        | isTrue h2 =>
          isTrue (by subst h0; subst h1; subst h2; rfl)
      else isFalse (fun e => h1 (by injection e <;> assumption))
    else isFalse (fun e => h0 (by injection e <;> assumption))
  | .bvar .., .fvar .. | .bvar .., .sort .. | .bvar .., .const ..
  | .bvar .., .app .. | .bvar .., .lam .. | .bvar .., .forallE ..
  | .bvar .., .letE .. | .bvar .., .lit .. | .bvar .., .proj ..
  | .fvar .., .bvar .. | .fvar .., .sort .. | .fvar .., .const ..
  | .fvar .., .app .. | .fvar .., .lam .. | .fvar .., .forallE ..
  | .fvar .., .letE .. | .fvar .., .lit .. | .fvar .., .proj ..
  | .sort .., .bvar .. | .sort .., .fvar .. | .sort .., .const ..
  | .sort .., .app .. | .sort .., .lam .. | .sort .., .forallE ..
  | .sort .., .letE .. | .sort .., .lit .. | .sort .., .proj ..
  | .const .., .bvar .. | .const .., .fvar .. | .const .., .sort ..
  | .const .., .app .. | .const .., .lam .. | .const .., .forallE ..
  | .const .., .letE .. | .const .., .lit .. | .const .., .proj ..
  | .app .., .bvar .. | .app .., .fvar .. | .app .., .sort ..
  | .app .., .const .. | .app .., .lam .. | .app .., .forallE ..
  | .app .., .letE .. | .app .., .lit .. | .app .., .proj ..
  | .lam .., .bvar .. | .lam .., .fvar .. | .lam .., .sort ..
  | .lam .., .const .. | .lam .., .app .. | .lam .., .forallE ..
  | .lam .., .letE .. | .lam .., .lit .. | .lam .., .proj ..
  | .forallE .., .bvar .. | .forallE .., .fvar .. | .forallE .., .sort ..
  | .forallE .., .const .. | .forallE .., .app .. | .forallE .., .lam ..
  | .forallE .., .letE .. | .forallE .., .lit .. | .forallE .., .proj ..
  | .letE .., .bvar .. | .letE .., .fvar .. | .letE .., .sort ..
  | .letE .., .const .. | .letE .., .app .. | .letE .., .lam ..
  | .letE .., .forallE .. | .letE .., .lit .. | .letE .., .proj ..
  | .lit .., .bvar .. | .lit .., .fvar .. | .lit .., .sort ..
  | .lit .., .const .. | .lit .., .app .. | .lit .., .lam ..
  | .lit .., .forallE .. | .lit .., .letE .. | .lit .., .proj ..
  | .proj .., .bvar .. | .proj .., .fvar .. | .proj .., .sort ..
  | .proj .., .const .. | .proj .., .app .. | .proj .., .lam ..
  | .proj .., .forallE .. | .proj .., .letE .. | .proj .., .lit .. =>
    isFalse (fun e => Expr.noConfusion e)

/-- Identity, decided, inside the equality itself: the pointer test at
runtime, the structural decision in the pure model.  The equality's own
probes (`enterBeq`'s `pa == pb`, `probeHit`'s passed filter) reach it
on equal addresses only, where the runtime pointer test answers
`isTrue` and the fallback is not run; it is the one compiled reference
to the structural `decEq`, which `decEqPtr` does not exist yet to
replace.  Code outside the equality uses `ptrDec`. -/
@[inline] def ptrDecStruct (a b : Expr) : Decidable (a = b) :=
  withPtrEqDecEq a b (fun _ => decEq a b)

/-- Does the entry at `key` identify the pair `(a, b)`?  The stored
addresses are the filter; the stored objects, tested by identity, are
the verification, and the proof behind a `true` is the entry's own.
At runtime a passed filter is an identity match, so `ptrDecStruct` decides
by pointer and never walks.  Not inlined, with everything borrowed: the
structural fallback inside `ptrDecStruct` takes its terms owned, and a
term that is an owned argument in `beqGoX` would make the descent's own
parameters owned (see `BeqSt.recordEq`). -/
@[noinline] def probeHit (m : @& BeqMap) (key : Nat) (pa pb : USize) (a b : @& Expr) :
    { h : Bool // h = true → a = b } :=
  let p := m.getD key EqPair.dflt
  if p.pa == pa && p.pb == pb then
    match ptrDecStruct p.fst a, ptrDecStruct p.snd b with
    | isTrue h1, isTrue h2 => ⟨true, fun _ => h1 ▸ h2 ▸ p.eq⟩
    | _, _ => ⟨false, fun h => Bool.noConfusion h⟩
  else ⟨false, fun h => Bool.noConfusion h⟩

/-! ### The memo discipline: memoise only what is shared (task #319)

The memo is the substitution walks' (`ConLeche/Cached/ExprOpsC.lean`,
"The substitution walks"), and the tree has ONE such discipline: at
every recursive child position `withExclusive`
(`ConLeche/Kernel/Exclusive.lean`) reads the count of the BORROWED
node, and only a pair whose two nodes are both SHARED is probed and
recorded — a pair with an exclusive side cannot be queried again
within this comparison, so it costs no key, no probe and no entry.
This is the official kernel's `expr_eq_fn::check_cache` guard
(`src/kernel/expr_eq_fn.cpp`: `if (is_shared(a) && is_shared(b))` in
front of the probe and the write), which the task #240 record could
not port because a Lean walk saw its arguments owned; task #317's
`withExclusive` reads a borrowed node's count, and `beqGoX`'s terms
are borrowed already.

The child step `enterBeq` plays `enter*P`'s part: the pointer test,
the computed-word test, the leaf test, then the two exclusivity
reads.  There is NO cutoff — the node budget that used to keep the
table away from small comparisons was the tree's second heuristic
cutoff after the walks' and went with it (task #319) — so the table
appears at the first shared/shared pair proved equal, the root pair
is never asked (it reaches `beqGoX` past `beqMemo`'s pointer and word
tests and cannot recur), and nothing bounds the table but the
comparison's own end.  The entries are `EqPair`s (the pair, its two
addresses, and its proof), the key is the packed address pair
(`beqKey`), and a hit is validated by identity on BOTH stored objects
(`probeHit`) — self-proving entries, so there is no table invariant
and no lemma about the table at all.  Every branch returns its state
(`BeqSt`: `fail`, or the memo) with the proof that it is not `fail`
exactly when its own `a`, `b` are equal, behind the quotient; the
per-node result is the state object itself, so the descent allocates
only the memo's entries, as official's `apply` returning a `bool`
(task #574).  `beqMemo_eq` is three lines, as it always was.

The table is `Std.HashMap`, created at the first recorded pair.
Official's `ptr_pair_set` (`src/kernel/ptr_pair_set.h`) keeps its first
16 slots inline in the `expr_eq_fn` object and allocates only on growth;
a Lean value has no caller frame to live in, so its twin would be the
first pairs as scalar fields of `BeqSt` itself.  `BeqSt.table`'s field,
`BeqSt.record` and `probeHit` are the only places the table type
appears (task #574 record, DESIGN.md). -/

/-- The state the descent threads, verdict and memo in one word: `fail`
once a pair proved unequal (a `false` aborts the whole comparison, so
the memo is dead from then on), `empty` before the first recorded pair,
`table m` after it.  `fail` and `empty` are scalars and a pass-through
returns the state it was given, so a node's comparison allocates
nothing but the memo's own growth — the official kernel's `apply`
returns a `bool` beside a member `m_cache` (`src/kernel/expr_eq_fn.cpp`).
The table type is this constructor's field: a different memo
representation replaces `BeqMap` here and in `BeqSt.record`/`probeHit`
and nowhere else. -/
inductive BeqSt where
  | fail
  | empty
  | table (m : BeqMap)

/-- Is the comparison still going (no unequal pair found)? -/
@[inline] def BeqSt.ok : BeqSt → Bool
  | .fail => false
  | _ => true

/-- The write-back: the entry under its key, in the table or in a
fresh one.  Never `fail`: it is applied to a completed `true` only. -/
@[inline] def BeqSt.record (st : BeqSt) (key : Nat) (p : EqPair) : BeqSt :=
  match st with
  | .table m => .table (m.insert key p)
  | _ => .table (({} : BeqMap).insert key p)

theorem BeqSt.record_ok (st : BeqSt) (key : Nat) (p : EqPair) :
    (st.record key p).ok = true := by
  cases st <;> rfl

/-- The write-back of a proved-equal pair at its addresses: the entry
built here, from BORROWED terms.  Not inlined: in `beqGoX` the child
terms are also passed on in tail calls, and a term that is a
constructor argument there is owned, which would make the descent's
own parameters owned (the compiler keeps a self tail call by owning
the parameter an owned argument is passed to). -/
@[noinline] def BeqSt.recordEq (st : BeqSt) (a b : @& Expr) (pa pb : USize) (h : a = b) :
    BeqSt :=
  st.record (beqKey pa pb) ⟨a, b, pa, pb, h⟩

/-- A state the descent may enter a node with: one that is not `fail`.
A subtype, so the proof is erased and the descent's parameter is the
`BeqSt` itself (an extra `Prop` parameter would make the compiler split
off a reduced-arity copy, which drops the terms' borrow annotations). -/
abbrev BeqOk := { s : BeqSt // s.ok = true }

/-- The result as the descent returns it: the state, with the proof
that it is not `fail` exactly when the pair is equal, behind a quotient
identifying all of them, so that it is a subsingleton — the decision is
fixed by the proof and the memo is unobservable.  Subtype and quotient
are erased by the compiler: at runtime this is the `BeqSt` itself. -/
abbrev BeqOutX (a b : Expr) := Squash { s : BeqSt // s.ok = true ↔ a = b }

/-- An equal pair: the state passes through. -/
@[inline] def BeqOutX.yes {a b : Expr} (st : BeqOk) (h : a = b) : BeqOutX a b :=
  Quot.mk _ ⟨st.1, fun _ => h, fun _ => st.2⟩

/-- An unequal pair: `fail`, and the memo is dropped. -/
@[inline] def BeqOutX.no {a b : Expr} (h : ¬ a = b) : BeqOutX a b :=
  Quot.mk _ ⟨.fail, fun e => Bool.noConfusion e, fun e => absurd e h⟩

/-- A node's own decision, the state passing through on `isTrue`. -/
@[inline] def BeqOutX.mk {a b : Expr} (d : Decidable (a = b)) (st : BeqOk) :
    BeqOutX a b :=
  match d with
  | isTrue h => .yes st h
  | isFalse h => .no h

/-- A child's result read as the parent's: the same state, the proof
moved along an equivalence of the two equalities (erased). -/
@[inline] def BeqOutX.cast {a b c d : Expr} (r : BeqOutX a b) (e : (a = b) ↔ (c = d)) :
    BeqOutX c d :=
  Squash.lift r fun r => Quot.mk _ ⟨r.1, r.2.trans e⟩

/-- The child step of `beqGoX`: pointer identity, the computed word,
the leaf test, then the exclusivity of each side — an exclusive side
means the pair cannot recur and the descent runs with the memo
untouched; a shared/shared pair is probed, and recorded on a completed
`true`.  The terms are borrowed, so the counts read are the counts of
the references inside the terms (the requirement stated in
`ConLeche/Cached/ExprOpsC.lean`; the check is the IR audit). -/
@[inline] def enterBeq (st : BeqOk) (a b : @& Expr)
    (rec : BeqOk → BeqOutX a b) : BeqOutX a b :=
  withAddr a fun pa => withAddr b fun pb =>
  if pa == pb then .mk (ptrDecStruct a b) st
  else if h : a.data != b.data then
    .no (fun e => by subst e; simp at h)
  else if !beqRecursive a then rec st
  else withExcl a fun ea =>
    if ea then rec st
    else withExcl b fun eb =>
    if eb then rec st
    else
      let hit : { h : Bool // h = true → a = b } :=
        match st.1 with
        | .table m => probeHit m (beqKey pa pb) pa pb a b
        | _ => ⟨false, fun h => Bool.noConfusion h⟩
      if hh : hit.1 then .yes st (hit.2 hh)
      else Squash.lift (rec st) fun r =>
        if h : r.1.ok then
          .yes ⟨r.1.recordEq a b pa pb (r.2.mp h), BeqSt.record_ok ..⟩ (r.2.mp h)
        else Quot.mk _ r

/-- The memoised structural descent, the official kernel's
`expr_eq_fn::apply` (`src/kernel/expr_eq_fn.cpp`): the constructor
cases with the child step (`enterBeq`) in front of every recursive call,
every branch returning its decision for its own `a`, `b` (the module
docstring above says why that is the whole proof).  An application
compares its LAST argument first and then walks down the spine: when
both functions are applications again the descent continues on them
directly — a partial application is neither probed nor recorded nor
word-tested, official's `while (true)` loop over `app_fn` — and the
heads go through the child step.  A `false` aborts the comparison at
every level (`fail`), so no unequal pair is ever re-queried and only
proved-equal pairs are stored.  The root pair reaches it past
`beqMemo`'s pointer and word tests and is never asked.  The terms are
borrowed (`@&`): the write-back is the only consumer that stores
them, and owned terms cost a reference-count pair per node — and the
exclusivity read would then answer `false` at every node
(`ConLeche/Kernel/Exclusive.lean`, "The borrowed-parameter
requirement"). -/
def beqGoX (st : BeqOk) (a b : @& Expr) : BeqOutX a b :=
  match a, b with
  | .bvar i, .bvar j =>
    .mk (if h : i = j then isTrue (by subst h; rfl)
         else isFalse (fun e => h (Expr.bvar.inj e))) st
  | .fvar i t, .fvar j u =>
    if h : i = j then
      (enterBeq st t u fun s => beqGoX s t u).cast
        ⟨fun h' => by subst h; subst h'; rfl, fun e => (Expr.fvar.inj e).2⟩
    else .no (fun e => h (Expr.fvar.inj e).1)
  | .sort u, .sort v =>
    .mk (if h : u == v then isTrue (by rw [beq_iff_eq.mp h])
         else isFalse (fun e => h (beq_iff_eq.mpr (Expr.sort.inj e)))) st
  | .const n us, .const m vs =>
    .mk (if h : n == m && us == vs then
           isTrue (by
             have h1 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1
             have h2 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
             rw [h1, h2])
         else isFalse (fun e => h (by
           obtain ⟨h1, h2⟩ := Expr.const.inj e
           subst h1; subst h2; simp))) st
  | .app f x, .app g y =>
    Squash.lift (enterBeq st x y fun s => beqGoX s x y) fun r₁ =>
      if h₁ : r₁.1.ok then
        have hx : x = y := r₁.2.mp h₁
        let rf : BeqOutX f g :=
          if hf : f.beqIsApp then
            if hg : g.beqIsApp then beqGoX ⟨r₁.1, h₁⟩ f g
            else .no (fun e => by subst e; exact hg hf)
          else enterBeq ⟨r₁.1, h₁⟩ f g fun s => beqGoX s f g
        rf.cast ⟨fun h' => by subst hx; subst h'; rfl, fun e => (Expr.app.inj e).1⟩
      else .no (fun e => h₁ (r₁.2.mpr (Expr.app.inj e).2))
  | .lam t b, .lam t' b' =>
    Squash.lift (enterBeq st t t' fun s => beqGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : t = t' := r₁.2.mp h₁
        (enterBeq ⟨r₁.1, h₁⟩ b b' fun s => beqGoX s b b').cast
          ⟨fun h' => by subst ht; subst h'; rfl, fun e => (Expr.lam.inj e).2⟩
      else .no (fun e => h₁ (r₁.2.mpr (Expr.lam.inj e).1))
  | .forallE t b, .forallE t' b' =>
    Squash.lift (enterBeq st t t' fun s => beqGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : t = t' := r₁.2.mp h₁
        (enterBeq ⟨r₁.1, h₁⟩ b b' fun s => beqGoX s b b').cast
          ⟨fun h' => by subst ht; subst h'; rfl, fun e => (Expr.forallE.inj e).2⟩
      else .no (fun e => h₁ (r₁.2.mpr (Expr.forallE.inj e).1))
  | .letE t v b, .letE t' v' b' =>
    Squash.lift (enterBeq st t t' fun s => beqGoX s t t') fun r₁ =>
      if h₁ : r₁.1.ok then
        have ht : t = t' := r₁.2.mp h₁
        Squash.lift (enterBeq ⟨r₁.1, h₁⟩ v v' fun s => beqGoX s v v') fun r₂ =>
          if h₂ : r₂.1.ok then
            have hv : v = v' := r₂.2.mp h₂
            (enterBeq ⟨r₂.1, h₂⟩ b b' fun s => beqGoX s b b').cast
              ⟨fun h' => by subst ht; subst hv; subst h'; rfl, fun e => (Expr.letE.inj e).2.2⟩
          else .no (fun e => h₂ (r₂.2.mpr (Expr.letE.inj e).2.1))
      else .no (fun e => h₁ (r₁.2.mpr (Expr.letE.inj e).1))
  | .lit l, .lit l' =>
    .mk (if h : l = l' then isTrue (by subst h; rfl)
         else isFalse (fun e => h (Expr.lit.inj e))) st
  | .proj s i e, .proj s' i' e' =>
    if h : s == s' && i == i' then
      (enterBeq st e e' fun s => beqGoX s e e').cast
        ⟨fun h' => by
          have h1 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).1
          have h2 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2
          rw [h1, h2, h'],
         fun e => (Expr.proj.inj e).2.2⟩
    else .no (fun e => h (by
      obtain ⟨h1, h2, _⟩ := Expr.proj.inj e
      subst h1; subst h2; simp))
  | .bvar .., .fvar .. | .bvar .., .sort .. | .bvar .., .const ..
  | .bvar .., .app .. | .bvar .., .lam .. | .bvar .., .forallE ..
  | .bvar .., .letE .. | .bvar .., .lit .. | .bvar .., .proj ..
  | .fvar .., .bvar .. | .fvar .., .sort .. | .fvar .., .const ..
  | .fvar .., .app .. | .fvar .., .lam .. | .fvar .., .forallE ..
  | .fvar .., .letE .. | .fvar .., .lit .. | .fvar .., .proj ..
  | .sort .., .bvar .. | .sort .., .fvar .. | .sort .., .const ..
  | .sort .., .app .. | .sort .., .lam .. | .sort .., .forallE ..
  | .sort .., .letE .. | .sort .., .lit .. | .sort .., .proj ..
  | .const .., .bvar .. | .const .., .fvar .. | .const .., .sort ..
  | .const .., .app .. | .const .., .lam .. | .const .., .forallE ..
  | .const .., .letE .. | .const .., .lit .. | .const .., .proj ..
  | .app .., .bvar .. | .app .., .fvar .. | .app .., .sort ..
  | .app .., .const .. | .app .., .lam .. | .app .., .forallE ..
  | .app .., .letE .. | .app .., .lit .. | .app .., .proj ..
  | .lam .., .bvar .. | .lam .., .fvar .. | .lam .., .sort ..
  | .lam .., .const .. | .lam .., .app .. | .lam .., .forallE ..
  | .lam .., .letE .. | .lam .., .lit .. | .lam .., .proj ..
  | .forallE .., .bvar .. | .forallE .., .fvar .. | .forallE .., .sort ..
  | .forallE .., .const .. | .forallE .., .app .. | .forallE .., .lam ..
  | .forallE .., .letE .. | .forallE .., .lit .. | .forallE .., .proj ..
  | .letE .., .bvar .. | .letE .., .fvar .. | .letE .., .sort ..
  | .letE .., .const .. | .letE .., .app .. | .letE .., .lam ..
  | .letE .., .forallE .. | .letE .., .lit .. | .letE .., .proj ..
  | .lit .., .bvar .. | .lit .., .fvar .. | .lit .., .sort ..
  | .lit .., .const .. | .lit .., .app .. | .lit .., .lam ..
  | .lit .., .forallE .. | .lit .., .letE .. | .lit .., .proj ..
  | .proj .., .bvar .. | .proj .., .fvar .. | .proj .., .sort ..
  | .proj .., .const .. | .proj .., .app .. | .proj .., .lam ..
  | .proj .., .forallE .. | .proj .., .letE .. | .proj .., .lit .. =>
    .no (fun e => Expr.noConfusion e)
termination_by structural a

/-- The descent's decision, from a fresh state (no table: the first
shared/shared pair proved equal creates it). -/
def beqDec (a b : Expr) : Decidable (a = b) :=
  Squash.lift (beqGoX ⟨.empty, rfl⟩ a b) fun r => decidable_of_iff _ r.2

/-- The executed equality: pointer test, computed-word test, then the
memoised descent.  What both `==` (`beq_eq_beqMemo`) and every
`DecidableEq` use (`decEqPtr`, `decEq_eq_decEqPtr`) run. -/
@[inline] def beqMemo (a b : Expr) : Bool :=
  withPtrEq a b (fun _ => if a.data == b.data then @decide (a = b) (beqDec a b) else false)
    (fun h => by subst h; simp)

/-- The executed equality decides `a = b`: `withPtrEq a b k h` is
*defined* as `k ()`, the word guard cannot reject an equal pair, and
`beqDec` is a decision of `a = b`. -/
theorem beqMemo_iff (a b : Expr) : beqMemo a b = true ↔ a = b := by
  show (if a.data == b.data then @decide (a = b) (beqDec a b) else false) = true ↔ a = b
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- Expression equality as it runs (task #554): the decision read off
the pointer-first, memoised `beqMemo`, as `Name.decEqPtr`,
`Level.decEqPtr` and `Literal.decEqPtr` are for theirs. -/
@[inline] def decEqPtr (a b : Expr) : Decidable (a = b) :=
  decidable_of_iff (beqMemo a b = true) (beqMemo_iff a b)

/-- The `Expr` twin of `Name.decEq_eq_decEqPtr`: `@[csimp]`, not
`@[implemented_by]`, on `Decidable`'s subsingleton property. -/
@[csimp] theorem decEq_eq_decEqPtr : @Expr.decEq = @Expr.decEqPtr := by
  funext a b; exact Subsingleton.elim _ _

/-- Every expression equality — `=` in an `if`, a derived instance of a
type with an `Expr` field — runs `Expr.decEqPtr`. -/
instance : DecidableEq Expr := Expr.decEq

/-- Identity, decided: the pointer test at runtime, the instance in the
pure model.  The memo tables' hit validation (`Cached/ExprOpsC.lean`);
a fallback that compiled code would run is `decEqPtr`, never the
structural walk. -/
@[inline] def ptrDec (a b : Expr) : Decidable (a = b) :=
  withPtrEqDecEq a b (fun _ => inferInstance)

/-- The executed equality is the specification. -/
theorem beqMemo_eq (a b : Expr) : beqMemo a b = decide (a = b) := by
  by_cases h : a = b
  · simp [h, (beqMemo_iff b b).mpr rfl]
  · simp [h, show beqMemo a b ≠ true from fun h' => h ((beqMemo_iff a b).mp h')]

/-- The executed structural equality.  Definitionally `decide (a = b)`,
hence definitionally the `BEq` any `DecidableEq` type has, with
`beqMemo` substituted by the compiler on the `@[csimp]` equation
below. -/
def beq (a b : Expr) : Bool := decide (a = b)

/-- `==` runs `beqMemo` directly: `@[csimp]` on a kernel-checked
equality, not `@[implemented_by]`. -/
@[csimp] theorem beq_eq_beqMemo : @Expr.beq = @Expr.beqMemo := by
  funext a b; exact (beqMemo_eq a b).symm

instance : BEq Expr := ⟨Expr.beq⟩

/-- `beq` is lawful — it *is* `decide (· = ·)`. -/
instance : LawfulBEq Expr where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq, Expr.beq]

/-! ## The shared `bvar` pool (task #177)

A `bvar` node is the smallest thing this checker builds and the one it
builds most: every substitution shifts loose indices, every abstraction
introduces one, the parser reads one per occurrence.  Each of those was
a fresh allocation — and, since the substitution walks stopped
recording their atoms in the per-walk memo, a fresh allocation that
nothing shared afterwards.

`bvarPool` is one **static** table of the first `bvarPoolSize` of them.
It is a closed top-level `def`, so the runtime builds it once at module
initialization and marks it persistent (`lean_mark_persistent` in the
generated C): handing out `bvarPool[i]` costs a bounds check and a
borrowed read, and its reference counting is free.  `mkBvar` is
representation-transparent (`mkBvar_eq`, `@[simp]`), so pattern
matching stays on `.bvar` and no statement anywhere changes.

**Where it is used.**  Every *runtime* `bvar` construction goes through
it, and the routing is one line: `ConLeche.Expr.mkBVar` is the
cached tier's only `bvar` builder, so the substitution and abstraction
walks and the frontend's parser are all covered at once.  The
remaining `.bvar` literals in the tree are either the pure *spec*
functions of `ConLeche/Kernel/ExprOps.lean` (which must keep the bare
constructor — they are what the pool is proved transparent against) or
closed constants such as the cores' `.bvar 0`, which the compiler
already lifts to a per-module `_init_…_closed__n` and marks persistent
itself.

The bound covers the corpus with room to spare: the deepest de Bruijn
index the battery produces is the 4 000-binder λ tower of
`good/perf/app-lam`. -/

/-- Size of the static `bvar` pool. -/
def bvarPoolSize : Nat := 4096

@[inherit_doc bvarPoolSize]
def bvarPool : Array Expr := (Array.range bvarPoolSize).map Expr.bvar

/-- The `bvar` smart constructor: the pooled node below `bvarPoolSize`,
a fresh one above it.  Same value either way (`mkBvar_eq`). -/
@[inline] def mkBvar (i : Nat) : Expr :=
  if h : i < bvarPool.size then bvarPool[i] else .bvar i

@[simp] theorem mkBvar_eq (i : Nat) : mkBvar i = .bvar i := by
  unfold mkBvar
  split
  · simp [bvarPool]
  · rfl

end Expr

end ConLeche
