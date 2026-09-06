module

public import Lech.Kernel.PropWhen
/- `withPtrEq` is `public` but not `@[expose]`, and its whole point here
is that it is *definitionally* `k ()` — which is what
`Level.beqPtr_eq` proves.  `import all` makes that body visible **in
this module only**; that theorem is the public relay, so no importer
needs it, and the executed `Level.beq` stays the plain
`decide (· = ·)` that the kernel can still reduce. -/
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

namespace Lech


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
deriving DecidableEq, Repr, Inhabited

/-- Hashing a level is an `O(1)` field read (the memo maps keyed by
`Level` — `lsimpC`, `lnzC`, `eqvC` — probe with this). -/
instance : Hashable Level := ⟨Level.hashData⟩

/-- Level equality in the official kernel's shape (task #176 P2):
the cached **hash** and the **pointer** before the structural walk —
`level.cpp:125` is `kind` → `hash` → `is_eqp` → structural.  The
implementation of `Level.beq`; `Level.beqPtr_eq` proves both guards
redundant. -/
@[inline] def Level.beqPtr (a b : Level) : Bool :=
  withPtrEq a b (fun _ => a.hashData == b.hashData && decide (a = b))
    (fun h => by subst h; simp)

/-- Both guards are redundant (see `Name.beqPtr_eq`). -/
theorem Level.beqPtr_eq (a b : Level) : Level.beqPtr a b = decide (a = b) := by
  show (a.hashData == b.hashData && decide (a = b)) = decide (a = b)
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- The executed level equality: definitionally `decide (a = b)`, with
`beqPtr` substituted by the compiler on the `@[csimp]` equation below
(see `Name.beq_eq_beqPtr` for why this is not an escape). -/
def Level.beq (a b : Level) : Bool := decide (a = b)

/-- The `Level` twin of `Name.beq_eq_beqPtr`: `@[csimp]`, not
`@[implemented_by]`, on a kernel-checked equality. -/
@[csimp] theorem Level.beq_eq_beqPtr : @Level.beq = @Level.beqPtr := by
  funext a b; exact (Level.beqPtr_eq a b).symm

instance : BEq Level := ⟨Level.beq⟩

/-- `Level.beq` is lawful — it *is* `decide (· = ·)`. -/
instance : LawfulBEq Level where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq, Level.beq]

/-- Binder annotations. Irrelevant to checking; kept for round-tripping and
error messages. -/
inductive BinderInfo where
  | default
  | implicit
  | strictImplicit
  | instImplicit
  deriving DecidableEq, Repr, Inhabited, Hashable

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
node's `hash` field is `O(1)` in the level's size *and* exact (before
task #176 P3 this was a depth-4-bounded walk, `Level.hashB`, because
the level had nowhere to put a hash — the same trade `Expr.hashB` made
before task #172 B3a). -/
@[inline] def levelHash (u : Level) : UInt64 := u.hashData

/-- `levelHash` folded over a level list. -/
def levelsHash : List Level → UInt64
  | [] => 13
  | u :: us => mixHash (levelHash u) (levelsHash us)

/-! ## The packed node word (task #167)

`Lean.Expr` stores its derived data in one `UInt64` (`Lean.Expr.Data`:
a 32-bit hash, a 20-bit `looseBVarRange`, flags).  `Lech.Expr` does
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

theorem hashOfData_lt (w : UInt64) : (hashOfData w).toNat < 4294967296 := by
  have hs := UInt64.toNat_lt_size w
  simp only [UInt64.size] at hs
  simp [hashOfData, UInt64.toNat_div]
  omega

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

theorem hashOfData_pack (h b f : UInt64) (lp : Bool)
    (_hh : h.toNat < 4294967296) (hb : b.toNat < 32768)
    (hf : f.toNat < 32768) :
    hashOfData (packData h b f lp) = hash32 h := by
  apply UInt64.toNat_inj.mp
  cases lp <;>
  · simp [hashOfData, hash32, packData, UInt64.toNat_add, UInt64.toNat_mul,
      UInt64.toNat_div, UInt64.toNat_mod]
    omega

theorem hash32_lt (w : UInt64) : (hash32 w).toNat < 4294967296 := by
  simp [hash32, UInt64.toNat_mod]; omega

/-- Kernel expressions.

`fvar idx name type`: an opened variable, identified by its de Bruijn level
`idx` *and* its type; the binder `name` is display-only.  Closed input terms
contain no `fvar`s.

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
in `Lech/Cached/ExprC.lean`'s module docstring. -/
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
  /-- The packed derived-data word: `hash` (32) ǀ reserved (1) ǀ
  `bvarB` (15, saturating) ǀ `fvarB` (15, saturating) ǀ `hasLP` (1). -/
  @[computed_field] data : Expr → UInt64
    | .bvar i =>
      packData (hash32 (mixHash 3 (Hashable.hash i))) (satSucc i) 0 false
    | .fvar idx n ty =>
      packData (hash32 (mixHash 5 (mixHash (Hashable.hash idx)
          (mixHash (Hashable.hash n) (hashOfData ty.data)))))
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
    | .lam n ty b m =>
      packData (hash32 (mixHash 19 (mixHash (Hashable.hash n)
          (mixHash (hashOfData ty.data)
            (mixHash (hashOfData b.data) (Hashable.hash m))))))
        (max (bvarOfData ty.data) (satPred (bvarOfData b.data)))
        (max (fvarOfData ty.data) (fvarOfData b.data))
        (lpOfData ty.data || lpOfData b.data || m.pw.hasParams)
    | .forallE n ty b m =>
      packData (hash32 (mixHash 23 (mixHash (Hashable.hash n)
          (mixHash (hashOfData ty.data)
            (mixHash (hashOfData b.data) (Hashable.hash m))))))
        (max (bvarOfData ty.data) (satPred (bvarOfData b.data)))
        (max (fvarOfData ty.data) (fvarOfData b.data))
        (lpOfData ty.data || lpOfData b.data || m.pw.hasParams)
    | .letE n ty v b =>
      packData (hash32 (mixHash 29 (mixHash (Hashable.hash n)
          (mixHash (hashOfData ty.data)
            (mixHash (hashOfData v.data) (hashOfData b.data))))))
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
deriving DecidableEq, Repr, Inhabited

/-! ## The packed word's accessors

`hash` and `hasLP` are exact bit reads.  `bvarBRaw`/`fvarBRaw` are the
*saturating* reads: below `satRange` they are the exact bound
(`bvarBRaw_exact`, `fvarBRaw_exact` in `Verify/Cached/Erase.lean`); at
`satRange` they mean "at least that", and `Expr.bvarB`/`Expr.fvarB`
(`Kernel/ExprOps.lean`) recover exactness there with a memoized
walk. -/

namespace Expr

/-- The node's 32-bit hash (`O(1)`; display-only payload is included,
which a hash may do — `DecidableEq` remains full structural
equality). -/
@[inline] def hash (e : Expr) : UInt64 := hashOfData e.data

/-- Has-level-param: is level instantiation ever non-trivial here?
One bit, so this read is *exact*. -/
@[inline] def hasLP (e : Expr) : Bool := lpOfData e.data

/-- The stored loose-bvar bound, saturating at `satRange`. -/
@[inline] def bvarBRaw (e : Expr) : Nat := (bvarOfData e.data).toNat

/-- The stored fvar range, saturating at `satRange`. -/
@[inline] def fvarBRaw (e : Expr) : Nat := (fvarOfData e.data).toNat

end Expr

/-- Hashing is the computed field: `O(1)`, no traversal.  (Before task
#172 B3a this was a *node-budgeted* walk, `Expr.hashB`, because the
pure representation had nowhere to put a hash.  `levelHash` kept a
depth budget for the same reason until task #176 P3 gave `Level` its
own computed field; no hash in the tree is budgeted any more.) -/
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
      simp only [satPred, beq_iff_eq, hne, hz', if_false, if_neg hs,
        toNat_sub_one hz]

@[simp] theorem bvarBRaw_bvar (i : Nat) :
    (Expr.bvar i).bvarBRaw = min (i + 1) satRange := by
  show (bvarOfData (packData _ (satSucc i) 0 false)).toNat = _
  rw [bvarOfData_pack _ _ _ _ (satSucc_lt i) (by decide), toNat_satSucc]

@[simp] theorem bvarBRaw_fvar (idx : Nat) (n : Name) (ty : Expr) :
    (Expr.fvar idx n ty).bvarBRaw = 0 := by
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

@[simp] theorem bvarBRaw_lam (n : Name) (ty b : Expr) (m : BinderMeta) :
    (Expr.lam n ty b m).bvarBRaw =
      max ty.bvarBRaw
        (if b.bvarBRaw = satRange then satRange else b.bvarBRaw - 1) := by
  show (bvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [bvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max,
    toNat_satPred (bvarOfData_lt _)]
  rfl

@[simp] theorem bvarBRaw_forallE (n : Name) (ty b : Expr) (m : BinderMeta) :
    (Expr.forallE n ty b m).bvarBRaw =
      max ty.bvarBRaw
        (if b.bvarBRaw = satRange then satRange else b.bvarBRaw - 1) := by
  show (bvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [bvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max,
    toNat_satPred (bvarOfData_lt _)]
  rfl

@[simp] theorem bvarBRaw_letE (n : Name) (ty v b : Expr) :
    (Expr.letE n ty v b).bvarBRaw =
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

@[simp] theorem fvarBRaw_fvar (idx : Nat) (n : Name) (ty : Expr) :
    (Expr.fvar idx n ty).fvarBRaw = min (idx + 1) satRange := by
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

@[simp] theorem fvarBRaw_lam (n : Name) (ty b : Expr) (m : BinderMeta) :
    (Expr.lam n ty b m).fvarBRaw = max ty.fvarBRaw b.fvarBRaw := by
  show (fvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [fvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max]
  rfl

@[simp] theorem fvarBRaw_forallE (n : Name) (ty b : Expr) (m : BinderMeta) :
    (Expr.forallE n ty b m).fvarBRaw = max ty.fvarBRaw b.fvarBRaw := by
  show (fvarOfData (packData _ (max _ (satPred _)) (max _ _) _)).toNat = _
  rw [fvarOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _)), toNat_max]
  rfl

@[simp] theorem fvarBRaw_letE (n : Name) (ty v b : Expr) :
    (Expr.letE n ty v b).fvarBRaw =
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

@[simp] theorem hasLP_fvar (idx : Nat) (n : Name) (ty : Expr) :
    (Expr.fvar idx n ty).hasLP = ty.hasLP := by
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

@[simp] theorem hasLP_lam (n : Name) (ty b : Expr) (m : BinderMeta) :
    (Expr.lam n ty b m).hasLP = (ty.hasLP || b.hasLP || m.pw.hasParams) := by
  show lpOfData (packData _ (max _ (satPred _)) (max _ _) _) = _
  rw [lpOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))]
  rfl

@[simp] theorem hasLP_forallE (n : Name) (ty b : Expr) (m : BinderMeta) :
    (Expr.forallE n ty b m).hasLP =
      (ty.hasLP || b.hasLP || m.pw.hasParams) := by
  show lpOfData (packData _ (max _ (satPred _)) (max _ _) _) = _
  rw [lpOfData_pack _ _ _ _
    (max_lt_32768 (bvarOfData_lt _) (satPred_lt (bvarOfData_lt _)))
    (max_lt_32768 (fvarOfData_lt _) (fvarOfData_lt _))]
  rfl

@[simp] theorem hasLP_letE (n : Name) (ty v b : Expr) :
    (Expr.letE n ty v b).hasLP = (ty.hasLP || v.hasLP || b.hasLP) := by
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

**The specification is plain decidable equality** (task #172 B3a).  It
used to be `beqSpec`, a hash-checking descent, because the hash was a
*stored* datum that could disagree with the term: the spec had to
compare it so that the `implemented_by` claim stayed faithful on
field-incorrect inputs.  Under `@[computed_field]` there are no
field-incorrect inputs — `a.hash` is a function of `a` — so the hash
test is an implementation detail of the fast path again, and
`beq = decide (a = b)` is defeq to the `BEq` instance any type gets
from its `DecidableEq`. -/

/-- `true` for the nodes whose comparison recurses.  The memo is
consulted and written **only** at these (task #192): a `bvar`, `sort`,
`const` or `lit` pair is decided without a descent, so an entry for it
can never save a walk and every one of them costs a probe, a bucket
cons cell and, at the end of the call, its `lean_dec_ref`.  Leaves are
the majority of the nodes of a real term. -/
@[inline] def beqRecursive : Expr → Bool
  | .fvar .. | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => true
  | _ => false

/-- The executed equality: pointer test, computed-word test, then a
**memoized** structural descent.

The memo is what keeps equality `O(DAG)` rather than `O(tree)`.  It is
not optional at this representation: hash-consing identifies
structurally equal terms *however they arose*, so the arena never
compares two distinct-but-equal DAGs; the clone does exactly that
whenever a reduction rebuilds a term the arena would have collapsed,
and without the memo `good/perf/app-lam` (24 k arena nodes, ~10^1160
unshared tree) is unreachable.  Pointer identity and the word test
still carry the overwhelming majority of comparisons; the memo is
allocated only on the descent.

**Its shape** (task #192; the previous one was
`Std.HashMap (USize × USize) Bool`).  Task #189 measured 46 – 52 % of
the five slowest Mathlib declarations in `mi_malloc_small` /
`lean_dec_ref_cold` under this function, and that traffic was the
memo's *keys*: a `USize × USize` key is three heap objects (the `Prod`
cell and a boxed `USize` each), allocated on **every** probe — hit or
miss — and again on every insert, and the `Bool` payload made a fourth
object of the bucket cons cell.  Three changes, none of them visible
to the answer:

* the key is `addr a` as a **`Nat`**, the value `addr b` as a `Nat`.
  An address is far below `LEAN_MAX_SMALL_NAT`, so `USize.toNat` is
  `lean_box` — a tag, not an allocation — and a probe now allocates
  nothing at all.  `Std.DHashMap`'s `scrambleHash` folds the high bits
  down, so the alignment zeros in the low bits do not cluster.
* only **`true`** is recorded, as official's `expr_eq_fn` does: a
  completed `false` aborts the whole comparison (every arm below
  propagates it to the root), so no `false` is ever re-queried and
  `getD pa 0 == pb` — address `0` is no object — is the whole probe.
  A key that gets re-bound (the same `a` proved equal to a second `b`)
  loses its old entry; that costs a re-walk, never an answer.
* leaves are neither probed nor recorded (`beqRecursive`).

Soundness is unchanged and rests on the same two runtime facts as
before (see `beqFast`): an entry is written only after a *completed*
descent proved that pair equal, and both roots stay live for the whole
call, so no keyed address can be recycled underneath it. -/
unsafe def beqGo (memo : Std.HashMap Nat Nat) (a b : Expr) :
    Bool × Std.HashMap Nat Nat :=
  let pa := (ptrAddrUnsafe a).toNat
  let pb := (ptrAddrUnsafe b).toNat
  if pa == pb then (true, memo)
  else if a.data != b.data then (false, memo)
  else
    let isRec := beqRecursive a
    if isRec && memo.getD pa 0 == pb then (true, memo)
    else
      let and2 := fun (memo : Std.HashMap Nat Nat)
          (x y : Expr) (z w : Expr) =>
        let (r₁, memo) := beqGo memo x y
        if r₁ then beqGo memo z w else (false, memo)
      let (r, memo) : Bool × Std.HashMap Nat Nat :=
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
      if r && isRec then (true, memo.insert pa pb) else (r, memo)

/-- Node budget of the allocation-free descent before the memoized one
takes over.  Almost every comparison the checker makes is decided by
the pointer test, the computed-word test, or a handful of nodes; paying
for a memo table there was measured at +33 % instructions on
`init-prelude`.  Beyond the budget the term is big enough that
`O(tree)` is the real risk, and the memoized descent is restarted from
scratch. -/
def beqBudget : Nat := 4096

/-- Allocation-free structural descent on a node budget: `none` when
the budget runs out (the caller retries under the memo). -/
unsafe def beqB (fuel : Nat) (a b : Expr) : Option Bool × Nat :=
  if ptrAddrUnsafe a == ptrAddrUnsafe b then (some true, fuel)
  else if a.data != b.data then (some false, fuel)
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
computed fields the cheap reject needs no side condition: the whole
packed word `a.data` is a function of `a` (task #192 widened the test
from `a.hash`, its top 32 bits, to the word — same instruction, and it
rejects on a `bvarB`, `fvarB` or `hasLP` disagreement too), so a word
mismatch is an inequality outright — task #172 B3a shrank this
argument exactly as B2 predicted.  What is left
to trust is two facts about the runtime: (a) *pointer equality implies structural equality* —
Lean objects are immutable, so two references to one address are one
value (the pointer short-circuits here and in `beqB`/`beqGo`, and the
address-keyed memo, all rest on this); (b) *the address-keyed memo
entries stay valid for the life of one comparison* — both roots are
live for the whole call, so every keyed subobject is reachable and
the collector, which never moves objects, cannot reuse a keyed
address.  The verification (`Lech/Verify/Cached/*`) consumes only
`beq`'s pure definition and never this function. -/
unsafe def beqFast (a b : Expr) : Bool :=
  if ptrAddrUnsafe a == ptrAddrUnsafe b then true
  else if a.data != b.data then false
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
it, and the routing is one line: `Lech.Cached.ExprC.mkBVar` is the
cached tier's only `bvar` builder, so the substitution and abstraction
walks, `ofView` and the frontend's parser are all covered at once.  The
remaining `.bvar` literals in the tree are either the pure *spec*
functions of `Lech/Kernel/ExprOps.lean` (which must keep the bare
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

end Lech

