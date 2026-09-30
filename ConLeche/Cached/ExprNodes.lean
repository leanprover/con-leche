module

public import Std.Data.HashMap
public import ConLeche.Kernel.Expr

@[expose] public section

/-!
# The node constructors, and the trust census of the one expression type

There is **one** expression type, `ConLeche.Expr`, carrying its
derived fields as Lean `@[computed_field]`s (`ConLeche/Kernel/Expr.lean`;
tasks #172 B3a, #285).  The executed, memoized operations live in its
namespace beside the pure specs they are proved equal to, under a `C`
suffix wherever the spec already owns the name (`instantiate1C`,
`wscopedBC`, …); this module holds the node constructors they build
with.  The fields being the compiler's, there is no smart-constructor
discipline to maintain, and with the hash a *function* of the node the
executed equality's specification is plain decidable equality.

Equality (`Expr.beq`) is the official kernel's: pointer equality
first, then the computed hashes, then structural descent.  Together
with the `O(1)` `Hashable` instance this is what makes
`Std.HashMap Expr α` a viable memo key without a hash-consing table.
Terms are shared *naturally*, by Lean's own structure sharing: the
operations return their children by reference, so the result of an
instantiation shares every unchanged subterm with its input, and the
pointer test then decides equality of those subterms in O(1) exactly
as an arena index comparison does.

## THE TRUST CENSUS (task #172 B3a) — the escapes, all of them

`#print axioms` measures the *proof* term; an
`implemented_by` escape is invisible to both, so the escapes are
enumerated here by hand and this list is the pin.  It has ONE row.

1. **The `@[computed_field]` machinery**.  The per-node derived
   data (`hash`, `bvarB`, `fvarB`, `hasLP` — since task #167 one
   packed `UInt64`, `Expr.data`; since task #176 P3 also
   `Name.hashData` and `Level.hashData`, the cached hashes
   `Lean.Name`/`Lean.Level` and the C++ kernel keep too) is declared
   in the inductive's `with`
   block; logically it is an ordinary recursive function, and the
   *agreement between the stored word and that function is the code
   generator's*, not a theorem of this repository.  `Lean/Elab/ComputedFields.lean:33`, verbatim: *"This
   file implements the computed fields feature by simulating it via
   `implemented_by`."*  Hence it is an escape, and it is likewise
   invisible to `#print axioms`.

   **USER RULING, 2026-09-04, verbatim:** *"Adopt computed_fields.
   It's a compiler feature, we trust the compiler."*

   What the row buys: the field functions reduce definitionally on
   constructors, so no hand-rolled field invariant is needed.  The
   escape replaces a hand-maintained discipline (every construction
   site must use a smart constructor) with the compiler's own, on the
   feature `Lean.Expr` itself is built from.

**Why the equalities are not rows.**  The pointer-first
`Name.beqPtr`/`Level.beqPtr` and the pointer-first, memoised
`Expr.beqMemo` (`ConLeche/Kernel/Name.lean`, `ConLeche/Kernel/Expr.lean`)
replace `Name.beq`/`Level.beq`/`Expr.beq` in compiled code through
**`@[csimp]`**, i.e. on the strength of a *kernel-checked equality*
(`Name.beq_eq_beqPtr`, `Level.beq_eq_beqPtr`, `Expr.beq_eq_beqMemo`) —
**USER RULING, 2026-09-05, verbatim:** *"do *not* use
`implemented_by`.  If you can prove them equal, use `csimp`."*  A
`csimp` substitution is not an escape at all: the compiler is licensed
by a theorem this repository proves, not by an unchecked attribute.
The address reads behind them go through `Init.Util`'s `withPtrEq` and
`withPtrAddr`, whose side conditions those files discharge, and the
equality memo carries its invariant in its value type (`Expr.EqPair`)
and verifies every hit by identity.  The tree's compiler-escape scan
(`tests/trust-surface.sh`) is the gate that keeps the census at this
one row.
-/

namespace ConLeche.Expr

/-! ## The constructors

Under `@[computed_field]` the compiler computes the derived fields, so
each of these is the plain constructor.  The names survive because they are the term the whole
cached tier and its verification are written in; each is `@[inline]`,
so nothing is added at runtime. -/

@[inline] def mkFVar (idx : Nat) (ty : Expr) : Expr :=
  .fvar idx ty

@[inline] def mkSort (u : Level) : Expr := .sort u

@[inline] def mkConst (n : Name) (us : List Level) : Expr := .const n us

@[inline] def mkApp (f a : Expr) : Expr := .app f a

@[inline] def mkLam (ty body : Expr) (m : BinderMeta) : Expr :=
  .lam ty body m

@[inline] def mkForallE (ty body : Expr) (m : BinderMeta) :
    Expr := .forallE ty body m

@[inline] def mkLetE (ty val body : Expr) : Expr :=
  .letE ty val body

@[inline] def mkLit (l : Literal) : Expr := .lit l

@[inline] def mkProj (s : Name) (i : Nat) (e : Expr) : Expr := .proj s i e

/-! ## Equality, hashing and the trust census

Both live in `ConLeche/Kernel/Expr.lean`, with the type
itself: `BEq Expr` must be **one** instance tree-wide (the pure tier
compares `Expr`s too, and two defeq-but-distinct instances make `rw`
and `simp` fail across the seam — measured, on `DiscC5`'s `defeqStep`
simulation).  `Expr.beq` is `Expr.beq`, verified there (`Expr.beqMemo_eq`); the
trust census is this module's header. -/

/-! ### The constructor equations

`mkApp f a = .app f a` and its nine siblings, all `rfl`; the cached
tier rewrites with them.  That every node's derived data satisfies its
recurrence is the compiler's (the census row above). -/

@[simp] theorem mkFVar_eq (idx : Nat) (ty : Expr) :
    mkFVar idx ty = .fvar idx ty := rfl

@[simp] theorem mkSort_eq (u : Level) : mkSort u = .sort u := rfl

@[simp] theorem mkConst_eq (n : Name) (us : List Level) :
    mkConst n us = .const n us := rfl

@[simp] theorem mkApp_eq (f a : Expr) : mkApp f a = .app f a := rfl

@[simp] theorem mkLam_eq (ty b : Expr) (m : BinderMeta) :
    mkLam ty b m = .lam ty b m := rfl

@[simp] theorem mkForallE_eq (ty b : Expr) (m : BinderMeta) :
    mkForallE ty b m = .forallE ty b m := rfl

@[simp] theorem mkLetE_eq (ty v b : Expr) :
    mkLetE ty v b = .letE ty v b := rfl

@[simp] theorem mkLit_eq (l : Literal) : mkLit l = .lit l := rfl

@[simp] theorem mkProj_eq (s : Name) (i : Nat) (e : Expr) :
    mkProj s i e = .proj s i e := rfl

end ConLeche.Expr
