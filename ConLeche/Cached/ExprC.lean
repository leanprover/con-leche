module

public import Std.Data.HashMap
import ConLeche.Kernel.Expr
public import ConLeche.Kernel.ExprOps
import ConLeche.Kernel.Level

@[expose] public section

/-!
# `ExprC`: the cached engine's namespace over the one expression type

**Task #172 B3a — the type unified.**  `ExprC` *was* a second
expression inductive whose constructors carried four hand-rolled
derived fields (`h bb fb lp`), maintained by smart constructors and
related to `ConLeche.Expr` by an erasure.  It is now an **abbreviation
for `ConLeche.Expr` itself**, which carries those four as Lean
`@[computed_field]`s (`ConLeche/Kernel/Expr.lean`) — the user's ruling,
*"Adopt computed_fields.  It's a compiler feature, we trust the
compiler."*

What survives, and why the name does: the cached engine's *operations*
(`instantiate1`, `abstractRange`, … — memoized, `Std.HashMap`-backed)
have the same names as the pure spec functions in `ConLeche.Expr`'s
namespace, and the verification's whole subject is that the two agree.
So `ConLeche.Cached.ExprC` remains as a **namespace** for the executed
operations; dot notation on an `ExprC`-typed value finds it first and
falls through to `ConLeche.Expr` for anything it does not define — which
is exactly how the four field readers now resolve.

What died with the type: `WFc`'s smart-constructor discipline
(nothing to maintain — the fields are the compiler's), the erasure's
mediation between a spec type and a runtime type (there is one type),
and, with the hash a *function* rather than a stored datum, the
`beqSpec` normal-form apparatus: the executed equality's specification
is now plain decidable equality.

Equality (`ExprC.beq`) is the official kernel's: pointer equality
first, then the computed hashes, then structural descent.  Together
with the `O(1)` `Hashable` instance this is what makes
`Std.HashMap ExprC α` a viable memo key without a hash-consing table.
Terms are shared *naturally*, by Lean's own structure sharing: the
operations return their children by reference, so the result of an
instantiation shares every unchanged subterm with its input, and the
pointer test then decides equality of those subterms in O(1) exactly
as an arena index comparison does.

## THE TRUST CENSUS (task #172 B3a, 2026-09-04) — the escapes, all of
them

`#print axioms` and `tests/proofdeps.sh` measure the *proof* term; an
`implemented_by` escape is invisible to both, so the escapes are
enumerated here by hand and this list is the pin.

1. **`ExprC.beqFast` for `ExprC.beq`** — written in this file,
   docstringed at its definition: pointer equality implies structural
   equality; address-keyed memo entries stay valid for one
   comparison's lifetime.
2. **The `@[computed_field]` machinery** (NEW).  The per-node derived
   data (`hash`, `bvarB`, `fvarB`, `hasLP` — since task #167 one
   packed `UInt64`, `Expr.data`; since task #176 P3 also
   `Name.hashData` and `Level.hashData`, the cached hashes
   `Lean.Name`/`Lean.Level` and the C++ kernel keep too) is declared
   in the inductive's `with`
   block; logically it is an ordinary recursive function, and the
   *agreement between the stored word and that function is the code
   generator's*, not a theorem of this repository.  `Lean/Elab/ComputedFields.lean:33`, verbatim: *"This
   file implements the computed fields feature by simulating it via
   `implemented_by`."*  Hence it is an escape of exactly the class of
   row 1, and it is likewise invisible to `#print axioms` and to
   `tests/proofdeps.sh`.

   **USER RULING, 2026-09-04, verbatim:** *"Adopt computed_fields.
   It's a compiler feature, we trust the compiler."*

   What the row buys, measured before adoption (task #172 B2 §5,
   probes `_tmp/tricore-b2/{CF,CF2,CF3}.lean`): the field functions
   reduce definitionally on constructors, so `WFc` — the hand-rolled
   field invariant — **disappears** rather than becomes true, and with
   it the smart-constructor discipline, the `WExprC`/`WDeclC`
   subtypes, `eraseC`/`ofExpr` and their injectivity lemma.  The
   escape replaces a hand-maintained discipline (every construction
   site must use a smart constructor) with the compiler's own, on the
   feature `Lean.Expr` itself is built from.

**Census history, so the count is readable.**  The task-#163 census
said *two* escapes (`beqFast`, `ofExprFast`); `ofExprFast` was
**deleted by architecture** on 2026-09-03 (see `ofExpr` below), which
left **one** — a shrink DESIGN.md records but this docstring did not,
so its "exactly two" was stale by one row when B3a opened.  The
corrected count with the computed-fields row is therefore **two, with
a different second member**, not three; the escape *class* is what B2
flagged for ruling, and it is the row above.

**Task #176 added no row, and it is worth saying why.**  The
pointer-and-hash-first `Name.beqPtr`/`Level.beqPtr`
(`ConLeche/Kernel/Expr.lean`) replace `Name.beq`/`Level.beq` in compiled
code through **`@[csimp]`**, i.e. on the strength of a *kernel-checked
equality* (`Name.beq_eq_beqPtr`, `Level.beq_eq_beqPtr`) — **USER
RULING, 2026-09-05, verbatim:** *"do *not* use `implemented_by`.  If
you can prove them equal, use `csimp`."*  A `csimp` substitution is
not an escape at all: the compiler is licensed by a theorem this
repository proves, not by an unchecked attribute.  So `beqFast`
(row 1) remains this tree's **only** `implemented_by`-class escape,
and it stands alone; the computed-fields row (row 2) merely gained two
users.
-/

namespace ConLeche.Cached

open ConLeche

/-- The cached engine's expression type **is** `ConLeche.Expr` (task
#172 B3a).  The four per-node derived data live in that type's single
packed `@[computed_field]` (task #167), so `e.hash`, `e.bvarB`,
`e.fvarB` and `e.hasLP` resolve here through this namespace to
`ConLeche.Expr`'s accessors — `O(1)` bit reads, exact, with `bvarB` and
`fvarB` falling back to a memoized exact walk on the saturated branch
alone. -/
abbrev ExprC := ConLeche.Expr

namespace ExprC

/-- The node's fvar flag (`fvarB ≠ 0`), `O(1)` — the field-read
counterpart of the pure `Expr.hasFvar` walk (`hasFvar_eq`). -/
@[inline] def hasFvar (e : ExprC) : Bool := e.fvarB != 0

/-! ## The constructors

Before task #172 B3a these were *smart* constructors: each computed the
four derived fields from its children's, and `WFc` was the discipline
that no raw constructor application escaped them.  Under
`@[computed_field]` the compiler does that, so each is now its own
constructor.  The names survive because they are the term the whole
cached tier and its verification are written in; each is `@[inline]`,
so nothing is added at runtime. -/

@[inline] def mkBVar (i : Nat) : ExprC := Expr.mkBvar i

@[inline] def mkFVar (idx : Nat) (ty : ExprC) : ExprC :=
  .fvar idx ty

@[inline] def mkSort (u : Level) : ExprC := .sort u

@[inline] def mkConst (n : Name) (us : List Level) : ExprC := .const n us

@[inline] def mkApp (f a : ExprC) : ExprC := .app f a

@[inline] def mkLam (ty body : ExprC) (m : BinderMeta) : ExprC :=
  .lam ty body m

@[inline] def mkForallE (ty body : ExprC) (m : BinderMeta) :
    ExprC := .forallE ty body m

@[inline] def mkLetE (ty val body : ExprC) : ExprC :=
  .letE ty val body

@[inline] def mkLit (l : Literal) : ExprC := .lit l

@[inline] def mkProj (s : Name) (i : Nat) (e : ExprC) : ExprC := .proj s i e

/-! ## Equality, hashing and the trust census

Both moved to `ConLeche/Kernel/Expr.lean` at task #172 B3a, with the type
itself: `BEq Expr` must be **one** instance tree-wide (the pure tier
compares `Expr`s too, and two defeq-but-distinct instances make `rw`
and `simp` fail across the seam — measured, on `DiscC5`'s `defeqStep`
simulation).  `ExprC.beq` is `Expr.beq`; the trust census, including
the `beqFast` escape and the computed-fields row, is that module's
header. -/

/-! ## The former `Expr` boundary, and the former field invariant

**Both are gone with the type** (task #172 B3a for the boundary, B3b
for the invariant).  `ofExpr`/`toExpr` converted between the checker's
`Expr`-typed declaration layer and the core's `ExprC`; with one type
there is nothing to convert, and every call site passes its argument
through.  The erasure `eraseC` and its injectivity lemma likewise: the
fields are functions of the node, so a node *is* its own erasure.

`WFc` outlived them by one batch, as the predicate of the `WDeclC`
subtype six direct-parse capstone letters were stated over.  With those
letters restated over `List DeclC` (ratified; a strengthening — the
dropped hypothesis was provable of everything), the whole tier goes:
`WFc`, `WFc_all`, `WFc.mk*`, `WExprC` and the `mk*W` constructors,
`DeclCWFc`/`WDeclC`, `ofExpr`/`ofExprSpec`.  What the invariant used to
buy — that every node's derived data satisfies its recurrence — is now
the compiler's, which is what the census's second escape names. -/

/-! ### The constructor equations

`mkApp f a = .app f a` and its nine siblings, all `rfl`.  They were
the erasure's "smart constructor erases to the plain constructor"
lemmas (`mkApp_eq` &c.); with one type they are the constructors'
own equations, and the tier still rewrites with them. -/

@[simp] theorem mkBVar_eq (i : Nat) : mkBVar i = .bvar i := Expr.mkBvar_eq i

@[simp] theorem mkFVar_eq (idx : Nat) (ty : ExprC) :
    mkFVar idx ty = .fvar idx ty := rfl

@[simp] theorem mkSort_eq (u : Level) : mkSort u = .sort u := rfl

@[simp] theorem mkConst_eq (n : Name) (us : List Level) :
    mkConst n us = .const n us := rfl

@[simp] theorem mkApp_eq (f a : ExprC) : mkApp f a = .app f a := rfl

@[simp] theorem mkLam_eq (ty b : ExprC) (m : BinderMeta) :
    mkLam ty b m = .lam ty b m := rfl

@[simp] theorem mkForallE_eq (ty b : ExprC) (m : BinderMeta) :
    mkForallE ty b m = .forallE ty b m := rfl

@[simp] theorem mkLetE_eq (ty v b : ExprC) :
    mkLetE ty v b = .letE ty v b := rfl

@[simp] theorem mkLit_eq (l : Literal) : mkLit l = .lit l := rfl

@[simp] theorem mkProj_eq (s : Name) (i : Nat) (e : ExprC) :
    mkProj s i e = .proj s i e := rfl

end ExprC

end ConLeche.Cached
