import Std.Data.HashMap
import Setlec.Kernel.Expr
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Level

/-!
# `ExprC`: the cached engine's namespace over the one expression type

**Task #172 B3a — the type unified.**  `ExprC` *was* a second
expression inductive whose constructors carried four hand-rolled
derived fields (`h bb fb lp`), maintained by smart constructors and
related to `Setlec.Expr` by an erasure.  It is now an **abbreviation
for `Setlec.Expr` itself**, which carries those four as Lean
`@[computed_field]`s (`Setlec/Kernel/Expr.lean`) — the user's ruling,
*"Adopt computed_fields.  It's a compiler feature, we trust the
compiler."*

What survives, and why the name does: the cached engine's *operations*
(`instantiate1`, `abstractRange`, … — memoized, `Std.HashMap`-backed)
have the same names as the pure spec functions in `Setlec.Expr`'s
namespace, and the verification's whole subject is that the two agree.
So `Setlec.Cached.ExprC` remains as a **namespace** for the executed
operations; dot notation on an `ExprC`-typed value finds it first and
falls through to `Setlec.Expr` for anything it does not define — which
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
   data (`hash`, `bvarB`, `fvarB`, `hasLP`) is declared in the
   inductive's `with` block; logically each is an ordinary recursive
   function, and the *agreement between the stored word and that
   function is the code generator's*, not a theorem of this
   repository.  `Lean/Elab/ComputedFields.lean:33`, verbatim: *"This
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
-/

namespace Setlec.Cached

open Setlec

/-- The cached engine's expression type **is** `Setlec.Expr` (task
#172 B3a).  The four per-node derived data are that type's
`@[computed_field]`s, so `e.hash`, `e.bvarB`, `e.fvarB` and `e.hasLP`
resolve here through this namespace to `Setlec.Expr`'s field
functions — `O(1)` reads, and definitional on constructors. -/
abbrev ExprC := Setlec.Expr

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

@[inline] def mkBVar (i : Nat) : ExprC := .bvar i

@[inline] def mkFVar (idx : Nat) (n : Name) (ty : ExprC) : ExprC :=
  .fvar idx n ty

@[inline] def mkSort (u : Level) : ExprC := .sort u

@[inline] def mkConst (n : Name) (us : List Level) : ExprC := .const n us

@[inline] def mkApp (f a : ExprC) : ExprC := .app f a

@[inline] def mkLam (n : Name) (ty body : ExprC) (m : BinderMeta) : ExprC :=
  .lam n ty body m

@[inline] def mkForallE (n : Name) (ty body : ExprC) (m : BinderMeta) :
    ExprC := .forallE n ty body m

@[inline] def mkLetE (n : Name) (ty val body : ExprC) : ExprC :=
  .letE n ty val body

@[inline] def mkLit (l : Literal) : ExprC := .lit l

@[inline] def mkProj (s : Name) (i : Nat) (e : ExprC) : ExprC := .proj s i e

/-! ## Equality, hashing and the trust census

Both moved to `Setlec/Kernel/Expr.lean` at task #172 B3a, with the type
itself: `BEq Expr` must be **one** instance tree-wide (the pure tier
compares `Expr`s too, and two defeq-but-distinct instances make `rw`
and `simp` fail across the seam — measured, on `DiscC5`'s `defeqStep`
simulation).  `ExprC.beq` is `Expr.beq`; the trust census, including
the `beqFast` escape and the computed-fields row, is that module's
header. -/

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


/-! ## The erasure and the field invariant (task #171)

Moved from `Setlec/Verify/Cached/Erase.lean` under the
self-contained-verification exception (the `Std.HashMap` pattern): the
direct-parse frontend (`Setlec/Frontend/ExportC.lean`) carries `WFc`
in its table types, so the invariant and its smart-constructor closure
must be visible implementation-side.  Same namespace as before — every
downstream reference is unchanged. -/

/-! ## The erasure -/

/-- Erase the four computed fields, yielding the plain expression the
node represents.  Non-injective on raw `ExprC` (garbage fields erase
away); injective on `WFc` (`eraseC_inj`). -/
def eraseC : ExprC → Expr
  | .bvar i .. => .bvar i
  | .fvar idx n ty .. => .fvar idx n (eraseC ty)
  | .sort u .. => .sort u
  | .const n us .. => .const n us
  | .app f a .. => .app (eraseC f) (eraseC a)
  | .lam n ty b m .. => .lam n (eraseC ty) (eraseC b) m
  | .forallE n ty b m .. => .forallE n (eraseC ty) (eraseC b) m
  | .letE n ty v b .. => .letE n (eraseC ty) (eraseC v) (eraseC b)
  | .lit l .. => .lit l
  | .proj s i e .. => .proj s i (eraseC e)

/-! The smart constructors erase to the plain constructors (the
"erasure half" of field exactness: all `rfl`). -/

@[simp] theorem eraseC_mkBVar (i : Nat) : eraseC (mkBVar i) = .bvar i := rfl

@[simp] theorem eraseC_mkFVar (idx : Nat) (n : Name) (ty : ExprC) :
    eraseC (mkFVar idx n ty) = .fvar idx n (eraseC ty) := rfl

@[simp] theorem eraseC_mkSort (u : Level) : eraseC (mkSort u) = .sort u := rfl

@[simp] theorem eraseC_mkConst (n : Name) (us : List Level) :
    eraseC (mkConst n us) = .const n us := rfl

@[simp] theorem eraseC_mkApp (f a : ExprC) :
    eraseC (mkApp f a) = .app (eraseC f) (eraseC a) := rfl

@[simp] theorem eraseC_mkLam (n : Name) (ty b : ExprC) (m : BinderMeta) :
    eraseC (mkLam n ty b m) = .lam n (eraseC ty) (eraseC b) m := rfl

@[simp] theorem eraseC_mkForallE (n : Name) (ty b : ExprC) (m : BinderMeta) :
    eraseC (mkForallE n ty b m) = .forallE n (eraseC ty) (eraseC b) m := rfl

@[simp] theorem eraseC_mkLetE (n : Name) (ty v b : ExprC) :
    eraseC (mkLetE n ty v b) = .letE n (eraseC ty) (eraseC v) (eraseC b) := rfl

@[simp] theorem eraseC_mkLit (l : Literal) : eraseC (mkLit l) = .lit l := rfl

@[simp] theorem eraseC_mkProj (s : Name) (i : Nat) (e : ExprC) :
    eraseC (mkProj s i e) = .proj s i (eraseC e) := rfl

/-- `ofExpr` (the pure conversion) is a section of the erasure. -/
@[simp] theorem eraseC_ofExpr : ∀ x : Expr, eraseC (ofExpr x) = x := by
  intro x
  induction x with
  | bvar i => rfl
  | fvar idx n ty ih =>
    show eraseC (mkFVar idx n (ofExprSpec ty)) = _
    simp [show ofExprSpec ty = ofExpr ty from rfl, ih]
  | sort u => rfl
  | const n us => rfl
  | app f a ihf iha =>
    show eraseC (mkApp (ofExprSpec f) (ofExprSpec a)) = _
    simp [show ofExprSpec f = ofExpr f from rfl,
      show ofExprSpec a = ofExpr a from rfl, ihf, iha]
  | lam n ty b m iht ihb =>
    show eraseC (mkLam n (ofExprSpec ty) (ofExprSpec b) m) = _
    simp [show ofExprSpec ty = ofExpr ty from rfl,
      show ofExprSpec b = ofExpr b from rfl, iht, ihb]
  | forallE n ty b m iht ihb =>
    show eraseC (mkForallE n (ofExprSpec ty) (ofExprSpec b) m) = _
    simp [show ofExprSpec ty = ofExpr ty from rfl,
      show ofExprSpec b = ofExpr b from rfl, iht, ihb]
  | letE n ty v b iht ihv ihb =>
    show eraseC (mkLetE n (ofExprSpec ty) (ofExprSpec v) (ofExprSpec b)) = _
    simp [show ofExprSpec ty = ofExpr ty from rfl,
      show ofExprSpec v = ofExpr v from rfl,
      show ofExprSpec b = ofExpr b from rfl, iht, ihv, ihb]
  | lit l => rfl
  | proj s i e ih =>
    show eraseC (mkProj s i (ofExprSpec e)) = _
    simp [show ofExprSpec e = ofExpr e from rfl, ih]

/-! ## The field invariant -/

/-- The field invariant: the term is exactly what the pure conversion
builds from its own erasure, i.e. every field of every node satisfies
the smart-constructor recurrence.  Everything the checker constructs
is `WFc`: raw constructor applications appear nowhere outside the
smart constructors. -/
def WFc (e : ExprC) : Prop := ofExpr (eraseC e) = e

/-- The conversion of any expression is well-formed. -/
theorem WFc_ofExpr (x : Expr) : WFc (ofExpr x) := by
  show ofExpr (eraseC (ofExpr x)) = ofExpr x
  rw [eraseC_ofExpr]

/-- **Injectivity on the invariant** — the arena's `denote_inj`
without a table: a well-formed node is determined by its erasure. -/
theorem eraseC_inj {a b : ExprC} (ha : WFc a) (hb : WFc b)
    (h : eraseC a = eraseC b) : a = b := by
  rw [← ha, ← hb, h]

/-! ### Closure under the smart constructors -/

protected theorem WFc.mkBVar (i : Nat) : WFc (mkBVar i) := rfl

protected theorem WFc.mkFVar {ty : ExprC} (idx : Nat) (n : Name)
    (hty : WFc ty) : WFc (mkFVar idx n ty) := by
  show ofExpr (eraseC (mkFVar idx n ty)) = _
  rw [eraseC_mkFVar]
  show mkFVar idx n (ofExprSpec (eraseC ty)) = mkFVar idx n ty
  rw [show ofExprSpec (eraseC ty) = ofExpr (eraseC ty) from rfl, hty]

protected theorem WFc.mkSort (u : Level) : WFc (mkSort u) := rfl

protected theorem WFc.mkConst (n : Name) (us : List Level) :
    WFc (mkConst n us) := rfl

protected theorem WFc.mkApp {f a : ExprC} (hf : WFc f) (ha : WFc a) :
    WFc (mkApp f a) := by
  show ofExpr (eraseC (mkApp f a)) = _
  rw [eraseC_mkApp]
  show mkApp (ofExprSpec (eraseC f)) (ofExprSpec (eraseC a)) = mkApp f a
  rw [show ofExprSpec (eraseC f) = ofExpr (eraseC f) from rfl,
    show ofExprSpec (eraseC a) = ofExpr (eraseC a) from rfl, hf, ha]

protected theorem WFc.mkLam {ty b : ExprC} (n : Name) (m : BinderMeta)
    (hty : WFc ty) (hb : WFc b) : WFc (mkLam n ty b m) := by
  show ofExpr (eraseC (mkLam n ty b m)) = _
  rw [eraseC_mkLam]
  show mkLam n (ofExprSpec (eraseC ty)) (ofExprSpec (eraseC b)) m =
    mkLam n ty b m
  rw [show ofExprSpec (eraseC ty) = ofExpr (eraseC ty) from rfl,
    show ofExprSpec (eraseC b) = ofExpr (eraseC b) from rfl, hty, hb]

protected theorem WFc.mkForallE {ty b : ExprC} (n : Name) (m : BinderMeta)
    (hty : WFc ty) (hb : WFc b) : WFc (mkForallE n ty b m) := by
  show ofExpr (eraseC (mkForallE n ty b m)) = _
  rw [eraseC_mkForallE]
  show mkForallE n (ofExprSpec (eraseC ty)) (ofExprSpec (eraseC b)) m =
    mkForallE n ty b m
  rw [show ofExprSpec (eraseC ty) = ofExpr (eraseC ty) from rfl,
    show ofExprSpec (eraseC b) = ofExpr (eraseC b) from rfl, hty, hb]

protected theorem WFc.mkLetE {ty v b : ExprC} (n : Name)
    (hty : WFc ty) (hv : WFc v) (hb : WFc b) : WFc (mkLetE n ty v b) := by
  show ofExpr (eraseC (mkLetE n ty v b)) = _
  rw [eraseC_mkLetE]
  show mkLetE n (ofExprSpec (eraseC ty)) (ofExprSpec (eraseC v))
    (ofExprSpec (eraseC b)) = mkLetE n ty v b
  rw [show ofExprSpec (eraseC ty) = ofExpr (eraseC ty) from rfl,
    show ofExprSpec (eraseC v) = ofExpr (eraseC v) from rfl,
    show ofExprSpec (eraseC b) = ofExpr (eraseC b) from rfl, hty, hv, hb]

protected theorem WFc.mkLit (l : Literal) : WFc (mkLit l) := rfl

protected theorem WFc.mkProj {e : ExprC} (s : Name) (i : Nat)
    (he : WFc e) : WFc (mkProj s i e) := by
  show ofExpr (eraseC (mkProj s i e)) = _
  rw [eraseC_mkProj]
  show mkProj s i (ofExprSpec (eraseC e)) = mkProj s i e
  rw [show ofExprSpec (eraseC e) = ofExpr (eraseC e) from rfl, he]



/-! ### The invariant-carrying constructors (task #171)

Subtype-wrapped smart constructors for the direct-parse tables: the
value is the smart constructor's, the invariant travels in the type,
and the wrapper erases at runtime. -/

/-- An `ExprC` carrying its field invariant. -/
abbrev WExprC := { e : ExprC // WFc e }

@[inline] def mkBVarW (i : Nat) : WExprC := ⟨mkBVar i, WFc.mkBVar i⟩
@[inline] def mkSortW (u : Level) : WExprC := ⟨mkSort u, WFc.mkSort u⟩
@[inline] def mkConstW (n : Name) (us : List Level) : WExprC :=
  ⟨mkConst n us, WFc.mkConst n us⟩
@[inline] def mkAppW (f a : WExprC) : WExprC :=
  ⟨mkApp f.1 a.1, WFc.mkApp f.2 a.2⟩
@[inline] def mkLamW (n : Name) (ty b : WExprC) (m : BinderMeta) : WExprC :=
  ⟨mkLam n ty.1 b.1 m, WFc.mkLam n m ty.2 b.2⟩
@[inline] def mkForallEW (n : Name) (ty b : WExprC) (m : BinderMeta) : WExprC :=
  ⟨mkForallE n ty.1 b.1 m, WFc.mkForallE n m ty.2 b.2⟩
@[inline] def mkLetEW (n : Name) (ty v b : WExprC) : WExprC :=
  ⟨mkLetE n ty.1 v.1 b.1, WFc.mkLetE n ty.2 v.2 b.2⟩
@[inline] def mkLitW (l : Literal) : WExprC := ⟨mkLit l, WFc.mkLit l⟩
@[inline] def mkProjW (s : Name) (i : Nat) (e : WExprC) : WExprC :=
  ⟨mkProj s i e.1, WFc.mkProj s i e.2⟩
@[inline] def ofExprW (x : Expr) : WExprC := ⟨ofExpr x, WFc_ofExpr x⟩

end ExprC

/-! ## The one-level view

`Setlec.ExprView` (defined in `Setlec/Kernel/Core.lean`) is the
representation-generic one-level view the core bodies destructure
through; `ExprC` instantiates it with no allocation on the read side. -/

end Setlec.Cached
