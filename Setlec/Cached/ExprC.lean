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

/-! ## The former `Expr` boundary, and the field invariant

**Both are gone with the type (task #172 B3a).**  `ofExpr`/`toExpr`
converted between the checker's `Expr`-typed declaration layer and the
core's `ExprC`; with one type there is nothing to convert, and every
call site now passes its argument through.  The erasure `eraseC` and
its injectivity lemma likewise: the fields are functions of the node,
so a node *is* its own erasure.

What is left of the tier is the field invariant `WFc`, and it is kept
for one reason, recorded so it is not mistaken for content: the
direct-parse capstone letters (`no_proof_of_Empty_SPCD_R` and its five
siblings, `Setlec/Verify/Cached/MainC.lean`) are stated over
`List WDeclC`, the subtype of declarations whose slots carry it.  A
frozen capstone statement does not move without a ratified-statement
ruling, so `WFc` — now *provably total* (`WFc_all`) — stays as the
subtype's predicate until that ruling.  It is stated without the
erasure: a node is well-formed when rebuilding it from itself is the
identity, which is what field exactness always meant.

`ofExprSpec`/`ofExpr` survive only as `WFc`'s witness-builder; the
rebuild is the identity (`ofExpr_eq_self`). -/

/-- Structural rebuild — every node re-created from its own payload.
The identity (`ofExpr_eq_self`), and `WFc`'s subject. -/
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

@[inherit_doc ofExprSpec]
def ofExpr (e : Expr) : ExprC := ofExprSpec e

/-- The rebuild is the identity. -/
@[simp] theorem ofExpr_eq_self : ∀ x : Expr, ofExpr x = x := by
  intro x
  induction x with
  | bvar i => rfl
  | sort u => rfl
  | const n us => rfl
  | lit l => rfl
  | fvar idx n ty ih =>
    show mkFVar idx n (ofExprSpec ty) = _
    simp [show ofExprSpec ty = ofExpr ty from rfl, ih, mkFVar]
  | app f a ihf iha =>
    show mkApp (ofExprSpec f) (ofExprSpec a) = _
    simp [show ofExprSpec f = ofExpr f from rfl,
      show ofExprSpec a = ofExpr a from rfl, ihf, iha, mkApp]
  | lam n ty b m iht ihb =>
    show mkLam n (ofExprSpec ty) (ofExprSpec b) m = _
    simp [show ofExprSpec ty = ofExpr ty from rfl,
      show ofExprSpec b = ofExpr b from rfl, iht, ihb, mkLam]
  | forallE n ty b m iht ihb =>
    show mkForallE n (ofExprSpec ty) (ofExprSpec b) m = _
    simp [show ofExprSpec ty = ofExpr ty from rfl,
      show ofExprSpec b = ofExpr b from rfl, iht, ihb, mkForallE]
  | letE n ty v b iht ihv ihb =>
    show mkLetE n (ofExprSpec ty) (ofExprSpec v) (ofExprSpec b) = _
    simp [show ofExprSpec ty = ofExpr ty from rfl,
      show ofExprSpec v = ofExpr v from rfl,
      show ofExprSpec b = ofExpr b from rfl, iht, ihv, ihb, mkLetE]
  | proj s i e ih =>
    show mkProj s i (ofExprSpec e) = _
    simp [show ofExprSpec e = ofExpr e from rfl, ih, mkProj]

/-! ### The constructor equations

`mkApp f a = .app f a` and its nine siblings, all `rfl`.  They were
the erasure's "smart constructor erases to the plain constructor"
lemmas (`mkApp_eq` &c.); with one type they are the constructors'
own equations, and the tier still rewrites with them. -/

@[simp] theorem mkBVar_eq (i : Nat) : mkBVar i = .bvar i := rfl

@[simp] theorem mkFVar_eq (idx : Nat) (n : Name) (ty : ExprC) :
    mkFVar idx n ty = .fvar idx n ty := rfl

@[simp] theorem mkSort_eq (u : Level) : mkSort u = .sort u := rfl

@[simp] theorem mkConst_eq (n : Name) (us : List Level) :
    mkConst n us = .const n us := rfl

@[simp] theorem mkApp_eq (f a : ExprC) : mkApp f a = .app f a := rfl

@[simp] theorem mkLam_eq (n : Name) (ty b : ExprC) (m : BinderMeta) :
    mkLam n ty b m = .lam n ty b m := rfl

@[simp] theorem mkForallE_eq (n : Name) (ty b : ExprC) (m : BinderMeta) :
    mkForallE n ty b m = .forallE n ty b m := rfl

@[simp] theorem mkLetE_eq (n : Name) (ty v b : ExprC) :
    mkLetE n ty v b = .letE n ty v b := rfl

@[simp] theorem mkLit_eq (l : Literal) : mkLit l = .lit l := rfl

@[simp] theorem mkProj_eq (s : Name) (i : Nat) (e : ExprC) :
    mkProj s i e = .proj s i e := rfl

/-- The field invariant: rebuilding the node from itself is the
identity.  **Total** (`WFc_all`, `Setlec/Verify/Cached/Erase.lean`) —
see the section note above for why it is still here. -/
def WFc (e : ExprC) : Prop := ofExpr e = e

/-- Every term is well-formed. -/
theorem WFc_all (e : ExprC) : WFc e := ofExpr_eq_self e

@[inherit_doc WFc_all] theorem WFc_ofExpr (x : Expr) : WFc (ofExpr x) :=
  WFc_all _

/-! ### Closure under the constructors (kept with `WFc`) -/

protected theorem WFc.mkBVar (i : Nat) : WFc (mkBVar i) := WFc_all _

protected theorem WFc.mkFVar {ty : ExprC} (idx : Nat) (n : Name)
    (_hty : WFc ty) : WFc (mkFVar idx n ty) := WFc_all _

protected theorem WFc.mkSort (u : Level) : WFc (mkSort u) := WFc_all _

protected theorem WFc.mkConst (n : Name) (us : List Level) :
    WFc (mkConst n us) := WFc_all _

protected theorem WFc.mkApp {f a : ExprC} (_hf : WFc f) (_ha : WFc a) :
    WFc (mkApp f a) := WFc_all _

protected theorem WFc.mkLam {ty b : ExprC} (n : Name) (m : BinderMeta)
    (_hty : WFc ty) (_hb : WFc b) : WFc (mkLam n ty b m) := WFc_all _

protected theorem WFc.mkForallE {ty b : ExprC} (n : Name) (m : BinderMeta)
    (_hty : WFc ty) (_hb : WFc b) : WFc (mkForallE n ty b m) := WFc_all _

protected theorem WFc.mkLetE {ty v b : ExprC} (n : Name)
    (_hty : WFc ty) (_hv : WFc v) (_hb : WFc b) : WFc (mkLetE n ty v b) :=
  WFc_all _

protected theorem WFc.mkLit (l : Literal) : WFc (mkLit l) := WFc_all _

protected theorem WFc.mkProj {e : ExprC} (s : Name) (i : Nat)
    (_he : WFc e) : WFc (mkProj s i e) := WFc_all _

/-! ### The invariant-carrying constructors

Kept with `WFc` and for the same reason (the direct-parse capstone
letters' `WDeclC`); the wrapper erases at runtime. -/

/-- An `ExprC` carrying its (total) field invariant. -/
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
