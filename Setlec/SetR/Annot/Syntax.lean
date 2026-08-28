import Setlec.TT.Subst

/-!
# `AVExpr`: the sort-annotated variant of `VExpr` (task #151, tier A)

`VExpr` (`Setlec/TT/Syntax.lean`) carries **no** universe information at
its binders: `pi A B` and `lam A b` are the bare formers, and the
interpretation reads them through the *collapsed* operators `piC`/`lamC`
(`Setlec/TT/Semantics/Interp.lean`), which is what makes the
universe-cohabitation wall of the T5 c5 record (`Setlec/SetR/DESIGN.md`)
unavoidable — `pt ∈ˢ piC A (fun _ => univ 0)` holds, so no *typing* can
separate a proposition's inhabitant from the proof point.

`AVExpr` is the same syntax with the binder formers carrying **ground
numeral sorts**:

| `VExpr` | `AVExpr` | annotation |
|---|---|---|
| `pi A B` | `pi u v A B` | the domain's sort `u` and the body's sort `v` |
| `lam A b` | `lam u A b` | the domain's sort `u` |
| `letE T x b` | `letE T x b` | **none** (decision below) |
| everything else | the same node | none |

**Design rulings this file implements** (task #151's own; recorded in
`Setlec/SetR/DESIGN.md`'s tier-A section):

* **Ground numerals, not `Level`s.**  `VExpr` already evaluates every
  level expression at its use site (`Setlec/TT/Syntax.lean`'s "universe
  levels are concrete `Nat`s"), so an annotation is a `Nat`.  There is
  no level substitution to commute with, which is what makes the whole
  substitution metatheory below *inert*.
* **Annotations are cached premises.**  A slot exists exactly where a
  `SetR` rule's own premises supply the fact (`Setlec/SetR/Rel.lean`
  I6's two `DefEq … (.sort _)` premises, I7's one) and a consumer reads
  it.  Hence:
* **`letE` carries no sort.**  I10 *does* supply one
  (`DefEq μ Δ tT (.sort u)` for the annotation `T`), but no consumer
  reads it: `interp`'s `letE` clause reads neither `T` nor its sort
  (`interp ρ (.letE _ v b) = interp (cons ⟦v⟧ ρ) b`), and a graded
  re-reading of the `let` former has nothing to grade — `let` is not a
  type former.  Caching a premise no consumer reads would be dead
  weight in every `AVExpr` traversal, so the slot is omitted.  (The
  premise is not lost: it is still in the derivation, and
  `Setlec/SetR/Annot/Pass.lean`'s `HasSort` names it.)
* **`eqE` keeps its (unannotated, unread) type slot**, exactly as
  `VExpr` does — see `Setlec/TT/Syntax.lean` on why `eqE`'s type slot is
  never constrained.

## The structural kit

`erase` forgets the annotations; `liftN`/`inst` are the de Bruijn
operations, defined *clause for clause* against
`Setlec/TT/Subst.lean`'s.  Their whole content is the pair of
commutations `erase_liftN` / `erase_inst`: **annotations are inert data
under substitution** — instantiation rewrites subterms and never
touches a numeral — so the annotated operations project onto the plain
ones on the nose.  That is what lets tier B and tier C move an
annotated term through a β/ζ/telescope step without re-deriving any
sort fact.
-/

namespace Setlec.SetR

open Setlec.TT

/-- `VExpr` with ground numeral sorts at the binder formers.  Node for
node the same syntax; see the module docstring for the annotation
table and for why `letE` has no slot. -/
inductive AVExpr where
  /-- de Bruijn index -/
  | bvar (i : Nat)
  /-- `Sort u` at a concrete level -/
  | sort (u : Nat)
  /-- a built-in constant at a concrete level instantiation -/
  | const (c : BConst) (us : List Nat)
  /-- application -/
  | app (f a : AVExpr)
  /-- `fun (_ : ty) => body`, with `ty`'s sort `u` -/
  | lam (u : Nat) (ty body : AVExpr)
  /-- `(_ : ty) → body`, with `ty`'s sort `u` and `body`'s sort `v` -/
  | pi (u v : Nat) (ty body : AVExpr)
  /-- `let _ : ty := value; body` — **no sort slot**, see the module
  docstring -/
  | letE (ty value body : AVExpr)
  /-- `@Eq ty lhs rhs`; the `ty` slot is carried and never read, as in
  `VExpr` -/
  | eqE (ty lhs rhs : AVExpr)
  /-- field `i` of a pair -/
  | proj (i : Nat) (e : AVExpr)
  /-- the canonical (irrelevant) proof of a derivable equation -/
  | prf
  deriving Repr, Inhabited

namespace AVExpr

/-- Forget the annotations. -/
def erase : AVExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c us => .const c us
  | .app f a => .app (erase f) (erase a)
  | .lam _ A b => .lam (erase A) (erase b)
  | .pi _ _ A B => .pi (erase A) (erase B)
  | .letE T v b => .letE (erase T) (erase v) (erase b)
  | .eqE T a b => .eqE (erase T) (erase a) (erase b)
  | .proj i e => .proj i (erase e)
  | .prf => .prf

@[simp] theorem erase_bvar (i : Nat) : erase (.bvar i) = .bvar i := rfl
@[simp] theorem erase_sort (u : Nat) : erase (.sort u) = .sort u := rfl
@[simp] theorem erase_const (c : BConst) (us : List Nat) :
    erase (.const c us) = .const c us := rfl
@[simp] theorem erase_app (f a : AVExpr) :
    erase (.app f a) = .app (erase f) (erase a) := rfl
@[simp] theorem erase_lam (u : Nat) (A b : AVExpr) :
    erase (.lam u A b) = .lam (erase A) (erase b) := rfl
@[simp] theorem erase_pi (u v : Nat) (A B : AVExpr) :
    erase (.pi u v A B) = .pi (erase A) (erase B) := rfl
@[simp] theorem erase_letE (T v b : AVExpr) :
    erase (.letE T v b) = .letE (erase T) (erase v) (erase b) := rfl
@[simp] theorem erase_eqE (T a b : AVExpr) :
    erase (.eqE T a b) = .eqE (erase T) (erase a) (erase b) := rfl
@[simp] theorem erase_proj (i : Nat) (e : AVExpr) :
    erase (.proj i e) = .proj i (erase e) := rfl
@[simp] theorem erase_prf : erase .prf = .prf := rfl

/-- Weakening: insert `n` fresh binders at depth `k`.  Clause for
clause `VExpr.liftN`; the numerals ride along untouched. -/
def liftN (n : Nat) : AVExpr → (k : Nat := 0) → AVExpr
  | .bvar i, k => .bvar (if i < k then i else i + n)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app f a, k => .app (liftN n f k) (liftN n a k)
  | .lam u A b, k => .lam u (liftN n A k) (liftN n b (k + 1))
  | .pi u v A B, k => .pi u v (liftN n A k) (liftN n B (k + 1))
  | .letE T v b, k => .letE (liftN n T k) (liftN n v k) (liftN n b (k + 1))
  | .eqE T a b, k => .eqE (liftN n T k) (liftN n a k) (liftN n b k)
  | .proj i e, k => .proj i (liftN n e k)
  | .prf, _ => .prf

/-- Weakening by one. -/
abbrev lift (e : AVExpr) : AVExpr := liftN 1 e

/-- Single substitution at depth `k`.  Clause for clause
`VExpr.inst`. -/
def inst : AVExpr → AVExpr → (k : Nat := 0) → AVExpr
  | .bvar i, a, k =>
    if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1)
  | .sort u, _, _ => .sort u
  | .const c us, _, _ => .const c us
  | .app f b, a, k => .app (inst f a k) (inst b a k)
  | .lam u A b, a, k => .lam u (inst A a k) (inst b a (k + 1))
  | .pi u v A B, a, k => .pi u v (inst A a k) (inst B a (k + 1))
  | .letE T v b, a, k => .letE (inst T a k) (inst v a k) (inst b a (k + 1))
  | .eqE T b c, a, k => .eqE (inst T a k) (inst b a k) (inst c a k)
  | .proj i e, a, k => .proj i (inst e a k)
  | .prf, _, _ => .prf

/-- Iterated application (`VExpr.mkAppN`'s transpose). -/
def mkAppN (f : AVExpr) : List AVExpr → AVExpr
  | [] => f
  | a :: as => mkAppN (.app f a) as

@[simp] theorem mkAppN_nil (f : AVExpr) : mkAppN f [] = f := rfl
@[simp] theorem mkAppN_cons (f a : AVExpr) (as : List AVExpr) :
    mkAppN f (a :: as) = mkAppN (.app f a) as := rfl

/-! ### Clause equations for the substitution operations -/

@[simp] theorem liftN_bvar (n k i : Nat) :
    liftN n (.bvar i) k = .bvar (if i < k then i else i + n) := rfl
@[simp] theorem liftN_sort (n k u : Nat) : liftN n (.sort u) k = .sort u := rfl
@[simp] theorem liftN_const (n k : Nat) (c : BConst) (us : List Nat) :
    liftN n (.const c us) k = .const c us := rfl
@[simp] theorem liftN_app (n k : Nat) (f a : AVExpr) :
    liftN n (.app f a) k = .app (liftN n f k) (liftN n a k) := rfl
@[simp] theorem liftN_lam (n k u : Nat) (A b : AVExpr) :
    liftN n (.lam u A b) k = .lam u (liftN n A k) (liftN n b (k + 1)) := rfl
@[simp] theorem liftN_pi (n k u v : Nat) (A B : AVExpr) :
    liftN n (.pi u v A B) k = .pi u v (liftN n A k) (liftN n B (k + 1)) := rfl
@[simp] theorem liftN_letE (n k : Nat) (T v b : AVExpr) :
    liftN n (.letE T v b) k =
      .letE (liftN n T k) (liftN n v k) (liftN n b (k + 1)) := rfl
@[simp] theorem liftN_eqE (n k : Nat) (T a b : AVExpr) :
    liftN n (.eqE T a b) k = .eqE (liftN n T k) (liftN n a k) (liftN n b k) := rfl
@[simp] theorem liftN_proj (n k i : Nat) (e : AVExpr) :
    liftN n (.proj i e) k = .proj i (liftN n e k) := rfl
@[simp] theorem liftN_prf (n k : Nat) : liftN n .prf k = .prf := rfl

@[simp] theorem inst_bvar (a : AVExpr) (k i : Nat) :
    inst (.bvar i) a k =
      (if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1)) :=
  rfl
@[simp] theorem inst_sort (a : AVExpr) (k u : Nat) :
    inst (.sort u) a k = .sort u := rfl
@[simp] theorem inst_const (a : AVExpr) (k : Nat) (c : BConst) (us : List Nat) :
    inst (.const c us) a k = .const c us := rfl
@[simp] theorem inst_app (a : AVExpr) (k : Nat) (f b : AVExpr) :
    inst (.app f b) a k = .app (inst f a k) (inst b a k) := rfl
@[simp] theorem inst_lam (a : AVExpr) (k u : Nat) (A b : AVExpr) :
    inst (.lam u A b) a k = .lam u (inst A a k) (inst b a (k + 1)) := rfl
@[simp] theorem inst_pi (a : AVExpr) (k u v : Nat) (A B : AVExpr) :
    inst (.pi u v A B) a k = .pi u v (inst A a k) (inst B a (k + 1)) := rfl
@[simp] theorem inst_letE (a : AVExpr) (k : Nat) (T v b : AVExpr) :
    inst (.letE T v b) a k =
      .letE (inst T a k) (inst v a k) (inst b a (k + 1)) := rfl
@[simp] theorem inst_eqE (a : AVExpr) (k : Nat) (T b c : AVExpr) :
    inst (.eqE T b c) a k = .eqE (inst T a k) (inst b a k) (inst c a k) := rfl
@[simp] theorem inst_proj (a : AVExpr) (k i : Nat) (e : AVExpr) :
    inst (.proj i e) a k = .proj i (inst e a k) := rfl
@[simp] theorem inst_prf (a : AVExpr) (k : Nat) : inst .prf a k = .prf := rfl

/-! ### The erase-commutations

**Annotations are inert data under substitution.**  Both operations
project onto `VExpr`'s on the nose: nothing in `liftN`/`inst` reads or
writes a numeral slot, so `erase` is a homomorphism for them.  These
two equations are the whole point of the structural kit — tier B and
tier C move annotated terms through β, ζ and telescope steps by
rewriting with them, never by re-deriving a sort fact. -/

/-- `erase` commutes with lifting. -/
@[simp] theorem erase_liftN : ∀ (e : AVExpr) (n k : Nat),
    erase (liftN n e k) = VExpr.liftN n (erase e) k := by
  intro e
  induction e with
  | bvar i => intros; rfl
  | sort u => intros; rfl
  | const c us => intros; rfl
  | app f a ihf iha => intro n k; simp only [liftN_app, erase_app, ihf, iha,
      VExpr.liftN_app]
  | lam u A b ihA ihb => intro n k; simp only [liftN_lam, erase_lam, ihA, ihb,
      VExpr.liftN_lam]
  | pi u v A B ihA ihB => intro n k; simp only [liftN_pi, erase_pi, ihA, ihB,
      VExpr.liftN_pi]
  | letE T v b ihT ihv ihb => intro n k; simp only [liftN_letE, erase_letE,
      ihT, ihv, ihb, VExpr.liftN_letE]
  | eqE T a b ihT iha ihb => intro n k; simp only [liftN_eqE, erase_eqE,
      ihT, iha, ihb, VExpr.liftN_eqE]
  | proj i e ih => intro n k; simp only [liftN_proj, erase_proj, ih,
      VExpr.liftN_proj]
  | prf => intros; rfl

/-- `erase` commutes with instantiation. -/
@[simp] theorem erase_inst : ∀ (e a : AVExpr) (k : Nat),
    erase (inst e a k) = VExpr.inst (erase e) (erase a) k := by
  intro e
  induction e with
  | bvar i =>
    intro a k
    simp only [inst_bvar, VExpr.inst_bvar, erase_bvar]
    split
    · rfl
    · split
      · exact erase_liftN a k 0
      · rfl
  | sort u => intros; rfl
  | const c us => intros; rfl
  | app f b ihf ihb => intro a k; simp only [inst_app, erase_app, ihf, ihb,
      VExpr.inst_app]
  | lam u A b ihA ihb => intro a k; simp only [inst_lam, erase_lam, ihA, ihb,
      VExpr.inst_lam]
  | pi u v A B ihA ihB => intro a k; simp only [inst_pi, erase_pi, ihA, ihB,
      VExpr.inst_pi]
  | letE T v b ihT ihv ihb => intro a k; simp only [inst_letE, erase_letE,
      ihT, ihv, ihb, VExpr.inst_letE]
  | eqE T b c ihT ihb ihc => intro a k; simp only [inst_eqE, erase_eqE,
      ihT, ihb, ihc, VExpr.inst_eqE]
  | proj i e ih => intro a k; simp only [inst_proj, erase_proj, ih,
      VExpr.inst_proj]
  | prf => intros; rfl

/-- `erase` commutes with application spines. -/
theorem erase_mkAppN : ∀ (as : List AVExpr) (f : AVExpr),
    erase (mkAppN f as) = VExpr.mkAppN (erase f) (as.map erase) := by
  intro as
  induction as with
  | nil => intro f; rfl
  | cons a as ih => intro f; simpa using ih (.app f a)

end AVExpr

end Setlec.SetR
