/-!
# `AVExpr` — annotated terms (**provisional**, tier B's local copy)

The two-regime interpretation is *term-directed*: every binder carries
the numeral its regime is chosen by, so the interpretation never has to
inspect a semantic value (that inspection is the domain-relative
collapse this campaign removes).  The annotated syntax carrying those
numerals is **tier A's** deliverable, `Setlec/SetR/Annot/Syntax.lean`.

This module is the agreed stand-in: a provisional `AVExpr` in tier B's
own namespace, so that `Interp2/*` can be written, built and verified
before tier A lands.  **When `Annot/Syntax.lean` lands, delete this file
and re-point `Interp2/Interp.lean`'s import**; the swap is recorded in
`Setlec/SetR/DESIGN.md`, tier B.

Relative to `Setlec.TT.VExpr` (`Setlec/TT/Syntax.lean`), which it
otherwise mirrors constructor for constructor:

* **`lam` carries `v`**, the sort of the body's type — the abstraction
  is squashed exactly when `v = 0`;
* **`pi` carries `u` and `v`**, the sorts of domain and codomain — the
  product is a truth value exactly when `v = 0`, and `u` is what the
  universe-placement law reads (`Interp2/Univ.lean`);
* **there is no `const`**.  The built-in constants' values
  (`Setlec.TT.bval`) are `lamC` towers, i.e. collapse-built; rebuilding
  them as `lamR` towers is the named tier-B follow-up (see DESIGN), and
  nothing in the interpretation, the lemma kit or the universe
  assessment depends on them.  Adding the case is a one-line extension
  of `interp2`.

`liftN`/`inst` are `Setlec.TT.VExpr`'s, with the annotations carried
through untouched — they are numerals, not terms.
-/

namespace Setlec.SetR.Interp2

/-- Annotated terms: `Setlec.TT.VExpr` with a binder-sort numeral on
each binder (see the module docstring; **provisional**). -/
inductive AVExpr where
  /-- de Bruijn index -/
  | bvar (i : Nat)
  /-- `Sort u` at a concrete level -/
  | sort (u : Nat)
  /-- application -/
  | app (f a : AVExpr)
  /-- `fun (_ : ty) => body`, where `body`'s type has sort `v` -/
  | lam (v : Nat) (ty body : AVExpr)
  /-- `(_ : ty) → body`, where `ty` has sort `u` and `body` sort `v` -/
  | pi (u v : Nat) (ty body : AVExpr)
  /-- `let _ : ty := value; body` -/
  | letE (ty value body : AVExpr)
  /-- `@Eq ty lhs rhs`; `ty` is never read -/
  | eqE (ty lhs rhs : AVExpr)
  /-- field `i` of a pair -/
  | proj (i : Nat) (e : AVExpr)
  /-- the canonical (irrelevant) proof -/
  | prf
  deriving Repr, Inhabited

namespace AVExpr

/-- Iterated application. -/
def mkAppN (f : AVExpr) : List AVExpr → AVExpr
  | [] => f
  | a :: as => mkAppN (.app f a) as

@[simp] theorem mkAppN_nil (f : AVExpr) : mkAppN f [] = f := rfl
@[simp] theorem mkAppN_cons (f a : AVExpr) (as : List AVExpr) :
    mkAppN f (a :: as) = mkAppN (.app f a) as := rfl

/-- Weakening: insert `n` fresh binders at depth `k`. -/
def liftN (n : Nat) : AVExpr → (k : Nat := 0) → AVExpr
  | .bvar i, k => .bvar (if i < k then i else i + n)
  | .sort u, _ => .sort u
  | .app f a, k => .app (liftN n f k) (liftN n a k)
  | .lam v A b, k => .lam v (liftN n A k) (liftN n b (k + 1))
  | .pi u v A B, k => .pi u v (liftN n A k) (liftN n B (k + 1))
  | .letE T e b, k => .letE (liftN n T k) (liftN n e k) (liftN n b (k + 1))
  | .eqE T a b, k => .eqE (liftN n T k) (liftN n a k) (liftN n b k)
  | .proj i e, k => .proj i (liftN n e k)
  | .prf, _ => .prf

/-- Weakening by one. -/
abbrev lift (e : AVExpr) : AVExpr := liftN 1 e

/-- Single substitution: replace the variable at depth `k` by `a`,
decrementing the variables above it. -/
def inst : AVExpr → AVExpr → (k : Nat := 0) → AVExpr
  | .bvar i, a, k =>
    if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1)
  | .sort u, _, _ => .sort u
  | .app f b, a, k => .app (inst f a k) (inst b a k)
  | .lam v A b, a, k => .lam v (inst A a k) (inst b a (k + 1))
  | .pi u v A B, a, k => .pi u v (inst A a k) (inst B a (k + 1))
  | .letE T e b, a, k => .letE (inst T a k) (inst e a k) (inst b a (k + 1))
  | .eqE T b c, a, k => .eqE (inst T a k) (inst b a k) (inst c a k)
  | .proj i e, a, k => .proj i (inst e a k)
  | .prf, _, _ => .prf

@[simp] theorem liftN_bvar (n k i : Nat) :
    liftN n (.bvar i) k = .bvar (if i < k then i else i + n) := rfl
@[simp] theorem liftN_sort (n k u : Nat) : liftN n (.sort u) k = .sort u := rfl
@[simp] theorem liftN_app (n k : Nat) (f a : AVExpr) :
    liftN n (.app f a) k = .app (liftN n f k) (liftN n a k) := rfl
@[simp] theorem liftN_lam (n k v : Nat) (A b : AVExpr) :
    liftN n (.lam v A b) k = .lam v (liftN n A k) (liftN n b (k + 1)) := rfl
@[simp] theorem liftN_pi (n k u v : Nat) (A B : AVExpr) :
    liftN n (.pi u v A B) k = .pi u v (liftN n A k) (liftN n B (k + 1)) := rfl
@[simp] theorem liftN_letE (n k : Nat) (T e b : AVExpr) :
    liftN n (.letE T e b) k =
      .letE (liftN n T k) (liftN n e k) (liftN n b (k + 1)) := rfl
@[simp] theorem liftN_eqE (n k : Nat) (T a b : AVExpr) :
    liftN n (.eqE T a b) k = .eqE (liftN n T k) (liftN n a k) (liftN n b k) := rfl
@[simp] theorem liftN_proj (n k i : Nat) (e : AVExpr) :
    liftN n (.proj i e) k = .proj i (liftN n e k) := rfl
@[simp] theorem liftN_prf (n k : Nat) : liftN n .prf k = .prf := rfl

@[simp] theorem inst_sort (a : AVExpr) (k u : Nat) :
    inst (.sort u) a k = .sort u := rfl
@[simp] theorem inst_app (a : AVExpr) (k : Nat) (f b : AVExpr) :
    inst (.app f b) a k = .app (inst f a k) (inst b a k) := rfl
@[simp] theorem inst_lam (a : AVExpr) (k v : Nat) (A b : AVExpr) :
    inst (.lam v A b) a k = .lam v (inst A a k) (inst b a (k + 1)) := rfl
@[simp] theorem inst_pi (a : AVExpr) (k u v : Nat) (A B : AVExpr) :
    inst (.pi u v A B) a k = .pi u v (inst A a k) (inst B a (k + 1)) := rfl
@[simp] theorem inst_letE (a : AVExpr) (k : Nat) (T e b : AVExpr) :
    inst (.letE T e b) a k =
      .letE (inst T a k) (inst e a k) (inst b a (k + 1)) := rfl
@[simp] theorem inst_eqE (a : AVExpr) (k : Nat) (T b c : AVExpr) :
    inst (.eqE T b c) a k = .eqE (inst T a k) (inst b a k) (inst c a k) := rfl
@[simp] theorem inst_proj (a : AVExpr) (k i : Nat) (e : AVExpr) :
    inst (.proj i e) a k = .proj i (inst e a k) := rfl
@[simp] theorem inst_prf (a : AVExpr) (k : Nat) : inst .prf a k = .prf := rfl

end AVExpr

end Setlec.SetR.Interp2
