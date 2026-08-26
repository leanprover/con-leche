import Setlec.TT.Syntax

/-!
# Lifting and instantiation

The two de Bruijn operations the judgment needs: `liftN` (weakening,
used by the `bvar` rule and by η) and `inst` (single substitution, used
by application, β and ζ).

**This module is deliberately tiny.**  lean4lean's corresponding file
is ~800 lines and 123 theorems of substitution boilerplate, roughly a
third of its declarative layer, because its metatheory (Church–Rosser,
unique typing, weakening, inversion) is *syntactic* and every step has
to commute lifts and substitutions past each other.  Here the only
metatheorem is soundness, which goes straight to the model, so the
substitution facts that are actually needed are two *semantic* lemmas
(`interp_liftN`, `interp_inst`, in `Setlec/TT/Semantics/Interp.lean`)
and nothing else.  Everything below is definitions plus their
constructor-wise `rfl` equations.
-/

namespace Setlec.TT
namespace VExpr

/-- Weakening: insert `n` fresh binders at depth `k`. -/
def liftN (n : Nat) : VExpr → (k : Nat := 0) → VExpr
  | .bvar i, k => .bvar (if i < k then i else i + n)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app f a, k => .app (liftN n f k) (liftN n a k)
  | .lam A b, k => .lam (liftN n A k) (liftN n b (k + 1))
  | .pi A B, k => .pi (liftN n A k) (liftN n B (k + 1))
  | .letE T v b, k => .letE (liftN n T k) (liftN n v k) (liftN n b (k + 1))
  | .eqE T a b, k => .eqE (liftN n T k) (liftN n a k) (liftN n b k)
  | .proj i e, k => .proj i (liftN n e k)
  | .prf, _ => .prf

/-- Weakening by one. -/
abbrev lift (e : VExpr) : VExpr := liftN 1 e

/-- Single substitution: replace the variable at depth `k` by `a`,
decrementing the variables above it. -/
def inst : VExpr → VExpr → (k : Nat := 0) → VExpr
  | .bvar i, a, k =>
    if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1)
  | .sort u, _, _ => .sort u
  | .const c us, _, _ => .const c us
  | .app f b, a, k => .app (inst f a k) (inst b a k)
  | .lam A b, a, k => .lam (inst A a k) (inst b a (k + 1))
  | .pi A B, a, k => .pi (inst A a k) (inst B a (k + 1))
  | .letE T v b, a, k => .letE (inst T a k) (inst v a k) (inst b a (k + 1))
  | .eqE T b c, a, k => .eqE (inst T a k) (inst b a k) (inst c a k)
  | .proj i e, a, k => .proj i (inst e a k)
  | .prf, _, _ => .prf

@[simp] theorem liftN_bvar (n k i : Nat) :
    liftN n (.bvar i) k = .bvar (if i < k then i else i + n) := rfl
@[simp] theorem liftN_sort (n k : Nat) (u : Nat) :
    liftN n (.sort u) k = .sort u := rfl
@[simp] theorem liftN_const (n k : Nat) (c : BConst) (us : List Nat) :
    liftN n (.const c us) k = .const c us := rfl
@[simp] theorem liftN_app (n k : Nat) (f a : VExpr) :
    liftN n (.app f a) k = .app (liftN n f k) (liftN n a k) := rfl
@[simp] theorem liftN_lam (n k : Nat) (A b : VExpr) :
    liftN n (.lam A b) k = .lam (liftN n A k) (liftN n b (k + 1)) := rfl
@[simp] theorem liftN_pi (n k : Nat) (A B : VExpr) :
    liftN n (.pi A B) k = .pi (liftN n A k) (liftN n B (k + 1)) := rfl
@[simp] theorem liftN_letE (n k : Nat) (T v b : VExpr) :
    liftN n (.letE T v b) k =
      .letE (liftN n T k) (liftN n v k) (liftN n b (k + 1)) := rfl
@[simp] theorem liftN_eqE (n k : Nat) (T a b : VExpr) :
    liftN n (.eqE T a b) k = .eqE (liftN n T k) (liftN n a k) (liftN n b k) := rfl
@[simp] theorem liftN_proj (n k i : Nat) (e : VExpr) :
    liftN n (.proj i e) k = .proj i (liftN n e k) := rfl
@[simp] theorem liftN_prf (n k : Nat) : liftN n .prf k = .prf := rfl

@[simp] theorem inst_bvar (a : VExpr) (k i : Nat) :
    inst (.bvar i) a k =
      (if i < k then .bvar i else if i = k then liftN k a else .bvar (i - 1)) :=
  rfl
@[simp] theorem inst_sort (a : VExpr) (k : Nat) (u : Nat) :
    inst (.sort u) a k = .sort u := rfl
@[simp] theorem inst_const (a : VExpr) (k : Nat) (c : BConst) (us : List Nat) :
    inst (.const c us) a k = .const c us := rfl
@[simp] theorem inst_app (a : VExpr) (k : Nat) (f b : VExpr) :
    inst (.app f b) a k = .app (inst f a k) (inst b a k) := rfl
@[simp] theorem inst_lam (a : VExpr) (k : Nat) (A b : VExpr) :
    inst (.lam A b) a k = .lam (inst A a k) (inst b a (k + 1)) := rfl
@[simp] theorem inst_pi (a : VExpr) (k : Nat) (A B : VExpr) :
    inst (.pi A B) a k = .pi (inst A a k) (inst B a (k + 1)) := rfl
@[simp] theorem inst_letE (a : VExpr) (k : Nat) (T v b : VExpr) :
    inst (.letE T v b) a k =
      .letE (inst T a k) (inst v a k) (inst b a (k + 1)) := rfl
@[simp] theorem inst_eqE (a : VExpr) (k : Nat) (T b c : VExpr) :
    inst (.eqE T b c) a k = .eqE (inst T a k) (inst b a k) (inst c a k) := rfl
@[simp] theorem inst_proj (a : VExpr) (k i : Nat) (e : VExpr) :
    inst (.proj i e) a k = .proj i (inst e a k) := rfl
@[simp] theorem inst_prf (a : VExpr) (k : Nat) : inst .prf a k = .prf := rfl

end VExpr

/-- Non-dependent function space.  (Outside the `VExpr` namespace so it
can be used without `open VExpr`, which would collide with
`SetTheory.app`.) -/
def arrow (A B : VExpr) : VExpr := .pi A B.lift

end Setlec.TT
