import Setlec.SetR.Annot.Syntax
import Setlec.SetR.Interp2.Value

/-!
# `interp2` — the collapse-free two-regime interpretation (task #151, tier B)

`interp2 V ρ e` maps an annotated term to an element of the
set-theoretic universe `V` under a variable environment `ρ : Nat → V`.

Three properties, each a design constraint rather than an observation:

* **Total.**  A plain function on terms — never derivation-indexed, so
  coherence is not a theorem to prove but the absence of a question.
* **Environment-free.**  No global environment, no `Option`, no
  auxiliary truthfulness predicate: `interp2` is a function of the term
  and the valuation alone.
* **Term-directed, and the regime is read off the annotation.**  The
  binder cases dispatch on the binder's codomain-sort *numeral*
  (`Interp2/Ops.lean`), never on the semantic value.  That inspection —
  "is this value everywhere the proof point over its domain?" — *is*
  the domain-relative collapse (task #100), and it is what this layer
  removes.  Its cost was the countermodel recorded in
  `Setlec/SetR/DESIGN.md`: empty-domain abstractions collapse at every
  level, so `⟦fun (x : ∀ p : Prop, p) => Prop⟧ = pt` and guarded beta
  produces `app pt univZero = pt ≠ univZero`.  Here
  `⟦fun (x : A) => e⟧` with a `Type`-sorted body is a graph over `⟦A⟧`
  whatever `⟦A⟧` is, empty included (`lamR_pos_empty`).

The clauses in one line each:

| term | value | regime |
|---|---|---|
| `bvar i` | `ρ i` | — |
| `sort u` | `univ u` | — |
| `const c us` | `bval2 c us` | annotation-free (the tower's own) |
| `app f a` | `app ⟦f⟧ ⟦a⟧` | uniform: graph application above `0`, `app pt _ = pt` at `0` |
| `lam v A b` | `lamR v ⟦A⟧ (fun x => ⟦b⟧ₓ)` | annotation |
| `pi u v A B` | `piR v ⟦A⟧ (fun x => ⟦B⟧ₓ)` | annotation |
| `letE _ e b` | `⟦b⟧` at `x := ⟦e⟧` | ζ; annotation-free |
| `eqE _ a b` | `eqv ⟦a⟧ ⟦b⟧` | truth value |
| `proj i e` | `sfst`/`ssnd` | — |
| `prf` | `pt` | the canonical proof |

`app` is *uniform*: it needs no annotation, because
`SetTheory.app`'s proof-point tag (`app pt a = pt`) is precisely the
squash regime's β, and its graph clause (`app_graph`) is precisely the
graph regime's.  So the whole two-regime dispatch lives in the two
binder cases and nowhere else.

`letE` is interpreted by ζ — substituting the value — which needs no
annotation.  Tier A's `letE` annotation decision therefore does not
change this clause; if tier A lands a `letE` whose type slot is
semantically load-bearing, the clause to revisit is this one and only
this one.
-/

namespace Setlec.SetR.Interp2

open SetTheory

universe w

/-! ## Variable environments

Pure `Nat → V` plumbing; no set theory is involved, so this section
carries no `SetTheory` instance.  These are `Setlec.TT.Semantics`'
`cons`/`shiftE`/`instE` with `V` implicit; they are duplicated rather
than imported so that `Interp2/*` depends on **no** module built over
the collapse operators. -/

section Env

variable {V : Type w}

/-- Extend an environment with a new innermost binding. -/
def cons (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

@[simp] theorem cons_zero (x : V) (ρ : Nat → V) : cons x ρ 0 = x := rfl
@[simp] theorem cons_succ (x : V) (ρ : Nat → V) (i : Nat) :
    cons x ρ (i + 1) = ρ i := rfl

/-- The environment transformation matching `AVExpr.liftN n · k`. -/
def shiftE (n k : Nat) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else ρ (i + n)

/-- The environment transformation matching `AVExpr.inst · a k`. -/
def instE (k : Nat) (x : V) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else if i = k then x else ρ (i - 1)

theorem shiftE_zero (n : Nat) (ρ : Nat → V) :
    shiftE n 0 ρ = fun i => ρ (i + n) := by
  funext i; simp [shiftE]

theorem shiftE_zero_zero (ρ : Nat → V) : shiftE 0 0 ρ = ρ := by
  funext i; simp [shiftE]

theorem instE_zero (x : V) (ρ : Nat → V) : instE 0 x ρ = cons x ρ := by
  funext i; cases i <;> simp [instE, cons]

theorem cons_shiftE (x : V) (n k : Nat) (ρ : Nat → V) :
    cons x (shiftE n k ρ) = shiftE n (k + 1) (cons x ρ) := by
  funext i
  cases i with
  | zero => simp [shiftE]
  | succ j =>
    show shiftE n k ρ j = shiftE n (k + 1) (cons x ρ) (j + 1)
    simp only [shiftE]
    by_cases h : j < k
    · rw [if_pos h, if_pos (show j + 1 < k + 1 by omega)]; rfl
    · rw [if_neg h, if_neg (show ¬ (j + 1 < k + 1) by omega)]
      show ρ (j + n) = cons x ρ (j + 1 + n)
      rw [show j + 1 + n = (j + n) + 1 by omega]; rfl

theorem cons_instE (x : V) (k : Nat) (y : V) (ρ : Nat → V) :
    cons x (instE k y ρ) = instE (k + 1) y (cons x ρ) := by
  funext i
  cases i with
  | zero => simp [instE]
  | succ j =>
    show instE k y ρ j = instE (k + 1) y (cons x ρ) (j + 1)
    simp only [instE]
    by_cases h : j < k
    · rw [if_pos h, if_pos (show j + 1 < k + 1 by omega)]; rfl
    · rw [if_neg h, if_neg (show ¬ (j + 1 < k + 1) by omega)]
      by_cases h2 : j = k
      · rw [if_pos h2, if_pos (show j + 1 = k + 1 by omega)]
      · rw [if_neg h2, if_neg (show ¬ (j + 1 = k + 1) by omega)]
        show ρ (j - 1) = cons x ρ (j + 1 - 1)
        rw [show j + 1 - 1 = (j - 1) + 1 by omega]; rfl

theorem shiftE_succ_cons (x : V) (k : Nat) (ρ : Nat → V) :
    shiftE (k + 1) 0 (cons x ρ) = shiftE k 0 ρ := by
  rw [shiftE_zero, shiftE_zero]
  funext i
  show cons x ρ (i + (k + 1)) = ρ (i + k)
  rw [show i + (k + 1) = (i + k) + 1 by omega]; rfl

end Env

variable (V : Type w) [SetTheory V]

/-! ## The interpretation -/

/-- The two-regime interpretation: total, term-directed, environment-free.
Binders read their annotation; nothing reads a value. -/
noncomputable def interp2 : (Nat → V) → AVExpr → V
  | ρ, .bvar i => ρ i
  | _, .sort u => univ u
  | _, .const c us => bval2 V c us
  | ρ, .app f a => SetTheory.app (interp2 ρ f) (interp2 ρ a)
  | ρ, .lam v A b => lamR v (interp2 ρ A) fun x => interp2 (cons x ρ) b
  | ρ, .pi _ v A B => piR v (interp2 ρ A) fun x => interp2 (cons x ρ) B
  | ρ, .letE _ e b => interp2 (cons (interp2 ρ e) ρ) b
  | ρ, .eqE _ a b => eqv (interp2 ρ a) (interp2 ρ b)
  | ρ, .proj i e => if i = 0 then sfst (interp2 ρ e) else ssnd (interp2 ρ e)
  | _, .prf => pt

@[simp] theorem interp2_bvar (ρ : Nat → V) (i : Nat) :
    interp2 V ρ (.bvar i) = ρ i := rfl
@[simp] theorem interp2_sort (ρ : Nat → V) (u : Nat) :
    interp2 V ρ (.sort u) = univ u := rfl
@[simp] theorem interp2_const (ρ : Nat → V) (c : Setlec.TT.BConst)
    (us : List Nat) : interp2 V ρ (.const c us) = bval2 V c us := rfl
@[simp] theorem interp2_app (ρ : Nat → V) (f a : AVExpr) :
    interp2 V ρ (.app f a) = SetTheory.app (interp2 V ρ f) (interp2 V ρ a) := rfl
@[simp] theorem interp2_lam (ρ : Nat → V) (v : Nat) (A b : AVExpr) :
    interp2 V ρ (.lam v A b) =
      lamR v (interp2 V ρ A) fun x => interp2 V (cons x ρ) b := rfl
@[simp] theorem interp2_pi (ρ : Nat → V) (u v : Nat) (A B : AVExpr) :
    interp2 V ρ (.pi u v A B) =
      piR v (interp2 V ρ A) fun x => interp2 V (cons x ρ) B := rfl
@[simp] theorem interp2_letE (ρ : Nat → V) (T e b : AVExpr) :
    interp2 V ρ (.letE T e b) = interp2 V (cons (interp2 V ρ e) ρ) b := rfl
@[simp] theorem interp2_eqE (ρ : Nat → V) (T a b : AVExpr) :
    interp2 V ρ (.eqE T a b) = eqv (interp2 V ρ a) (interp2 V ρ b) := rfl
@[simp] theorem interp2_proj (ρ : Nat → V) (i : Nat) (e : AVExpr) :
    interp2 V ρ (.proj i e) =
      (if i = 0 then sfst (interp2 V ρ e) else ssnd (interp2 V ρ e)) := rfl
@[simp] theorem interp2_prf (ρ : Nat → V) : interp2 V ρ .prf = pt := rfl

end Setlec.SetR.Interp2
