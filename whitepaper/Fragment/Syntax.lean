module

public import Fragment.PropWhen

@[expose] public section

/-!
# Terms

The fragment's terms are Lean's kernel terms without `let`, literals,
projections and metadata, with **de Bruijn indices** for bound
variables (the paper writes named variables; the real checker opens a
binder with a free variable carrying its own type, `fvar`, and keeps no
context — a performance device the fragment does not need).

Every binder carries, besides its domain, the annotation datum
`pw : PropWhen` (`PropWhen.lean`): when its body is a proposition.
The interpretation reads it (`Interp.lean`); inference checks it
(`Rules.lean`); the reduction and equality rules carry it along and
compare it.

Mirrors `ConLeche.Expr` (`ConLeche/Kernel/Expr.lean`) restricted to
the fragment, and the annotated `AnnotTerm` of
`ConLeche/Semantics/Syntax.lean`, whose lifting/instantiation this
file copies.
-/

namespace Fragment

/-- Annotated terms. -/
inductive Expr where
  /-- A bound variable, by de Bruijn index. -/
  | bvar (i : Nat)
  /-- The sort `Sort l`. -/
  | sort (l : Level)
  /-- A constant of the environment at a level instantiation. -/
  | const (c : Name) (ls : List Level)
  /-- Application. -/
  | app (f a : Expr)
  /-- Abstraction `fun (x : A) => b`, annotated with when `b` is a
  proposition. -/
  | lam (A : Expr) (pw : PropWhen) (b : Expr)
  /-- The dependent product `(x : A) → B`, annotated with when `B` is a
  proposition. -/
  | pi (A : Expr) (pw : PropWhen) (B : Expr)
  deriving DecidableEq

namespace Expr

/-! ## Lifting and instantiation -/

/-- Lift the free indices `≥ k` by `n` (the term is moved under `n`
more binders). -/
def liftN (n : Nat) : Expr → (k : Nat := 0) → Expr
  | bvar i, k => bvar (if i < k then i else i + n)
  | sort u, _ => sort u
  | const c ls, _ => const c ls
  | app f a, k => app (liftN n f k) (liftN n a k)
  | lam A pw b, k => lam (liftN n A k) pw (liftN n b (k + 1))
  | pi A pw B, k => pi (liftN n A k) pw (liftN n B (k + 1))

/-- Instantiate the bound variable `k` by `a` (and lower the indices
above it): `e.inst a` is `e[x := a]` for the innermost binder. -/
def inst : Expr → Expr → (k : Nat := 0) → Expr
  | bvar i, a, k =>
    if i < k then bvar i else if i = k then liftN k a else bvar (i - 1)
  | sort u, _, _ => sort u
  | const c ls, _, _ => const c ls
  | app f b, a, k => app (inst f a k) (inst b a k)
  | lam A pw b, a, k => lam (inst A a k) pw (inst b a (k + 1))
  | pi A pw B, a, k => pi (inst A a k) pw (inst B a (k + 1))

@[simp] theorem liftN_bvar (n k i : Nat) :
    liftN n (bvar i) k = bvar (if i < k then i else i + n) := rfl
@[simp] theorem liftN_sort (n k : Nat) (u : Level) : liftN n (sort u) k = sort u := rfl
@[simp] theorem liftN_const (n k : Nat) (c : Name) (ls : List Level) :
    liftN n (const c ls) k = const c ls := rfl
@[simp] theorem liftN_app (n k : Nat) (f a : Expr) :
    liftN n (app f a) k = app (liftN n f k) (liftN n a k) := rfl
@[simp] theorem liftN_lam (n k : Nat) (A : Expr) (pw : PropWhen) (b : Expr) :
    liftN n (lam A pw b) k = lam (liftN n A k) pw (liftN n b (k + 1)) := rfl
@[simp] theorem liftN_pi (n k : Nat) (A : Expr) (pw : PropWhen) (B : Expr) :
    liftN n (pi A pw B) k = pi (liftN n A k) pw (liftN n B (k + 1)) := rfl

@[simp] theorem inst_bvar (a : Expr) (k i : Nat) :
    inst (bvar i) a k =
      if i < k then bvar i else if i = k then liftN k a else bvar (i - 1) := rfl
@[simp] theorem inst_sort (a : Expr) (k : Nat) (u : Level) : inst (sort u) a k = sort u := rfl
@[simp] theorem inst_const (a : Expr) (k : Nat) (c : Name) (ls : List Level) :
    inst (const c ls) a k = const c ls := rfl
@[simp] theorem inst_app (a : Expr) (k : Nat) (f b : Expr) :
    inst (app f b) a k = app (inst f a k) (inst b a k) := rfl
@[simp] theorem inst_lam (a : Expr) (k : Nat) (A : Expr) (pw : PropWhen) (b : Expr) :
    inst (lam A pw b) a k = lam (inst A a k) pw (inst b a (k + 1)) := rfl
@[simp] theorem inst_pi (a : Expr) (k : Nat) (A : Expr) (pw : PropWhen) (B : Expr) :
    inst (pi A pw B) a k = pi (inst A a k) pw (inst B a (k + 1)) := rfl

/-! ## Level instantiation

A constant's declared type (and value, and recursor rules) is stated
over its level parameters; a use `const c ls` instantiates them at
`ls`.  The annotations are instantiated too, by `PropWhen.substL`. -/

/-- Instantiate the level parameters `ps` at the levels `ls`, in
sorts, constants and annotations. -/
def instL (ps : List Name) (ls : List Level) : Expr → Expr
  | bvar i => bvar i
  | sort u => sort (u.subst ps ls)
  | const c us => const c (us.map (Level.subst ps ls))
  | app f a => app (instL ps ls f) (instL ps ls a)
  | lam A pw b => lam (instL ps ls A) (pw.substL ps ls) (instL ps ls b)
  | pi A pw B => pi (instL ps ls A) (pw.substL ps ls) (instL ps ls B)

@[simp] theorem instL_bvar (ps : List Name) (ls : List Level) (i : Nat) :
    instL ps ls (bvar i) = bvar i := rfl
@[simp] theorem instL_sort (ps : List Name) (ls : List Level) (u : Level) :
    instL ps ls (sort u) = sort (u.subst ps ls) := rfl
@[simp] theorem instL_const (ps : List Name) (ls : List Level) (c : Name) (us : List Level) :
    instL ps ls (const c us) = const c (us.map (Level.subst ps ls)) := rfl
@[simp] theorem instL_app (ps : List Name) (ls : List Level) (f a : Expr) :
    instL ps ls (app f a) = app (instL ps ls f) (instL ps ls a) := rfl
@[simp] theorem instL_lam (ps : List Name) (ls : List Level) (A : Expr) (pw : PropWhen)
    (b : Expr) :
    instL ps ls (lam A pw b) = lam (instL ps ls A) (pw.substL ps ls) (instL ps ls b) := rfl
@[simp] theorem instL_pi (ps : List Name) (ls : List Level) (A : Expr) (pw : PropWhen)
    (B : Expr) :
    instL ps ls (pi A pw B) = pi (instL ps ls A) (pw.substL ps ls) (instL ps ls B) := rfl

/-! ## Spines and telescopes -/

/-- `f a₁ … aₙ`. -/
def mkAppN (f : Expr) (args : List Expr) : Expr := args.foldl app f

@[simp] theorem mkAppN_nil (f : Expr) : mkAppN f [] = f := rfl
@[simp] theorem mkAppN_cons (f a : Expr) (args : List Expr) :
    mkAppN f (a :: args) = mkAppN (app f a) args := rfl

theorem mkAppN_append (f : Expr) (as bs : List Expr) :
    mkAppN f (as ++ bs) = mkAppN (mkAppN f as) bs := by
  simp [mkAppN, List.foldl_append]

/-- Walk a syntactic `Π`-telescope along a list of arguments and
collect the binder domains each argument meets, each instantiated with
the arguments before it: `piDomains ((x : A) → B) (a :: as)` is
`A :: piDomains (B[x := a]) as`.  `none` when the telescope is too
short — the type must be a `Π` *syntactically* at every step, which is
what a stored recursor's or constructor's type is. -/
def piDomains : Expr → List Expr → Option (List Expr)
  | _, [] => some []
  | pi A _ B, a :: as => (piDomains (B.inst a) as).map (A :: ·)
  | _, _ :: _ => none

/-- The **residual** of walking a syntactic `Π`-telescope along a list
of arguments: what is left of the type once every argument has met
its binder and been substituted in — for a constructor's type walked
along a constructor application, the family at the application's
parameters and index expressions.  `none` when the telescope is too
short. -/
def piResidual : Expr → List Expr → Option Expr
  | T, [] => some T
  | pi _ _ B, a :: as => piResidual (B.inst a) as
  | _, _ :: _ => none

@[simp] theorem piResidual_nil (T : Expr) : piResidual T [] = some T := rfl
@[simp] theorem piResidual_pi_cons (A : Expr) (pw : PropWhen) (B a : Expr) (as : List Expr) :
    piResidual (pi A pw B) (a :: as) = piResidual (B.inst a) as := rfl

theorem length_of_piDomains : ∀ {T : Expr} {args doms : List Expr},
    piDomains T args = some doms → doms.length = args.length
  | _, [], _, h => by simp [piDomains] at h; subst h; rfl
  | pi _ _ B, a :: as, _, h => by
    simp only [piDomains, Option.map_eq_some_iff] at h
    obtain ⟨ds, hds, rfl⟩ := h
    simp [length_of_piDomains hds]
  | bvar _, _ :: _, _, h => by simp [piDomains] at h
  | sort _, _ :: _, _, h => by simp [piDomains] at h
  | const _ _, _ :: _, _, h => by simp [piDomains] at h
  | app _ _, _ :: _, _, h => by simp [piDomains] at h
  | lam _ _ _, _ :: _, _, h => by simp [piDomains] at h

end Expr

end Fragment
