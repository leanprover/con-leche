import Setlec.Kernel.Env
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Level
import Setlec.Kernel.Basis.Names

/-!
# `sortSpec` — the reduction-free structural sort function

`sortSpec` answers *"`e : Sort u`, what is `u`?"* by walking the term
and the **declared** types it points at.  It never calls `whnf` or
`inferTypeCore`, is not fuel-indexed, and is a plain structural
recursion on `Expr`.

## The four functions

* `levelOf T` — `T` *is* a universe: read its level.  Syntactic
  `.sort` only; anything else is `none` (reading a level through a
  definitional unfolding would be δ, which is banned).
* `piCod T n` — the sort of `x a₁ … aₙ` for `x : T`: strip `n`
  `forallE` binders off `T` and `levelOf` what is left.  This is the
  brief's **declared-codomain walker**.  It takes **no context and no
  environment**: the only thing it ever reads out is a `Level` sitting
  inside a syntactic `.sort` node, and `Level`s contain no expression
  `bvar`s.  That is why the sort-context below needs no de Bruijn
  shifting anywhere.
* `ctxCod Γ i n` — `piCod` of the `i`-th sort-context entry.
* `sortApp σ Γ e n` — the sort of `e a₁ … aₙ`.  `sortSpec σ Γ e` is
  `sortApp σ Γ e 0`.

## Argument-blindness

No clause ever inspects an argument: `.app` throws the argument away
and only bumps the counter, `.lam` and `.letE` push the *binder type*
(resp. drop the let-value) rather than substituting.  Seal 0's (P3) is
therefore true **by construction** — see `SortSpec/DESIGN.md` seal 1
for what that costs at the ι clause.

## The constant oracle `σ`

The `.const` clause is not `env`-recursive.  It calls an abstract
oracle `σ : SortEnv`, and the canonical instantiation `constCod env`
performs *exactly one* declared-type read (`inferBody`'s own `.const`
clause — level-arity guard included) followed by `piCod`.

## Literals have no clause

A literal is never a type: `3 : Nat` and `Nat` is not a universe, so
`sortSpec (.lit _) = none`.  (Seal 1 shipped a `.lit` clause that
returned the sort of the literal's *type name* — the sort of `Nat`,
not of `3`.  Seal 2's agreement work caught it; see DESIGN seal 2.)

## The constant oracle `σ`, continued

Chaining declared-type reads — needed when a declared type's residual
is itself a constant (`def A : Alias`) — has no termination measure:
`EnvWF` is `∀ c ∈ env.consts, ConstWF env c`, which resolves every
constant against the *whole* environment and so admits `def A : B`
together with `def B : A`.  A δ-chaining `sortSpec` would need an
env-*order* invariant that this campaign's `EnvWF` does not carry, so
the pilot stops at one read and answers `none` beyond it.  See seal 1.
-/

namespace Setlec.SetR.SortSpec

open Setlec (Env Expr Level Name)

/-- The constant oracle: for `c.{us}` applied to `n` arguments, the
sort of the application.  Abstracted so that `sortApp` is *environment
free* — seal 0's (P1) bare-`Env` escape cannot be triggered by a
statement that never quantifies over an `Env`. -/
abbrev SortEnv := Name → List Level → Nat → Option Level

/-- `T` is a universe: its level.  No δ, so `.sort` only. -/
def levelOf : Expr → Option Level
  | .sort u => some u
  | _ => none

/-- The declared-codomain walker: strip `n` `forallE` binders off the
type `T` and read the residual as a universe. -/
def piCod : Expr → Nat → Option Level
  | .forallE _ _ b _, n + 1 => piCod b n
  | t, 0 => levelOf t
  | _, _ + 1 => none

/-- `piCod` of the `i`-th sort-context entry.  No shifting: `piCod`
ignores the context it is read in. -/
def ctxCod : List Expr → Nat → Nat → Option Level
  | [], _, _ => none
  | t :: _, 0, n => piCod t n
  | _ :: g, i + 1, n => ctxCod g i n

/-- The sort of `e a₁ … aₙ` in sort-context `Γ` (head of the list =
innermost binder; entries are the binders' **type expressions**). -/
def sortApp (σ : SortEnv) : List Expr → Expr → Nat → Option Level
  | g, .app f _, n => sortApp σ g f (n + 1)
  | _, .sort u, 0 => some (.succ u)
  | g, .forallE _ a b _, 0 =>
    match sortApp σ g a 0, sortApp σ (a :: g) b 0 with
    | some u, some v => some (.imax u v)
    | _, _ => none
  | g, .lam _ a b _, n + 1 => sortApp σ (a :: g) b n
  | g, .letE _ a _ b, n => sortApp σ (a :: g) b n
  | g, .bvar i, n => ctxCod g i n
  | _, .fvar _ _ t, n => piCod t n
  | _, .const c us, n => σ c us n
  | _, _, _ => none

/-- The sort of `e` itself. -/
def sortSpec (σ : SortEnv) (g : List Expr) (e : Expr) : Option Level :=
  sortApp σ g e 0

/-! ## The canonical oracle -/

/-- One declared-type read, `inferBody`'s `.const` clause verbatim
(`Kernel/Core.lean`: `find?`, the level-arity guard, then
`instantiateLevelParams`), followed by the codomain walk. -/
def constCod (env : Env) : SortEnv := fun c us n =>
  match env.find? c with
  | some ci =>
    if us.length = ci.toConstantVal.levelParams.length then
      piCod (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) n
    else none
  | none => none

/-- `sortSpec` at the canonical oracle. -/
def sortSpecE (env : Env) (g : List Expr) (e : Expr) : Option Level :=
  sortSpec (constCod env) g e

/-! ## Clause equations

`piCod` and `sortApp` overlap their patterns, so these are the
rewrite rules consumers use. -/

@[simp] theorem piCod_zero (t : Expr) : piCod t 0 = levelOf t := by
  cases t <;> rfl

@[simp] theorem piCod_forallE (n : Name) (a b : Expr)
    (bi : Setlec.BinderMeta) (k : Nat) :
    piCod (.forallE n a b bi) (k + 1) = piCod b k := rfl

@[simp] theorem sortApp_app (σ : SortEnv) (g : List Expr)
    (f a : Expr) (n : Nat) :
    sortApp σ g (.app f a) n = sortApp σ g f (n + 1) := rfl

@[simp] theorem sortApp_sort_zero (σ : SortEnv) (g : List Expr)
    (u : Level) : sortApp σ g (.sort u) 0 = some (.succ u) := rfl

@[simp] theorem sortApp_sort_succ (σ : SortEnv) (g : List Expr)
    (u : Level) (n : Nat) :
    sortApp σ g (.sort u) (n + 1) = none := rfl

@[simp] theorem sortApp_forallE_zero (σ : SortEnv) (g : List Expr)
    (nm : Name) (a b : Expr) (bi : Setlec.BinderMeta) :
    sortApp σ g (.forallE nm a b bi) 0 =
      match sortApp σ g a 0, sortApp σ (a :: g) b 0 with
      | some u, some v => some (.imax u v)
      | _, _ => none := rfl

@[simp] theorem sortApp_forallE_succ (σ : SortEnv) (g : List Expr)
    (nm : Name) (a b : Expr) (bi : Setlec.BinderMeta) (n : Nat) :
    sortApp σ g (.forallE nm a b bi) (n + 1) = none := rfl

@[simp] theorem sortApp_lam_succ (σ : SortEnv) (g : List Expr)
    (nm : Name) (a b : Expr) (bi : Setlec.BinderMeta) (n : Nat) :
    sortApp σ g (.lam nm a b bi) (n + 1) = sortApp σ (a :: g) b n :=
  rfl

@[simp] theorem sortApp_lam_zero (σ : SortEnv) (g : List Expr)
    (nm : Name) (a b : Expr) (bi : Setlec.BinderMeta) :
    sortApp σ g (.lam nm a b bi) 0 = none := rfl

@[simp] theorem sortApp_letE (σ : SortEnv) (g : List Expr)
    (nm : Name) (a v b : Expr) (n : Nat) :
    sortApp σ g (.letE nm a v b) n = sortApp σ (a :: g) b n := rfl

@[simp] theorem sortApp_bvar (σ : SortEnv) (g : List Expr)
    (i n : Nat) : sortApp σ g (.bvar i) n = ctxCod g i n := rfl

@[simp] theorem sortApp_fvar (σ : SortEnv) (g : List Expr)
    (idx : Nat) (nm : Name) (t : Expr) (n : Nat) :
    sortApp σ g (.fvar idx nm t) n = piCod t n := rfl

@[simp] theorem sortApp_const (σ : SortEnv) (g : List Expr)
    (c : Name) (us : List Level) (n : Nat) :
    sortApp σ g (.const c us) n = σ c us n := rfl

@[simp] theorem sortApp_proj (σ : SortEnv) (g : List Expr)
    (s : Name) (i : Nat) (e : Expr) (n : Nat) :
    sortApp σ g (.proj s i e) n = none := rfl

@[simp] theorem sortApp_lit (σ : SortEnv) (g : List Expr)
    (l : Setlec.Literal) (n : Nat) :
    sortApp σ g (.lit l) n = none := by cases l <;> rfl

end Setlec.SetR.SortSpec
