import Setlec.SetR.SortSpec.Defs
import Setlec.Verify.EnvWF

/-!
# Substitution stability for `sortSpec`

The brief predicted an **equation**: substituting into a term does not
change its structural sort.  That equation is **false**, and the
countermodel is not an artifact — `not_sortApp_subst_eq` below
mechanizes it.  What is true, and what this file proves, is the
*monotone* half: a sort that `sortSpec` **computes** is preserved by
substitution, level expression and all.

## Why the equation fails

In the context `(α : Sort 1) (x : α)` the term `x` has no structural
sort: `α` is a variable, so `piCod α 0 = levelOf (bvar 0) = none` —
`sortSpec` cannot tell whether `x` is a type.  Substitute `α := Sort
0` and `x : Sort 0`, so `x` *is* a type and `sortSpec x = some 0`.
Substitution therefore **creates** sorts.  It never destroys or
changes one, which is exactly `sortApp_instantiate1`.

Semantically this is the honest behaviour: the abstract answer `none`
is not "no sort", it is "not structurally determined", and a
substitution can determine it.  A `sortSpec` that returned a sort in
the abstract context would have to guess.

## The trap ledger (seal 0)

* **(P1) bare-`Env` escape.**  `sortApp` is *environment free*: the
  environment enters only through the oracle `σ`, so the main theorem
  cannot be stated over a bare `Env` at all.  The `constCod env`
  corollary carries `EnvWF env` as required, and says so about not
  needing it.
* **Smallest instance.**  At `Δ = []`, `e = .bvar 0`, `n = 0` the
  theorem *is* its own premise `hv` — not trivially true.  At
  `e = .sort u` both sides are `some (.succ u)` — trivially true.  So
  the statement is neither uniformly trivial nor degenerate.
* **Vacuity.**  `hv` is satisfiable: `A = Sort 1`, `v = Sort 0` (see
  `SortSpec/Examples.lean`), and `subst_nonvacuous` below exhibits an
  instance in which *both* sides are `some`.
* **Wrong side of a run.**  There is no run: no clause and no premise
  mentions `whnf`, `inferTypeCore`, or a fuel.
-/

namespace Setlec.SetR.SortSpec

open Setlec (Env Expr Level Name EnvWF)

/-! ## `levelOf` and `piCod` inversions -/

theorem levelOf_eq_some {t : Expr} {w : Level}
    (h : levelOf t = some w) : t = .sort w := by
  cases t <;> simp_all [levelOf]

theorem piCod_succ_inv {t : Expr} {n : Nat} {w : Level}
    (h : piCod t (n + 1) = some w) :
    ∃ nm a b bi, t = .forallE nm a b bi ∧ piCod b n = some w := by
  cases t <;> simp only [piCod] at h
  case forallE nm a b bi => exact ⟨nm, a, b, bi, rfl, h⟩
  all_goals exact nomatch h

/-! ## `piCod` is substitution-monotone

The declared-codomain walker never loses a level under substitution:
stripping `forallE`s commutes with `instantiate1`, and a residual that
is syntactically `.sort u` stays `.sort u` (levels carry no expression
`bvar`s). -/

theorem piCod_instantiate1 (v : Expr) :
    ∀ (n : Nat) (t : Expr) (d : Nat) (w : Level),
      piCod t n = some w →
      piCod (t.instantiate1 v d) n = some w := by
  intro n
  induction n with
  | zero =>
    intro t d w h
    rw [piCod_zero] at h
    have ht := levelOf_eq_some h
    subst ht
    rfl
  | succ k ih =>
    intro t d w h
    obtain ⟨nm, a, b, bi, rfl, hb⟩ := piCod_succ_inv h
    simpa [Expr.instantiate1] using ih b (d + 1) w hb

/-! ## The substituted sort-context

`Δ` is the part of the context inside the binder being substituted.
Its `i`-th entry lives under the entries after it, so it sees the
substituted variable at de Bruijn index `(Δ.drop (i+1)).length`. -/

def substCtx (v : Expr) : List Expr → List Expr
  | [] => []
  | t :: d => t.instantiate1 v d.length :: substCtx v d

@[simp] theorem substCtx_nil (v : Expr) : substCtx v [] = [] := rfl

@[simp] theorem substCtx_cons (v t : Expr) (d : List Expr) :
    substCtx v (t :: d) =
      t.instantiate1 v d.length :: substCtx v d := rfl

/-- The substituted variable's own context slot. -/
theorem ctxCod_append_length (Γ : List Expr) (A : Expr) :
    ∀ (Δ : List Expr) (n : Nat),
      ctxCod (Δ ++ A :: Γ) Δ.length n = piCod A n := by
  intro Δ
  induction Δ with
  | nil => intro n; rfl
  | cons t Δ ih => intro n; simpa [ctxCod] using ih n

/-! ## The `bvar` case

The whole content of the theorem sits here: index bookkeeping in the
two branches that do not move (`i` below or above the substituted
slot), and the premise `hv` in the one that does. -/

/-- `instantiate1` at a `bvar`, spelled out. -/
theorem inst_bvar (i d : Nat) (v : Expr) :
    (Expr.bvar i).instantiate1 v d =
      if i = d then v
      else if i > d then .bvar (i - 1) else .bvar i := rfl

theorem ctxCod_instantiate1 {σ : SortEnv} {Γ : List Expr}
    {A v : Expr}
    (hv : ∀ (Θ : List Expr) (m : Nat) (w : Level),
      piCod A m = some w → sortApp σ Θ v m = some w) :
    ∀ (Δ : List Expr) (i n : Nat) (w : Level),
      ctxCod (Δ ++ A :: Γ) i n = some w →
      sortApp σ (substCtx v Δ ++ Γ)
        ((Expr.bvar i).instantiate1 v Δ.length) n = some w := by
  intro Δ
  induction Δ with
  | nil =>
    intro i n w h
    cases i with
    | zero => exact hv Γ n w h
    | succ j =>
      rw [List.length_nil, inst_bvar, if_neg (by omega),
        if_pos (by omega)]
      simpa [ctxCod] using h
  | cons t Δ ih =>
    intro i n w h
    simp only [List.cons_append] at h
    simp only [List.length_cons, substCtx_cons, List.cons_append]
    cases i with
    | zero =>
      simp only [ctxCod] at h
      rw [inst_bvar, if_neg (by omega), if_neg (by omega)]
      simpa [ctxCod] using piCod_instantiate1 v n t Δ.length w h
    | succ j =>
      simp only [ctxCod] at h
      rcases Nat.lt_trichotomy j Δ.length with hj | hj | hj
      · rw [inst_bvar, if_neg (by omega), if_neg (by omega)]
        have hi := ih j n w h
        rw [inst_bvar, if_neg (by omega), if_neg (by omega)] at hi
        simpa [ctxCod] using hi
      · subst hj
        rw [ctxCod_append_length] at h
        rw [inst_bvar, if_pos rfl]
        exact hv _ n w h
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [inst_bvar, if_neg (by omega), if_pos (by omega)]
        have hi := ih (j' + 1) n w h
        rw [inst_bvar, if_neg (by omega), if_pos (by omega)] at hi
        simpa [ctxCod] using hi

/-! ## Substitution stability, the monotone form -/

/-- **Substitution never loses a structural sort.**  If `sortSpec`
computes the sort `w` for `e a₁ … aₙ` in a context whose `Δ.length`-th
binder has type `A`, then it computes the *same* `w` after
substituting any `v` whose sort profile matches `A`'s codomain
profile (`hv` — "`v : A`", at the sort level).

Stated over an abstract oracle `σ`, so no `Env` is quantified. -/
theorem sortApp_instantiate1 {σ : SortEnv} {Γ : List Expr}
    {A v : Expr}
    (hv : ∀ (Θ : List Expr) (m : Nat) (w : Level),
      piCod A m = some w → sortApp σ Θ v m = some w) :
    ∀ (e : Expr) (Δ : List Expr) (n : Nat) (w : Level),
      sortApp σ (Δ ++ A :: Γ) e n = some w →
      sortApp σ (substCtx v Δ ++ Γ) (e.instantiate1 v Δ.length) n
        = some w := by
  intro e
  induction e with
  | bvar i => intro Δ n w h; exact ctxCod_instantiate1 hv Δ i n w h
  | fvar idx nm t => intro Δ n w h; simpa [Expr.instantiate1] using h
  | sort u =>
    intro Δ n w h
    cases n with
    | zero => simpa [Expr.instantiate1] using h
    | succ k => exact nomatch h
  | const c us => intro Δ n w h; simpa [Expr.instantiate1] using h
  | lit l =>
    intro Δ n w h
    cases n with
    | zero => cases l <;> exact h
    | succ k => cases l <;> exact nomatch h
  | proj s i e _ => intro Δ n w h; exact nomatch h
  | app f a ihf _ =>
    intro Δ n w h
    simpa [Expr.instantiate1] using ihf Δ (n + 1) w h
  | lam nm a b bi _ ihb =>
    intro Δ n w h
    cases n with
    | zero => exact nomatch h
    | succ k =>
      have := ihb (a :: Δ) k w h
      simpa [Expr.instantiate1] using this
  | letE nm a val b _ _ ihb =>
    intro Δ n w h
    have := ihb (a :: Δ) n w h
    simpa [Expr.instantiate1] using this
  | forallE nm a b bi iha ihb =>
    intro Δ n w h
    cases n with
    | succ k => exact nomatch h
    | zero =>
      rw [sortApp_forallE_zero] at h
      split at h
      · next u x hu hx =>
        have ha := iha Δ 0 u hu
        have hb := ihb (a :: Δ) 0 x hx
        simp only [Expr.instantiate1, sortApp_forallE_zero]
        simp only [substCtx_cons, List.cons_append,
          List.length_cons] at hb
        rw [ha, hb]
        exact h
      · exact nomatch h

/-- The top-level reading: a computed sort survives opening the
outermost binder with any sort-compatible `v`. -/
theorem sortSpec_instantiate1 {σ : SortEnv} {Γ : List Expr}
    {A v e : Expr} {w : Level}
    (hv : ∀ (Θ : List Expr) (m : Nat) (x : Level),
      piCod A m = some x → sortApp σ Θ v m = some x)
    (h : sortSpec σ (A :: Γ) e = some w) :
    sortSpec σ Γ (e.instantiate1 v) = some w :=
  sortApp_instantiate1 hv e [] 0 w h

/-- The canonical-oracle instance.  `EnvWF` is carried because seal 0
(P1) binds every `Env`-quantified statement in this pilot; the proof
does **not** use it, and cannot need it: `sortApp` reads the
environment only through `constCod env`, which is a parameter here.
That the environment cannot escape is a property of the *architecture*
(the oracle), not of this proof. -/
theorem sortSpecE_instantiate1 {env : Env} (_henv : EnvWF env)
    {Γ : List Expr} {A v e : Expr} {w : Level}
    (hv : ∀ (Θ : List Expr) (m : Nat) (x : Level),
      piCod A m = some x →
      sortApp (constCod env) Θ v m = some x)
    (h : sortSpecE env (A :: Γ) e = some w) :
    sortSpecE env Γ (e.instantiate1 v) = some w :=
  sortSpec_instantiate1 hv h

/-! ## The equational form is refuted

`(α : Sort 1) (x : α)`, substituting `α := Sort 0`.  Before: `x`'s
sort is not structurally determined.  After: `x : Sort 0`, a type of
sort `0`.  The premise `hv` holds (`Sort 0 : Sort 1`), so this is a
countermodel to the *equation*, not to its hypotheses. -/

private def A₀ : Expr := .sort (.succ .zero)
private def v₀ : Expr := .sort .zero
private def σ₀ : SortEnv := fun _ _ _ => none

/-- The premise of `sortApp_instantiate1` holds for `A₀`, `v₀`. -/
theorem hv₀ : ∀ (Θ : List Expr) (m : Nat) (w : Level),
    piCod A₀ m = some w → sortApp σ₀ Θ v₀ m = some w := by
  intro Θ m w h
  cases m with
  | zero =>
    simp only [A₀, piCod_zero, levelOf, Option.some.injEq] at h
    subst h; rfl
  | succ k => exact nomatch h

/-- Abstract context `[α] ++ [Sort 1]`: `x`'s sort is undetermined. -/
theorem before₀ :
    sortApp σ₀ ([Expr.bvar 0] ++ A₀ :: []) (.bvar 0) 0 = none := rfl

/-- After `α := Sort 0`: `x : Sort 0`, sort `0`. -/
theorem after₀ :
    sortApp σ₀ (substCtx v₀ [Expr.bvar 0] ++ [])
      ((Expr.bvar 0).instantiate1 v₀ [Expr.bvar 0].length) 0
      = some .zero := rfl

/-- **Substitution stability is not an equation.**  No hypothesis is
weakened away here: the witness satisfies the very premise
`sortApp_instantiate1` uses. -/
theorem not_sortApp_subst_eq :
    ¬ (∀ (σ : SortEnv) (Γ : List Expr) (A v : Expr),
        (∀ (Θ : List Expr) (m : Nat) (w : Level),
          piCod A m = some w → sortApp σ Θ v m = some w) →
        ∀ (e : Expr) (Δ : List Expr) (n : Nat),
          sortApp σ (substCtx v Δ ++ Γ)
              (e.instantiate1 v Δ.length) n
            = sortApp σ (Δ ++ A :: Γ) e n) := by
  intro hall
  have := hall σ₀ [] A₀ v₀ hv₀ (.bvar 0) [Expr.bvar 0] 0
  rw [after₀, before₀] at this
  exact nomatch this

/-! ## Non-vacuity: an instance with `some` on both sides

`Γ = []`, `A = Sort 1`, `v = Sort 0`, `e = ∀ (_ : α), α`.  Abstractly
the sort is `imax 1 1` (read off `α`'s binder type); after
`α := Sort 0` the term is `∀ (_ : Sort 0), Sort 0`, whose sort is
`imax 1 1` again. -/

private def e₀ : Expr :=
  .forallE .anonymous (.bvar 0) (.bvar 1) ⟨.default⟩

theorem subst_nonvacuous :
    sortApp σ₀ ([] ++ A₀ :: []) e₀ 0
        = some (.imax (.succ .zero) (.succ .zero)) ∧
      sortApp σ₀ (substCtx v₀ [] ++ [])
          (e₀.instantiate1 v₀ ([] : List Expr).length) 0
        = some (.imax (.succ .zero) (.succ .zero)) :=
  ⟨rfl, rfl⟩

end Setlec.SetR.SortSpec
