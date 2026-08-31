import Setlec.SetR.SortSpec.Subst
import Setlec.SetR.Annot.Canon
import Setlec.Verify.InferLemmas
import Setlec.Verify.BinderLoop

/-!
# Agreement: where `sortSpec` commits, the checker agrees

The pilot's real test.  `sortSpec` is a structural recursion on the
term; `sortOfE` (`SetR/Annot/Canon.lean`) is *infer, then whnf, then
`Level.eval`* — a fuel-indexed **run**.  This file makes them meet.

    noLet e →
    sortSpecE env [] e = some u →
    inferTypeCore μ env F d e = .ok t →
    sortOfE μ env φ (F + 2) d e = some (u.eval φ)

Read: **`sortSpec` never lies.**  It is partial, and where it declines
it says nothing; but wherever it commits to a level, a checker run
that infers *anything at all* for the same subject infers exactly that
sort.  The direction is the only one that is true — the converse is
false, not merely unproved (see `DESIGN.md` seal 2).

## The engine: `piCod` under the run

The whole proof is one invariant, carried through the fuel induction:

> if `sortApp σ [] e n = some u` and the checker infers `t` for `e`,
> then `piCod t n = some u`.

At `n = 0` that says `t = .sort u` outright, which is what `sortOfE`'s
`whnf`-to-a-sort step needs.  The two steps that move it are exactly
the two theorems seal 1 landed:

* the `.app` clause consumes an argument, and the checker's residual
  is `body.instantiate1 a` — closed by **`piCod_instantiate1`**, the
  substitution-monotonicity lemma of seal 1;
* the `.forallE` and `.lam` clauses open a binder with
  `.fvar d n ty`, and the sort-context entry must become the `fvar`'s
  carried type — closed by **`sortApp_instantiate1`** at `Δ = []`,
  whose premise `hv` is *free* here because
  `sortApp σ Θ (.fvar d n A) m` **is** `piCod A m`, definitionally
  (`sortApp_open`).

Neither step needs δ, a defeq fact, or a level equivalence.  The
reason is seal 1's partiality: `sortSpec` commits only when the
declared codomain is *already* a syntactic `.sort`, and a `.sort`
carries no expression `bvar`s — so the checker's argument
substitutions cannot touch it.

## What this proof does NOT need

* **No `DeltaSortLinked`.**  See seal 2.
* **No `mode.verified`.**  `μ` is universally quantified.  The λ
  clause's verified-only codomain check is a *side* check; it can make
  the run fail, and the run's success is a premise, but it never
  changes the inferred type.  So the pilot does not collide with the
  parked `Denote2Total`'s seal-10 problem.
* **No `EnvWF`.**  Carried on the statements below because seal 0 (P1)
  binds every `Env`-quantified statement in this pilot, but unused,
  and structurally unusable: both sides read the *same* declared type
  through the *same* `instantiateLevelParams`, so a bare-`Env` escape
  produces identical garbage on both sides.  Agreement is a *relative*
  statement, and the escape cannot separate the two functions it
  relates.
-/

namespace Setlec.SetR.SortSpec

open Setlec (Env Expr Level Name CheckMode EnvWF inferTypeCore whnf
  ensureSortCore)
open Setlec.SetR.Interp2 (sortOfE)

/-! ## The `letE` restriction

`sortSpec`'s `letE` clause reads the *annotation* `A` and drops the
value; the checker substitutes the value and infers
`b.instantiate1 v`.  Bridging the two needs
`sortApp σ Θ v m = piCod A m` — i.e. that the value's structural sort
profile matches its annotation's.  Nothing structural supplies it: the
checker establishes only `defeq (infer v) A`, so recovering it needs
defeq soundness on sorts, which is a *run* fact.  Seal 2 stops there
and restricts the subject instead. -/

def noLet : Expr → Bool
  | .letE _ _ _ _ => false
  | .app f a => noLet f && noLet a
  | .lam _ t b _ => noLet t && noLet b
  | .forallE _ t b _ => noLet t && noLet b
  | .proj _ _ e => noLet e
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .lit _ => true

theorem noLet_instantiate1 (v : Expr) (hv : noLet v = true) :
    ∀ (e : Expr) (d : Nat),
      noLet e = true → noLet (e.instantiate1 v d) = true := by
  intro e
  induction e with
  | bvar i =>
    intro d _
    rw [inst_bvar]
    split
    · exact hv
    · split <;> rfl
  | letE _ _ _ _ _ _ _ => intro d h; exact nomatch h
  | app f a ihf iha =>
    intro d h
    simp only [noLet, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, noLet, Bool.and_eq_true]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam _ t b _ iht ihb =>
    intro d h
    simp only [noLet, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, noLet, Bool.and_eq_true]
    exact ⟨iht d h.1, ihb (d + 1) h.2⟩
  | forallE _ t b _ iht ihb =>
    intro d h
    simp only [noLet, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, noLet, Bool.and_eq_true]
    exact ⟨iht d h.1, ihb (d + 1) h.2⟩
  | proj _ _ e ihe =>
    intro d h
    simp only [Expr.instantiate1, noLet]
    exact ihe d h
  | _ => intro d _; rfl

/-! ## Two small lemmas the run needs -/

/-- `piCod` survives abstraction, exactly as it survives substitution
(`piCod_instantiate1`): `abstract1` preserves the `forallE` spine and
leaves a `.sort` residual alone. -/
theorem piCod_abstract1 (dv : Nat) :
    ∀ (n : Nat) (t : Expr) (k : Nat) (w : Level),
      piCod t n = some w →
      piCod (t.abstract1 dv k) n = some w := by
  intro n
  induction n with
  | zero =>
    intro t k w h
    rw [piCod_zero] at h
    have ht := levelOf_eq_some h
    subst ht
    rfl
  | succ j ih =>
    intro t k w h
    obtain ⟨nm, a, b, bi, rfl, hb⟩ := piCod_succ_inv h
    simpa [Expr.abstract1] using ih b (k + 1) w hb

/-- `whnf` is the identity on a sort, at any fuel that succeeds — the
`.sort` twin of `whnf_forallE_eq`. -/
theorem whnf_sort_eq {μ : CheckMode} {env : Env} {fuel d : Nat}
    {u : Level} {e' : Expr}
    (h : whnf μ env fuel d (.sort u) = .ok e') : e' = .sort u := by
  have h1 := whnf_mono (Nat.le_add_right fuel 2) h
  have h2 := Setlec.whnf_sort (mode := μ) env fuel d u
  rw [h1] at h2
  exact Except.ok.inj h2

/-! ## Two `inferTypeCore` inversions not already in `InferLemmas` -/

theorem inferTypeCore_sort_inv {μ : CheckMode} {env : Env}
    {fuel d : Nat} {u : Level} {t : Expr}
    (h : inferTypeCore μ env fuel d (.sort u) = .ok t) :
    t = .sort (.succ u) := by
  match fuel, h with
  | 0, h => rw [Setlec.inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    rw [Setlec.inferTypeCore_succ] at h
    simp only [Setlec.inferBody, Setlec.viewM, Setlec.Expr.view, pure,
      Except.pure, Bind.bind, Except.bind, Except.ok.injEq] at h
    exact h.symm

theorem inferTypeCore_fvar_inv {μ : CheckMode} {env : Env}
    {fuel d idx : Nat} {nm : Name} {ty t : Expr}
    (h : inferTypeCore μ env fuel d (.fvar idx nm ty) = .ok t) :
    t = ty := by
  match fuel, h with
  | 0, h => rw [Setlec.inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    rw [Setlec.inferTypeCore_succ] at h
    simp only [Setlec.inferBody, Setlec.viewM, Setlec.Expr.view, pure,
      Except.pure, Bind.bind, Except.bind] at h
    revert h
    split
    · intro h
      simp only [Except.ok.injEq] at h
      exact h.symm
    · intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Opening a binder is free -/

/-- The sort-context entry `A` and the carried type of `.fvar d nm A`
are the same datum, so `sortApp_instantiate1`'s premise holds by
`rfl`: **opening a binder with its own variable costs nothing**. -/
theorem sortApp_open {σ : SortEnv} {Γ : List Expr} {A e : Expr}
    {n : Nat} {u : Level} (d : Nat) (nm : Name)
    (h : sortApp σ (A :: Γ) e n = some u) :
    sortApp σ Γ (e.instantiate1 (.fvar d nm A)) n = some u :=
  sortApp_instantiate1 (v := .fvar d nm A) (fun _ _ _ hh => hh)
    e [] n u h

/-! ## The invariant -/

/-- **`piCod` under the run.**  If the structural walk commits to `u`
for `e` at `n` arguments, then whatever type the checker infers for
`e` has `u` as its `n`-th codomain sort. -/
theorem piCod_agree {μ : CheckMode} {env : Env} :
    ∀ (F : Nat) (e : Expr) (d n : Nat) (u : Level) (t : Expr),
      noLet e = true →
      sortApp (constCod env) [] e n = some u →
      inferTypeCore μ env F d e = .ok t →
      piCod t n = some u := by
  intro F
  induction F with
  | zero =>
    intro e d n u t _ _ hi
    rw [Setlec.inferTypeCore_zero] at hi
    exact nomatch hi
  | succ F ih =>
    intro e d n u t hnl hs hi
    match e with
    | .bvar i => exact nomatch hs
    | .lit l => rw [sortApp_lit] at hs; exact nomatch hs
    | .proj _ _ _ => exact nomatch hs
    | .letE _ _ _ _ => exact nomatch hnl
    | .sort v =>
      cases n with
      | succ k => exact nomatch hs
      | zero =>
        rw [sortApp_sort_zero] at hs
        rw [inferTypeCore_sort_inv hi, piCod_zero, levelOf]
        exact hs
    | .fvar idx nm ty =>
      rw [sortApp_fvar] at hs
      rw [inferTypeCore_fvar_inv hi]
      exact hs
    | .const c us =>
      rw [sortApp_const] at hs
      obtain ⟨ci, hf, rfl⟩ := Setlec.inferTypeCore_const_inv hi
      simp only [constCod, hf] at hs
      split at hs
      · exact hs
      · exact nomatch hs
    | .app f a =>
      rw [sortApp_app] at hs
      simp only [noLet, Bool.and_eq_true] at hnl
      obtain ⟨tf, n', ty', body', m', h1, h2, rfl, -⟩ :=
        Setlec.inferTypeCore_app_inv hi
      have hf := ih f d (n + 1) u tf hnl.1 hs h1
      obtain ⟨nm2, a2, b2, bi2, rfl, hb⟩ := piCod_succ_inv hf
      have heq := Setlec.whnf_forallE_eq h2
      obtain ⟨-, -, hbody, -⟩ := Expr.forallE.inj heq
      rw [← hbody] at hb
      exact piCod_instantiate1 a n body' 0 u hb
    | .lam nm A b bi =>
      cases n with
      | zero => exact nomatch hs
      | succ k =>
        rw [sortApp_lam_succ] at hs
        simp only [noLet, Bool.and_eq_true] at hnl
        obtain ⟨tty, u0, bt, -, -, h3, -, rfl⟩ :=
          Setlec.inferTypeCore_lam_inv hi
        have hopen := sortApp_open d nm hs
        have hbt := ih _ (d + 1) k u bt
          (noLet_instantiate1 _ rfl b 0 hnl.2) hopen h3
        rw [piCod_forallE]
        exact piCod_abstract1 d k bt 0 u hbt
    | .forallE nm A B bi =>
      cases n with
      | succ k => exact nomatch hs
      | zero =>
        simp only [noLet, Bool.and_eq_true] at hnl
        obtain ⟨tty, u0, bt, v0, h1, h2, h3, h4, rfl⟩ :=
          Setlec.inferTypeCore_forall_inv hi
        cases hA : sortApp (constCod env) [] A 0 with
        | none => rw [sortApp_forallE_zero, hA] at hs; exact nomatch hs
        | some uA =>
          cases hB : sortApp (constCod env) [A] B 0 with
          | none =>
            rw [sortApp_forallE_zero, hA, hB] at hs; exact nomatch hs
          | some uB =>
            rw [sortApp_forallE_zero, hA, hB] at hs
            have hty := ih A d 0 uA tty hnl.1 hA h1
            rw [piCod_zero] at hty
            have httyE := levelOf_eq_some hty
            subst httyE
            have hu0 := whnf_sort_eq h2
            obtain rfl : u0 = uA := (Expr.sort.inj hu0)
            have hopen := sortApp_open d nm hB
            have hbt := ih _ (d + 1) 0 uB bt
              (noLet_instantiate1 _ rfl B 0 hnl.2) hopen h3
            rw [piCod_zero] at hbt
            have hbtE := levelOf_eq_some hbt
            subst hbtE
            have hv0 := whnf_sort_eq (Setlec.ensureSortCore_inv h4)
            obtain rfl : v0 = uB := (Expr.sort.inj hv0)
            rw [piCod_zero, levelOf]
            exact hs

/-! ## Agreement -/

/-- **`sortSpec` never lies.**  Where the structural function commits
to `u`, the checker's own sort computation returns `u.eval φ`.

`EnvWF` is carried per seal 0 (P1); the proof does not use it and
structurally cannot — see the module docstring. -/
theorem sortSpec_agree {μ : CheckMode} {env : Env} (φ : Name → Nat)
    (_henv : EnvWF env) {e : Expr} {d F : Nat} {u : Level} {t : Expr}
    (hnl : noLet e = true)
    (hs : sortSpecE env [] e = some u)
    (hi : inferTypeCore μ env F d e = .ok t) :
    sortOfE μ env φ (F + 2) d e = some (u.eval φ) := by
  have hp := piCod_agree F e d 0 u t hnl hs hi
  rw [piCod_zero] at hp
  have ht := levelOf_eq_some hp
  subst ht
  have hi2 := Setlec.inferTypeCore_mono (Nat.le_add_right F 2) hi
  simp only [sortOfE, hi2, Except.toOption,
    Setlec.whnf_sort (mode := μ) env F d u]

/-- The `∃ F` form. -/
theorem sortSpec_agree_exists {μ : CheckMode} {env : Env}
    (φ : Name → Nat) (henv : EnvWF env) {e : Expr} {d F : Nat}
    {u : Level} {t : Expr}
    (hnl : noLet e = true)
    (hs : sortSpecE env [] e = some u)
    (hi : inferTypeCore μ env F d e = .ok t) :
    ∃ F', sortOfE μ env φ F' d e = some (u.eval φ) :=
  ⟨F + 2, sortSpec_agree φ henv hnl hs hi⟩

end Setlec.SetR.SortSpec
