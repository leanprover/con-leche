module

public import ConLeche.Verify.Cached.SimC

public section

set_option linter.unusedSimpArgs false

/-!
# The verdict side of the cached simulation (NESTKN-S0)

`SimC` relates the cached run's SUCCESSES to the fueled family's.  A catch
(`tryCatchVerdict`) turns the body's verdict error into a success of the
handler, so simulating a catch needs the body's verdicts too:

* `SimCE mode env s₀ P c p` — `SimC`, and a cached VERDICT error from `s₀` is the
  fueled family's error from some fuel on (the fuel may not matter: the verdict
  persists at every larger one).
* `SimCE.pure`/`throw`/`bind` — the kit; `bind` needs no stability of the fueled
  side, the "from some fuel on" form carries it.
* `SimC.tryCatchVerdict` — a catch simulates when its body does WITH verdicts
  (`SimCE`) and its handler does (`SimC`).
* `SimC.tryCatchVerdict_rethrow` — a catch whose handler never succeeds (a
  reclassification: `typeAtK`, `asInternalK`, the layout's joint typing) simulates
  from the body's `SimC` alone.
* `SimCE.tryCatchVerdict` — with verdicts, from the body's and the handler's.

What is NOT here (NESTKN-S0's handoff, S0.3): `SimCE` of the cached core's entry
points (`opE … (·.infer)`, `opS`), i.e. that the cached core throws a verdict only
where the fueled core throws the same one.  The success side is `ssimC`
(`KnotC.lean`); the verdict side is its twin over the same `DiscC*` walks.
-/

namespace ConLeche.Cached

open ConLeche

variable {mode : CheckMode}

/-- The simulation with the verdict side: `SimC`, and a cached VERDICT error from `s₀`
is the fueled family's error from some fuel on. -/
@[expose] def SimCE (mode : CheckMode) (env : Env) (s₀ : CState) {β α : Type}
    (P : β → α → Prop) (c : CheckCM β) (p : FueledM α) : Prop :=
  SimC mode env s₀ P c p ∧
    ∀ e, c s₀ = .error e → e.isVerdict = true →
      ∃ F₀, ∀ F, F₀ ≤ F → p.val F = .error e

namespace SimCE

variable {env : Env} {s₀ : CState}

theorem toSimC {β α : Type} {P : β → α → Prop} {c : CheckCM β} {p : FueledM α}
    (h : SimCE mode env s₀ P c p) : SimC mode env s₀ P c p := h.1

protected theorem pure {β α : Type} {P : β → α → Prop}
    {b : β} {a : α} (hs : CSOK mode env s₀) (h : P b a) :
    SimCE mode env s₀ P (pure b) (pure a) :=
  ⟨SimC.pure hs h, fun _ he => nomatch he⟩

protected theorem throw {β α : Type} {P : β → α → Prop} {e : CheckError} :
    SimCE mode env s₀ P (throw e : CheckCM β) (throw e : FueledM α) := by
  refine ⟨SimC.throw, fun e' he _ => ⟨0, fun F _ => ?_⟩⟩
  simp only [throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind,
    ExceptT.lift, liftM, monadLift, MonadLift.monadLift] at he
  cases he
  rfl

/-- Bind: a verdict of the first part is the whole's; a verdict of the continuation
after a success is the whole's from the larger of the two fuels on. -/
protected theorem bind {β β' α α' : Type}
    {P : β → α → Prop} {Q : β' → α' → Prop}
    {c : CheckCM β} {k : β → CheckCM β'}
    {p : FueledM α} {q : α → FueledM α'}
    (hx : SimCE mode env s₀ P c p)
    (hf : ∀ s₁ b a, CSOK mode env s₁ → P b a →
      SimCE mode env s₁ Q (k b) (q a)) :
    SimCE mode env s₀ Q (c >>= k) (p >>= q) := by
  refine ⟨SimC.bind hx.1 (fun s₁ b a hs₁ hP => (hf s₁ b a hs₁ hP).1), ?_⟩
  intro e hr he
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e' =>
    rw [hc] at hr
    cases hr
    obtain ⟨F₀, hF⟩ := hx.2 _ hc he
    refine ⟨F₀, fun F hle => ?_⟩
    rw [FueledM.atF_bind, hF F hle]
    rfl
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, a, hP, F₁, hp₁⟩ := hx.1 b s₁ hc
    obtain ⟨F₂, hF₂⟩ := (hf s₁ b a hs₁ hP).2 e hr he
    refine ⟨max F₁ F₂, fun F hle => ?_⟩
    rw [FueledM.atF_bind]
    simp only [Bind.bind]
    rw [p.property (Nat.le_trans (Nat.le_max_left F₁ F₂) hle) hp₁]
    exact hF₂ F (Nat.le_trans (Nat.le_max_right F₁ F₂) hle)

end SimCE

/-- The cached catch at a state: the body's run, or on its error the handler's from the
PRE-catch state. -/
theorem tryCatchC_run {α : Type} (x : CheckCM α) (h : CheckError → CheckCM α)
    (s : CState) :
    tryCatchThe CheckError x h s =
      match x s with
      | .ok r => .ok r
      | .error e => h e s := by
  show tryCatchThe CheckError (x s) (fun e => h e s) = _
  cases x s <;> rfl

/-- The fueled catch takes the handler at a fuel where the body's verdict has settled. -/
theorem tryCatchVerdictF_handler {α : Type} {x : FueledM α} {h : CheckError → FueledM α}
    {e : CheckError} (he : e.isVerdict = true) {F₀ : Nat}
    (hx : ∀ F, F₀ ≤ F → x.val F = .error e) {F : Nat} (hle : F₀ ≤ F) :
    (tryCatchVerdict x h).val F = (h e).val F := by
  unfold tryCatchVerdict
  rw [FueledM.atF_tryCatch, hx F hle]
  dsimp only
  rw [if_pos ⟨he, fun F' h' => hx F' (Nat.le_trans hle h')⟩]
  simp only [he, if_true]

/-- The fueled catch on a body's success. -/
theorem tryCatchVerdictF_ok {α : Type} {x : FueledM α} {h : CheckError → FueledM α}
    {F : Nat} {v : α} (hx : x.val F = .ok v) :
    (tryCatchVerdict x h).val F = .ok v := by
  unfold tryCatchVerdict
  rw [FueledM.atF_tryCatch, hx]

namespace SimC

variable {env : Env} {s₀ : CState}

/-- **A catch simulates**: the body with its verdicts (`SimCE`), the handler at the
pre-catch state for every verdict. -/
protected theorem tryCatchVerdict {β α : Type} {P : β → α → Prop}
    {x : CheckCM β} {h : CheckError → CheckCM β}
    {x' : FueledM α} {h' : CheckError → FueledM α}
    (hx : SimCE mode env s₀ P x x')
    (hh : ∀ e, e.isVerdict = true → SimC mode env s₀ P (h e) (h' e)) :
    SimC mode env s₀ P (tryCatchVerdict x h) (tryCatchVerdict x' h') := by
  intro v' s' hr
  unfold tryCatchVerdict at hr
  rw [tryCatchC_run] at hr
  cases hxs : x s₀ with
  | ok r =>
    rw [hxs] at hr
    cases hr
    obtain ⟨hs', v, hP, F, hF⟩ := hx.1 v' s' hxs
    exact ⟨hs', v, hP, F, tryCatchVerdictF_ok hF⟩
  | error e =>
    rw [hxs] at hr
    dsimp only at hr
    cases he : e.isVerdict with
    | false =>
      rw [he] at hr
      simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind,
        ExceptT.lift, liftM, monadLift, MonadLift.monadLift] at hr
    | true =>
      rw [he, if_pos rfl] at hr
      obtain ⟨F₀, hF₀⟩ := hx.2 e hxs he
      obtain ⟨hs', v, hP, F₁, hF₁⟩ := hh e he v' s' hr
      refine ⟨hs', v, hP, max F₀ F₁, ?_⟩
      rw [tryCatchVerdictF_handler he hF₀ (Nat.le_max_left F₀ F₁)]
      exact (h' e).property (Nat.le_max_right F₀ F₁) hF₁

/-- **A reclassifying catch simulates from its body's successes alone**: its handler
never succeeds, so the whole succeeds only where the body did. -/
theorem tryCatchVerdict_rethrow {β α : Type} {P : β → α → Prop}
    {x : CheckCM β} {h : CheckError → CheckCM β}
    {x' : FueledM α} {h' : CheckError → FueledM α}
    (hx : SimC mode env s₀ P x x')
    (hh : ∀ e v s', h e s₀ ≠ .ok (v, s')) :
    SimC mode env s₀ P (tryCatchVerdict x h) (tryCatchVerdict x' h') := by
  intro v' s' hr
  unfold tryCatchVerdict at hr
  rw [tryCatchC_run] at hr
  cases hxs : x s₀ with
  | ok r =>
    rw [hxs] at hr
    cases hr
    obtain ⟨hs', v, hP, F, hF⟩ := hx v' s' hxs
    exact ⟨hs', v, hP, F, tryCatchVerdictF_ok hF⟩
  | error e =>
    rw [hxs] at hr
    dsimp only at hr
    cases he : e.isVerdict with
    | false =>
      rw [he] at hr
      simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind,
        ExceptT.lift, liftM, monadLift, MonadLift.monadLift] at hr
    | true =>
      rw [he, if_pos rfl] at hr
      exact absurd hr (hh e v' s')

end SimC

namespace SimCE

variable {env : Env} {s₀ : CState}

/-- A catch simulates WITH verdicts: the body's, and the handler's for every verdict. -/
protected theorem tryCatchVerdict {β α : Type} {P : β → α → Prop}
    {x : CheckCM β} {h : CheckError → CheckCM β}
    {x' : FueledM α} {h' : CheckError → FueledM α}
    (hx : SimCE mode env s₀ P x x')
    (hh : ∀ e, e.isVerdict = true → SimCE mode env s₀ P (h e) (h' e)) :
    SimCE mode env s₀ P (tryCatchVerdict x h) (tryCatchVerdict x' h') := by
  refine ⟨SimC.tryCatchVerdict hx (fun e he => (hh e he).1), ?_⟩
  intro e' hr he'
  unfold tryCatchVerdict at hr
  rw [tryCatchC_run] at hr
  cases hxs : x s₀ with
  | ok r =>
    rw [hxs] at hr
    cases hr
  | error e =>
    rw [hxs] at hr
    dsimp only at hr
    cases he : e.isVerdict with
    | false =>
      rw [he] at hr
      simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind,
        ExceptT.lift, liftM, monadLift, MonadLift.monadLift] at hr
      subst hr
      rw [he] at he'
      cases he'
    | true =>
      rw [he, if_pos rfl] at hr
      obtain ⟨F₀, hF₀⟩ := hx.2 e hxs he
      obtain ⟨F₁, hF₁⟩ := (hh e he).2 e' hr he'
      refine ⟨max F₀ F₁, fun F hle => ?_⟩
      rw [tryCatchVerdictF_handler he hF₀ (Nat.le_trans (Nat.le_max_left F₀ F₁) hle)]
      exact hF₁ F (Nat.le_trans (Nat.le_max_right F₀ F₁) hle)

end SimCE

end ConLeche.Cached
