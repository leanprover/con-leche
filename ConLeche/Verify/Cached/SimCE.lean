module

public import ConLeche.Verify.Cached.SimC
public import ConLeche.Verify.BridgeDecl
public import ConLeche.Cached.CheckerC

public section

set_option linter.unusedSimpArgs false

/-!
# The verdict side of the cached simulation (NESTKN-S0)

`SimC` relates the cached run's SUCCESSES to the fueled family's.  The trial
(`CheckerOps.attempt`) turns its body's verdict into the success `false`, so
simulating a trial needs the body's verdicts too:

* `SimCE mode env s₀ P c p` — `SimC`, and a cached VERDICT error from `s₀` is matched
  by a fueled verdict (not necessarily the same one) at every fuel from some fuel on.
* `SimCE.pure`/`throw`/`bind` — the kit; `bind` needs no stability of the fueled
  side, the "from some fuel on" form carries it.
* `SimC.attempt` — a trial simulates when its body does WITH verdicts.

What is NOT here (NESTKN-S0's handoff, S0.3): `SimCE` of the cached core's entry
points (`opE … (·.infer)`, `opS`, `opB`), i.e. that the cached core ends in a verdict
only where the fueled core does.  The success side is `ssimC` (`KnotC.lean`); the
verdict side is its twin over the same `DiscC*` walks.
-/

namespace ConLeche.Cached

open ConLeche

variable {mode : CheckMode}

/-- The simulation with the verdict side: `SimC`, and a cached VERDICT error from `s₀`
is matched by a fueled verdict from some fuel on. -/
@[expose] def SimCE (mode : CheckMode) (env : Env) (s₀ : CState) {β α : Type}
    (P : β → α → Prop) (c : CheckCM β) (p : FueledM α) : Prop :=
  SimC mode env s₀ P c p ∧
    ∀ e, c s₀ = .error e → e.isVerdict = true →
      ∃ F₀, ∀ F, F₀ ≤ F → ∃ e', p.val F = .error e' ∧ e'.isVerdict = true

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
  refine ⟨SimC.throw, fun e' he hv => ⟨0, fun F _ => ⟨e', ?_, hv⟩⟩⟩
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
    obtain ⟨e', hF, he'⟩ := hF F hle
    exact ⟨e', by rw [FueledM.atF_bind, hF]; rfl, he'⟩
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, a, hP, F₁, hp₁⟩ := hx.1 b s₁ hc
    obtain ⟨F₂, hF₂⟩ := (hf s₁ b a hs₁ hP).2 e hr he
    refine ⟨max F₁ F₂, fun F hle => ?_⟩
    obtain ⟨e', hF, he'⟩ := hF₂ F (Nat.le_trans (Nat.le_max_right F₁ F₂) hle)
    refine ⟨e', ?_, he'⟩
    rw [FueledM.atF_bind]
    simp only [Bind.bind]
    rw [p.property (Nat.le_trans (Nat.le_max_left F₁ F₂) hle) hp₁]
    exact hF

end SimCE

/-- **The trial simulates**: its body with its verdicts.  A cached success is the
fueled body's success (`true`); a cached verdict is `false` at the PRE-trial state, and
the fueled body's verdicts from some fuel on make the fueled trial `false` there. -/
theorem SimC.attempt {env : Env} {s₀ : CState} (hs : CSOK mode env s₀)
    {x : CheckCM Unit} {x' : FueledM Unit}
    (hx : SimCE mode env s₀ (fun _ _ => True) x x') :
    SimC mode env s₀ RelVC ((sharedOpsC mode (mkFEnv env)).attempt x)
      ((fueledOpsM mode).attempt x') := by
  intro v' s' hr
  dsimp only [sharedOpsC] at hr
  revert hr
  cases hxs : x s₀ with
  | ok p =>
    obtain ⟨u, s₁⟩ := p
    intro hr
    cases hr
    obtain ⟨hs₁, w, -, F, hF⟩ := hx.1 u _ hxs
    refine ⟨hs₁, true, rfl, F, ?_⟩
    show (match x'.val F with
      | .ok () => .ok true
      | .error e =>
        @ite _ (e.isVerdict = true ∧
            ∀ F', F ≤ F' → ∃ e' : CheckError, x'.val F' = .error e' ∧ e'.isVerdict = true)
          (Classical.propDecidable _) (.ok false) (.error e) : CheckM Bool) = _
    rw [hF]
  | error e =>
    dsimp only
    cases he : e.isVerdict with
    | false => intro hr; exact nomatch hr
    | true =>
      intro hr
      cases hr
      obtain ⟨F₀, hF₀⟩ := hx.2 e hxs he
      refine ⟨hs, false, rfl, F₀, ?_⟩
      obtain ⟨e', hF, he'⟩ := hF₀ F₀ (Nat.le_refl _)
      show (match x'.val F₀ with
        | .ok () => .ok true
        | .error e =>
          @ite _ (e.isVerdict = true ∧
              ∀ F', F₀ ≤ F' → ∃ e' : CheckError, x'.val F' = .error e' ∧ e'.isVerdict = true)
            (Classical.propDecidable _) (.ok false) (.error e) : CheckM Bool) = _
      rw [hF]
      dsimp only
      rw [if_pos ⟨he', fun F' h' => hF₀ F' h'⟩]

end ConLeche.Cached
