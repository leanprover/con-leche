module

public import ConLeche.Verify.EnvExt.Scope
public import ConLeche.Kernel.Core

public section

/-!
# Env extension, part 4: the relational currency

`Ok P q p`: the run `q` (at `E₂`) IS the run `p` (at `E₁`), and every
success of `p` satisfies `P` (for an `Expr` result: scoped).  The
currency is closed under the monad's operations, so a body walk is a
chain of `Ok.bind`s whose continuations receive a scoped value.
`RecOK` is the currency at a pair of core records, the knot induction's
hypothesis.
-/

namespace ConLeche.EnvExt

open ConLeche

/-- The run at `E₂` equals the run at `E₁`, whose successes satisfy `P`. -/
@[expose] def Ok {α : Type} (P : α → Prop) (q p : CheckM α) : Prop :=
  q = p ∧ ∀ v, p = .ok v → P v

namespace Ok

variable {α β : Type} {P : α → Prop} {Q : β → Prop}

theorem bind {q p : CheckM α} {g f : α → CheckM β}
    (h : Ok P q p) (hf : ∀ v, P v → Ok Q (g v) (f v)) : Ok Q (q >>= g) (p >>= f) := by
  obtain ⟨rfl, hP⟩ := h
  cases hq : q with
  | error e =>
    refine ⟨rfl, fun v hv => ?_⟩
    simp [Bind.bind, Except.bind] at hv
  | ok a =>
    have := hf a (hP a hq)
    simpa [Bind.bind, Except.bind] using this

theorem pure {v : α} (h : P v) : Ok P (Pure.pure v) (Pure.pure v) :=
  ⟨rfl, fun w hw => by cases hw; exact h⟩

theorem throw (e : CheckError) : Ok P (MonadExceptOf.throw e) (MonadExceptOf.throw e) :=
  ⟨rfl, fun w hw => by simp [MonadExceptOf.throw] at hw⟩

theorem throw' (e : CheckError) : Ok P (throwThe CheckError e) (throwThe CheckError e) :=
  ⟨rfl, fun w hw => by simp [throwThe, MonadExceptOf.throw] at hw⟩

theorem throw_bind (e : CheckError) {g f : α → CheckM β} :
    Ok Q (MonadExceptOf.throw e >>= g) (MonadExceptOf.throw e >>= f) :=
  ⟨rfl, fun w hw => by simp [MonadExceptOf.throw, Bind.bind, Except.bind] at hw⟩

theorem unit : Ok (fun _ => True) (Pure.pure ()) (Pure.pure ()) := pure trivial

theorem mono {q p : CheckM α} {P' : α → Prop} (h : Ok P q p) (hPP : ∀ v, P v → P' v) :
    Ok P' q p :=
  ⟨h.1, fun v hv => hPP v (h.2 v hv)⟩

theorem true_of_eq {q p : CheckM α} (h : q = p) : Ok (fun _ => True) q p :=
  ⟨h, fun _ _ => trivial⟩

theorem refl_true {p : CheckM α} : Ok (fun _ => True) p p := true_of_eq rfl

theorem rw_left {q q' p : CheckM α} (hq : q' = q) (h : Ok P q p) : Ok P q' p := hq ▸ h

theorem ite {c : Prop} [Decidable c] {q₁ q₂ p₁ p₂ : CheckM α} (h₁ : c → Ok P q₁ p₁)
    (h₂ : ¬c → Ok P q₂ p₂) : Ok P (if c then q₁ else q₂) (if c then p₁ else p₂) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact h₁ hc
  · rw [if_neg hc, if_neg hc]; exact h₂ hc

theorem liftFueled (what : String) (o : Option α) (h : ∀ v, o = some v → P v) :
    Ok P (ConLeche.liftFueled what o) (ConLeche.liftFueled what o) := by
  cases o with
  | none => exact throw _
  | some v => exact pure (h v rfl)

end Ok

/-- An optional result, scoped where present. -/
@[expose] def OSc (N : Name → Prop) (o : Option Expr) : Prop := ∀ e, o = some e → Sc N e

/-- **The currency at a pair of core records**: every entry point, at
scoped arguments, runs the same in both and returns scoped results. -/
structure RecOK (N : Name → Prop) (r₁ r₂ : CoreFns CheckM) : Prop where
  whnfCore : ∀ d e, Sc N e → Ok (Sc N) (r₂.whnfCore d e) (r₁.whnfCore d e)
  whnf : ∀ d e, Sc N e → Ok (Sc N) (r₂.whnf d e) (r₁.whnf d e)
  infer : ∀ d e, Sc N e → Ok (Sc N) (r₂.infer d e) (r₁.infer d e)
  defeq : ∀ d a b, Sc N a → Sc N b → Ok (fun _ => True) (r₂.defeq d a b) (r₁.defeq d a b)
  annotate : ∀ d e, Sc N e → Ok (Sc N) (r₂.annotate d e) (r₁.annotate d e)
  inferIO : ∀ d e, Sc N e → Ok (Sc N) (r₂.inferIO d e) (r₁.inferIO d e)

theorem RecOK.ioView {N : Name → Prop} {r₁ r₂ : CoreFns CheckM} (h : RecOK N r₁ r₂) :
    RecOK N r₁.ioView r₂.ioView :=
  ⟨h.whnfCore, h.whnf, h.inferIO, h.defeq, h.annotate, h.inferIO⟩

end ConLeche.EnvExt
