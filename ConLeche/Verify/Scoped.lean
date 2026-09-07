import Lech.Verify.Fueled
import Lech.Verify.InferLemmas
import Lech.Verify.InferLeaves
import Lech.Verify.InferIOLeaves
import Lech.Verify.Abstract

/-!
# The cache-refinement bridge, part B₀: the scoped-call discipline

The memoized knot (`Lech/Kernel/TypeCheckerC.lean`) consults its
depth-free caches **without any runtime scope check**: this module
supplies the proof that makes that sound.  Two ingredients:

* `ScopedSim mode env f` — the *conditional* simulation: every cached
  entry-point run on a well-scoped argument is reproduced by the pure
  fueled family and preserves the cache invariant `CacheOK`.
  (`Lech/Verify/Bridge.lean` closes the knot induction.)
* the **call discipline**: every core body, run at the cached record on
  well-scoped inputs, only ever invokes the record on well-scoped
  arguments at the ambient depth.  This is proven by exhibiting the
  run as a run of the same body at the *guarded* verification-only
  record `gFns` (each entry wrapped in a `wscopedB` test that throws on
  violation): `DiscV` relates the two run-by-run, the site lemmas
  discharge the guards from the arguments' well-scopedness, and the
  per-body walks (`Lech/Verify/Disc.lean`) thread the scoping facts
  through every call site — the result-scoping of intermediate values
  comes from the conditional simulation plus the pure preservation
  lemmas (`whnfCore_WScoped` and friends).

The pair battery then applies to `(fueledFns, gFns f)` — related
*unconditionally* (`gFns_rel`: an ill-scoped entry throws, vacuously
related) — so the per-body simulation lemmas come for free, exactly as
before the guards were removed from the executable.
-/

set_option linter.unusedSimpArgs false

namespace Lech

variable {mode : CheckMode}

open Expr

/-! ## The cache invariant and the simulation relation -/

/-- Every cache entry is backed by a pure run at some fuel, at every
depth at which the key is well-scoped. -/
def CacheOK (mode : CheckMode) (env : Env) (σ : KCache) : Prop :=
  (∀ e r, σ.whnfCore[e]? = some r →
    ∃ F, ∀ d, e.wscopedB d = true → whnfCore mode env F d e = .ok r) ∧
  (∀ e r, σ.whnf[e]? = some r →
    ∃ F, ∀ d, e.wscopedB d = true → whnf mode env F d e = .ok r) ∧
  (∀ e r, σ.infer[e]? = some r →
    ∃ F, ∀ d, e.wscopedB d = true → inferTypeCore mode env F d e = .ok r) ∧
  (∀ a b r, σ.defeq[((a, b) : Expr × Expr)]? = some r →
    ∃ F, ∀ d, a.wscopedB d = true → b.wscopedB d = true →
      isDefEqCore mode env F d a b = .ok r) ∧
  (∀ e r, σ.annot[e]? = some r →
    ∃ F, ∀ d, e.wscopedB d = true → annotateCore mode env F d e = .ok r) ∧
  (∀ e r, σ.inferIO[e]? = some r →
    ∃ F, ∀ d, e.wscopedB d = true → inferTypeIO mode env F d e = .ok r)

theorem CacheOK.empty (env : Env) : CacheOK mode env {} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e r hl
    rw [Std.HashMap.getElem?_empty] at hl
    exact nomatch hl
  · intro e r hl
    rw [Std.HashMap.getElem?_empty] at hl
    exact nomatch hl
  · intro e r hl
    rw [Std.HashMap.getElem?_empty] at hl
    exact nomatch hl
  · intro a b r hl
    rw [Std.HashMap.getElem?_empty] at hl
    exact nomatch hl
  · intro e r hl
    rw [Std.HashMap.getElem?_empty] at hl
    exact nomatch hl
  · intro e r hl
    rw [Std.HashMap.getElem?_empty] at hl
    exact nomatch hl

/-- The simulation relation: from a backed cache, a successful cached
run yields a value backed by some pure fuel, and the cache stays
backed. -/
def simRel (mode : CheckMode) (env : Env) : MonadRel FueledM CheckSM where
  R p c := ∀ σ, CacheOK mode env σ → ∀ v σ', c σ = .ok (v, σ') →
    (∃ F, p.val F = .ok v) ∧ CacheOK mode env σ'
  pure_rel a := by
    intro σ hσ v σ' h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
    exact ⟨⟨0, rfl⟩, hσ⟩
  bind_rel {α β x₁ x₂ f₁ f₂} hx hf := by
    intro σ hσ v σ' h
    simp only [Bind.bind, StateT.bind] at h
    cases hx2 : x₂ σ with
    | error e =>
      rw [hx2] at h
      exact nomatch h
    | ok p =>
      obtain ⟨a, σ₁⟩ := p
      rw [hx2] at h
      dsimp only [Except.bind] at h
      obtain ⟨⟨F₁, hp1⟩, hσ₁⟩ := hx σ hσ a σ₁ hx2
      obtain ⟨⟨F₂, hp2⟩, hσ'⟩ := hf a σ₁ hσ₁ v σ' h
      refine ⟨⟨max F₁ F₂, ?_⟩, hσ'⟩
      rw [FueledM.atF_bind]
      simp only [Bind.bind]
      rw [x₁.property (Nat.le_max_left F₁ F₂) hp1]
      dsimp only [Except.bind]
      exact (f₁ a).property (Nat.le_max_right F₁ F₂) hp2
  throw_rel e := by
    intro σ hσ v σ' h
    exact nomatch h

/-! ## The conditional simulation and the guarded record -/

/-- The conditional (scoping-hypothesis-carrying) simulation of the
cached knot at one fuel by the fueled families: on *well-scoped*
arguments, every entry point is `simRel`-related.  (For ill-scoped
arguments no relation is claimed — the call discipline proves such
calls never happen.) -/
structure ScopedSim (mode : CheckMode) (env : Env) (f : Nat) : Prop where
  whnfCore : ∀ {d : Nat} {e : Expr}, e.wscopedB d = true →
    (simRel mode env).R ((fueledFns mode env).whnfCore d e)
      ((cachedFns mode env f).whnfCore d e)
  whnf : ∀ {d : Nat} {e : Expr}, e.wscopedB d = true →
    (simRel mode env).R ((fueledFns mode env).whnf d e)
      ((cachedFns mode env f).whnf d e)
  infer : ∀ {d : Nat} {e : Expr}, e.wscopedB d = true →
    (simRel mode env).R ((fueledFns mode env).infer d e)
      ((cachedFns mode env f).infer d e)
  defeq : ∀ {d : Nat} {a b : Expr}, a.wscopedB d = true →
    b.wscopedB d = true →
    (simRel mode env).R ((fueledFns mode env).defeq d a b)
      ((cachedFns mode env f).defeq d a b)
  annotate : ∀ {d : Nat} {e : Expr}, e.wscopedB d = true →
    (simRel mode env).R ((fueledFns mode env).annotate d e)
      ((cachedFns mode env f).annotate d e)
  /-- the io slot (task #172 B4): the memoized knot's `inferIO` entry
  simulates the fueled `inferTypeIO` family -/
  inferIO : ∀ {d : Nat} {e : Expr}, e.wscopedB d = true →
    (simRel mode env).R ((fueledFns mode env).inferIO d e)
      ((cachedFns mode env f).inferIO d e)

/-- The *guarded* twin of the cached record (verification-only): each
entry checks its argument's scoping and throws on violation.  The call
discipline exhibits every disciplined cached-body run as a run at this
record; the pair battery applies to it unconditionally (`gFns_rel`). -/
def gFns (mode : CheckMode) (env : Env) (f : Nat) : CoreFns CheckSM where
  whnfCore d e :=
    if e.wscopedB d then (cachedFns mode env f).whnfCore d e
    else throw (.internal "scope discipline")
  whnf d e :=
    if e.wscopedB d then (cachedFns mode env f).whnf d e
    else throw (.internal "scope discipline")
  infer d e :=
    if e.wscopedB d then (cachedFns mode env f).infer d e
    else throw (.internal "scope discipline")
  defeq d a b :=
    if a.wscopedB d && b.wscopedB d then (cachedFns mode env f).defeq d a b
    else throw (.internal "scope discipline")
  annotate d e :=
    if e.wscopedB d then (cachedFns mode env f).annotate d e
    else throw (.internal "scope discipline")
  inferIO d e :=
    if e.wscopedB d then (cachedFns mode env f).inferIO d e
    else throw (.internal "scope discipline")

theorem gFns_whnfCore_pos {env : Env} {f d : Nat} {e : Expr}
    (hg : e.wscopedB d = true) :
    (gFns mode env f).whnfCore d e = (cachedFns mode env f).whnfCore d e := by
  simp only [gFns]
  exact if_pos hg

theorem gFns_whnf_pos {env : Env} {f d : Nat} {e : Expr}
    (hg : e.wscopedB d = true) :
    (gFns mode env f).whnf d e = (cachedFns mode env f).whnf d e := by
  simp only [gFns]
  exact if_pos hg

theorem gFns_infer_pos {env : Env} {f d : Nat} {e : Expr}
    (hg : e.wscopedB d = true) :
    (gFns mode env f).infer d e = (cachedFns mode env f).infer d e := by
  simp only [gFns]
  exact if_pos hg

theorem gFns_defeq_pos {env : Env} {f d : Nat} {a b : Expr}
    (hga : a.wscopedB d = true) (hgb : b.wscopedB d = true) :
    (gFns mode env f).defeq d a b = (cachedFns mode env f).defeq d a b := by
  simp only [gFns]
  exact if_pos (by simp [hga, hgb])

theorem gFns_annotate_pos {env : Env} {f d : Nat} {e : Expr}
    (hg : e.wscopedB d = true) :
    (gFns mode env f).annotate d e = (cachedFns mode env f).annotate d e := by
  simp only [gFns]
  exact if_pos hg

theorem gFns_inferIO_pos {env : Env} {f d : Nat} {e : Expr}
    (hg : e.wscopedB d = true) :
    (gFns mode env f).inferIO d e = (cachedFns mode env f).inferIO d e := by
  simp only [gFns]
  exact if_pos hg

/-- The guarded record is `simRel`-related to the fueled families
*unconditionally*: on well-scoped arguments by the conditional
simulation, on ill-scoped ones vacuously (the guard throws). -/
theorem gFns_rel {env : Env} {f : Nat} (ih : ScopedSim mode env f) :
    FnsRel (simRel mode env) (fueledFns mode env) (gFns mode env f) := by
  refine ⟨fun d e => ?_, fun d e => ?_, fun d e => ?_, fun d a b => ?_,
    fun d e => ?_, fun d e => ?_⟩
  · by_cases hg : e.wscopedB d
    · rw [gFns_whnfCore_pos hg]
      exact ih.whnfCore hg
    · intro σ hσ v σ' h
      have hgg : (gFns mode env f).whnfCore d e =
          throw (.internal "scope discipline") := by
        simp only [gFns]
        exact if_neg hg
      rw [hgg] at h
      exact nomatch h
  · by_cases hg : e.wscopedB d
    · rw [gFns_whnf_pos hg]
      exact ih.whnf hg
    · intro σ hσ v σ' h
      have hgg : (gFns mode env f).whnf d e =
          throw (.internal "scope discipline") := by
        simp only [gFns]
        exact if_neg hg
      rw [hgg] at h
      exact nomatch h
  · by_cases hg : e.wscopedB d
    · rw [gFns_infer_pos hg]
      exact ih.infer hg
    · intro σ hσ v σ' h
      have hgg : (gFns mode env f).infer d e =
          throw (.internal "scope discipline") := by
        simp only [gFns]
        exact if_neg hg
      rw [hgg] at h
      exact nomatch h
  · by_cases hg : (a.wscopedB d && b.wscopedB d) = true
    · obtain ⟨hga, hgb⟩ := Bool.and_eq_true .. ▸ hg
      rw [gFns_defeq_pos hga hgb]
      exact ih.defeq hga hgb
    · intro σ hσ v σ' h
      have hgg : (gFns mode env f).defeq d a b =
          throw (.internal "scope discipline") := by
        simp only [gFns]
        exact if_neg (by simpa using hg)
      rw [hgg] at h
      exact nomatch h
  · by_cases hg : e.wscopedB d
    · rw [gFns_annotate_pos hg]
      exact ih.annotate hg
    · intro σ hσ v σ' h
      have hgg : (gFns mode env f).annotate d e =
          throw (.internal "scope discipline") := by
        simp only [gFns]
        exact if_neg hg
      rw [hgg] at h
      exact nomatch h
  · -- the io slot (task #172 B4), the same guard discipline
    by_cases hg : e.wscopedB d
    · rw [gFns_inferIO_pos hg]
      exact ih.inferIO hg
    · intro σ hσ v σ' h
      have hgg : (gFns mode env f).inferIO d e =
          throw (.internal "scope discipline") := by
        simp only [gFns]
        exact if_neg hg
      rw [hgg] at h
      exact nomatch h

/-! ## The discipline relation

`DiscV mode env P x g`: every successful run of the (real, unguarded) cached
computation `x` from a backed cache is reproduced verbatim by its
guarded twin `g`, keeps the cache backed, and its value satisfies `P`.
The value predicate is what carries the scoping of intermediate results
to later call sites in the body walks. -/

def DiscV (mode : CheckMode) (env : Env) {α : Type} (P : α → Prop) (x g : CheckSM α) : Prop :=
  ∀ σ, CacheOK mode env σ → ∀ v σ', x σ = .ok (v, σ') →
    g σ = .ok (v, σ') ∧ CacheOK mode env σ' ∧ P v

namespace DiscV

variable {env : Env}

protected theorem pure {α : Type} {P : α → Prop} {a : α} (h : P a) :
    DiscV mode env P (pure a) (pure a) := by
  intro σ hσ v σ' hr
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨rfl, hσ, h⟩

protected theorem throw {α : Type} {P : α → Prop} (e : CheckError) :
    DiscV mode env P (throw e) (throw e) := by
  intro σ hσ v σ' hr
  exact nomatch hr

protected theorem bind {α β : Type} {P : α → Prop} {Q : β → Prop}
    {x₁ g₁ : CheckSM α} {x₂ g₂ : α → CheckSM β}
    (hx : DiscV mode env P x₁ g₁)
    (hf : ∀ a, P a → DiscV mode env Q (x₂ a) (g₂ a)) :
    DiscV mode env Q (x₁ >>= x₂) (g₁ >>= g₂) := by
  intro σ hσ v σ' h
  simp only [Bind.bind, StateT.bind] at h ⊢
  cases hx1 : x₁ σ with
  | error e =>
    rw [hx1] at h
    exact nomatch h
  | ok p =>
    obtain ⟨a, σ₁⟩ := p
    rw [hx1] at h
    dsimp only [Except.bind] at h
    obtain ⟨hg1, hσ₁, hPa⟩ := hx σ hσ a σ₁ hx1
    rw [hg1]
    dsimp only [Except.bind]
    exact hf a hPa σ₁ hσ₁ v σ' h

/-- A conditional, branch by branch (for bodies too large for `split`'s
simp budget). -/
protected theorem ite {α : Type} {P : α → Prop} {c : Prop} [Decidable c]
    {x x' g g' : CheckSM α} (hx : c → DiscV mode env P x g)
    (hy : ¬ c → DiscV mode env P x' g') :
    DiscV mode env P (if c then x else x') (if c then g else g') := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

protected theorem mono {α : Type} {P Q : α → Prop} {x g : CheckSM α}
    (hPQ : ∀ a, P a → Q a) (h : DiscV mode env P x g) : DiscV mode env Q x g := by
  intro σ hσ v σ' hr
  obtain ⟨h1, h2, h3⟩ := h σ hσ v σ' hr
  exact ⟨h1, h2, hPQ v h3⟩

protected theorem liftFueled {α : Type} {P : α → Prop} (what : String)
    (o : Option α) (h : ∀ a, o = some a → P a) :
    DiscV mode env P (liftFueled what o) (liftFueled what o) := by
  cases o with
  | some a => exact DiscV.pure (h a rfl)
  | none => exact DiscV.throw _

protected theorem liftFueled_true {α : Type} (what : String)
    (o : Option α) :
    DiscV mode env (fun _ => True) (liftFueled what o) (liftFueled what o) :=
  DiscV.liftFueled what o (fun _ _ => trivial)

end DiscV

/-! ## Site lemmas: record calls on well-scoped arguments

Each lemma turns a well-scoped record call into its guarded twin and
supplies the result's scoping through the conditional simulation plus
the pure preservation lemmas. -/

section Sites

variable {env : Env} {f : Nat}

theorem ScopedSim.site_whnfCore (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d) ((cachedFns mode env f).whnfCore d e)
      ((gFns mode env f).whnfCore d e) := by
  intro σ hσ v σ' h
  rw [gFns_whnfCore_pos hw.to_wscopedB]
  obtain ⟨⟨F, hpure⟩, hσ'⟩ := ih.whnfCore hw.to_wscopedB σ hσ v σ' h
  exact ⟨h, hσ', whnfCore_WScoped henv F hpure hw⟩

theorem ScopedSim.site_whnf (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d) ((cachedFns mode env f).whnf d e)
      ((gFns mode env f).whnf d e) := by
  intro σ hσ v σ' h
  rw [gFns_whnf_pos hw.to_wscopedB]
  obtain ⟨⟨F, hpure⟩, hσ'⟩ := ih.whnf hw.to_wscopedB σ hσ v σ' h
  exact ⟨h, hσ', whnf_WScoped henv F hpure hw⟩

theorem ScopedSim.site_infer (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d) ((cachedFns mode env f).infer d e)
      ((gFns mode env f).infer d e) := by
  intro σ hσ v σ' h
  rw [gFns_infer_pos hw.to_wscopedB]
  obtain ⟨⟨F, hpure⟩, hσ'⟩ := ih.infer hw.to_wscopedB σ hσ v σ' h
  exact ⟨h, hσ', inferTypeCore_WScoped henv F hpure hw⟩

theorem ScopedSim.site_defeq (ih : ScopedSim mode env f)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV mode env (fun _ => True) ((cachedFns mode env f).defeq d a b)
      ((gFns mode env f).defeq d a b) := by
  intro σ hσ v σ' h
  rw [gFns_defeq_pos hwa.to_wscopedB hwb.to_wscopedB]
  obtain ⟨-, hσ'⟩ := ih.defeq hwa.to_wscopedB hwb.to_wscopedB σ hσ v σ' h
  exact ⟨h, hσ', trivial⟩

theorem ScopedSim.site_annotate (ih : ScopedSim mode env f)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d) ((cachedFns mode env f).annotate d e)
      ((gFns mode env f).annotate d e) := by
  intro σ hσ v σ' h
  rw [gFns_annotate_pos hw.to_wscopedB]
  obtain ⟨⟨F, hpure⟩, hσ'⟩ := ih.annotate hw.to_wscopedB σ hσ v σ' h
  exact ⟨h, hσ', annotateCore_WScoped F e hpure hw⟩

theorem ScopedSim.site_inferIO (ih : ScopedSim mode env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV mode env (WScoped d) ((cachedFns mode env f).inferIO d e)
      ((gFns mode env f).inferIO d e) := by
  intro σ hσ v σ' h
  rw [gFns_inferIO_pos hw.to_wscopedB]
  obtain ⟨⟨F, hpure⟩, hσ'⟩ := ih.inferIO hw.to_wscopedB σ hσ v σ' h
  exact ⟨h, hσ', inferTypeIO_WScoped henv F hpure hw⟩

end Sites

end Lech
