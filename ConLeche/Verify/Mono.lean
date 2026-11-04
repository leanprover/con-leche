module

public import ConLeche.Verify.PairM

public section

/-!
# Fuel monotonicity, via the relational pair monad

Instantiates `PairM` with success-refinement between two `CheckM`
computations; one induction at the knot yields fuel monotonicity for
every fueled entry point.
-/

namespace ConLeche

variable {mode : CheckMode} {eager : Bool}

/-- `q` succeeds wherever `p` succeeds, with the same value. -/
@[expose] def MRefines {α : Type} (p q : CheckM α) : Prop :=
  ∀ v, p = .ok v → q = .ok v

theorem MRefines.rfl {α : Type} {p : CheckM α} : MRefines p p := fun _ h => h

/-- Success refinement as a monad relation. -/
@[expose] def refinesRel : MonadRel CheckM CheckM where
  R := MRefines
  pure_rel _ := MRefines.rfl
  bind_rel {α β x₁ x₂ f₁ f₂} hx hf := by
    intro v h
    cases hx1 : x₁ with
    | error e =>
      rw [show (x₁ >>= f₁) = Except.bind x₁ f₁ from rfl, hx1] at h
      exact nomatch h
    | ok a =>
      rw [show (x₁ >>= f₁) = Except.bind x₁ f₁ from rfl, hx1] at h
      dsimp only [Except.bind] at h
      rw [show (x₂ >>= f₂) = Except.bind x₂ f₂ from rfl, hx a hx1]
      exact hf a v h
  throw_rel _ := fun _ h => nomatch h

/-- Componentwise refinement between two pure records. -/
abbrev FnsRefines (r₁ r₂ : CoreFns CheckM) : Prop :=
  FnsRel refinesRel r₁ r₂

section Mono

variable {r₁ r₂ : CoreFns CheckM} {env : Env}

/-! Per-body monotonicity, extracted from the pair instantiation. -/

theorem whnfCoreBody_mono (h : FnsRefines r₁ r₂) (c : Bool) (d : Nat) (e : Expr) :
    MRefines (whnfCoreBody mode r₁ env c d e) (whnfCoreBody mode r₂ env c d e) := by
  have := (whnfCoreBody mode (pairFns r₁ r₂ h) env c d e).property
  rwa [whnfCoreBody_fst_proj, whnfCoreBody_snd_proj] at this

theorem whnfBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (whnfBody r₁ env d e) (whnfBody r₂ env d e) := by
  have := (whnfBody (pairFns r₁ r₂ h) env d e).property
  rwa [whnfBody_fst_proj, whnfBody_snd_proj] at this

theorem inferBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (inferBody r₁ env d e) (inferBody r₂ env d e) := by
  have := (inferBody (pairFns r₁ r₂ h) env d e).property
  rwa [inferBody_fst_proj, inferBody_snd_proj] at this

theorem defeqBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (defeqBody mode eager r₁ env d a b) (defeqBody mode eager r₂ env d a b) := by
  have := (defeqBody mode eager (pairFns r₁ r₂ h) env d a b).property
  rwa [defeqBody_fst_proj, defeqBody_snd_proj] at this

theorem inferBodyIO_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (inferBodyIO r₁ env d e) (inferBodyIO r₂ env d e) := by
  have := (inferBodyIO (pairFns r₁ r₂ h) env d e).property
  rwa [inferBodyIO_fst_proj, inferBodyIO_snd_proj] at this

theorem ensureSort_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (ensureSort r₁ env d e) (ensureSort r₂ env d e) := by
  have := (ensureSort (pairFns r₁ r₂ h) env d e).property
  rwa [ensureSort_fst_proj, ensureSort_snd_proj] at this

end Mono

/-! ## Fuel monotonicity at the knot -/

/-- The knot induction, over both flags at once: the eager slot ties the
knot at `eager := true` (task #353). -/
private theorem pureFns_mono_all (env : Env) : ∀ {f f' : Nat}, f ≤ f' →
    ∀ (eager : Bool), FnsRefines (pureFns mode eager env f) (pureFns mode eager env f')
  | 0, f', _, eager => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c d e v hv
      rw [show (pureFns mode eager env 0).whnfCore c d e = whnfCore mode eager env 0 d e c from rfl,
        whnfCore_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d e v hv
      rw [show (pureFns mode eager env 0).whnf d e = whnf mode eager env 0 d e from rfl,
        whnf_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d e v hv
      rw [show (pureFns mode eager env 0).infer d e = inferTypeCore mode eager env 0 d e from rfl,
        inferTypeCore_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d a b v hv
      rw [show (pureFns mode eager env 0).defeq d a b = isDefEqCore mode eager env 0 d a b from rfl,
        isDefEqCore_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d a b v hv
      rw [show (pureFns mode eager env 0).defeqE d a b =
        throw (.internal "fuel exhausted: defeq") from rfl] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d e v hv
      rw [show (pureFns mode eager env 0).inferIO d e =
        throw (.internal "fuel exhausted: infer") from rfl] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
  | f + 1, f' + 1, hle, eager => by
    have ih := pureFns_mono_all env (Nat.le_of_succ_le_succ hle) eager
    have ihE := pureFns_mono_all env (Nat.le_of_succ_le_succ hle) true
    refine ⟨fun c d e => whnfCoreBody_mono ih c d e,
      fun d e => whnfBody_mono ih d e,
      fun d e => inferBody_mono ih d e,
      fun d a b => defeqBody_mono ih d a b,
      fun d a b => defeqBody_mono ihE d a b,
      fun d e => inferBodyIO_mono ih.ioView d e⟩

theorem pureFns_mono (env : Env) {f f' : Nat} (hle : f ≤ f') :
    FnsRefines (pureFns mode eager env f) (pureFns mode eager env f') :=
  pureFns_mono_all env hle eager

/-! ## Fueled corollaries -/

theorem whnfCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} {c : Bool} (h : whnfCore mode eager env f d e c = .ok r) :
    whnfCore mode eager env f' d e c = .ok r :=
  (pureFns_mono env hle).1 c d e r h

theorem whnf_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : whnf mode eager env f d e = .ok r) :
    whnf mode eager env f' d e = .ok r :=
  (pureFns_mono env hle).2.1 d e r h

theorem inferTypeCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : inferTypeCore mode eager env f d e = .ok r) :
    inferTypeCore mode eager env f' d e = .ok r :=
  (pureFns_mono env hle).2.2.1 d e r h

theorem isDefEqCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {a b : Expr} {r : Bool} (h : isDefEqCore mode eager env f d a b = .ok r) :
    isDefEqCore mode eager env f' d a b = .ok r :=
  (pureFns_mono env hle).2.2.2.1 d a b r h

/-- The full-grade argument check at a larger fuel (task #353: at the
argument's mode, `defeqArg_def`). -/
theorem defeqArg_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {a ta ty : Expr} {r : Bool}
    (h : defeqArg (pureFns mode eager env f) d a ta ty = .ok r) :
    defeqArg (pureFns mode eager env f') d a ta ty = .ok r := by
  rw [defeqArg_def] at h ⊢
  exact isDefEqCore_mono hle h

theorem inferTypeIO_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : inferTypeIO mode eager env f d e = .ok r) :
    inferTypeIO mode eager env f' d e = .ok r :=
  (pureFns_mono env hle).2.2.2.2.2 d e r h

theorem ensureSortCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e : Expr} {u : Level}
    (h : ensureSortCore mode eager env f d e = .ok u) :
    ensureSortCore mode eager env f' d e = .ok u := by
  cases f with
  | zero =>
    rw [show ensureSortCore mode eager env 0 d e =
      ensureSort (pureFns mode eager env 0) env d e from rfl] at h
    revert h
    unfold ensureSort
    rw [show (pureFns mode eager env 0).whnf d e = whnf mode eager env 0 d e from rfl, whnf_zero]
    intro h
    simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
  | succ f =>
    cases f' with
    | zero => exact absurd hle (by omega)
    | succ f' =>
      exact ensureSort_mono (pureFns_mono env hle) d e u h

end ConLeche
