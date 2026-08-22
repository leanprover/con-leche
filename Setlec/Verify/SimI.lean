import Setlec.Verify.IExprOps
import Setlec.Verify.Fueled
import Setlec.Verify.InferLeaves
import Setlec.Verify.InferLemmas
import Setlec.Verify.Abstract

/-!
# The interned-core faithfulness kit (task #26)

The relation and combinators for proving that the interned twin core
(`Setlec/Kernel/CoreI.lean`) simulates the pure fueled families under
the denotation:

* `ISOK env s` — the interned-state invariant: the arena is canonical
  (`EStore.WF`), the lazy stored-constant caches denote the
  level-instantiated stored data, and every entry-point memo entry is
  backed by a pure run at some fuel, valid at every depth at which the
  key is well-scoped (the `CacheOK` shape, transported along `denote`).
* `SimAt env s₀ P c p` — a successful interned run of `c` from `s₀`
  preserves `ISOK`, extends the arena, and produces a value `P`-related
  to a successful run of the fueled computation `p` at some fuel.
* `IEff env s₀ Q c` — a twin-only effect (interning, cache fill): no
  fueled counterpart, just invariant preservation plus a value fact.

The per-body walks (`Setlec/Verify/DiscI*.lean`) compose these; the
knot induction and the entry-point bridges are in
`Setlec/Verify/BridgeI.lean`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open EStore Expr

/-! ## The state invariant -/

/-- The interned-state invariant (see module docstring). -/
structure ISOK (env : Env) (s : IState) : Prop where
  wf : s.store.WF
  constTy : ∀ n us i, s.constTyAt[(n, us)]? = some i → ∃ ci,
    env.find? n = some ci ∧ s.store.denote i = some
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us)
  constVal : ∀ n us i, s.constValAt[(n, us)]? = some i → ∃ cv v h,
    env.find? n = some (.defnInfo cv v h) ∧ s.store.denote i = some
      (v.instantiateLevelParams cv.levelParams us)
  ruleRhs : ∀ c j us i, s.ruleRhsAt[(c, j, us)]? = some i →
    ∃ cv mI rP rules rl,
    env.find? c = some (.recInfo cv mI rP rules) ∧
    rules.find? (fun r' => r'.ctor == j) = some rl ∧
    s.store.denote i = some (rl.rhs.instantiateLevelParams cv.levelParams us)
  whnfCoreC : ∀ i j, s.whnfCoreC[i]? = some j → ∃ a b,
    s.store.denote i = some a ∧ s.store.denote j = some b ∧
    ∃ F, ∀ d, a.wscopedB d = true → whnfCore env F d a = .ok b
  whnfC : ∀ i j, s.whnfC[i]? = some j → ∃ a b,
    s.store.denote i = some a ∧ s.store.denote j = some b ∧
    ∃ F, ∀ d, a.wscopedB d = true → whnf env F d a = .ok b
  inferC : ∀ i j, s.inferC[i]? = some j → ∃ a b,
    s.store.denote i = some a ∧ s.store.denote j = some b ∧
    ∃ F, ∀ d, a.wscopedB d = true → inferTypeCore env F d a = .ok b
  annotC : ∀ i j, s.annotC[i]? = some j → ∃ a b,
    s.store.denote i = some a ∧ s.store.denote j = some b ∧
    ∃ F, ∀ d, a.wscopedB d = true → annotateCore env F d a = .ok b
  defeqC : ∀ i j r, s.defeqC[(i, j)]? = some r → ∃ a b,
    s.store.denote i = some a ∧ s.store.denote j = some b ∧
    ∃ F, ∀ d, a.wscopedB d = true → b.wscopedB d = true →
      isDefEqCore env F d a b = .ok r

/-- The invariant holds for a fresh state over any canonical arena
(all caches empty). -/
theorem ISOK.fresh (env : Env) {store : EStore} (hwf : store.WF) :
    ISOK env { store := store } := by
  refine ⟨hwf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intros; simp_all)

/-- Replacing the arena by a well-formed extension preserves the
invariant (all clauses only assert denotations, which are
`Ext`-stable). -/
theorem ISOK.withStore {env : Env} {s : IState} (h : ISOK env s)
    {st' : EStore} (hwf' : st'.WF) (hext : Ext s.store st') :
    ISOK env { s with store := st' } := by
  refine ⟨hwf', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n us i hl
    obtain ⟨ci, h1, h2⟩ := h.constTy n us i hl
    exact ⟨ci, h1, denote_mono hext h2⟩
  · intro n us i hl
    obtain ⟨cv, v, hh, h1, h2⟩ := h.constVal n us i hl
    exact ⟨cv, v, hh, h1, denote_mono hext h2⟩
  · intro c j us i hl
    obtain ⟨cv, mI, rP, rules, rl, h1, h2, h3⟩ := h.ruleRhs c j us i hl
    exact ⟨cv, mI, rP, rules, rl, h1, h2, denote_mono hext h3⟩
  · intro i j hl
    obtain ⟨a, b, h1, h2, h3⟩ := h.whnfCoreC i j hl
    exact ⟨a, b, denote_mono hext h1, denote_mono hext h2, h3⟩
  · intro i j hl
    obtain ⟨a, b, h1, h2, h3⟩ := h.whnfC i j hl
    exact ⟨a, b, denote_mono hext h1, denote_mono hext h2, h3⟩
  · intro i j hl
    obtain ⟨a, b, h1, h2, h3⟩ := h.inferC i j hl
    exact ⟨a, b, denote_mono hext h1, denote_mono hext h2, h3⟩
  · intro i j hl
    obtain ⟨a, b, h1, h2, h3⟩ := h.annotC i j hl
    exact ⟨a, b, denote_mono hext h1, denote_mono hext h2, h3⟩
  · intro i j r hl
    obtain ⟨a, b, h1, h2, h3⟩ := h.defeqC i j r hl
    exact ⟨a, b, denote_mono hext h1, denote_mono hext h2, h3⟩

/-! ## The simulation and effect relations -/

/-- A successful interned run from `s₀` preserves the invariant,
extends the arena, and its value is `P`-related (at the final state) to
the value of a successful fueled run. -/
def SimAt (env : Env) (s₀ : IState) {β α : Type}
    (P : IState → β → α → Prop) (c : CheckIM β) (p : FueledM α) : Prop :=
  ∀ v' s', c s₀ = .ok (v', s') →
    ISOK env s' ∧ Ext s₀.store s'.store ∧
    ∃ v, P s' v' v ∧ ∃ F, p.val F = .ok v

/-- A twin-only effect: invariant preservation, arena extension, and a
value fact — no fueled counterpart. -/
def IEff (env : Env) (s₀ : IState) {β : Type} (Q : IState → β → Prop)
    (c : CheckIM β) : Prop :=
  ∀ v' s', c s₀ = .ok (v', s') →
    ISOK env s' ∧ Ext s₀.store s'.store ∧ Q s' v'

/-- The result relation for expression-valued entry points: the index
denotes the fueled value, well-scoped at the ambient depth. -/
def RelE (d : Nat) (s : IState) (j : EIdx) (v : Expr) : Prop :=
  s.store.denote j = some v ∧ WScoped d v

/-- The result relation for `Bool`/`Level` and other data results. -/
def RelV {α : Type} (_s : IState) (b : α) (a : α) : Prop := b = a

/-- The result relation for optional expression results. -/
def RelO (d : Nat) (s : IState) : Option EIdx → Option Expr → Prop
  | none, none => True
  | some j, some v => RelE d s j v
  | _, _ => False

namespace SimAt

variable {env : Env} {s₀ : IState}

protected theorem pure {β α : Type} {P : IState → β → α → Prop}
    {b : β} {a : α} (hs : ISOK env s₀) (h : P s₀ b a) :
    SimAt env s₀ P (pure b) (pure a) := by
  intro v' s' hr
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hs, Ext.refl _, a, h, 0, rfl⟩

protected theorem throw {β α : Type} {P : IState → β → α → Prop}
    {e : CheckError} {p : FueledM α} :
    SimAt env s₀ P (throw e) p := by
  intro v' s' hr
  exact nomatch hr

/-- Bind: run the first components, hand the continuation the
intermediate state (with the invariant, the extension, and the value
relation). -/
protected theorem bind {β β' α α' : Type}
    {P : IState → β → α → Prop} {Q : IState → β' → α' → Prop}
    {c : CheckIM β} {k : β → CheckIM β'}
    {p : FueledM α} {q : α → FueledM α'}
    (hx : SimAt env s₀ P c p)
    (hf : ∀ s₁ b a, ISOK env s₁ → Ext s₀.store s₁.store → P s₁ b a →
      SimAt env s₁ Q (k b) (q a)) :
    SimAt env s₀ Q (c >>= k) (p >>= q) := by
  intro v' s' hr
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e => rw [hc] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, hext₁, a, hP, F₁, hp₁⟩ := hx b s₁ hc
    obtain ⟨hs', hext₂, a', hQ, F₂, hp₂⟩ := hf s₁ b a hs₁ hext₁ hP v' s' hr
    refine ⟨hs', hext₁.trans hext₂, a', hQ, max F₁ F₂, ?_⟩
    rw [FueledM.atF_bind]
    simp only [Bind.bind]
    rw [p.property (Nat.le_max_left F₁ F₂) hp₁]
    dsimp only [Except.bind]
    exact (q a).property (Nat.le_max_right F₁ F₂) hp₂

/-- Left bind: a twin-only effect before the simulated remainder. -/
protected theorem bind_left {β β' α : Type}
    {Q : IState → β → Prop} {P : IState → β' → α → Prop}
    {c : CheckIM β} {k : β → CheckIM β'} {p : FueledM α}
    (hx : IEff env s₀ Q c)
    (hf : ∀ s₁ b, ISOK env s₁ → Ext s₀.store s₁.store → Q s₁ b →
      SimAt env s₁ P (k b) p) :
    SimAt env s₀ P (c >>= k) p := by
  intro v' s' hr
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e => rw [hc] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, hext₁, hQ⟩ := hx b s₁ hc
    obtain ⟨hs', hext₂, a, hP, F, hp⟩ := hf s₁ b hs₁ hext₁ hQ v' s' hr
    exact ⟨hs', hext₁.trans hext₂, a, hP, F, hp⟩

/-- Peel a read (`viewI`): same state, value = the node lookup. -/
protected theorem view {β α : Type} {P : IState → β → α → Prop}
    {e : EIdx} {k : Option ENode → CheckIM β} {p : FueledM α}
    (h : SimAt env s₀ P (k s₀.store.nodes[e]?) p) :
    SimAt env s₀ P (viewI e >>= k) p := by
  intro v' s' hr
  apply h v' s'
  simpa only [viewI, Bind.bind, StateT.bind, Functor.map, StateT.map,
    get, getThe, MonadStateOf.get, StateT.get, Except.map, Except.bind,
    pure, StateT.pure, Except.pure] using hr

/-- Peel a read (`withStore`). -/
protected theorem withStore {β α γ : Type} {P : IState → β → α → Prop}
    {f : EStore → γ} {k : γ → CheckIM β} {p : FueledM α}
    (h : SimAt env s₀ P (k (f s₀.store)) p) :
    SimAt env s₀ P (Setlec.withStore f >>= k) p := by
  intro v' s' hr
  apply h v' s'
  simpa only [Setlec.withStore, Bind.bind, StateT.bind, Functor.map,
    StateT.map, get, getThe, MonadStateOf.get, StateT.get, Except.map,
    Except.bind, pure, StateT.pure, Except.pure] using hr

/-- Weaken the value relation. -/
protected theorem mono {β α : Type} {P Q : IState → β → α → Prop}
    {c : CheckIM β} {p : FueledM α}
    (hPQ : ∀ s b a, P s b a → Q s b a) (h : SimAt env s₀ P c p) :
    SimAt env s₀ Q c p := by
  intro v' s' hr
  obtain ⟨hs', hext, a, hP, F, hp⟩ := h v' s' hr
  exact ⟨hs', hext, a, hPQ s' v' a hP, F, hp⟩

protected theorem liftFueled {α : Type} (what : String) (o : Option α)
    (hs : ISOK env s₀) :
    SimAt env s₀ RelV (liftFueled what o) (liftFueled what o) := by
  cases o with
  | some a => exact SimAt.pure hs rfl
  | none => exact SimAt.throw

end SimAt

namespace IEff

variable {env : Env} {s₀ : IState}

protected theorem pure {β : Type} {Q : IState → β → Prop} {b : β}
    (hs : ISOK env s₀) (h : Q s₀ b) : IEff env s₀ Q (pure b) := by
  intro v' s' hr
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hs, Ext.refl _, h⟩

protected theorem throw {β : Type} {Q : IState → β → Prop}
    {e : CheckError} : IEff env s₀ Q (throw e) := by
  intro v' s' hr
  exact nomatch hr

protected theorem bind {β β' : Type} {Q : IState → β → Prop}
    {R : IState → β' → Prop} {c : CheckIM β} {k : β → CheckIM β'}
    (hx : IEff env s₀ Q c)
    (hf : ∀ s₁ b, ISOK env s₁ → Ext s₀.store s₁.store → Q s₁ b →
      IEff env s₁ R (k b)) :
    IEff env s₀ R (c >>= k) := by
  intro v' s' hr
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e => rw [hc] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, hext₁, hQ⟩ := hx b s₁ hc
    obtain ⟨hs', hext₂, hR⟩ := hf s₁ b hs₁ hext₁ hQ v' s' hr
    exact ⟨hs', hext₁.trans hext₂, hR⟩

protected theorem view {β : Type} {Q : IState → β → Prop}
    {e : EIdx} {k : Option ENode → CheckIM β}
    (h : IEff env s₀ Q (k s₀.store.nodes[e]?)) :
    IEff env s₀ Q (viewI e >>= k) := by
  intro v' s' hr
  apply h v' s'
  simpa only [viewI, Bind.bind, StateT.bind, Functor.map, StateT.map,
    get, getThe, MonadStateOf.get, StateT.get, Except.map, Except.bind,
    pure, StateT.pure, Except.pure] using hr

protected theorem withStore {β γ : Type} {Q : IState → β → Prop}
    {f : EStore → γ} {k : γ → CheckIM β}
    (h : IEff env s₀ Q (k (f s₀.store))) :
    IEff env s₀ Q (Setlec.withStore f >>= k) := by
  intro v' s' hr
  apply h v' s'
  simpa only [Setlec.withStore, Bind.bind, StateT.bind, Functor.map,
    StateT.map, get, getThe, MonadStateOf.get, StateT.get, Except.map,
    Except.bind, pure, StateT.pure, Except.pure] using hr

end IEff

/-! ## Effect specs for the store helpers -/

section Effects

variable {env : Env} {s₀ : IState}

private theorem internI_run (n : ENode) (s : IState) :
    internI n s = .ok ((s.store.intern n).1,
      { s with store := (s.store.intern n).2 }) := rfl

private theorem internExprM_run (x : Expr) (s : IState) :
    internExprM x s = .ok ((s.store.internExpr x).1,
      { s with store := (s.store.internExpr x).2 }) := rfl

private theorem inst1M_run (e v : EIdx) (d : Nat) (s : IState) :
    inst1M e v d s = .ok ((s.store.instantiate1I e v d).1,
      { s with store := (s.store.instantiate1I e v d).2 }) := rfl

private theorem abstract1M_run (e : EIdx) (d : Nat) (s : IState) :
    abstract1M e d s = .ok ((s.store.abstract1I e d).1,
      { s with store := (s.store.abstract1I e d).2 }) := rfl

private theorem mkAppNM_run (f : EIdx) (args : List EIdx) (s : IState) :
    mkAppNM f args s = .ok ((s.store.mkAppNI f args).1,
      { s with store := (s.store.mkAppNI f args).2 }) := rfl

private theorem instSpineM_run (args : List EIdx) (t : Nat) (e : EIdx)
    (s : IState) :
    instSpineM args t e s = .ok ((s.store.instSpineI args t e).1,
      { s with store := (s.store.instSpineI args t e).2 }) := rfl

private theorem piResidualM_run (e : EIdx) (args : List EIdx) (s : IState) :
    piResidualM e args s = .ok ((s.store.piResidualI e args).1,
      { s with store := (s.store.piResidualI e args).2 }) := rfl

private theorem pisToLamsM_run (k : Nat) (e body : EIdx) (s : IState) :
    pisToLamsM k e body s = .ok ((s.store.pisToLamsI k e body).1,
      { s with store := (s.store.pisToLamsI k e body).2 }) := rfl

theorem internI_eff (hs : ISOK env s₀) {n : ENode} {x : Expr}
    (hd : denoteNode s₀.store.denote n = some x) :
    IEff env s₀ (fun s i => s.store.denote i = some x) (internI n) := by
  intro v' s' hr
  rw [internI_run] at hr
  obtain ⟨hwf', hext, hden⟩ := intern_spec hs.wf hd
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem internExprM_eff (hs : ISOK env s₀) (x : Expr) :
    IEff env s₀ (fun s i => s.store.denote i = some x) (internExprM x) := by
  intro v' s' hr
  rw [internExprM_run] at hr
  obtain ⟨hwf', hext, hden⟩ := internExpr_spec hs.wf x
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem inst1M_eff (hs : ISOK env s₀) {e v : EIdx} {d : Nat} {a w : Expr}
    (he : s₀.store.denote e = some a) (hv : s₀.store.denote v = some w) :
    IEff env s₀ (fun s i => s.store.denote i = some (a.instantiate1 w d))
      (inst1M e v d) := by
  intro v' s' hr
  rw [inst1M_run] at hr
  obtain ⟨hwf', hext, hden⟩ := instantiate1I_spec (d := d) hs.wf he hv
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem abstract1M_eff (hs : ISOK env s₀) {e : EIdx} {d : Nat} {a : Expr}
    (he : s₀.store.denote e = some a) :
    IEff env s₀ (fun s i => s.store.denote i = some (a.abstract1 d))
      (abstract1M e d) := by
  intro v' s' hr
  rw [abstract1M_run] at hr
  obtain ⟨hwf', hext, hden⟩ := abstract1I_spec (k := 0) hs.wf he
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem mkAppNM_eff (hs : ISOK env s₀) {f : EIdx} {args : List EIdx}
    {x : Expr} {xs : List Expr}
    (hf : s₀.store.denote f = some x) (hargs : DenL s₀.store args xs) :
    IEff env s₀ (fun s i => s.store.denote i = some (Expr.mkAppN x xs))
      (mkAppNM f args) := by
  intro v' s' hr
  rw [mkAppNM_run] at hr
  obtain ⟨hwf', hext, hden⟩ := mkAppNI_spec hs.wf hf hargs
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem instSpineM_eff (hs : ISOK env s₀) {args : List EIdx} {t : Nat}
    {e : EIdx} {x : Expr} {xs : List Expr}
    (he : s₀.store.denote e = some x) (hargs : DenL s₀.store args xs) :
    IEff env s₀ (fun s i => s.store.denote i = some (Expr.instSpine xs t x))
      (instSpineM args t e) := by
  intro v' s' hr
  rw [instSpineM_run] at hr
  obtain ⟨hwf', hext, hden⟩ := instSpineI_spec hs.wf he hargs
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem piResidualM_eff (hs : ISOK env s₀) {e : EIdx} {args : List EIdx}
    {x : Expr} {xs : List Expr}
    (he : s₀.store.denote e = some x) (hargs : DenL s₀.store args xs) :
    IEff env s₀ (fun s o => OptDen s.store o (piResidual x xs))
      (piResidualM e args) := by
  intro v' s' hr
  rw [piResidualM_run] at hr
  obtain ⟨hwf', hext, hden⟩ := piResidualI_spec hs.wf he hargs
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem pisToLamsM_eff (hs : ISOK env s₀) {k : Nat} {e body : EIdx}
    {x xb : Expr}
    (he : s₀.store.denote e = some x) (hb : s₀.store.denote body = some xb) :
    IEff env s₀ (fun s o => OptDen s.store o (Expr.pisToLams k x xb))
      (pisToLamsM k e body) := by
  intro v' s' hr
  rw [pisToLamsM_run] at hr
  obtain ⟨hwf', hext, hden⟩ := pisToLamsI_spec (k := k) hs.wf he hb
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

end Effects

/-! ## Cache-fill effects (the lazy stored-constant caches) -/

section CacheFill

variable {env : Env} {s₀ : IState}

private theorem get_run (s : IState) : (get : CheckIM IState) s = .ok (s, s) := rfl

private theorem modify_run (f : IState → IState) (s : IState) :
    (modify f : CheckIM Unit) s = .ok ((), f s) := rfl

/-- Inserting a backed entry into `constTyAt` preserves the invariant. -/
theorem ISOK.insertConstTy {s : IState} (hs : ISOK env s)
    {n : Name} {us : List Level} {i : EIdx} {ci : ConstantInfo}
    (hfind : env.find? n = some ci)
    (hden : s.store.denote i = some
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us)) :
    ISOK env { s with constTyAt := s.constTyAt.insert (n, us) i } := by
  refine ⟨hs.wf, ?_, hs.constVal, hs.ruleRhs, hs.whnfCoreC, hs.whnfC,
    hs.inferC, hs.annotC, hs.defeqC⟩
  intro n' us' i' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((n, us) : Name × List Level) == (n', us')
  · rw [if_pos hk] at hl
    obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := by
      have := eq_of_beq hk
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    cases hl
    exact ⟨ci, hfind, hden⟩
  · rw [if_neg hk] at hl
    exact hs.constTy n' us' i' hl

/-- Inserting a backed entry into `constValAt` preserves the invariant. -/
theorem ISOK.insertConstVal {s : IState} (hs : ISOK env s)
    {n : Name} {us : List Level} {i : EIdx} {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hfind : env.find? n = some (.defnInfo cv v hint))
    (hden : s.store.denote i = some
      (v.instantiateLevelParams cv.levelParams us)) :
    ISOK env { s with constValAt := s.constValAt.insert (n, us) i } := by
  refine ⟨hs.wf, hs.constTy, ?_, hs.ruleRhs, hs.whnfCoreC, hs.whnfC,
    hs.inferC, hs.annotC, hs.defeqC⟩
  intro n' us' i' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((n, us) : Name × List Level) == (n', us')
  · rw [if_pos hk] at hl
    obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := by
      have := eq_of_beq hk
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    cases hl
    exact ⟨cv, v, hint, hfind, hden⟩
  · rw [if_neg hk] at hl
    exact hs.constVal n' us' i' hl

/-- Inserting a backed entry into `ruleRhsAt` preserves the invariant. -/
theorem ISOK.insertRuleRhs {s : IState} (hs : ISOK env s)
    {c j : Name} {us : List Level} {i : EIdx} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {rl : RecRule}
    (hfind : env.find? c = some (.recInfo cv mI rP rules))
    (hrl : rules.find? (fun r' => r'.ctor == j) = some rl)
    (hden : s.store.denote i = some
      (rl.rhs.instantiateLevelParams cv.levelParams us)) :
    ISOK env { s with ruleRhsAt := s.ruleRhsAt.insert (c, j, us) i } := by
  refine ⟨hs.wf, hs.constTy, hs.constVal, ?_, hs.whnfCoreC, hs.whnfC,
    hs.inferC, hs.annotC, hs.defeqC⟩
  intro c' j' us' i' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((c, j, us) : Name × Name × List Level) == (c', j', us')
  · rw [if_pos hk] at hl
    obtain ⟨rfl, rfl, rfl⟩ : c = c' ∧ j = j' ∧ us = us' := by
      have := eq_of_beq hk
      exact ⟨congrArg Prod.fst this, congrArg (·.2.1) this,
        congrArg (·.2.2) this⟩
    cases hl
    exact ⟨cv, mI, rP, rules, rl, hfind, hrl, hden⟩
  · rw [if_neg hk] at hl
    exact hs.ruleRhs c' j' us' i' hl

/-- `constTyAtM` under the index of `env`: the result denotes the
level-instantiated stored type. -/
theorem constTyAtM_eff (hs : ISOK env s₀) {n : Name} {us : List Level}
    {ci : ConstantInfo} (hfind : env.find? n = some ci) :
    IEff env s₀ (fun s i => s.store.denote i = some
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us))
      (constTyAtM (mkFEnv env) n us) := by
  intro v' s' hr
  rw [show constTyAtM (mkFEnv env) n us = (do
      match (← get).constTyAt[(n, us)]? with
      | some i => pure i
      | none =>
        match (mkFEnv env).find? n with
        | some ci =>
          let cv := ci.toConstantVal
          let i ← internExprM
            (cv.type.instantiateLevelParams cv.levelParams us)
          modify fun s =>
            let mp := s.constTyAt
            let s := { s with constTyAt := ∅ }
            { s with constTyAt := mp.insert (n, us) i }
          pure i
        | none => throw (.internal "constTyAtM: unknown constant") :
        CheckIM EIdx) from rfl] at hr
  simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, pure, Except.pure] at hr
  cases hl : s₀.constTyAt[(n, us)]? with
  | some i =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨ci', hfind', hden⟩ := hs.constTy n us _ hl
    rw [hfind] at hfind'
    cases hfind'
    exact ⟨hs, Ext.refl _, hden⟩
  | none =>
    rw [hl] at hr
    rw [mkFEnv_find?, hfind] at hr
    dsimp only at hr
    simp only [Bind.bind, StateT.bind, Except.bind] at hr
    cases hrun : internExprM (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) s₀ with
    | error he => rw [hrun] at hr; exact nomatch hr
    | ok pr =>
      obtain ⟨i, s₁⟩ := pr
      rw [hrun] at hr
      dsimp only at hr
      obtain ⟨hs₁, hext₁, hden⟩ := internExprM_eff hs _ i s₁ hrun
      simp only [modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, Bind.bind, StateT.bind, Except.bind, pure,
        StateT.pure, Except.pure, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      exact ⟨hs₁.insertConstTy hfind hden, hext₁, hden⟩

/-- `constValAtM` under the index of `env`. -/
theorem constValAtM_eff (hs : ISOK env s₀) {n : Name} {us : List Level}
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hfind : env.find? n = some (.defnInfo cv v hint)) :
    IEff env s₀ (fun s i => s.store.denote i = some
        (v.instantiateLevelParams cv.levelParams us))
      (constValAtM (mkFEnv env) n us) := by
  intro v' s' hr
  rw [show constValAtM (mkFEnv env) n us = (do
      match (← get).constValAt[(n, us)]? with
      | some i => pure i
      | none =>
        match (mkFEnv env).find? n with
        | some (.defnInfo cv v _) =>
          let i ← internExprM (v.instantiateLevelParams cv.levelParams us)
          modify fun s =>
            let mp := s.constValAt
            let s := { s with constValAt := ∅ }
            { s with constValAt := mp.insert (n, us) i }
          pure i
        | _ => throw (.internal "constValAtM: not a stored definition") :
        CheckIM EIdx) from rfl] at hr
  simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, pure, Except.pure] at hr
  cases hl : s₀.constValAt[(n, us)]? with
  | some i =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨cv', v'', hint', hfind', hden⟩ := hs.constVal n us _ hl
    rw [hfind] at hfind'
    cases hfind'
    exact ⟨hs, Ext.refl _, hden⟩
  | none =>
    rw [hl] at hr
    rw [mkFEnv_find?, hfind] at hr
    dsimp only at hr
    simp only [Bind.bind, StateT.bind, Except.bind] at hr
    cases hrun : internExprM (v.instantiateLevelParams cv.levelParams us) s₀
        with
    | error he => rw [hrun] at hr; exact nomatch hr
    | ok pr =>
      obtain ⟨i, s₁⟩ := pr
      rw [hrun] at hr
      dsimp only at hr
      obtain ⟨hs₁, hext₁, hden⟩ := internExprM_eff hs _ i s₁ hrun
      simp only [modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, Bind.bind, StateT.bind, Except.bind, pure,
        StateT.pure, Except.pure, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      exact ⟨hs₁.insertConstVal hfind hden, hext₁, hden⟩

/-- `ruleRhsAtM` under the index of `env`. -/
theorem ruleRhsAtM_eff (hs : ISOK env s₀) {c j : Name} {us : List Level}
    {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule} {rl : RecRule}
    (hfind : env.find? c = some (.recInfo cv mI rP rules))
    (hrl : rules.find? (fun r' => r'.ctor == j) = some rl) :
    IEff env s₀ (fun s i => s.store.denote i = some
        (rl.rhs.instantiateLevelParams cv.levelParams us))
      (ruleRhsAtM (mkFEnv env) c j us) := by
  intro v' s' hr
  rw [show ruleRhsAtM (mkFEnv env) c j us = (do
      match (← get).ruleRhsAt[(c, j, us)]? with
      | some i => pure i
      | none =>
        match (mkFEnv env).find? c with
        | some (.recInfo cv _ _ rules) =>
          match rules.find? (fun r' => r'.ctor == j) with
          | some rl =>
            let i ← internExprM
              (rl.rhs.instantiateLevelParams cv.levelParams us)
            modify fun s =>
              let mp := s.ruleRhsAt
              let s := { s with ruleRhsAt := ∅ }
              { s with ruleRhsAt := mp.insert (c, j, us) i }
            pure i
          | none => throw (.internal "ruleRhsAtM: no rule for constructor")
        | _ => throw (.internal "ruleRhsAtM: not a stored recursor") :
        CheckIM EIdx) from rfl] at hr
  simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, Except.bind, pure, Except.pure] at hr
  cases hl : s₀.ruleRhsAt[(c, j, us)]? with
  | some i =>
    rw [hl] at hr
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
    obtain ⟨cv', mI', rP', rules', rl', hfind', hrl', hden⟩ :=
      hs.ruleRhs c j us _ hl
    rw [hfind] at hfind'
    cases hfind'
    rw [hrl] at hrl'
    cases hrl'
    exact ⟨hs, Ext.refl _, hden⟩
  | none =>
    rw [hl] at hr
    rw [mkFEnv_find?, hfind] at hr
    dsimp only at hr
    rw [hrl] at hr
    dsimp only at hr
    simp only [Bind.bind, StateT.bind, Except.bind] at hr
    cases hrun : internExprM (rl.rhs.instantiateLevelParams
        cv.levelParams us) s₀ with
    | error he => rw [hrun] at hr; exact nomatch hr
    | ok pr =>
      obtain ⟨i, s₁⟩ := pr
      rw [hrun] at hr
      dsimp only at hr
      obtain ⟨hs₁, hext₁, hden⟩ := internExprM_eff hs _ i s₁ hrun
      simp only [modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, Bind.bind, StateT.bind, Except.bind, pure,
        StateT.pure, Except.pure, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      exact ⟨hs₁.insertRuleRhs hfind hrl hden, hext₁, hden⟩

end CacheFill

end Setlec
