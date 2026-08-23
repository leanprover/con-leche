import Setlec.Verify.IExprOps
import Setlec.Verify.ILevel
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

/-- The interned-state invariant (see module docstring).  The lazy
stored-constant caches are keyed by level-*index* lists; each entry
carries the denotation of its key (task #62). -/
structure ISOK (env : Env) (s : IState) : Prop where
  wf : s.store.WF
  constTy : ∀ n us i, s.constTyAt[(n, us)]? = some i → ∃ lus ci,
    denoteLList s.store.denoteL us = some lus ∧
    env.find? n = some ci ∧ s.store.denote i = some
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams lus)
  constVal : ∀ n us i, s.constValAt[(n, us)]? = some i → ∃ lus cv v h,
    denoteLList s.store.denoteL us = some lus ∧
    (env.find? n = some (.defnInfo cv v h) ∨
      env.find? n = some (.thmInfo cv v)) ∧ s.store.denote i = some
      (v.instantiateLevelParams cv.levelParams lus)
  ruleRhs : ∀ c j us i, s.ruleRhsAt[(c, j, us)]? = some i →
    ∃ lus cv mI rP rules rl,
    denoteLList s.store.denoteL us = some lus ∧
    env.find? c = some (.recInfo cv mI rP rules) ∧
    rules.find? (fun r' => r'.ctor == j) = some rl ∧
    s.store.denote i = some (rl.rhs.instantiateLevelParams cv.levelParams lus)
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
  lsimp : LvlMemoInv s.store Level.simplify s.lsimpC
  lnz : LvlQMemoInv s.store Level.isNonZero s.lnzC
  eqv : EqvMemoInv s.store s.eqvC
  bvarB : EStore.BoundMemoInv s.store s.bvarB
  /-- The interned environment is self-certifying (task #78): each
  entry's indices denote exactly its tags — the invariant never
  mentions `env`, so it survives arena extension, every flush and
  every environment transition. -/
  ienv : ∀ (nm : Name) (ent : IConstE), s.ienv[nm]? = some ent →
    s.store.denote ent.ty = some ent.tyE ∧
    ∀ vE vi, ent.val = some (vE, vi) → s.store.denote vi = some vE

/-- The invariant holds for a fresh state over any canonical arena
(all caches empty). -/
theorem ISOK.fresh (env : Env) {store : EStore} (hwf : store.WF) :
    ISOK env { store := store } := by
  refine ⟨hwf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | exact LvlMemoInv.empty
      | exact LvlQMemoInv.empty
      | exact EqvMemoInv.empty
      | exact EStore.BoundMemoInv.empty
      | (intros; simp_all)

/-- The environment-free residue of the invariant: exactly the clauses
`flushS` preserves (task #78) — arena canonicity, the level-operation
caches, the bound cache and the self-certifying interned environment.
None of them mentions the environment, so the residue crosses every
environment transition and every declaration boundary. -/
structure ISOKF (s : IState) : Prop where
  wf : s.store.WF
  lsimp : LvlMemoInv s.store Level.simplify s.lsimpC
  lnz : LvlQMemoInv s.store Level.isNonZero s.lnzC
  eqv : EqvMemoInv s.store s.eqvC
  bvarB : EStore.BoundMemoInv s.store s.bvarB
  ienv : ∀ (nm : Name) (ent : IConstE), s.ienv[nm]? = some ent →
    s.store.denote ent.ty = some ent.tyE ∧
    ∀ vE vi, ent.val = some (vE, vi) → s.store.denote vi = some vE

/-- Every invariant state carries the residue. -/
theorem ISOK.residue {env : Env} {s : IState} (h : ISOK env s) : ISOKF s :=
  ⟨h.wf, h.lsimp, h.lnz, h.eqv, h.bvarB, h.ienv⟩

/-- A fresh state over a canonical arena carries the residue. -/
theorem ISOKF.fresh {store : EStore} (hwf : store.WF) :
    ISOKF { store := store } := by
  refine ⟨hwf, LvlMemoInv.empty, LvlQMemoInv.empty, EqvMemoInv.empty,
    EStore.BoundMemoInv.empty, ?_⟩
  intro nm ent h
  simp at h

/-- Replacing the arena by a well-formed extension preserves the
invariant (all clauses only assert denotations, which are
`Ext`-stable). -/
theorem ISOK.withStore {env : Env} {s : IState} (h : ISOK env s)
    {st' : EStore} (hwf' : st'.WF) (hext : Ext s.store st') :
    ISOK env { s with store := st' } := by
  refine ⟨hwf', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n us i hl
    obtain ⟨lus, ci, h0, h1, h2⟩ := h.constTy n us i hl
    exact ⟨lus, ci, denoteLList_mono hext h0, h1, denote_mono hext h2⟩
  · intro n us i hl
    obtain ⟨lus, cv, v, hh, h0, h1, h2⟩ := h.constVal n us i hl
    exact ⟨lus, cv, v, hh, denoteLList_mono hext h0, h1,
      denote_mono hext h2⟩
  · intro c j us i hl
    obtain ⟨lus, cv, mI, rP, rules, rl, h0, h1, h2, h3⟩ :=
      h.ruleRhs c j us i hl
    exact ⟨lus, cv, mI, rP, rules, rl, denoteLList_mono hext h0, h1, h2,
      denote_mono hext h3⟩
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
  · exact h.lsimp.mono hext
  · exact h.lnz.mono hext
  · exact h.eqv.mono hext
  · exact h.bvarB.mono hext h.wf
  · intro nm ent hl
    obtain ⟨hty, hval⟩ := h.ienv nm ent hl
    exact ⟨denote_mono hext hty,
      fun vE vi hv => denote_mono hext (hval vE vi hv)⟩

/-- Replacing the arena and the simplify memo together (the
`simplifyLM`/`isEquivLM` wrappers). -/
theorem ISOK.withStoreLsimp {env : Env} {s : IState} (h : ISOK env s)
    {st' : EStore} {m' : EStore.LMemo} (hwf' : st'.WF)
    (hext : Ext s.store st')
    (hinv' : LvlMemoInv st' Level.simplify m') :
    ISOK env { s with store := st', lsimpC := m' } := by
  have base := h.withStore hwf' hext
  exact ⟨base.wf, base.constTy, base.constVal, base.ruleRhs,
    base.whnfCoreC, base.whnfC, base.inferC, base.annotC, base.defeqC,
    hinv', base.lnz, base.eqv, base.bvarB, base.ienv⟩

/-- Replacing the `isNonZero` memo (the `isNonZeroLM` wrapper; the
arena is untouched). -/
theorem ISOK.withLnz {env : Env} {s : IState} (h : ISOK env s)
    {m' : Std.HashMap LIdx Bool}
    (hinv' : LvlQMemoInv s.store Level.isNonZero m') :
    ISOK env { s with lnzC := m' } :=
  ⟨h.wf, h.constTy, h.constVal, h.ruleRhs, h.whnfCoreC, h.whnfC,
    h.inferC, h.annotC, h.defeqC, h.lsimp, hinv', h.eqv, h.bvarB, h.ienv⟩

/-- Replacing the loose-bvar-bound cache (the `bvarBoundM` wrapper;
the arena is untouched, task #72). -/
theorem ISOK.withBvarB {env : Env} {s : IState} (h : ISOK env s)
    {m' : EStore.BMemo}
    (hinv' : EStore.BoundMemoInv s.store m') :
    ISOK env { s with bvarB := m' } :=
  ⟨h.wf, h.constTy, h.constVal, h.ruleRhs, h.whnfCoreC, h.whnfC,
    h.inferC, h.annotC, h.defeqC, h.lsimp, h.lnz, h.eqv, hinv', h.ienv⟩

/-- Replacing the arena, the simplify memo and the equivalence result
cache together (the `isEquivLM` wrapper). -/
theorem ISOK.withStoreLsimpEqv {env : Env} {s : IState} (h : ISOK env s)
    {st' : EStore} {m' : EStore.LMemo}
    {ec' : Std.HashMap (LIdx × LIdx) Bool} (hwf' : st'.WF)
    (hext : Ext s.store st')
    (hinv' : LvlMemoInv st' Level.simplify m')
    (heqv' : EqvMemoInv st' ec') :
    ISOK env { s with store := st', lsimpC := m', eqvC := ec' } := by
  have base := h.withStore hwf' hext
  exact ⟨base.wf, base.constTy, base.constVal, base.ruleRhs,
    base.whnfCoreC, base.whnfC, base.inferC, base.annotC, base.defeqC,
    hinv', base.lnz, heqv', base.bvarB, base.ienv⟩

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

/-- The result relation for `Bool` and other data results. -/
def RelV {α : Type} (_s : IState) (b : α) (a : α) : Prop := b = a

/-- The result relation for level results: the index denotes the
fueled value (task #62). -/
def RelL (s : IState) (u : LIdx) (l : Level) : Prop :=
  s.store.denoteL u = some l

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

/-- Peel a pure value bound on the twin side. -/
protected theorem bind_pure_left {β β' α : Type}
    {P : IState → β' → α → Prop} {c : β} {k : β → CheckIM β'}
    {p : FueledM α}
    (h : SimAt env s₀ P (k c) p) :
    SimAt env s₀ P (pure c >>= k) p := by
  intro v' s' hr
  apply h v' s'
  simpa only [Bind.bind, StateT.bind, pure, StateT.pure, Except.pure,
    Except.bind] using hr

/-- Peel a pure value bound on the fueled side. -/
protected theorem bind_pure_right {β α α' : Type}
    {P : IState → β → α' → Prop} {c : CheckIM β} {a : α}
    {k : α → FueledM α'}
    (h : SimAt env s₀ P c (k a)) :
    SimAt env s₀ P c (pure a >>= k) := by
  intro v' s' hr
  obtain ⟨hs', hext, v, hP, F, hp⟩ := h v' s' hr
  exact ⟨hs', hext, v, hP, F, hp⟩

/-- A twin-side `throw` composed with anything never succeeds. -/
protected theorem throw_bind {β β' α : Type}
    {P : IState → β' → α → Prop} {er : CheckError}
    {k : β → CheckIM β'} {p : FueledM α} :
    SimAt env s₀ P ((throw er : CheckIM β) >>= k) p := by
  intro v' s' hr
  exact nomatch hr

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

/-- Bind that *remembers* the first component's fueled run: the
continuation may consume the existence of a successful pure run
(task #72: the binder-loop compositions seed the chained tails' domain
facts from the walked pre-checks). -/
protected theorem bindR {β β' α α' : Type}
    {P : IState → β → α → Prop} {Q : IState → β' → α' → Prop}
    {c : CheckIM β} {k : β → CheckIM β'}
    {p : FueledM α} {q : α → FueledM α'}
    (hx : SimAt env s₀ P c p)
    (hf : ∀ s₁ b a, ISOK env s₁ → Ext s₀.store s₁.store → P s₁ b a →
      (∃ F, p.val F = .ok a) → SimAt env s₁ Q (k b) (q a)) :
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
    obtain ⟨hs', hext₂, a', hQ, F₂, hp₂⟩ :=
      hf s₁ b a hs₁ hext₁ hP ⟨F₁, hp₁⟩ v' s' hr
    refine ⟨hs', hext₁.trans hext₂, a', hQ, max F₁ F₂, ?_⟩
    rw [FueledM.atF_bind]
    simp only [Bind.bind]
    rw [p.property (Nat.le_max_left F₁ F₂) hp₁]
    dsimp only [Except.bind]
    exact (q a).property (Nat.le_max_right F₁ F₂) hp₂

/-- Strengthen the value relation using the fueled run's success. -/
protected theorem wp {β α : Type} {P Q : IState → β → α → Prop}
    {c : CheckIM β} {p : FueledM α}
    (h : SimAt env s₀ P c p)
    (himp : ∀ s v' v, P s v' v → (∃ F, p.val F = .ok v) → Q s v' v) :
    SimAt env s₀ Q c p := by
  intro v' s' hr
  obtain ⟨hs', hext, v, hP, F, hp⟩ := h v' s' hr
  exact ⟨hs', hext, v, himp s' v' v hP ⟨F, hp⟩, F, hp⟩

/-- Weaken the fueled side: any computation whose successful values
subsume `p`'s (at some fuel) can replace it. -/
protected theorem wr {β α : Type} {P : IState → β → α → Prop}
    {c : CheckIM β} {p q : FueledM α}
    (h : SimAt env s₀ P c p)
    (himp : ∀ (v : α) (F : Nat), p.val F = .ok v →
      ∃ F', q.val F' = .ok v) :
    SimAt env s₀ P c q := by
  intro v' s' hr
  obtain ⟨hs', hext, v, hP, F, hp⟩ := h v' s' hr
  obtain ⟨F', hq⟩ := himp v F hp
  exact ⟨hs', hext, v, hP, F', hq⟩

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
    internExprM x s = .ok ((s.store.internExprFast x).1,
      { s with store := (s.store.internExprFast x).2 }) := rfl

private theorem inst1M_run (e v : EIdx) (d : Nat) (s : IState) :
    inst1M e v d s = .ok
      (let s₁ : IState :=
        { s with bvarB := (EStore.bvarBoundIGo s.store s.bvarB e).2 }
       if (EStore.bvarBoundIGo s.store s.bvarB e).1 ≤ d then (e, s₁)
       else ((s₁.store.instantiate1I e v d).1,
         { s₁ with store := (s₁.store.instantiate1I e v d).2 })) := rfl

private theorem instListM_run (e : EIdx) (vs : List EIdx) (d : Nat)
    (s : IState) :
    instListM e vs d s = .ok
      (let s₁ : IState :=
        { s with bvarB := (EStore.bvarBoundIGo s.store s.bvarB e).2 }
       if (EStore.bvarBoundIGo s.store s.bvarB e).1 ≤ d then (e, s₁)
       else ((s₁.store.instantiateListI e vs d).1,
         { s₁ with store := (s₁.store.instantiateListI e vs d).2 })) := rfl

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
    (hd : denoteNode s₀.store.denote s₀.store.denoteL n = some x) :
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
  rw [EStore.internExprFast_eq hs.wf] at hr
  obtain ⟨hwf', hext, hden⟩ := internExpr_spec hs.wf x
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

/-- `storedTyIdxM` yields an index denoting the given type — the
interned-environment hit path via the self-certifying `ienv` clause
(the pointer gate ties the tag to the argument), the miss paths via
`internExprM_eff` (task #78). -/
theorem storedTyIdxM_eff (hs : ISOK env s₀) {n : Name} (x : Expr) :
    IEff env s₀ (fun s i => s.store.denote i = some x)
      (storedTyIdxM n x) := by
  intro v' s' hr
  rw [show storedTyIdxM n x = (do
      let ent? : Option IConstE ← modifyGet fun s => (s.ienv[n]?, s)
      match ent? with
      | some ent =>
        if EStore.exprPtrBEq ent.tyE x then pure ent.ty
        else internExprM x
      | none => internExprM x : CheckIM EIdx) from rfl] at hr
  simp only [Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, pure, Except.pure] at hr
  cases hl : s₀.ienv[n]? with
  | some ent =>
    rw [hl] at hr
    dsimp only at hr
    by_cases hgate : EStore.exprPtrBEq ent.tyE x
    · rw [if_pos hgate] at hr
      have hEq : ent.tyE = x := by
        have : (ent.tyE == x) = true := hgate
        simpa using this
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
      exact ⟨hs, Ext.refl _, hEq ▸ (hs.ienv n ent hl).1⟩
    · rw [if_neg hgate] at hr
      exact internExprM_eff hs x v' s' hr
  | none =>
    rw [hl] at hr
    exact internExprM_eff hs x v' s' hr

/-- `storedValIdxM` yields an index denoting the given value (see
`storedTyIdxM_eff`). -/
theorem storedValIdxM_eff (hs : ISOK env s₀) {n : Name} (x : Expr) :
    IEff env s₀ (fun s i => s.store.denote i = some x)
      (storedValIdxM n x) := by
  intro v' s' hr
  rw [show storedValIdxM n x = (do
      let ent? : Option IConstE ← modifyGet fun s => (s.ienv[n]?, s)
      match ent? with
      | some ⟨_, _, some (vE, vi)⟩ =>
        if EStore.exprPtrBEq vE x then pure vi
        else internExprM x
      | _ => internExprM x : CheckIM EIdx) from rfl] at hr
  simp only [Bind.bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, pure, Except.pure] at hr
  cases hl : s₀.ienv[n]? with
  | some ent =>
    rw [hl] at hr
    obtain ⟨tyE, ty, val⟩ := ent
    cases hval : val with
    | some p =>
      obtain ⟨vE, vi⟩ := p
      subst hval
      dsimp only at hr
      by_cases hgate : EStore.exprPtrBEq vE x
      · rw [if_pos hgate] at hr
        have hEq : vE = x := by
          have : (vE == x) = true := hgate
          simpa using this
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
        exact ⟨hs, Ext.refl _,
          hEq ▸ (hs.ienv n ⟨tyE, ty, some (vE, vi)⟩ hl).2 vE vi rfl⟩
      · rw [if_neg hgate] at hr
        exact internExprM_eff hs x v' s' hr
    | none =>
      subst hval
      dsimp only at hr
      exact internExprM_eff hs x v' s' hr
  | none =>
    rw [hl] at hr
    exact internExprM_eff hs x v' s' hr

theorem inst1M_eff (hs : ISOK env s₀) {e v : EIdx} {d : Nat} {a w : Expr}
    (he : s₀.store.denote e = some a) (hv : s₀.store.denote v = some w) :
    IEff env s₀ (fun s i => s.store.denote i = some (a.instantiate1 w d))
      (inst1M e v d) := by
  intro v' s' hr
  rw [inst1M_run] at hr
  rcases hgo : EStore.bvarBoundIGo s₀.store s₀.bvarB e with ⟨b, memo⟩
  rw [hgo] at hr
  obtain ⟨hinvB, hbound⟩ := EStore.bvarBoundIGo_spec e hs.wf hs.bvarB hgo
  have hs₁ : ISOK env { s₀ with bvarB := memo } := hs.withBvarB hinvB
  injection hr with h1
  dsimp only at h1
  by_cases hble : b ≤ d
  · rw [if_pos hble] at h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1.symm
    refine ⟨hs₁, Ext.refl _, ?_⟩
    rw [instantiate1_eq_self (EStore.lbbMono hble (hbound a he))]
    exact he
  · rw [if_neg hble] at h1
    obtain ⟨hwf', hext, hden⟩ := instantiate1I_spec (d := d) hs.wf he hv
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1.symm
    exact ⟨hs₁.withStore hwf' hext, hext, hden⟩

theorem instListM_eff (hs : ISOK env s₀) {e : EIdx} {vs : List EIdx}
    {d : Nat} {a : Expr} {ws : List Expr}
    (he : s₀.store.denote e = some a) (hvs : DenL s₀.store vs ws) :
    IEff env s₀
      (fun s i => s.store.denote i = some (a.instantiateList ws d))
      (instListM e vs d) := by
  intro v' s' hr
  rw [instListM_run] at hr
  rcases hgo : EStore.bvarBoundIGo s₀.store s₀.bvarB e with ⟨b, memo⟩
  rw [hgo] at hr
  obtain ⟨hinvB, hbound⟩ := EStore.bvarBoundIGo_spec e hs.wf hs.bvarB hgo
  have hs₁ : ISOK env { s₀ with bvarB := memo } := hs.withBvarB hinvB
  injection hr with h1
  dsimp only at h1
  by_cases hble : b ≤ d
  · rw [if_pos hble] at h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1.symm
    refine ⟨hs₁, Ext.refl _, ?_⟩
    rw [Expr.instantiateList_eq_self (EStore.lbbMono hble (hbound a he))]
    exact he
  · rw [if_neg hble] at h1
    obtain ⟨hwf', hext, hden⟩ := instantiateListI_spec (d := d) hs.wf he hvs
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1.symm
    exact ⟨hs₁.withStore hwf' hext, hext, hden⟩

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

private theorem abstractRangeM_run (e : EIdx) (d k : Nat) (s : IState) :
    abstractRangeM e d k s = .ok ((s.store.abstractRangeI e d k).1,
      { s with store := (s.store.abstractRangeI e d k).2 }) := rfl

theorem abstractRangeM_eff (hs : ISOK env s₀) {e : EIdx} {d k : Nat}
    {a : Expr} (he : s₀.store.denote e = some a) :
    IEff env s₀ (fun s i => s.store.denote i = some (a.abstractRange d k))
      (abstractRangeM e d k) := by
  intro v' s' hr
  rw [abstractRangeM_run] at hr
  obtain ⟨hwf', hext, hden⟩ := abstractRangeI_spec (c := 0) hs.wf he
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

private theorem bvarBoundM_run (e : EIdx) (s : IState) :
    bvarBoundM e s = .ok ((EStore.bvarBoundIGo s.store s.bvarB e).1,
      { s with bvarB := (EStore.bvarBoundIGo s.store s.bvarB e).2 }) := rfl

theorem bvarBoundM_eff (hs : ISOK env s₀) {e : EIdx} :
    IEff env s₀ (fun s b => ∀ x, s.store.denote e = some x →
      x.looseBVarsBounded b = true) (bvarBoundM e) := by
  intro v' s' hr
  rw [bvarBoundM_run] at hr
  rcases hgo : EStore.bvarBoundIGo s₀.store s₀.bvarB e with ⟨b, memo⟩
  rw [hgo] at hr
  obtain ⟨hinvB, hbound⟩ := EStore.bvarBoundIGo_spec e hs.wf hs.bvarB hgo
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1.symm
  exact ⟨hs.withBvarB hinvB, Ext.refl _, hbound⟩

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

/-! ## Level-operation effects (task #62) -/

section LevelEffects

variable {env : Env} {s₀ : IState}

private theorem internLM_run (n : LNode) (s : IState) :
    internLM n s = .ok ((s.store.internL n).1,
      { s with store := (s.store.internL n).2 }) := rfl

private theorem substLM_run (ks : List Name) (us : List LIdx) (u : LIdx)
    (s : IState) :
    substLM ks us u s = .ok ((s.store.substLI ks us u).1,
      { s with store := (s.store.substLI ks us u).2 }) := rfl

private theorem substLevelTreeM_run (ks : List Name) (us : List LIdx)
    (l : Level) (s : IState) :
    substLevelTreeM ks us l s = .ok ((s.store.internLevelSubst ks us l).1,
      { s with store := (s.store.internLevelSubst ks us l).2 }) := rfl

private theorem substLevelTreesM_run (ks : List Name) (us : List LIdx)
    (ls : List Level) (s : IState) :
    substLevelTreesM ks us ls s
      = .ok ((s.store.internLevelSubsts ks us ls).1,
        { s with store := (s.store.internLevelSubsts ks us ls).2 }) := rfl

private theorem simplifyLM_run (u : LIdx) (s : IState) :
    simplifyLM u s = .ok ((simplifyLIGo s.store s.lsimpC u).1,
      { s with store := (simplifyLIGo s.store s.lsimpC u).2.1,
               lsimpC := (simplifyLIGo s.store s.lsimpC u).2.2 }) := rfl

private theorem isNonZeroLM_run (u : LIdx) (s : IState) :
    isNonZeroLM u s = .ok ((isNonZeroLIGo s.store s.lnzC u).1,
      { s with lnzC := (isNonZeroLIGo s.store s.lnzC u).2 }) := rfl

private theorem instLevelParamsM_run (ks : List Name) (us : List LIdx)
    (e : EIdx) (s : IState) :
    instLevelParamsM ks us e s
      = .ok ((s.store.instantiateLevelParamsI ks us e).1,
        { s with store := (s.store.instantiateLevelParamsI ks us e).2 })
      := rfl

private theorem modifyGetI_run {α : Type} (f : IState → α × IState)
    (s : IState) : (modifyGet f : CheckIM α) s = .ok (f s) := rfl

theorem internLM_eff (hs : ISOK env s₀) {n : LNode} {l : Level}
    (hd : denoteLNode s₀.store.denoteL n = some l) :
    IEff env s₀ (fun s u => s.store.denoteL u = some l) (internLM n) := by
  intro v' s' hr
  rw [internLM_run] at hr
  have hc : ∀ c ∈ n.children, c < s₀.store.lnodes.size := by
    intro c hcin
    obtain ⟨b, hb⟩ := denoteLNode_children_some hd c hcin
    exact denoteL_lt_size hb
  obtain ⟨hwf', hext, hden⟩ := internL_step hs.wf hc hd
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem substLM_eff (hs : ISOK env s₀) {ks : List Name} {us : List LIdx}
    {lus : List Level} {u : LIdx} {la : Level}
    (hus : denoteLList s₀.store.denoteL us = some lus)
    (hl : s₀.store.denoteL u = some la) :
    IEff env s₀
      (fun s v => s.store.denoteL v = some (Level.subst ks lus la))
      (substLM ks us u) := by
  intro v' s' hr
  rw [substLM_run] at hr
  rcases hgo : s₀.store.substLI ks us u with ⟨r, st'⟩
  obtain ⟨hwf', hext, hden⟩ := substLI_spec hs.wf hus hl hgo
  rw [hgo] at hr
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem substLevelTreeM_eff (hs : ISOK env s₀) {ks : List Name}
    {us : List LIdx} {lus : List Level} (l : Level)
    (hus : denoteLList s₀.store.denoteL us = some lus) :
    IEff env s₀
      (fun s v => s.store.denoteL v = some (Level.subst ks lus l))
      (substLevelTreeM ks us l) := by
  intro v' s' hr
  rw [substLevelTreeM_run] at hr
  rcases hgo : s₀.store.internLevelSubst ks us l with ⟨r, st'⟩
  obtain ⟨hwf', hext, hden⟩ := internLevelSubst_spec l hs.wf hus hgo
  rw [hgo] at hr
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem substLevelTreesM_eff (hs : ISOK env s₀) {ks : List Name}
    {us : List LIdx} {lus : List Level} (ls : List Level)
    (hus : denoteLList s₀.store.denoteL us = some lus) :
    IEff env s₀
      (fun s vs => denoteLList s.store.denoteL vs
        = some (ls.map (Level.subst ks lus)))
      (substLevelTreesM ks us ls) := by
  intro v' s' hr
  rw [substLevelTreesM_run] at hr
  rcases hgo : s₀.store.internLevelSubsts ks us ls with ⟨rs, st'⟩
  obtain ⟨hwf', hext, hden⟩ := internLevelSubsts_spec ls hs.wf hus hgo
  rw [hgo] at hr
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem simplifyLM_eff (hs : ISOK env s₀) {u : LIdx} {la : Level}
    (hl : s₀.store.denoteL u = some la) :
    IEff env s₀ (fun s v => s.store.denoteL v = some la.simplify)
      (simplifyLM u) := by
  intro v' s' hr
  rw [simplifyLM_run] at hr
  rcases hgo : simplifyLIGo s₀.store s₀.lsimpC u with ⟨r, st', memo'⟩
  obtain ⟨hwf', hext, hinv', hden⟩ :=
    simplifyLIGo_spec u hs.wf hs.lsimp hgo
  rw [hgo] at hr
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStoreLsimp hwf' hext hinv', hext, hden la hl⟩

theorem isNonZeroLM_eff (hs : ISOK env s₀) {u : LIdx} {la : Level}
    (hl : s₀.store.denoteL u = some la) :
    IEff env s₀ (fun _s b => b = la.isNonZero) (isNonZeroLM u) := by
  intro v' s' hr
  rw [isNonZeroLM_run] at hr
  rcases hgo : isNonZeroLIGo s₀.store s₀.lnzC u with ⟨b, memo'⟩
  obtain ⟨hinv', hden⟩ := isNonZeroLIGo_spec hs.wf u hs.lnz hgo
  rw [hgo] at hr
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withLnz hinv', Ext.refl _, (hden la hl).symm⟩


/-- Twin gate of `codNonZero` (task #49): the interned binder
annotation's codomain slot denotes the spec annotation's, so the
memoized nonzero test returns exactly `codNonZero` of the denoted
binder metadata. -/
theorem codNonZeroIM_eff (hs : ISOK env s₀) {mt : IBinderMeta}
    {bm : BinderMeta}
    (hbm : denoteBM s₀.store.denoteL mt = some bm) :
    IEff env s₀ (fun _s b => b = codNonZero bm) (codNonZeroIM mt) := by
  obtain ⟨bi, cod⟩ := mt
  cases cod with
  | none =>
    simp only [denoteBM, Option.some.injEq] at hbm
    subst hbm
    exact IEff.pure hs rfl
  | some v =>
    simp only [denoteBM, Option.map_eq_some_iff] at hbm
    obtain ⟨l, hl, rfl⟩ := hbm
    exact isNonZeroLM_eff hs hl

theorem instLevelParamsM_eff (hs : ISOK env s₀) {ks : List Name}
    {us : List LIdx} {lus : List Level} {e : EIdx} {a : Expr}
    (hus : denoteLList s₀.store.denoteL us = some lus)
    (he : s₀.store.denote e = some a) :
    IEff env s₀
      (fun s i => s.store.denote i
        = some (a.instantiateLevelParams ks lus))
      (instLevelParamsM ks us e) := by
  intro v' s' hr
  rw [instLevelParamsM_run] at hr
  obtain ⟨hwf', hext, hden⟩ := instantiateLevelParamsI_spec hs.wf hus he
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  exact ⟨hs.withStore hwf' hext, hext, hden⟩

theorem isEquivLM_eff (hs : ISOK env s₀) {l r : LIdx} {la ra : Level}
    (hl : s₀.store.denoteL l = some la)
    (hr : s₀.store.denoteL r = some ra) :
    IEff env s₀ (fun _s ob => ob = Level.isEquiv la ra)
      (isEquivLM l r) := by
  intro v' s' hrun
  unfold isEquivLM at hrun
  rw [modifyGetI_run] at hrun
  dsimp only at hrun
  cases hc : s₀.eqvC[(l, r)]? with
  | some b =>
    rw [hc] at hrun
    injection hrun with h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
    obtain ⟨la', ra', hl', hr', heq⟩ := hs.eqv l r b hc
    cases Option.some.inj (hl.symm.trans hl')
    cases Option.some.inj (hr.symm.trans hr')
    exact ⟨hs, Ext.refl _, heq.symm⟩
  | none =>
    rw [hc] at hrun
    rcases hgo1 : simplifyLIGo s₀.store s₀.lsimpC l with ⟨ls, st₁, m₁⟩
    obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ :=
      simplifyLIGo_spec l hs.wf hs.lsimp hgo1
    rcases hgo2 : simplifyLIGo st₁ m₁ r with ⟨rs, st₂, m₂⟩
    obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ :=
      simplifyLIGo_spec r hwf₁ hinv₁ hgo2
    have hext : Ext s₀.store st₂ := hext₁.trans hext₂
    have hls : st₂.denoteL ls = some la.simplify :=
      denoteL_mono hext₂ (hden₁ la hl)
    have hrs : st₂.denoteL rs = some ra.simplify :=
      hden₂ ra (denoteL_mono hext₁ hr)
    rw [hgo1] at hrun
    try dsimp only at hrun
    rw [hgo2] at hrun
    try dsimp only at hrun
    cases hbeq : ls == rs with
    | true =>
      simp only [hbeq, if_true] at hrun
      injection hrun with h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
      have hss : la.simplify = ra.simplify := by
        have hlr : ls = rs := eq_of_beq hbeq
        rw [hlr] at hls
        exact Option.some.inj (hls.symm.trans hrs)
      have hob : (some true : Option Bool) = Level.isEquiv la ra := by
        rw [Level.isEquiv, if_pos hss]; rfl
      refine ⟨hs.withStoreLsimpEqv hwf₂ hext hinv₂
        ((hs.eqv.mono hext).insert (denoteL_mono hext hl)
          (denoteL_mono hext hr) hob.symm), hext, hob⟩
    | false =>
      simp only [hbeq, Bool.false_eq_true, if_false] at hrun
      rw [readbackL_spec hls, readbackL_spec hrs] at hrun
      try dsimp only at hrun
      have hss : ¬ la.simplify = ra.simplify := by
        intro hE
        have hrs' : st₂.denoteL rs = some la.simplify := by rw [hE]; exact hrs
        have hlr : ls = rs := denoteL_inj hwf₂ hls hrs'
        rw [hlr, beq_self_eq_true] at hbeq
        exact Bool.true_eq_false ▸ hbeq
      have hisoE : Level.isEquiv la ra =
          match Level.leqCore Level.defaultFuel la.simplify ra.simplify 0 with
          | none => none
          | some false => some false
          | some true =>
            match Level.leqCore Level.defaultFuel ra.simplify la.simplify 0 with
            | none => none
            | some b2 => some b2 := by
        rw [Level.isEquiv, if_neg hss]
        simp only [Level.leq, Bind.bind, Option.bind]
        cases Level.leqCore Level.defaultFuel la.simplify ra.simplify 0 with
        | none => rfl
        | some b1 =>
          cases b1 with
          | false => rfl
          | true =>
            cases Level.leqCore Level.defaultFuel ra.simplify la.simplify 0 with
            | none => rfl
            | some b2 => rfl
      cases hb1 : Level.leqCore Level.defaultFuel la.simplify ra.simplify 0 with
      | none =>
        rw [hb1] at hrun
        injection hrun with h1
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
        refine ⟨hs.withStoreLsimpEqv hwf₂ hext hinv₂ (hs.eqv.mono hext),
          hext, ?_⟩
        rw [hisoE, hb1]
      | some b1 =>
        rw [hb1] at hrun
        cases b1 with
        | false =>
          injection hrun with h1
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
          have hob : (some false : Option Bool) = Level.isEquiv la ra := by
            rw [hisoE, hb1]
          refine ⟨hs.withStoreLsimpEqv hwf₂ hext hinv₂
            ((hs.eqv.mono hext).insert (denoteL_mono hext hl)
              (denoteL_mono hext hr) hob.symm), hext, hob⟩
        | true =>
          cases hb2 : Level.leqCore Level.defaultFuel ra.simplify la.simplify 0 with
          | none =>
            rw [hb2] at hrun
            injection hrun with h1
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
            refine ⟨hs.withStoreLsimpEqv hwf₂ hext hinv₂ (hs.eqv.mono hext),
              hext, ?_⟩
            rw [hisoE, hb1, hb2]
          | some b2 =>
            rw [hb2] at hrun
            injection hrun with h1
            obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
            have hob : (some b2 : Option Bool) = Level.isEquiv la ra := by
              rw [hisoE, hb1, hb2]
            refine ⟨hs.withStoreLsimpEqv hwf₂ hext hinv₂
              ((hs.eqv.mono hext).insert (denoteL_mono hext hl)
                (denoteL_mono hext hr) hob.symm), hext, hob⟩

theorem isEquivListLM_eff :
    ∀ {ls rs : List LIdx} {s₀ : IState} {las ras : List Level},
      ISOK env s₀ →
      denoteLList s₀.store.denoteL ls = some las →
      denoteLList s₀.store.denoteL rs = some ras →
      IEff env s₀ (fun _s ob => ob = Level.isEquivList las ras)
        (isEquivListLM ls rs) := by
  intro ls
  induction ls with
  | nil =>
    intro rs s₀ las ras hs hls hrs
    cases rs with
    | nil =>
      cases hls
      cases hrs
      exact IEff.pure hs rfl
    | cons r rs' =>
      simp only [denoteLList, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hls hrs
      cases hls
      obtain ⟨rb, hrb, rsb, hrsb, rfl⟩ := hrs
      exact IEff.pure hs rfl
  | cons l ls' ih =>
    intro rs s₀ las ras hs hls hrs
    simp only [denoteLList, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hls
    obtain ⟨lb, hlb, lsb, hlsb, rfl⟩ := hls
    cases rs with
    | nil =>
      cases hrs
      exact IEff.pure hs rfl
    | cons r rs' =>
      simp only [denoteLList, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hrs
      obtain ⟨rb, hrb, rsb, hrsb, rfl⟩ := hrs
      rw [show isEquivListLM (l :: ls') (r :: rs') = (do
        match ← isEquivLM l r with
        | none => pure none
        | some false => pure (some false)
        | some true => isEquivListLM ls' rs' :
        CheckIM (Option Bool)) from rfl]
      refine (isEquivLM_eff hs hlb hrb).bind ?_
      intro s₁ ob hs₁ hext₁ hob
      subst hob
      cases hE : Level.isEquiv lb rb with
      | none =>
        refine IEff.pure hs₁ ?_
        simp [Level.isEquivList, hE]
      | some b =>
        cases b with
        | false =>
          refine IEff.pure hs₁ ?_
          simp [Level.isEquivList, hE]
        | true =>
          intro v' s' hrun2
          obtain ⟨hs₂, hext₂, hobs⟩ := ih hs₁ (denoteLList_mono hext₁ hlsb)
            (denoteLList_mono hext₁ hrsb) v' s' hrun2
          exact ⟨hs₂, hext₂, by simp [Level.isEquivList, hE, hobs]⟩

theorem readbackLevelM_eff (hs : ISOK env s₀) {u : LIdx} {la : Level}
    (hl : s₀.store.denoteL u = some la) :
    IEff env s₀ (fun _s lv => lv = la) (readbackLevelM u) := by
  rw [show readbackLevelM u = (Setlec.withStore (·.readbackL u) >>=
    fun o => match o with
    | some l => pure l
    | none => throw (.internal "interned level readback failed") :
    CheckIM Level) from rfl]
  refine IEff.withStore ?_
  rw [readbackL_spec hl]
  exact IEff.pure hs rfl

theorem readbackLevelsM_eff :
    ∀ {us : List LIdx} {s₀ : IState} {las : List Level},
      ISOK env s₀ →
      denoteLList s₀.store.denoteL us = some las →
      IEff env s₀ (fun _s lvs => lvs = las) (readbackLevelsM us) := by
  intro us
  induction us with
  | nil =>
    intro s₀ las hs hus
    cases hus
    exact IEff.pure hs rfl
  | cons u us' ih =>
    intro s₀ las hs hus
    simp only [denoteLList, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hus
    obtain ⟨l, hl, ls, hls, rfl⟩ := hus
    rw [show readbackLevelsM (u :: us') = (do
      let l ← readbackLevelM u
      let ls ← readbackLevelsM us'
      pure (l :: ls) : CheckIM (List Level)) from rfl]
    refine (readbackLevelM_eff hs hl).bind ?_
    intro s₁ b hs₁ hext₁ hb
    subst hb
    refine (ih hs₁ (denoteLList_mono hext₁ hls)).bind ?_
    intro s₂ bs hs₂ hext₂ hbs
    subst hbs
    exact IEff.pure hs₂ rfl

end LevelEffects

/-! ## Cache-fill effects (the lazy stored-constant caches) -/

section CacheFill

variable {env : Env} {s₀ : IState}

private theorem get_run (s : IState) : (get : CheckIM IState) s = .ok (s, s) := rfl

private theorem modify_run (f : IState → IState) (s : IState) :
    (modify f : CheckIM Unit) s = .ok ((), f s) := rfl

/-- Inserting a backed entry into `constTyAt` preserves the invariant. -/
theorem ISOK.insertConstTy {s : IState} (hs : ISOK env s)
    {n : Name} {us : List LIdx} {lus : List Level} {i : EIdx}
    {ci : ConstantInfo}
    (hus : denoteLList s.store.denoteL us = some lus)
    (hfind : env.find? n = some ci)
    (hden : s.store.denote i = some
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams lus)) :
    ISOK env { s with constTyAt := s.constTyAt.insert (n, us) i } := by
  refine ⟨hs.wf, ?_, hs.constVal, hs.ruleRhs, hs.whnfCoreC, hs.whnfC,
    hs.inferC, hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, hs.bvarB,
    hs.ienv⟩
  intro n' us' i' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((n, us) : Name × List LIdx) == (n', us')
  · rw [if_pos hk] at hl
    obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := by
      have := eq_of_beq hk
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    cases hl
    exact ⟨lus, ci, hus, hfind, hden⟩
  · rw [if_neg hk] at hl
    exact hs.constTy n' us' i' hl

/-- Inserting a backed entry into `constValAt` preserves the invariant. -/
theorem ISOK.insertConstVal {s : IState} (hs : ISOK env s)
    {n : Name} {us : List LIdx} {lus : List Level} {i : EIdx}
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hus : denoteLList s.store.denoteL us = some lus)
    (hfind : env.find? n = some (.defnInfo cv v hint) ∨
      env.find? n = some (.thmInfo cv v))
    (hden : s.store.denote i = some
      (v.instantiateLevelParams cv.levelParams lus)) :
    ISOK env { s with constValAt := s.constValAt.insert (n, us) i } := by
  refine ⟨hs.wf, hs.constTy, ?_, hs.ruleRhs, hs.whnfCoreC, hs.whnfC,
    hs.inferC, hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, hs.bvarB,
    hs.ienv⟩
  intro n' us' i' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((n, us) : Name × List LIdx) == (n', us')
  · rw [if_pos hk] at hl
    obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := by
      have := eq_of_beq hk
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    cases hl
    exact ⟨lus, cv, v, hint, hus, hfind, hden⟩
  · rw [if_neg hk] at hl
    exact hs.constVal n' us' i' hl

/-- Inserting a backed entry into `ruleRhsAt` preserves the invariant. -/
theorem ISOK.insertRuleRhs {s : IState} (hs : ISOK env s)
    {c j : Name} {us : List LIdx} {lus : List Level} {i : EIdx}
    {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {rl : RecRule}
    (hus : denoteLList s.store.denoteL us = some lus)
    (hfind : env.find? c = some (.recInfo cv mI rP rules))
    (hrl : rules.find? (fun r' => r'.ctor == j) = some rl)
    (hden : s.store.denote i = some
      (rl.rhs.instantiateLevelParams cv.levelParams lus)) :
    ISOK env { s with ruleRhsAt := s.ruleRhsAt.insert (c, j, us) i } := by
  refine ⟨hs.wf, hs.constTy, hs.constVal, ?_, hs.whnfCoreC, hs.whnfC,
    hs.inferC, hs.annotC, hs.defeqC, hs.lsimp, hs.lnz, hs.eqv, hs.bvarB,
    hs.ienv⟩
  intro c' j' us' i' hl
  simp only at hl
  rw [Std.HashMap.getElem?_insert] at hl
  by_cases hk : ((c, j, us) : Name × Name × List LIdx) == (c', j', us')
  · rw [if_pos hk] at hl
    obtain ⟨rfl, rfl, rfl⟩ : c = c' ∧ j = j' ∧ us = us' := by
      have := eq_of_beq hk
      exact ⟨congrArg Prod.fst this, congrArg (·.2.1) this,
        congrArg (·.2.2) this⟩
    cases hl
    exact ⟨lus, cv, mI, rP, rules, rl, hus, hfind, hrl, hden⟩
  · rw [if_neg hk] at hl
    exact hs.ruleRhs c' j' us' i' hl

/-- `constTyAtM` under the index of `env`: the result denotes the
level-instantiated stored type at the key's denotation. -/
theorem constTyAtM_eff (hs : ISOK env s₀) {n : Name} {us : List LIdx}
    {lus : List Level} {ci : ConstantInfo}
    (hus : denoteLList s₀.store.denoteL us = some lus)
    (hfind : env.find? n = some ci) :
    IEff env s₀ (fun s i => s.store.denote i = some
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams lus))
      (constTyAtM (mkFEnv env) n us) := by
  intro v' s' hr
  rw [show constTyAtM (mkFEnv env) n us = (do
      match (← get).constTyAt[(n, us)]? with
      | some i => pure i
      | none =>
        match (mkFEnv env).find? n with
        | some ci =>
          let cv := ci.toConstantVal
          let raw ← storedTyIdxM n cv.type
          let i ← instLevelParamsM cv.levelParams us raw
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
    obtain ⟨lus', ci', hus', hfind', hden⟩ := hs.constTy n us _ hl
    rw [hfind] at hfind'
    cases hfind'
    rw [hus] at hus'
    cases hus'
    exact ⟨hs, Ext.refl _, hden⟩
  | none =>
    rw [hl] at hr
    rw [mkFEnv_find?, hfind] at hr
    dsimp only at hr
    simp only [Bind.bind, StateT.bind, Except.bind] at hr
    cases hrun : storedTyIdxM n ci.toConstantVal.type s₀ with
    | error he => rw [hrun] at hr; exact nomatch hr
    | ok pr =>
      obtain ⟨raw, s₁⟩ := pr
      rw [hrun] at hr
      dsimp only at hr
      obtain ⟨hs₁, hext₁, hdenraw⟩ := storedTyIdxM_eff hs _ raw s₁ hrun
      cases hrun₂ : instLevelParamsM ci.toConstantVal.levelParams us raw s₁
          with
      | error he => rw [hrun₂] at hr; exact nomatch hr
      | ok pr₂ =>
        obtain ⟨i, s₂⟩ := pr₂
        rw [hrun₂] at hr
        dsimp only at hr
        obtain ⟨hs₂, hext₂, hden⟩ := instLevelParamsM_eff hs₁
          (denoteLList_mono hext₁ hus) hdenraw i s₂ hrun₂
        simp only [modify, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, Bind.bind, StateT.bind, Except.bind, pure,
          StateT.pure, Except.pure, Except.ok.injEq] at hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
        exact ⟨hs₂.insertConstTy
          (denoteLList_mono hext₂ (denoteLList_mono hext₁ hus))
          hfind hden, hext₁.trans hext₂, hden⟩

/-- `constValAtM` under the index of `env` (the head is a stored
definition or theorem). -/
theorem constValAtM_eff (hs : ISOK env s₀) {n : Name} {us : List LIdx}
    {lus : List Level}
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hus : denoteLList s₀.store.denoteL us = some lus)
    (hfind : env.find? n = some (.defnInfo cv v hint) ∨
      env.find? n = some (.thmInfo cv v)) :
    IEff env s₀ (fun s i => s.store.denote i = some
        (v.instantiateLevelParams cv.levelParams lus))
      (constValAtM (mkFEnv env) n us) := by
  intro v' s' hr
  rw [show constValAtM (mkFEnv env) n us = (do
      match (← get).constValAt[(n, us)]? with
      | some i => pure i
      | none =>
        match (mkFEnv env).find? n with
        | some (.defnInfo cv v _) =>
          let raw ← storedValIdxM n v
          let i ← instLevelParamsM cv.levelParams us raw
          modify fun s =>
            let mp := s.constValAt
            let s := { s with constValAt := ∅ }
            { s with constValAt := mp.insert (n, us) i }
          pure i
        | some (.thmInfo cv v) =>
          let raw ← storedValIdxM n v
          let i ← instLevelParamsM cv.levelParams us raw
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
    obtain ⟨lus', cv', v'', hint', hus', hfind', hden⟩ :=
      hs.constVal n us _ hl
    rcases hfind with hfind | hfind <;>
      rcases hfind' with hfind' | hfind' <;>
      rw [hfind] at hfind' <;> cases hfind' <;>
      rw [hus] at hus' <;> cases hus' <;>
      exact ⟨hs, Ext.refl _, hden⟩
  | none =>
    rw [hl] at hr
    rcases hfind with hfind | hfind <;>
    · rw [mkFEnv_find?, hfind] at hr
      dsimp only at hr
      simp only [Bind.bind, StateT.bind, Except.bind] at hr
      cases hrun : storedValIdxM n v s₀ with
      | error he => rw [hrun] at hr; exact nomatch hr
      | ok pr =>
        obtain ⟨raw, s₁⟩ := pr
        rw [hrun] at hr
        dsimp only at hr
        obtain ⟨hs₁, hext₁, hdenraw⟩ := storedValIdxM_eff hs _ raw s₁ hrun
        cases hrun₂ : instLevelParamsM cv.levelParams us raw s₁ with
        | error he => rw [hrun₂] at hr; exact nomatch hr
        | ok pr₂ =>
          obtain ⟨i, s₂⟩ := pr₂
          rw [hrun₂] at hr
          dsimp only at hr
          obtain ⟨hs₂, hext₂, hden⟩ := instLevelParamsM_eff hs₁
            (denoteLList_mono hext₁ hus) hdenraw i s₂ hrun₂
          simp only [modify, modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, Bind.bind, StateT.bind, Except.bind, pure,
            StateT.pure, Except.pure, Except.ok.injEq] at hr
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
          first
          | exact ⟨hs₂.insertConstVal
              (denoteLList_mono hext₂ (denoteLList_mono hext₁ hus))
              (Or.inl hfind) hden, hext₁.trans hext₂, hden⟩
          | exact ⟨hs₂.insertConstVal (hint := .opaque)
              (denoteLList_mono hext₂ (denoteLList_mono hext₁ hus))
              (Or.inr hfind) hden, hext₁.trans hext₂, hden⟩

/-- `ruleRhsAtM` under the index of `env`. -/
theorem ruleRhsAtM_eff (hs : ISOK env s₀) {c j : Name} {us : List LIdx}
    {lus : List Level}
    {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule} {rl : RecRule}
    (hus : denoteLList s₀.store.denoteL us = some lus)
    (hfind : env.find? c = some (.recInfo cv mI rP rules))
    (hrl : rules.find? (fun r' => r'.ctor == j) = some rl) :
    IEff env s₀ (fun s i => s.store.denote i = some
        (rl.rhs.instantiateLevelParams cv.levelParams lus))
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
            let raw ← internExprM rl.rhs
            let i ← instLevelParamsM cv.levelParams us raw
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
    obtain ⟨lus', cv', mI', rP', rules', rl', hus', hfind', hrl', hden⟩ :=
      hs.ruleRhs c j us _ hl
    rw [hfind] at hfind'
    cases hfind'
    rw [hrl] at hrl'
    cases hrl'
    rw [hus] at hus'
    cases hus'
    exact ⟨hs, Ext.refl _, hden⟩
  | none =>
    rw [hl] at hr
    rw [mkFEnv_find?, hfind] at hr
    dsimp only at hr
    rw [hrl] at hr
    dsimp only at hr
    simp only [Bind.bind, StateT.bind, Except.bind] at hr
    cases hrun : internExprM rl.rhs s₀ with
    | error he => rw [hrun] at hr; exact nomatch hr
    | ok pr =>
      obtain ⟨raw, s₁⟩ := pr
      rw [hrun] at hr
      dsimp only at hr
      obtain ⟨hs₁, hext₁, hdenraw⟩ := internExprM_eff hs _ raw s₁ hrun
      cases hrun₂ : instLevelParamsM cv.levelParams us raw s₁ with
      | error he => rw [hrun₂] at hr; exact nomatch hr
      | ok pr₂ =>
        obtain ⟨i, s₂⟩ := pr₂
        rw [hrun₂] at hr
        dsimp only at hr
        obtain ⟨hs₂, hext₂, hden⟩ := instLevelParamsM_eff hs₁
          (denoteLList_mono hext₁ hus) hdenraw i s₂ hrun₂
        simp only [modify, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, Bind.bind, StateT.bind, Except.bind, pure,
          StateT.pure, Except.pure, Except.ok.injEq] at hr
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
        exact ⟨hs₂.insertRuleRhs
          (denoteLList_mono hext₂ (denoteLList_mono hext₁ hus))
          hfind hrl hden, hext₁.trans hext₂, hden⟩

end CacheFill

end Setlec
