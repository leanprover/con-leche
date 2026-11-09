module

public import ConLeche.Cached.StateC
public import ConLeche.Verify.Cached.OpsC
public import ConLeche.Verify.Fueled

public section

/-!
# The cached-core faithfulness kit (task #163, batch 5)

The relation and combinators for proving that the cached clone core
(`ConLeche/Cached/CoreC.lean`) simulates the pure fueled families.  The
cached and pure sides are *the same terms*, so the value relation is
equality.

The walks themselves are `Std.WP` triples (`Grind.lean`); `SimC`/`CEff`
are what a triple says about one run (`triple_iff_run`,
`SimC.of_triple`), the form the knot (`SSimC`), the binder loops' tail
compositions and the driver's run theorems consume, with the few
run-level combinators they use (`SimC.pure`, `SimC.throw`, `SimC.wp`,
`SimC.wr`, `SimC.liftFueled`, `CEff.pure`).

* `CSOK mode eager env s` — the cached-state invariant: the lazy
  stored-constant caches hold `RelC`-related conversions of the
  level-instantiated stored data and every entry-point memo entry is
  backed by a pure run at some fuel, valid at every depth at which the
  key is well scoped.
* `SimC mode eager env s₀ P c p` — a successful cached run of `c` from `s₀`
  preserves `CSOK` and produces a value `P`-related to a successful run
  of the fueled computation `p` at some fuel.
* `CEff mode eager env s₀ Q c` — a twin-only effect (conversion, cache fill):
  no fueled counterpart, just invariant preservation plus a value fact.

The value relation is **state-free**.  Memo clauses assert facts that
are a **function of the key** — a `beq` collision pins the stored key
to the query (`beq_sound`, i.e. `eq_of_beq`).
-/

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode} {eager : Bool}

/-! ## Lawful keys

The memo tables of `CState` are keyed by `Expr`, `Level`, `Name` and
tuples/lists of those.  `Erase.lean` supplies the `Expr` instances and
`OpsC.lean` the `Expr × β` products; everything else is `LawfulBEq`
(all keys are `DecidableEq`-derived) except *lists of `Expr`*, which
inherit the component instances the same way products do. -/

section ProdKey

private theorem prod_beq {α β : Type} [BEq α] [BEq β] (a c : α) (b d : β) :
    ((a, b) == (c, d)) = ((a == c) && (b == d)) := rfl

private theorem prod_hash {α β : Type} [Hashable α] [Hashable β] (a : α)
    (b : β) : hash (a, b) = mixHash (hash a) (hash b) := rfl

instance {α β : Type} [BEq α] [BEq β] [EquivBEq α] [EquivBEq β] :
    EquivBEq (α × β) where
  symm := by
    intro p q h
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    rw [prod_beq, Bool.and_eq_true] at h
    rw [prod_beq, Bool.and_eq_true]
    exact ⟨BEq.symm h.1, BEq.symm h.2⟩
  trans := by
    intro p q t h₁ h₂
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    obtain ⟨e, f⟩ := t
    rw [prod_beq, Bool.and_eq_true] at h₁ h₂
    rw [prod_beq, Bool.and_eq_true]
    exact ⟨BEq.trans h₁.1 h₂.1, BEq.trans h₁.2 h₂.2⟩
  rfl := by
    intro p
    obtain ⟨a, b⟩ := p
    rw [prod_beq, Bool.and_eq_true]
    exact ⟨BEq.refl a, BEq.refl b⟩

instance {α β : Type} [BEq α] [Hashable α] [BEq β] [Hashable β]
    [LawfulHashable α] [LawfulHashable β] : LawfulHashable (α × β) where
  hash_eq := by
    intro p q h
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    rw [prod_beq, Bool.and_eq_true] at h
    rw [prod_hash, prod_hash, LawfulHashable.hash_eq _ _ h.1,
      LawfulHashable.hash_eq _ _ h.2]

end ProdKey

section ListKey

variable {α : Type} [BEq α]

private theorem list_beq_cons {a b : α} {as bs : List α} :
    ((a :: as) == (b :: bs)) = (a == b && as == bs) := rfl

private theorem list_beq_nil_cons {b : α} {bs : List α} :
    (([] : List α) == (b :: bs)) = false := rfl

private theorem list_beq_cons_nil {a : α} {as : List α} :
    ((a :: as) == ([] : List α)) = false := rfl

variable [EquivBEq α]

instance : EquivBEq (List α) where
  symm := by
    intro a
    induction a with
    | nil =>
      intro b h
      cases b with
      | nil => rfl
      | cons y ys => rw [list_beq_nil_cons] at h; exact nomatch h
    | cons x xs ih =>
      intro b h
      cases b with
      | nil => rw [list_beq_cons_nil] at h; exact nomatch h
      | cons y ys =>
        rw [list_beq_cons, Bool.and_eq_true] at h ⊢
        exact ⟨BEq.symm h.1, ih h.2⟩
  trans := by
    intro a
    induction a with
    | nil =>
      intro b c h₁ h₂
      cases b with
      | nil => exact h₂
      | cons y ys => rw [list_beq_nil_cons] at h₁; exact nomatch h₁
    | cons x xs ih =>
      intro b c h₁ h₂
      cases b with
      | nil => rw [list_beq_cons_nil] at h₁; exact nomatch h₁
      | cons y ys =>
        cases c with
        | nil => rw [list_beq_cons_nil] at h₂; exact nomatch h₂
        | cons z zs =>
          rw [list_beq_cons, Bool.and_eq_true] at h₁ h₂ ⊢
          exact ⟨BEq.trans h₁.1 h₂.1, ih h₁.2 h₂.2⟩
  rfl := by
    intro a
    induction a with
    | nil => rfl
    | cons x xs ih =>
      rw [list_beq_cons, Bool.and_eq_true]
      exact ⟨BEq.refl x, ih⟩

omit [EquivBEq α] in
/-- `List`'s hash is a `foldl` of `mixHash`, so `BEq`-equal lists fold
to the same value from any seed. -/
private theorem list_hash_fold [Hashable α] [LawfulHashable α] :
    ∀ {a b : List α}, (a == b) = true → ∀ r : UInt64,
      List.foldl (fun r (x : α) => mixHash r (Hashable.hash x)) r a
        = List.foldl (fun r (x : α) => mixHash r (Hashable.hash x)) r b := by
  intro a
  induction a with
  | nil =>
    intro b h r
    cases b with
    | nil => rfl
    | cons y ys => rw [list_beq_nil_cons] at h; exact nomatch h
  | cons x xs ih =>
    intro b h r
    cases b with
    | nil => rw [list_beq_cons_nil] at h; exact nomatch h
    | cons y ys =>
      rw [list_beq_cons, Bool.and_eq_true] at h
      simp only [List.foldl_cons, LawfulHashable.hash_eq _ _ h.1]
      exact ih h.2 _

instance [Hashable α] [LawfulHashable α] : LawfulHashable (List α) where
  hash_eq := fun _ _ h => list_hash_fold h 7

end ListKey

/-- A memo whose entries all satisfy `P` keeps them so under the insert of
an entry satisfying `P`: with a lawful key equality a colliding key IS the
inserted one.  Every `CSOK` memo clause is such a `P`. -/
theorem HashMap.insert_backed {K V : Type} [BEq K] [LawfulBEq K] [Hashable K]
    {P : K → V → Prop} {m : Std.HashMap K V} (hm : ∀ k v, m[k]? = some v → P k v)
    {i : K} {j : V} (hij : P i j) : ∀ k v, (m.insert i j)[k]? = some v → P k v := by
  intro k v h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i hk; cases h; exact eq_of_beq hk ▸ hij
  · exact hm k v h

/-! ## The value relations -/

/-- The cached value relation: state-free **equality**.  The name marks
*which* side is which (the `DiscC*.lean` walks are written in it). -/
@[expose] def RelC (v' : Expr) (v : Expr) : Prop := v' = v

theorem RelC.erase {v' : Expr} {v : Expr} (h : RelC v' v) : v' = v := h

/-- Every expression is related to itself (there is one type). -/
theorem RelC.refl (x : Expr) : RelC x x := by rfl

/-! ## The state invariant -/

/-- The mode-memo invariant (task #361): the six entry-point memos of
a `ModeMemos` set are backed by runs at `mode` — the clauses `CSOK`
states of the state's own six fields, for the eager tower's stored set
(`CSOK.eager`, at `eager := true`). -/
structure ModeMemosOK (mode : CheckMode) (eager : Bool) (env : Env) (mm : ModeMemos) : Prop where
  whnfCoreC : ∀ k v, mm.whnfCoreC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      whnfCore mode eager env F d k = .ok v
  whnfCoreCheapC : ∀ k v, mm.whnfCoreCheapC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      whnfCore mode eager env F d k true = .ok v
  whnfC : ∀ k v, mm.whnfC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      whnf mode eager env F d k = .ok v
  inferC : ∀ k v, mm.inferC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      inferTypeCore mode eager env F d k = .ok v
  inferIOC : ∀ k v, mm.inferIOC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      inferTypeIO mode eager env F d k = .ok v
  defeqC : ∀ a b r, mm.defeqC[(a, b)]? = some r →
    ∃ F, ∀ d, (Expr.wscopedB d a) = true → (Expr.wscopedB d b) = true →
      isDefEqCore mode eager env F d a b = .ok r

/-- The empty set is backed everywhere. -/
theorem ModeMemosOK.empty : ModeMemosOK mode eager env {} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intros; simp_all)

/-- The cached-state invariant (see the module docstring); its value
legs are `RelC` and its keys are trees.

The memo clauses are *functions of their keys*, so a `beq` collision,
which pins the stored key to the query, preserves them. -/
structure CSOK (mode : CheckMode) (eager : Bool) (env : Env) (s : CState) : Prop where
  constTy : ∀ n us i, s.constTyAt[(n, us)]? = some i → ∃ ci,
    env.find? n = some ci ∧
    RelC i (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us)
  constVal : ∀ n us i, s.constValAt[(n, us)]? = some i → ∃ cv v h,
    env.find? n = some (.defnInfo cv v h) ∧
    RelC i (v.instantiateLevelParams cv.levelParams us)
  ruleRhs : ∀ c j us i, s.ruleRhsAt[(c, j, us)]? = some i →
    ∃ cv mI rP isK rules rl,
    env.find? c = some (.recInfo cv mI rP isK rules) ∧
    rules.find? (fun r' => r'.ctor == j) = some rl ∧
    RelC i (rl.rhs.instantiateLevelParams cv.levelParams us)
  whnfCoreC : ∀ k v, s.whnfCoreC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      whnfCore mode eager env F d k = .ok v
  /-- The cheap-projection head normalization's memo (`whnfCore` at
  `cheap_proj`, lane CHEAPPROJ). -/
  whnfCoreCheapC : ∀ k v, s.whnfCoreCheapC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      whnfCore mode eager env F d k true = .ok v
  whnfC : ∀ k v, s.whnfC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      whnf mode eager env F d k = .ok v
  inferC : ∀ k v, s.inferC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      inferTypeCore mode eager env F d k = .ok v
  /-- The io memo's clause (task #172 B4, the task-#170 memo ruling):
  an entry is backed by an io-*slot* run — the WEAKER invariant, since
  the io slot witnesses fewer checks than `inferC`'s
  clause consumes.  A hit here never serves a full-infer query (the
  maps are separate), which is exactly what lets this clause be
  weaker. -/
  inferIOC : ∀ k v, s.inferIOC[k]? = some v →
    ∃ F, ∀ d, (Expr.wscopedB d k) = true →
      inferTypeIO mode eager env F d k = .ok v
  defeqC : ∀ a b r, s.defeqC[(a, b)]? = some r →
    ∃ F, ∀ d, (Expr.wscopedB d a) = true → (Expr.wscopedB d b) = true →
      isDefEqCore mode eager env F d a b = .ok r
  lsimp : ∀ u v, s.lsimpC[u]? = some v → v = Level.simplify u
  lnz : ∀ u b, s.lnzC[u]? = some b → b = Level.isNonZero u
  eqv : ∀ l r b, s.eqvC[(l, r)]? = some b → Level.isEquiv l r = some b
  instC : ∀ (k : Expr) (vs : List Expr) (d : Nat) (r : Expr),
    s.instC[(k, vs, d)]? = some r →
      r = (Expr.instantiateList k vs d)
  /-- The eager tower's stored memos (task #361) are backed by runs at
  `eager := true`, the flag the `defeqE` slot runs them at. -/
  eager : ModeMemosOK mode true env s.eagerMemos

/-- The environment-free residue: exactly the clauses `flushC`
preserves — the level-operation memos. -/
structure CSOKF (s : CState) : Prop where
  lsimp : ∀ u v, s.lsimpC[u]? = some v → v = Level.simplify u
  lnz : ∀ u b, s.lnzC[u]? = some b → b = Level.isNonZero u
  eqv : ∀ l r b, s.eqvC[(l, r)]? = some b → Level.isEquiv l r = some b

/-- Every invariant state carries the residue. -/
theorem CSOK.residue {env : Env} {s : CState} (h : CSOK mode eager env s) :
    CSOKF s := ⟨h.lsimp, h.lnz, h.eqv⟩

/-- A declaration's fresh state, empty memos at a maximum `Nat` size, carries the residue. -/
theorem CSOKF.fresh (maxNatSize : Nat) : CSOKF ({ maxNatSize := maxNatSize } : CState) := by
  refine ⟨?_, ?_, ?_⟩ <;> (intros; simp_all)

/-! ## Flush

`flushC` drops every environment-dependent cache, so from the residue
it re-establishes the full invariant *for any environment* — the
transition lemma the declaration fold uses. -/

theorem flushC_run (s : CState) : flushC s = .ok ((), s.flushed) := rfl

/-- After a flush the invariant holds for any environment: the
surviving components are the residue and the dropped caches' clauses
are vacuous. -/
theorem flushC_csok {env' : Env} {s : CState} (hs : CSOKF s) :
    CSOK mode eager env' s.flushed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs.lsimp, hs.lnz, hs.eqv,
    ?_, ModeMemosOK.empty⟩ <;> (intros; simp_all [CState.flushed])

/-- Flushing preserves the residue (it touches none of its
components). -/
theorem CSOKF.flushed {s : CState} (hs : CSOKF s) : CSOKF s.flushed :=
  ⟨hs.lsimp, hs.lnz, hs.eqv⟩

/-! ## The simulation and effect relations -/

/-- A successful cached run from `s₀` preserves the invariant and its
value is `P`-related to the value of a successful fueled run. -/
@[expose] def SimC (mode : CheckMode) (eager : Bool) (env : Env) (s₀ : CState) {β α : Type}
    (P : β → α → Prop) (c : CheckCM β) (p : FueledM α) : Prop :=
  ∀ v' s', c s₀ = .ok (v', s') →
    CSOK mode eager env s' ∧ ∃ v, P v' v ∧ ∃ F, p.val F = .ok v

/-- A twin-only effect: invariant preservation and a value fact — no
fueled counterpart. -/
@[expose] def CEff (mode : CheckMode) (eager : Bool) (env : Env) (s₀ : CState) {β : Type}
    (Q : β → Prop) (c : CheckCM β) : Prop :=
  ∀ v' s', c s₀ = .ok (v', s') → CSOK mode eager env s' ∧ Q v'

/-! ## The eager tower's memos (tasks #353, #361)

`withEagerMemos` swaps the eager tower's stored memos in for the run
and back out after it.  The invariant follows the swap: the entered
state carries the invariant at `eager := true` (its six fields are the
stored set, backed there by `CSOK.eager`; its eager slot is empty), and
the left state takes its six fields from the caller's state and its
eager set — the run's six fields — from the run's state at
`eager := true`.  With the flag already set nothing moves. -/

/-- The plain fields, as a set, are backed at the state's mode. -/
theorem CSOK.modeMemos {s : CState} (hs : CSOK mode eager env s) : ModeMemosOK mode eager env
    s.modeMemos :=
  ⟨hs.whnfCoreC, hs.whnfCoreCheapC, hs.whnfC, hs.inferC, hs.inferIOC, hs.defeqC⟩

/-- The entered state carries the invariant at the eager tower's flag. -/
theorem CSOK.enterEager {s : CState} (hs : CSOK mode eager env s) :
    CSOK mode true env (s.enterEager eager).2 := by
  cases eager with
  | true => exact hs
  | false =>
    exact ⟨hs.constTy, hs.constVal, hs.ruleRhs, hs.eager.whnfCoreC, hs.eager.whnfCoreCheapC,
      hs.eager.whnfC, hs.eager.inferC, hs.eager.inferIOC, hs.eager.defeqC, hs.lsimp, hs.lnz,
      hs.eqv, hs.instC, ModeMemosOK.empty⟩

/-- The left state: the caller's plain memos, the run's six fields as
the eager set, the run's mode-free caches (with the flag already set,
the run's state as it is). -/
theorem CSOK.leaveEager {s₀ s₂ : CState} (hs₀ : CSOK mode eager env s₀)
    (hs₂ : CSOK mode true env s₂) :
    CSOK mode eager env (s₂.leaveEager (s₀.enterEager eager).1) := by
  cases eager with
  | true => exact hs₂
  | false =>
    exact ⟨hs₂.constTy, hs₂.constVal, hs₂.ruleRhs, hs₀.whnfCoreC, hs₀.whnfCoreCheapC,
      hs₀.whnfC, hs₀.inferC, hs₀.inferIOC, hs₀.defeqC, hs₂.lsimp, hs₂.lnz, hs₂.eqv, hs₂.instC,
      hs₂.modeMemos⟩

/-- **A run on the eager tower's memos** simulates what the run
simulates at `eager := true`, from the caller's invariant at `eager`. -/
theorem SimC.eagerMemos {s₀ : CState} {β α : Type}
    {P : β → α → Prop} {x : CheckCM β} {p : FueledM α}
    (hs : CSOK mode eager env s₀)
    (hx : ∀ {s₁ : CState}, CSOK mode true env s₁ → SimC mode true env s₁ P x p) :
    SimC mode eager env s₀ P (withEagerMemos eager x) p := by
  intro v' s' (hr : withEagerMemos eager x s₀ = .ok (v', s'))
  have hrun : withEagerMemos eager x s₀ =
      (match x (s₀.enterEager eager).2 with
        | .ok (v, s₂) => .ok (v, s₂.leaveEager (s₀.enterEager eager).1)
        | .error e => .error e) := by
    simp only [withEagerMemos, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, modify, pure, StateT.pure, Except.pure, Except.bind]
    cases x (s₀.enterEager eager).2 <;> rfl
  rw [hrun] at hr
  cases hx₁ : x (s₀.enterEager eager).2 with
  | error err => rw [hx₁] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨v, s₂⟩ := pr
    rw [hx₁] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨hs₂, w, hP, F, hF⟩ := hx hs.enterEager v s₂ hx₁
    exact ⟨hs.leaveEager hs₂, w, hP, F, hF⟩

/-- A simulation only reads its fueled side's runs: two fueled
computations with the same runs are interchangeable. -/
theorem SimC.congr_fueled {s₀ : CState} {β α : Type} {P : β → α → Prop}
    {c : CheckCM β} {p q : FueledM α} (hpq : ∀ F, q.val F = p.val F)
    (h : SimC mode eager env s₀ P c p) : SimC mode eager env s₀ P c q := by
  intro v' s' hr
  obtain ⟨hs', v, hP, F, hF⟩ := h v' s' hr
  exact ⟨hs', v, hP, F, by rw [hpq]; exact hF⟩

/-- The result relation for expression-valued entry points: the cached
term is related to the fueled value, well scoped at the ambient
depth. -/
@[expose] def RelEC (d : Nat) (v' : Expr) (v : Expr) : Prop :=
  RelC v' v ∧ Expr.WScoped d v

/-- The result relation for `Bool` and other data results. -/
@[expose] def RelVC {α : Type} (b a : α) : Prop := b = a

namespace SimC

variable {env : Env} {s₀ : CState}

protected theorem pure {β α : Type} {P : β → α → Prop}
    {b : β} {a : α} (hs : CSOK mode eager env s₀) (h : P b a) :
    SimC mode eager env s₀ P (pure b) (pure a) := by
  intro v' s' hr
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hs, a, h, 0, rfl⟩

protected theorem throw {β α : Type} {P : β → α → Prop}
    {e : CheckError} {p : FueledM α} :
    SimC mode eager env s₀ P (throw e) p := by
  intro v' s' hr
  exact nomatch hr

/-- Strengthen the value relation using the fueled run's success. -/
protected theorem wp {β α : Type} {P Q : β → α → Prop}
    {c : CheckCM β} {p : FueledM α}
    (h : SimC mode eager env s₀ P c p)
    (himp : ∀ v' v, P v' v → (∃ F, p.val F = .ok v) → Q v' v) :
    SimC mode eager env s₀ Q c p := by
  intro v' s' hr
  obtain ⟨hs', v, hP, F, hp⟩ := h v' s' hr
  exact ⟨hs', v, himp v' v hP ⟨F, hp⟩, F, hp⟩

/-- Weaken the fueled side: any computation whose successful values
subsume `p`'s (at some fuel) can replace it. -/
protected theorem wr {β α : Type} {P : β → α → Prop}
    {c : CheckCM β} {p q : FueledM α}
    (h : SimC mode eager env s₀ P c p)
    (himp : ∀ (v : α) (F : Nat), p.val F = .ok v → ∃ F', q.val F' = .ok v) :
    SimC mode eager env s₀ P c q := by
  intro v' s' hr
  obtain ⟨hs', v, hP, F, hp⟩ := h v' s' hr
  obtain ⟨F', hq⟩ := himp v F hp
  exact ⟨hs', v, hP, F', hq⟩

protected theorem liftFueled {α : Type} (what : String) (o : Option α)
    (hs : CSOK mode eager env s₀) :
    SimC mode eager env s₀ RelVC (liftFueled what o) (liftFueled what o) := by
  cases o with
  | some a => exact SimC.pure hs rfl
  | none => exact SimC.throw

end SimC

namespace CEff

variable {env : Env} {s₀ : CState}

protected theorem pure {β : Type} {Q : β → Prop} {b : β}
    (hs : CSOK mode eager env s₀) (h : Q b) : CEff mode eager env s₀ Q (pure b) := by
  intro v' s' hr
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hs, h⟩

end CEff

end ConLeche.Cached
