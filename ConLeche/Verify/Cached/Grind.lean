module

public import ConLeche.Verify.Cached.SimC
public import ConLeche.Verify.Cached.GrindAttr
public import Std.WP
import ConLeche.Verify.EnvBound
import ConLeche.Verify.InstSpine
import ConLeche.Verify.InferLemmas

public section

/-!
# The cached simulation as `Std.WP` triples, and its `grind` vocabulary

A walk proof of the cached-to-pure simulation is

```lean
  sym only [conleche_grind, local facts…] =>
    vcgen [f, unfolding lemmas, callee specs…] <;> finish
```

`vcgen` runs in `grind`'s symbolic mode (`SymM`), generates the
verification conditions of the cached program `f` and internalizes
each one's hypotheses into the E-graph as it introduces them; `finish`
closes every condition in that same E-graph.  `only`: the project's set
(`@[conleche_grind]`, `GrindAttr.lean`) and nothing else.  This module
holds the vocabulary more than one walk uses; a walk module adds only
what is about its own walk (its arm equations, named blocks and
restatements, the scope facts of its own constructions).  The rules a
statement follows are those of `CLAUDE.md`'s "The cached simulation
proofs".

1. **Triples are statements about runs** (§1).  A walk is the triple
   `⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode eager env s' ∧ Runs p v ∧ W v; ⊤⦄`:
   partial correctness, the exception post `⊤`.  `triple_iff_run` reads
   it as "every successful run from `s₀` …", which is what the run-level
   consumers (the knot's `SimC`, the install and driver theorems) take.
2. **The pure side's answer as a named predicate** (§2).  `Runs p v`:
   the fuelled computation `p` succeeds with `v` at some fuel.  Fuel is
   the one witness that is not a function of anything a walk names, so it
   stays inside `Runs`; `Runs.pure_eq`, `Runs.bind_eq` (keyed by the
   step's answer and the bind) and `Runs.pure_bind_eq` are equations
   whose proofs merge it by `FueledM`'s monotonicity.  A post states the
   cached value AS the pure answer, never `∃ w, v = w ∧ Runs p w`.  Two
   program equations on the pure side (`FueledM.pure_bind_eq`,
   `liftFueled_some_bind`) peel what needs no fuel.
3. **The triple forms of `SimC`/`CEff`** (§3): `SimC.triple`/
   `SimC.of_triple` at a value relation that is equality up to a side
   condition `W`, `SimC.tripleVC`/`SimC.of_tripleVC` at `RelVC` (plain
   equality), `CEff.triple`; and the one shared effect, `liftFueled_spec`.
4. **Scope side conditions as named predicates** (§4): `AllWS`, `OptWS`,
   `StepWS` and the generic `ListAll` over a named element predicate,
   each with one equation per constructor or list operation, so that no
   `∀` or `match` reaches `grind`.  `Expr.WScoped` itself is opened one
   constructor at a time (`wscoped_app_eq`, …) and carried through the
   operations the walks perform (instantiation, opening and closing a
   binder, spine building and reading, level instantiation of a closed
   term), each fact keyed by the operation's term.
5. **The index and the cached operations are the pure ones** (§5): the
   cached index `mkFEnv env` answers `env.find?`, and the operation-free
   cached twins (`getAppArgsC`, `instSpineC`, `instLevelParams`,
   `mkBvar`) are their `Expr` originals, as unconditional equations.
6. **The value relations as answers** (§6): `RelEC` splits into the
   equation and the side condition.
7. **The knot's slots** (§7): `BodySpec`/`BodySpecB`, a body's
   simulation as a named predicate, so that a memo wrapper's hypothesis
   is an atom and its triple enters `vcgen`'s list as a term.

What is NOT here, and why: the knot hypothesis `SSimC` and the triple
forms of its fields (`DiscC1.lean`: they name the cached knot
`coreKnotI`, which this module does not import), the memo wrappers'
triples (`SimCEff.lean`, beside their `CSOK` hit and insert lemmas), and
the shared operations' triples at the `sharedOpsC` projections
(`SimCS.lean`, after the knot).
-/

namespace ConLeche.Cached

open ConLeche Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool} {env : Env}

/-! ## 1. A `CheckCM` triple is a statement about the successful runs -/

/-- A partial-correctness triple from a fixed initial state is a
statement about the successful runs. -/
theorem triple_iff_run {β : Type} {s₀ : CState} {c : CheckCM β}
    {Q : β → CState → Prop} :
    (⦃fun s => s = s₀⦄ c ⦃fun v s' => Q v s'; ⊤⦄) ↔
      ∀ v' s', c s₀ = .ok (v', s') → Q v' s' := by
  constructor
  · intro ⟨h⟩ v' s' hr
    have := h s₀ rfl
    rw [StateT.wp_apply_eq, StateT.run, hr] at this
    exact this
  · intro h
    refine ⟨fun s hs => ?_⟩
    obtain rfl : s = s₀ := hs
    rw [StateT.wp_apply_eq, StateT.run]
    cases hc : c s with
    | ok r => obtain ⟨v, s'⟩ := r; exact h v s' hc
    | error e =>
      show (⊤ : CheckError → Prop) e
      rw [Lean.Order.top_apply, Lean.Order.top_prop_eq]; trivial

/-! ## 2. The pure side's answer -/

/-- The fuelled computation `p` succeeds with `v` at some fuel. -/
@[expose] def Runs {α : Type} (p : FueledM α) (v : α) : Prop :=
  ∃ F, p.val F = .ok v

theorem Runs.pure {α : Type} (a : α) : Runs (pure a : FueledM α) a := ⟨0, rfl⟩

theorem Runs.bind {α β : Type} {x : FueledM α} {f : α → FueledM β} {a : α} {b : β}
    (hx : Runs x a) (hf : Runs (f a) b) : Runs (x >>= f) b := by
  obtain ⟨F₁, h₁⟩ := hx
  obtain ⟨F₂, h₂⟩ := hf
  refine ⟨max F₁ F₂, ?_⟩
  rw [FueledM.atF_bind]
  simp only [Bind.bind]
  rw [x.property (Nat.le_max_left F₁ F₂) h₁]
  exact (f a).property (Nat.le_max_right F₁ F₂) h₂

/-- A `pure` answers its value and nothing else. -/
@[conleche_grind =] theorem Runs.pure_eq {α : Type} (a b : α) :
    Runs (Pure.pure a : FueledM α) b = (a = b) := by
  apply propext; constructor
  · intro ⟨F, h⟩; exact Except.ok.inj h
  · rintro rfl; exact Runs.pure a

/-- Past a first step that answers `a`, a bind answers what its
continuation at `a` answers.  The equation (rather than `Runs.bind`'s
implication) is what lets `grind` push a goal `Runs (x >>= f) b` into
the continuation: it fires on the step's answer and the bind, both of
which are terms of the verification condition. -/
theorem Runs.bind_eq {α β : Type} {x : FueledM α} {f : α → FueledM β} {a : α} (b : β)
    (hx : Runs x a) : Runs (x >>= f) b = Runs (f a) b := by
  apply propext; constructor
  · intro ⟨F, h⟩
    obtain ⟨F₁, h₁⟩ := hx
    refine ⟨max F F₁, ?_⟩
    have h' := (x >>= f).property (Nat.le_max_left F F₁) h
    rw [FueledM.atF_bind] at h'
    simp only [Bind.bind] at h'
    rw [x.property (Nat.le_max_right F F₁) h₁] at h'
    exact h'
  · intro hf; exact Runs.bind hx hf
grind_pattern [conleche_grind] Runs.bind_eq => Runs x a, Runs (x >>= f) b

/-- Past a first step that is a `pure`, a bind answers what its
continuation answers (`Runs.bind_eq` needs a `Runs` term of the first
step, which no callee spec supplies when the step is operation-free). -/
@[conleche_grind =] theorem Runs.pure_bind_eq {α β : Type} (a : α) (f : α → FueledM β) (b : β) :
    Runs (Pure.pure a >>= f) b = Runs (f a) b :=
  Runs.bind_eq b (Runs.pure a)

@[conleche_grind =] theorem FueledM.pure_bind_eq {α β : Type} (a : α) (g : α → FueledM β) :
    (pure a >>= g : FueledM β) = g a := rfl

/-- A `liftFueled` of a present answer is that answer. -/
@[conleche_grind =] theorem liftFueled_some_bind {α β : Type} (w : String) (a : α)
    (g : α → FueledM β) : (liftFueled w (some a) >>= g : FueledM β) = g a := rfl

/-! ## 3. The triple forms of `SimC` and `CEff` -/

/-- A simulation whose value relation is equality up to `W` is a triple
whose post names the cached value as the pure side's answer. -/
theorem SimC.triple {β : Type} {P : β → β → Prop} {W : β → Prop} {s₀ : CState}
    {c : CheckCM β} {p : FueledM β} (hP : ∀ v' v, P v' v → v' = v ∧ W v')
    (h : SimC mode eager env s₀ P c p) :
    ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode eager env s' ∧ Runs p v ∧ W v; ⊤⦄ := by
  refine triple_iff_run.mpr fun v' s' hr => ?_
  obtain ⟨hs', v, hP', F, hF⟩ := h v' s' hr
  obtain ⟨rfl, hW⟩ := hP v' v hP'
  exact ⟨hs', ⟨F, hF⟩, hW⟩

/-- The converse of `SimC.triple`: an answer-shaped triple is a
simulation for any value relation that holds on the diagonal under `W`. -/
theorem SimC.of_triple {β : Type} {P : β → β → Prop} {W : β → Prop} {s₀ : CState}
    {c : CheckCM β} {p : FueledM β} (hP : ∀ v, W v → P v v)
    (h : ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode eager env s' ∧ Runs p v ∧ W v; ⊤⦄) :
    SimC mode eager env s₀ P c p := by
  intro v' s' hr
  obtain ⟨hs', ⟨F, hF⟩, hW⟩ := triple_iff_run.mp h v' s' hr
  exact ⟨hs', v', hP v' hW, F, hF⟩

/-- A simulation at `RelVC` (plain equality) is a triple whose post
names the cached value as the pure answer. -/
theorem SimC.tripleVC {β : Type} {s₀ : CState} {c : CheckCM β} {p : FueledM β}
    (h : SimC mode eager env s₀ RelVC c p) :
    ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode eager env s' ∧ Runs p v; ⊤⦄ := by
  refine triple_iff_run.mpr fun v' s' hr => ?_
  obtain ⟨hs', v, rfl, F, hF⟩ := h v' s' hr
  exact ⟨hs', ⟨F, hF⟩⟩

/-- The converse of `SimC.tripleVC`. -/
theorem SimC.of_tripleVC {β : Type} {s₀ : CState} {c : CheckCM β} {p : FueledM β}
    (h : ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode eager env s' ∧ Runs p v; ⊤⦄) :
    SimC mode eager env s₀ RelVC c p := by
  intro v' s' hr
  obtain ⟨hs', ⟨F, hF⟩⟩ := triple_iff_run.mp h v' s' hr
  exact ⟨hs', v', rfl, F, hF⟩

theorem CEff.triple {β : Type} {Q : β → Prop} {s₀ : CState} {c : CheckCM β}
    (h : CEff mode eager env s₀ Q c) :
    ⦃fun s => s = s₀⦄ c ⦃fun v s' => CSOK mode eager env s' ∧ Q v; ⊤⦄ :=
  triple_iff_run.mpr h

/-- The fuel-exhaustion lift is the same on both sides. -/
theorem liftFueled_spec {α : Type} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (what : String) (o : Option α) :
    ⦃fun s => s = s₀⦄ (liftFueled what o : CheckCM α)
    ⦃fun a s' => CSOK mode eager env s' ∧ Runs (liftFueled what o) a; ⊤⦄ :=
  (SimC.liftFueled what o hs).tripleVC

/-! ## 4. Scope side conditions

Each a named predicate with one equation per constructor or list
operation, so that no `∀` or `match` reaches `grind`; `Expr.WScoped`
itself is opened one constructor at a time and carried through the
operations the walks perform. -/

/-! ### The predicates -/

/-- Every element of the list is well scoped at `d`. -/
@[expose] def AllWS (d : Nat) (xs : List Expr) : Prop := ∀ x ∈ xs, Expr.WScoped d x

@[conleche_grind =] theorem AllWS.nil_eq (d : Nat) : AllWS d [] = True := by
  simp [AllWS]

@[conleche_grind =] theorem AllWS.cons_eq (d : Nat) (x : Expr) (xs : List Expr) :
    AllWS d (x :: xs) = (Expr.WScoped d x ∧ AllWS d xs) := by
  simp [AllWS]

@[conleche_grind =] theorem AllWS.reverse_eq (d : Nat) (xs : List Expr) :
    AllWS d xs.reverse = AllWS d xs := by
  simp [AllWS]

theorem AllWS.append {d : Nat} {xs ys : List Expr} (h : AllWS d xs) (h' : AllWS d ys) :
    AllWS d (xs ++ ys) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · exact h' x hx
grind_pattern [conleche_grind] AllWS.append => AllWS d (xs ++ ys)

/-- A prefix of well-scoped terms is well scoped. -/
theorem AllWS.take {d : Nat} {xs : List Expr} (h : AllWS d xs) (k : Nat) :
    AllWS d (xs.take k) :=
  fun x hx => h x (List.mem_of_mem_take hx)
grind_pattern [conleche_grind] AllWS.take => AllWS d xs, xs.take k

/-- A suffix of well-scoped terms is well scoped. -/
theorem AllWS.drop {d : Nat} {xs : List Expr} (h : AllWS d xs) (k : Nat) :
    AllWS d (xs.drop k) :=
  fun x hx => h x (List.mem_of_mem_drop hx)
grind_pattern [conleche_grind] AllWS.drop => AllWS d xs, xs.drop k

theorem AllWS.getD {d : Nat} {xs : List Expr} (h : AllWS d xs) (n : Nat) :
    Expr.WScoped d (xs.getD n (.bvar 0)) :=
  wscoped_getD h n
grind_pattern [conleche_grind] AllWS.getD => AllWS d xs, xs.getD n (.bvar 0)

theorem AllWS.mono {d d' : Nat} {xs : List Expr} (hle : d ≤ d') (h : AllWS d xs) :
    AllWS d' xs := fun x hx => Expr.WScoped.mono hle (h x hx)

/-- An optional answer is well scoped at `d` where present. -/
@[expose] def OptWS (d : Nat) : Option Expr → Prop
  | none => True
  | some e => Expr.WScoped d e

@[conleche_grind =] theorem OptWS.none_eq (d : Nat) : OptWS d none = True := rfl

@[conleche_grind =] theorem OptWS.some_eq (d : Nat) (e : Expr) :
    OptWS d (some e) = Expr.WScoped d e := rfl

/-- A loop step's term is well scoped at `d`. -/
@[expose] def StepWS (d : Nat) : WhnfStep → Prop
  | .done e => Expr.WScoped d e
  | .cont e => Expr.WScoped d e

@[conleche_grind =] theorem StepWS.done_eq (d : Nat) (e : Expr) :
    StepWS d (.done e) = Expr.WScoped d e := rfl

@[conleche_grind =] theorem StepWS.cont_eq (d : Nat) (e : Expr) :
    StepWS d (.cont e) = Expr.WScoped d e := rfl

/-- Every element of the list satisfies `P` (a named predicate, so that
no `∀` reaches `grind`; `P` is itself a named predicate, never a
`fun`). -/
@[expose] def ListAll {α : Type} (P : α → Prop) (xs : List α) : Prop := ∀ x ∈ xs, P x

@[conleche_grind =] theorem ListAll.nil_eq {α : Type} (P : α → Prop) :
    ListAll P [] = True := by
  simp [ListAll]

@[conleche_grind =] theorem ListAll.cons_eq {α : Type} (P : α → Prop) (x : α) (xs : List α) :
    ListAll P (x :: xs) = (P x ∧ ListAll P xs) := by
  simp [ListAll]

@[conleche_grind =] theorem ListAll.append_eq {α : Type} (P : α → Prop) (xs ys : List α) :
    ListAll P (xs ++ ys) = (ListAll P xs ∧ ListAll P ys) := by
  simp only [ListAll, List.mem_append]
  exact propext ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

@[conleche_grind =] theorem ListAll.reverse_eq {α : Type} (P : α → Prop) (xs : List α) :
    ListAll P xs.reverse = ListAll P xs := by
  simp [ListAll]

/-! ### `Expr.WScoped`, one constructor at a time -/

@[conleche_grind =] theorem wscoped_app_eq (d : Nat) (g a : Expr) :
    Expr.WScoped d (.app g a) = (Expr.WScoped d g ∧ Expr.WScoped d a) := by
  rw [Expr.WScoped]

@[conleche_grind =] theorem wscoped_lam_eq (d : Nat) (ty body : Expr) :
    Expr.WScoped d (.lam ty body) = (Expr.WScoped d ty ∧ Expr.WScoped d body) := by
  rw [Expr.WScoped]

@[conleche_grind =] theorem wscoped_forallE_eq (d : Nat) (ty body : Expr) :
    Expr.WScoped d (.forallE ty body) = (Expr.WScoped d ty ∧ Expr.WScoped d body) := by
  rw [Expr.WScoped]

@[conleche_grind =] theorem wscoped_letE_eq (d : Nat) (ty v b : Expr) :
    Expr.WScoped d (.letE ty v b) =
      (Expr.WScoped d ty ∧ Expr.WScoped d v ∧ Expr.WScoped d b) := by
  rw [Expr.WScoped]

@[conleche_grind =] theorem wscoped_fvar_eq (k i : Nat) (ty : Expr) :
    Expr.WScoped k (.fvar i ty) = (i < k ∧ Expr.WScoped i ty) := by
  rw [Expr.WScoped]

@[conleche_grind =] theorem wscoped_proj_eq (d : Nat) (sn : Name) (i : Nat) (e : Expr) :
    Expr.WScoped d (.proj sn i e) = Expr.WScoped d e := by
  rw [Expr.WScoped]

@[conleche_grind =] theorem wscoped_sort_eq (d : Nat) (u : Level) :
    Expr.WScoped d (.sort u) = True := by
  rw [Expr.WScoped]

@[conleche_grind =] theorem wscoped_const_eq (d : Nat) (n : Name) (us : List Level) :
    Expr.WScoped d (.const n us) = True := by
  rw [Expr.WScoped]

@[conleche_grind =] theorem wscoped_lit_eq (d : Nat) (l : Literal) :
    Expr.WScoped d (.lit l) = True := by
  rw [Expr.WScoped]

/-- A closed term is scoped at every depth (a fact the walks state at
the depths they need: as a pattern on every `WScoped` term it would
cost every walk its instances). -/
theorem wscoped_of_hasFvar_false {d : Nat} {e : Expr} (h : e.hasFvar = false) :
    Expr.WScoped d e :=
  Expr.WScoped.of_not_hasFvar h

/-! ### `Expr.WScoped` through the walks' operations -/

/-- One more binder in scope keeps a term well scoped. -/
theorem wscoped_succ {d : Nat} {e : Expr} (h : Expr.WScoped d e) : Expr.WScoped (d + 1) e :=
  h.mono (Nat.le_succ d)
grind_pattern [conleche_grind] wscoped_succ => Expr.WScoped d e, Expr.WScoped (d + 1) e

/-- Instantiation with a well-scoped value keeps a term well scoped. -/
theorem wscoped_instantiate1_gen {d : Nat} {e v : Expr} (k : Nat) (hv : Expr.WScoped d v)
    (he : Expr.WScoped d e) : Expr.WScoped d (e.instantiate1 v k) :=
  Expr.WScoped.instantiate1_gen hv k he
grind_pattern [conleche_grind] wscoped_instantiate1_gen =>
  Expr.WScoped d v, Expr.WScoped d e, e.instantiate1 v k

/-- Opening a binder at the next free variable scopes the body one
deeper. -/
theorem wscoped_open {d : Nat} {ty e : Expr} (k : Nat) (hty : Expr.WScoped d ty)
    (he : Expr.WScoped d e) : Expr.WScoped (d + 1) (e.instantiate1 (.fvar d ty) k) :=
  Expr.WScoped.instantiate1 hty k he
grind_pattern [conleche_grind] wscoped_open =>
  Expr.WScoped d e, e.instantiate1 (.fvar d ty) k

/-- Bulk instantiation with well-scoped values keeps a well-scoped term
well scoped. -/
theorem wscoped_instantiateList {d : Nat} {e : Expr} (he : Expr.WScoped d e) :
    ∀ {vs : List Expr} {k : Nat}, AllWS d vs → Expr.WScoped d (e.instantiateList vs k) := by
  intro vs
  induction vs with
  | nil => intro k _; rw [Expr.instantiateList_nil]; exact he
  | cons v vs ih =>
    intro k hvs
    rw [Expr.instantiateList_cons]
    rw [AllWS.cons_eq] at hvs
    exact Expr.WScoped.instantiate1_gen hvs.1 k (ih hvs.2)
grind_pattern [conleche_grind] wscoped_instantiateList =>
  Expr.WScoped d e, e.instantiateList vs k

theorem instList_lam_eq (ty body : Expr) (ws : List Expr) :
    (Expr.lam ty body).instantiateList ws
      = .lam (ty.instantiateList ws) (body.instantiateList ws 1) := by
  simp [Expr.instantiateList]
grind_pattern [conleche_grind] instList_lam_eq => (Expr.lam ty body).instantiateList ws

theorem instList_forallE_eq (ty body : Expr) (ws : List Expr) :
    (Expr.forallE ty body).instantiateList ws
      = .forallE (ty.instantiateList ws) (body.instantiateList ws 1) := by
  simp [Expr.instantiateList]
grind_pattern [conleche_grind] instList_forallE_eq => (Expr.forallE ty body).instantiateList ws

/-- One binder opened at the next free variable: the body, instantiated
with it in front of the accumulator, is scoped one deeper. -/
theorem wscoped_open_binder {D D' : Nat} {ty body : Expr} {ws : List Expr}
    (hty : Expr.WScoped D ty) (hb : Expr.WScoped D (body.instantiateList ws 1))
    (hD : D' = D + 1) :
    Expr.WScoped D' (body.instantiateList (Expr.fvar D ty :: ws)) := by
  subst hD
  rw [Expr.instantiateList_cons]
  exact Expr.WScoped.instantiate1 hty 0 hb
grind_pattern [conleche_grind] wscoped_open_binder =>
  Expr.WScoped D' (body.instantiateList (Expr.fvar D ty :: ws))

/-- Pushing on the accumulator array conses on its reversed read
(task #97: the loops keep the opened fvars innermost-**last**; the
mirrors' lists stay innermost-first). -/
@[conleche_grind =] theorem toListRev_push {α} (a : Array α) (x : α) :
    (a.push x).toList.reverse = x :: a.toList.reverse := by
  simp

theorem toListRev_singleton {α} (x : α) :
    (#[x] : Array α).toList.reverse = [x] := by
  simp

theorem toListRev_empty {α} :
    (#[] : Array α).toList.reverse = ([] : List α) := by
  simp

/-- A spine over a well-scoped head and arguments is well scoped: keyed
by the head's scope fact (forward) and by the goal (the head is a term
the walk computed, whose scope is derived on demand). -/
theorem wscoped_mkAppN {d : Nat} {g : Expr} {xs : List Expr} (hg : Expr.WScoped d g)
    (hxs : AllWS d xs) : Expr.WScoped d (Expr.mkAppN g xs) :=
  Expr.WScoped.mkAppN hg hxs
grind_pattern [conleche_grind] wscoped_mkAppN => Expr.WScoped d g, Expr.mkAppN g xs
grind_pattern [conleche_grind] wscoped_mkAppN => Expr.WScoped d (Expr.mkAppN g xs)

/-- A constant applied to well-scoped arguments is well scoped. -/
theorem wscoped_mkAppN_const {d : Nat} {n : Name} {us : List Level} {xs : List Expr}
    (h : AllWS d xs) : Expr.WScoped d (Expr.mkAppN (.const n us) xs) :=
  Expr.WScoped.mkAppN (by rw [Expr.WScoped]; trivial) h
grind_pattern [conleche_grind] wscoped_mkAppN_const => AllWS d xs, Expr.mkAppN (.const n us) xs

/-- A well-scoped spine's head is well scoped. -/
theorem wscoped_getAppFn {d : Nat} {e : Expr} (h : Expr.WScoped d e) :
    Expr.WScoped d e.getAppFn :=
  h.getAppFn
grind_pattern [conleche_grind] wscoped_getAppFn => Expr.WScoped d e, e.getAppFn

/-- A well-scoped spine's arguments are well scoped. -/
theorem allWS_getAppArgs {d : Nat} {e : Expr} (h : Expr.WScoped d e) :
    AllWS d e.getAppArgs :=
  h.getAppArgs
grind_pattern [conleche_grind] allWS_getAppArgs => Expr.WScoped d e, e.getAppArgs

/-- A level instantiation of an `fvar`-free term (a stored type or rule
right-hand side) is well scoped. -/
theorem wscoped_instLevels {d : Nat} {e : Expr} (h : e.hasFvar = false) (ps : List Name)
    (us : List Level) : Expr.WScoped d (e.instantiateLevelParams ps us) :=
  wscoped_instLevels_of_not_hasFvar h ps us
grind_pattern [conleche_grind] wscoped_instLevels =>
  Expr.WScoped d (e.instantiateLevelParams ps us)

/-! ## 5. The index and the operation-free cached operations -/

attribute [conleche_grind =] mkFEnv_find? mkFEnv_findTable? Expr.getAppArgsC_spec Expr.mkBvar_eq
  Expr.instSpineC_spec Expr.instLevelParams_spec

/-- The index's lookup as a function (for the readers that take the
lookup itself as an argument). -/
@[conleche_grind =] theorem mkFEnv_find_fun (env : Env) :
    (mkFEnv env).find? = env.find? :=
  funext (mkFEnv_find? env)

@[conleche_grind =] theorem mkFEnv_findTable_fun (env : Env) :
    (mkFEnv env).findTable? = env.findTable? :=
  funext (mkFEnv_findTable? env)

/-! ## 6. The value relations as answers -/

theorem relEC_inv {d : Nat} (v' v : Expr) (h : RelEC d v' v) : v' = v ∧ Expr.WScoped d v' :=
  ⟨h.1, h.1 ▸ h.2⟩

theorem relEC_diag {d : Nat} (v : Expr) (h : Expr.WScoped d v) : RelEC d v v := ⟨rfl, h⟩

/-! ## 7. The knot's slots

A memo wrapper's body is specified as a named predicate (`BodySpec`,
`BodySpecB`), not as a `∀`-triple hypothesis: a `∀` fact in the context
is an E-matching theorem `grind` instantiates at every state and input
in sight, while the named predicate is an atom, and its triple enters
`vcgen`'s list as the term `hbody.triple`. -/

/-- A unary entry point's body simulates its fueled body on well-scoped
inputs, with a well-scoped answer. -/
@[expose] def BodySpec (mode : CheckMode) (eager : Bool) (env : Env) (body : Nat → Expr → CheckCM
    Expr)
    (spec : Nat → Expr → FueledM Expr) : Prop :=
  ∀ {s₀ : CState} {d : Nat} {i : Expr}, CSOK mode eager env s₀ → Expr.WScoped d i →
    ⦃fun s => s = s₀⦄ body d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs (spec d i) r ∧ Expr.WScoped d r; ⊤⦄

theorem BodySpec.triple {body : Nat → Expr → CheckCM Expr} {spec : Nat → Expr → FueledM Expr}
    (h : BodySpec mode eager env body spec) {s₀ : CState} {d : Nat} {i : Expr}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ body d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs (spec d i) r ∧ Expr.WScoped d r; ⊤⦄ := h hs hw

/-- A binary `Bool`-valued entry point's body simulates its fueled body
on well-scoped inputs (`BodySpec` for the defeq slot). -/
@[expose] def BodySpecB (mode : CheckMode) (eager : Bool) (env : Env) (body : Nat → Expr → Expr →
    CheckCM Bool)
    (spec : Nat → Expr → Expr → FueledM Bool) : Prop :=
  ∀ {s₀ : CState} {d : Nat} {a b : Expr}, CSOK mode eager env s₀ → Expr.WScoped d a →
    Expr.WScoped d b →
    ⦃fun s => s = s₀⦄ body d a b ⦃fun r s' => CSOK mode eager env s' ∧ Runs (spec d a b) r; ⊤⦄

theorem BodySpecB.triple {body : Nat → Expr → Expr → CheckCM Bool}
    {spec : Nat → Expr → Expr → FueledM Bool} (h : BodySpecB mode eager env body spec)
    {s₀ : CState} {d : Nat} {a b : Expr} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ body d a b ⦃fun r s' => CSOK mode eager env s' ∧ Runs (spec d a b) r; ⊤⦄ :=
  h hs hwa hwb

end ConLeche.Cached
