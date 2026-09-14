module

public import ConLeche.Verify.Inductives.NestedRestore
import ConLeche.Verify.Inductives.NestedWalk
import ConLeche.Verify.Inductives.NestedLedger
import ConLeche.Verify.Inductives.NestedFacts
import ConLeche.Verify.AbstractRange
public import ConLeche.Verify.Inductives.NestedLeaves

public section

/-!
# The restore undoes the walk (task #279 M-D′, step (1), DESIGN §M.45)

The constructor read's syntactic half (`CopyWalkFacts`) compares a
copy's STORED constructor field — what K.17's witness restores and
`whnf`s — with the container's constructor instantiated at the pin.
The link between the two is the elimination's walk: the container's
instantiated field is the walk's INPUT, the processed constructor's
field its OUTPUT, and the restore (`restoreI`, `NestedRestore.lean`)
is the walk's inverse on any input that mentions no table name.

* **`restoreI_walk`** (W1, the restore form): for a walk
  `replaceAllNested … st e = .ok (e', st')` on an input `e` mentioning
  no table name outside `fvar` annotations, and any instantiation of
  the two at free variables, `restoreI R (instSeq xs t e')` is
  `instSeq xs t e` up to erasure — with `R` a table whose pins are the
  final state's pins at the parameters (`R.pins.lookup q.aux =
  some q.pin`).  At a fire the copy application restores to the pin,
  which is the container application the fire consumed; at every
  other node the restore descends as the walk did (the output's head
  constant at a non-fire node is the input's, `replaceAllNested_head_of_nofire`,
  so no table key heads a node the walk did not fire on).
* **`instSeq_abstractRange`**: the pin round trip — a term whose `fvar`
  leaves are the openers, abstracted over them and instantiated back,
  is itself — which puts `restoreTbl`'s abstracted pins back at the
  parameters (`restoreTbl_instAt_lookup`).
-/

namespace ConLeche

open Expr

/-! ## The walk's node inversions, completed -/

/-- The walk at an application: pruned (the input, the state), a fire
at the top, or the children at a declined node. -/
theorem replaceAllNested_app' {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {f a r : Expr}
    (h : replaceAllNested env blvls params pbs st (.app f a) = .ok (r, st')) :
    (r = .app f a ∧ st' = st) ∨
    replaceIfNested env blvls params pbs st (.app f a) = .ok (some (r, st')) ∨
    (replaceIfNested env blvls params pbs st (.app f a) = .ok none ∧
      ∃ (f' a' : Expr) (st₁ : ElimState),
        replaceAllNested env blvls params pbs st f = .ok (f', st₁) ∧
          replaceAllNested env blvls params pbs st₁ a = .ok (a', st') ∧ r = .app f' a') := by
  rw [replaceAllNested] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · split at h
    · exact nomatch h
    · next p hp =>
      obtain rfl := Except.ok.inj h
      exact Or.inr (Or.inl hp)
    · next hnone =>
      split at h
      · exact nomatch h
      · next f' st₁ hf =>
        split at h
        · exact nomatch h
        · next a' st₂ ha =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr (Or.inr ⟨hnone, f', a', st₁, hf, ha, rfl⟩)

/-- The walk is a congruence at a `let`. -/
theorem replaceAllNested_letE {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {ty v b r : Expr}
    (h : replaceAllNested env blvls params pbs st (.letE ty v b) = .ok (r, st')) :
    ∃ (ty' v' b' : Expr) (st₁ st₂ : ElimState),
      replaceAllNested env blvls params pbs st ty = .ok (ty', st₁) ∧
        replaceAllNested env blvls params pbs st₁ v = .ok (v', st₂) ∧
        replaceAllNested env blvls params pbs st₂ b = .ok (b', st') ∧
        r = .letE ty' v' b' := by
  rw [replaceAllNested] at h
  split at h
  · next hpr =>
    simp only [Bool.not_eq_true', List.any_eq_false] at hpr
    have hty : st.newNames.any (fun T => ty.mentionsConst T) = false := by
      rw [List.any_eq_false]
      intro T hT
      have := hpr T hT
      simp only [Expr.mentionsConst, Bool.or_eq_true, not_or, Bool.not_eq_true] at this
      simp [this.1.1]
    have hv : st.newNames.any (fun T => v.mentionsConst T) = false := by
      rw [List.any_eq_false]
      intro T hT
      have := hpr T hT
      simp only [Expr.mentionsConst, Bool.or_eq_true, not_or, Bool.not_eq_true] at this
      simp [this.1.2]
    have hb : st.newNames.any (fun T => b.mentionsConst T) = false := by
      rw [List.any_eq_false]
      intro T hT
      have := hpr T hT
      simp only [Expr.mentionsConst, Bool.or_eq_true, not_or, Bool.not_eq_true] at this
      simp [this.2]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ty, v, b, st, st, replaceAllNested_prune hty, replaceAllNested_prune hv,
      replaceAllNested_prune hb, rfl⟩
  · rw [show replaceIfNested env blvls params pbs st (.letE ty v b) = .ok none from rfl] at h
    dsimp only at h
    split at h
    · exact nomatch h
    · next ty' st₁ hty =>
      split at h
      · exact nomatch h
      · next v' st₂ hv =>
        split at h
        · exact nomatch h
        · next b' st₃ hb =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨ty', v', b', st₁, st₂, hty, hv, hb, rfl⟩

/-- The walk is a congruence at a projection. -/
theorem replaceAllNested_proj {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {s : Name} {i : Nat} {x r : Expr}
    (h : replaceAllNested env blvls params pbs st (.proj s i x) = .ok (r, st')) :
    ∃ x' : Expr, replaceAllNested env blvls params pbs st x = .ok (x', st') ∧ r = .proj s i x' := by
  rw [replaceAllNested] at h
  split at h
  · next hpr =>
    simp only [Bool.not_eq_true', List.any_eq_false] at hpr
    have hx : st.newNames.any (fun T => x.mentionsConst T) = false := by
      rw [List.any_eq_false]
      intro T hT
      have := hpr T hT
      simp only [Expr.mentionsConst, Bool.or_eq_true, not_or, Bool.not_eq_true] at this
      simp [this.2]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨x, replaceAllNested_prune hx, rfl⟩
  · rw [show replaceIfNested env blvls params pbs st (.proj s i x) = .ok none from rfl] at h
    dsimp only at h
    split at h
    · exact nomatch h
    · next x' st₁ hx =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨x', hx, rfl⟩

/-- A leaf is its own walk. -/
theorem replaceAllNested_bvar {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st : ElimState} {i : Nat} :
    replaceAllNested env blvls params pbs st (.bvar i) = .ok (.bvar i, st) := by
  unfold replaceAllNested
  split <;> rfl

theorem replaceAllNested_fvar {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st : ElimState} {i : Nat} {ty : Expr} :
    replaceAllNested env blvls params pbs st (.fvar i ty) = .ok (.fvar i ty, st) := by
  unfold replaceAllNested
  split <;> rfl

theorem replaceAllNested_sort {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st : ElimState} {u : Level} :
    replaceAllNested env blvls params pbs st (.sort u) = .ok (.sort u, st) := by
  unfold replaceAllNested
  split <;> rfl

theorem replaceAllNested_const {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st : ElimState} {n : Name} {us : List Level} :
    replaceAllNested env blvls params pbs st (.const n us) = .ok (.const n us, st) := by
  unfold replaceAllNested
  split <;> rfl

theorem replaceAllNested_lit {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st : ElimState} {l : Literal} :
    replaceAllNested env blvls params pbs st (.lit l) = .ok (.lit l, st) := by
  unfold replaceAllNested
  split <;> rfl

/-! ## The output's head at a non-fire node -/

/-- The blind mention at the head. -/
theorem Expr.mentionsConstE_of_getAppFn {T : Name} :
    ∀ (e : Expr) (us : List Level), e.getAppFn = .const T us → e.mentionsConstE T = true
  | .app f a, us, h => by
    simp only [Expr.mentionsConstE, Bool.or_eq_true]
    exact Or.inl (mentionsConstE_of_getAppFn f us h)
  | .const n vs, us, h => by
    simp only [Expr.getAppFn, Expr.const.injEq] at h
    simp [Expr.mentionsConstE, h.1]
  | .bvar _, _, h | .fvar _ _, _, h | .sort _, _, h | .lam _ _ _, _, h
  | .forallE _ _ _, _, h | .letE _ _ _, _, h | .lit _, _, h | .proj _ _ _, _, h => by
    simp [Expr.getAppFn] at h

/-- **The output's head constant at a node the walk did not fire on is
the input's**: a fire below the top would have fired at the top
(`replaceIfNested_app_of_fire`), so an application's function is walked
without a fire too, and every other node keeps its constructor. -/
theorem replaceAllNested_head_of_nofire {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs st e = .ok (e', st') →
      (∀ r, replaceIfNested env blvls params pbs st e ≠ .ok (some r)) →
      ∀ {n : Name} {us : List Level}, e'.getAppFn = .const n us → e.getAppFn = .const n us
  | .app f a, st, st', e', h, hnf, n, us, hfn => by
    rcases replaceAllNested_app' h with ⟨rfl, -⟩ | hfire | ⟨-, f', a', st₁, hf, -, rfl⟩
    · exact hfn
    · exact absurd hfire (hnf _)
    · have hnf' : ∀ r, replaceIfNested env blvls params pbs st f ≠ .ok (some r) := by
        intro r hr
        obtain ⟨r', hr'⟩ := replaceIfNested_app_of_fire (a := a) hr
        exact hnf _ hr'
      exact replaceAllNested_head_of_nofire f hf hnf' hfn
  | .lam ty b bm, st, st', e', h, _, n, us, hfn => by
    obtain ⟨ty', b', st₁, -, -, he'⟩ := replaceAllNested_lam h
    rw [he'] at hfn
    simp [Expr.getAppFn] at hfn
  | .forallE ty b bm, st, st', e', h, _, n, us, hfn => by
    obtain ⟨ty', b', st₁, -, -, he'⟩ := replaceAllNested_forallE h
    rw [he'] at hfn
    simp [Expr.getAppFn] at hfn
  | .letE ty v b, st, st', e', h, _, n, us, hfn => by
    obtain ⟨ty', v', b', st₁, st₂, -, -, -, he'⟩ := replaceAllNested_letE h
    rw [he'] at hfn
    simp [Expr.getAppFn] at hfn
  | .proj s i x, st, st', e', h, _, n, us, hfn => by
    obtain ⟨x', -, he'⟩ := replaceAllNested_proj h
    rw [he'] at hfn
    simp [Expr.getAppFn] at hfn
  | .bvar i, st, st', e', h, _, n, us, hfn => by
    rw [replaceAllNested_bvar] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact hfn
  | .fvar i ty, st, st', e', h, _, n, us, hfn => by
    rw [replaceAllNested_fvar] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact hfn
  | .sort u, st, st', e', h, _, n, us, hfn => by
    rw [replaceAllNested_sort] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact hfn
  | .const c vs, st, st', e', h, _, n, us, hfn => by
    rw [replaceAllNested_const] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact hfn
  | .lit l, st, st', e', h, _, n, us, hfn => by
    rw [replaceAllNested_lit] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact hfn

/-! ## The restore's descent -/

/-- The head step declines at a spine whose head names no table key. -/
theorem restoreHeadI_none_of_head {R : RestoreTbl} (hR : R.Named) {e : Expr}
    (hne : ∀ (n : Name) (us : List Level), e.getAppFn = .const n us → n ∉ R.auxNames) :
    restoreHeadI R e = none := by
  unfold restoreHeadI
  split
  · next n us hn =>
    have hnot := hne n us hn
    cases hl : R.pins.lookup n with
    | some pin => exact absurd (hR.pinsNamed _ (List.mem_of_lookup_some hl)) hnot
    | none =>
      dsimp only
      cases hf : R.ctorPins.find? (fun q => q.1 == n) with
      | some x =>
        have hmem := List.mem_of_find?_eq_some hf
        have hx : x.1 = n := by
          have := List.find?_some hf
          exact beq_iff_eq.mp this
        exact absurd (hx ▸ hR.ctorPinsNamed x hmem) hnot
      | none => rfl
  · rfl

/-- The node step declines at an application whose head names no
table key. -/
theorem restoreNodeI_app_none {R : RestoreTbl} (hR : R.Named) {f a : Expr}
    (hne : ∀ (n : Name) (us : List Level), (Expr.app f a).getAppFn = .const n us →
      n ∉ R.auxNames) :
    restoreNodeI R (.app f a) = none := by
  rw [restoreNodeI_eq]
  exact restoreHeadI_none_of_head hR hne

/-- The restore descends through an application whose node step
declines. -/
theorem restoreI_app' {R : RestoreTbl} (hR : R.Named) (f a : Expr)
    (hnode : restoreNodeI R (.app f a) = none) :
    restoreI R (.app f a) = .app (restoreI R f) (restoreI R a) := by
  by_cases hp : ∀ n ∈ R.auxNames, (Expr.app f a).mentionsConst n = false
  · rw [restoreI_app, restoreStepI_prune hp]
    have hf : ∀ n ∈ R.auxNames, f.mentionsConstE n = false := by
      intro n hn
      have := hp n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      cases hE : f.mentionsConstE n with
      | false => rfl
      | true => rw [Expr.mentionsConst_of_mentionsConstE f hE] at this; exact nomatch this.1
    have ha : ∀ n ∈ R.auxNames, a.mentionsConstE n = false := by
      intro n hn
      have := hp n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      cases hE : a.mentionsConstE n with
      | false => rfl
      | true => rw [Expr.mentionsConst_of_mentionsConstE a hE] at this; exact nomatch this.2
    rw [restoreI_eq_self hR f hf, restoreI_eq_self hR a ha]
  · have hsome : ∃ n ∈ R.auxNames, (Expr.app f a).mentionsConst n = true := by
      refine Classical.byContradiction fun hne => hp fun n hn => ?_
      cases hm : (Expr.app f a).mentionsConst n with
      | false => rfl
      | true => exact absurd ⟨n, hn, hm⟩ hne
    obtain ⟨n, hn, hm⟩ := hsome
    exact restoreI_of_decline_app hn hm hnode

/-- Descent through a `λ`, unconditionally. -/
theorem restoreI_lam' {R : RestoreTbl} (hR : R.Named) (ty b : Expr) (bm : BinderMeta) :
    restoreI R (.lam ty b bm) = .lam (restoreI R ty) (restoreI R b) bm := by
  by_cases hp : ∀ n ∈ R.auxNames, (Expr.lam ty b bm).mentionsConst n = false
  · rw [restoreI_lam, restoreStepI_prune hp]
    have hty : ∀ n ∈ R.auxNames, ty.mentionsConstE n = false := by
      intro n hn
      have := hp n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      cases hE : ty.mentionsConstE n with
      | false => rfl
      | true => rw [Expr.mentionsConst_of_mentionsConstE ty hE] at this; exact nomatch this.1
    have hb : ∀ n ∈ R.auxNames, b.mentionsConstE n = false := by
      intro n hn
      have := hp n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      cases hE : b.mentionsConstE n with
      | false => rfl
      | true => rw [Expr.mentionsConst_of_mentionsConstE b hE] at this; exact nomatch this.2
    rw [restoreI_eq_self hR ty hty, restoreI_eq_self hR b hb]
  · have hsome : ∃ n ∈ R.auxNames, (Expr.lam ty b bm).mentionsConst n = true := by
      refine Classical.byContradiction fun hne => hp fun n hn => ?_
      cases hm : (Expr.lam ty b bm).mentionsConst n with
      | false => rfl
      | true => exact absurd ⟨n, hn, hm⟩ hne
    obtain ⟨n, hn, hm⟩ := hsome
    exact restoreI_of_decline_lam hn hm (by
      rw [restoreNodeI_eq (R := R)]
      exact restoreHeadI_nonconst (fun _ _ h => by simp [Expr.getAppFn] at h))

/-- Descent through a `let`, unconditionally. -/
theorem restoreI_letE' {R : RestoreTbl} (hR : R.Named) (ty v b : Expr) :
    restoreI R (.letE ty v b) = .letE (restoreI R ty) (restoreI R v) (restoreI R b) := by
  by_cases hp : ∀ n ∈ R.auxNames, (Expr.letE ty v b).mentionsConst n = false
  · rw [restoreI_letE, restoreStepI_prune hp]
    have hty : ∀ n ∈ R.auxNames, ty.mentionsConstE n = false := by
      intro n hn
      have := hp n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      cases hE : ty.mentionsConstE n with
      | false => rfl
      | true => rw [Expr.mentionsConst_of_mentionsConstE ty hE] at this; exact nomatch this.1.1
    have hv : ∀ n ∈ R.auxNames, v.mentionsConstE n = false := by
      intro n hn
      have := hp n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      cases hE : v.mentionsConstE n with
      | false => rfl
      | true => rw [Expr.mentionsConst_of_mentionsConstE v hE] at this; exact nomatch this.1.2
    have hb : ∀ n ∈ R.auxNames, b.mentionsConstE n = false := by
      intro n hn
      have := hp n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      cases hE : b.mentionsConstE n with
      | false => rfl
      | true => rw [Expr.mentionsConst_of_mentionsConstE b hE] at this; exact nomatch this.2
    rw [restoreI_eq_self hR ty hty, restoreI_eq_self hR v hv, restoreI_eq_self hR b hb]
  · have hsome : ∃ n ∈ R.auxNames, (Expr.letE ty v b).mentionsConst n = true := by
      refine Classical.byContradiction fun hne => hp fun n hn => ?_
      cases hm : (Expr.letE ty v b).mentionsConst n with
      | false => rfl
      | true => exact absurd ⟨n, hn, hm⟩ hne
    obtain ⟨n, hn, hm⟩ := hsome
    exact restoreI_of_decline_letE hn hm (by
      rw [restoreNodeI_eq (R := R)]
      exact restoreHeadI_nonconst (fun _ _ h => by simp [Expr.getAppFn] at h))

/-- Descent through a projection, unconditionally. -/
theorem restoreI_proj' {R : RestoreTbl} (hR : R.Named) (s : Name) (i : Nat) (x : Expr) :
    restoreI R (.proj s i x) = .proj s i (restoreI R x) := by
  by_cases hp : ∀ n ∈ R.auxNames, (Expr.proj s i x).mentionsConst n = false
  · rw [restoreI_proj, restoreStepI_prune hp]
    have hx : ∀ n ∈ R.auxNames, x.mentionsConstE n = false := by
      intro n hn
      have := hp n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      cases hE : x.mentionsConstE n with
      | false => rfl
      | true => rw [Expr.mentionsConst_of_mentionsConstE x hE] at this; exact nomatch this.2
    rw [restoreI_eq_self hR x hx]
  · have hsome : ∃ n ∈ R.auxNames, (Expr.proj s i x).mentionsConst n = true := by
      refine Classical.byContradiction fun hne => hp fun n hn => ?_
      cases hm : (Expr.proj s i x).mentionsConst n with
      | false => rfl
      | true => exact absurd ⟨n, hn, hm⟩ hne
    obtain ⟨n, hn, hm⟩ := hsome
    exact restoreI_of_decline_proj hn hm (by
      rw [restoreNodeI_eq (R := R)]
      exact restoreHeadI_nonconst (fun _ _ h => by simp [Expr.getAppFn] at h))

/-! ## W1, the restore form -/

/-- The blind mention of a child is the parent's. -/
theorem Expr.mentionsConstE_children {T : Name} :
    (∀ {f a : Expr}, (Expr.app f a).mentionsConstE T = false →
      f.mentionsConstE T = false ∧ a.mentionsConstE T = false) ∧
    (∀ {ty b : Expr} {bm : BinderMeta}, (Expr.lam ty b bm).mentionsConstE T = false →
      ty.mentionsConstE T = false ∧ b.mentionsConstE T = false) ∧
    (∀ {ty b : Expr} {bm : BinderMeta}, (Expr.forallE ty b bm).mentionsConstE T = false →
      ty.mentionsConstE T = false ∧ b.mentionsConstE T = false) ∧
    (∀ {ty v b : Expr}, (Expr.letE ty v b).mentionsConstE T = false →
      ty.mentionsConstE T = false ∧ v.mentionsConstE T = false ∧ b.mentionsConstE T = false) ∧
    (∀ {s : Name} {i : Nat} {x : Expr}, (Expr.proj s i x).mentionsConstE T = false →
      x.mentionsConstE T = false) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    simp only [Expr.mentionsConstE, Bool.or_eq_false_iff] at h
  · exact h
  · exact h
  · exact h
  · exact ⟨h.1.1, h.1.2, h.2⟩
  · exact h.2

/-- **The restore undoes the walk** (W1, the restore form — DESIGN
§M.45): a walk on an input mentioning no table name outside `fvar`
annotations, instantiated at free variables, restores to the
instantiated input up to erasure.  `R` holds, at the parameters, every
pin of the final state (`P` lists them); at a fire the copy application
at the parameters and index arguments restores to `q.pin` at those
arguments, which is the container application the fire consumed
(`replaceIfNested_some`); elsewhere the restore descends. -/
theorem restoreI_walk {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {R : RestoreTbl} (hR : R.Named)
    (hnP : R.nP = params.length) (hparC : ∀ p ∈ params, p.looseBVarsBounded 0 = true)
    {P : List NestedPin}
    (hP : ∀ q ∈ P, R.pins.lookup q.aux = some q.pin ∧ R.recMap.lookup q.aux = none ∧
      ∀ x ∈ q.pin.getAppArgs, x.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs st e = .ok (e', st') →
      (∀ q ∈ st'.pins, q ∈ P) →
      (∀ n ∈ R.auxNames, e.mentionsConstE n = false) →
      ∀ (xs : List Expr) (t : Nat), Expr.AllFvars xs → xs.length ≤ t + 1 →
        Expr.ErasedEq (restoreI R (Expr.instSeq xs t e')) (Expr.instSeq xs t e)
  | .app f a, st, st', e', h, hst', he, xs, t, hxs, hlen => by
    rcases replaceAllNested_app' h with ⟨rfl, -⟩ | hfire | ⟨hnone, f', a', st₁, hf, ha, rfl⟩
    · -- pruned: the output is the input, its own restoration
      rw [restoreI_eq_self hR _ (fun n hn => by
        rw [Expr.mentionsConstE_instSeq_fvars xs hxs]; exact he n hn)]
      exact Expr.ErasedEq.rfl _
    · -- a fire: the copy application restores to the pin
      obtain ⟨I, lvls, ci, aux, -, -, hshape, hr, q, hq, hqa, hqp⟩ := replaceIfNested_some hfire
      obtain ⟨hlook, hrec, hargsC⟩ := hP q (hst' q hq)
      have hDsC : ∀ x ∈ (Expr.app f a).getAppArgs.take ci.nP, x.looseBVarsBounded 0 = true := by
        intro x hx
        refine hargsC x ?_
        rw [hqp, Expr.getAppArgs_mkAppN]
        simpa [Expr.getAppArgs] using hx
      have hparI : params.map (Expr.instSeq xs t) = params := by
        rw [List.map_congr_left (fun p hp => instSeq_eq_self xs t (hparC p hp)), List.map_id']
      have hDsI : ((Expr.app f a).getAppArgs.take ci.nP).map (Expr.instSeq xs t)
          = (Expr.app f a).getAppArgs.take ci.nP := by
        rw [List.map_congr_left (fun x hx => instSeq_eq_self xs t (hDsC x hx)), List.map_id']
      rw [hr, instSeq_mkAppN, instSeq_mkAppN, hparI,
        instSeq_eq_self xs t (e := .const aux blvls) rfl, ← Expr.mkAppN_append,
        restoreI_fire hR (by rw [← hqa]; exact hlook) hnP.symm (fun _ => by rw [← hqa]; exact hrec),
        hqp, ← Expr.mkAppN_append]
      have hE : Expr.instSeq xs t (Expr.app f a)
          = Expr.mkAppN (.const I lvls) ((Expr.app f a).getAppArgs.map (Expr.instSeq xs t)) := by
        have h1 := congrArg (Expr.instSeq xs t) hshape
        rw [instSeq_mkAppN, instSeq_eq_self xs t (e := .const I lvls) rfl] at h1
        exact h1
      rw [hE, ← List.take_append_drop ci.nP (Expr.app f a).getAppArgs, List.map_append, hDsI,
        List.take_append_drop]
      exact Expr.ErasedEq.rfl _
    · -- a declined node: descend
      obtain ⟨hef, hea⟩ : (∀ n ∈ R.auxNames, f.mentionsConstE n = false) ∧
          (∀ n ∈ R.auxNames, a.mentionsConstE n = false) :=
        ⟨fun n hn => (Expr.mentionsConstE_children.1 (he n hn)).1,
          fun n hn => (Expr.mentionsConstE_children.1 (he n hn)).2⟩
      have hst₁ : ∀ q ∈ st₁.pins, q ∈ P := by
        intro q hq
        obtain ⟨new, hpins, -⟩ := replaceAllNested_grows a ha
        exact hst' q (by rw [hpins]; exact List.mem_append_left _ hq)
      have ihf := restoreI_walk hR hnP hparC hP f hf hst₁ hef xs t hxs hlen
      have iha := restoreI_walk hR hnP hparC hP a ha hst' hea xs t hxs hlen
      rw [instSeq_app, instSeq_app]
      have hnode : restoreNodeI R (.app (Expr.instSeq xs t f') (Expr.instSeq xs t a')) = none := by
        refine restoreNodeI_app_none hR fun n us hfn hn => ?_
        rw [← instSeq_app, getAppFn_instSeq_const_iff hxs hlen] at hfn
        have hfn' := replaceAllNested_head_of_nofire (.app f a) h
          (fun r hr => by rw [hnone] at hr; exact nomatch hr) hfn
        have := Expr.mentionsConstE_of_getAppFn _ us hfn'
        rw [he n hn] at this
        exact nomatch this
      rw [restoreI_app' hR _ _ hnode]
      exact ⟨ihf, iha⟩
  | .lam ty b bm, st, st', e', h, hst', he, xs, t, hxs, hlen => by
    obtain ⟨ty', b', st₁, hty, hb, rfl⟩ := replaceAllNested_lam h
    have hst₁ : ∀ q ∈ st₁.pins, q ∈ P := by
      intro q hq
      obtain ⟨new, hpins, -⟩ := replaceAllNested_grows b hb
      exact hst' q (by rw [hpins]; exact List.mem_append_left _ hq)
    have ih₁ := restoreI_walk hR hnP hparC hP ty hty hst₁
      (fun n hn => (Expr.mentionsConstE_children.2.1 (he n hn)).1) xs t hxs hlen
    have ih₂ := restoreI_walk hR hnP hparC hP b hb hst'
      (fun n hn => (Expr.mentionsConstE_children.2.1 (he n hn)).2) xs (t + 1) hxs (by omega)
    rw [instSeq_lam _ _ _ _ _ hlen, instSeq_lam _ _ _ _ _ hlen, restoreI_lam' hR]
    exact ⟨rfl, ih₁, ih₂⟩
  | .forallE ty b bm, st, st', e', h, hst', he, xs, t, hxs, hlen => by
    obtain ⟨ty', b', st₁, hty, hb, rfl⟩ := replaceAllNested_forallE h
    have hst₁ : ∀ q ∈ st₁.pins, q ∈ P := by
      intro q hq
      obtain ⟨new, hpins, -⟩ := replaceAllNested_grows b hb
      exact hst' q (by rw [hpins]; exact List.mem_append_left _ hq)
    have ih₁ := restoreI_walk hR hnP hparC hP ty hty hst₁
      (fun n hn => (Expr.mentionsConstE_children.2.2.1 (he n hn)).1) xs t hxs hlen
    have ih₂ := restoreI_walk hR hnP hparC hP b hb hst'
      (fun n hn => (Expr.mentionsConstE_children.2.2.1 (he n hn)).2) xs (t + 1) hxs (by omega)
    rw [instSeq_forallE _ _ _ _ _ hlen, instSeq_forallE _ _ _ _ _ hlen, restoreI_forallE' hR]
    exact ⟨rfl, ih₁, ih₂⟩
  | .letE ty v b, st, st', e', h, hst', he, xs, t, hxs, hlen => by
    obtain ⟨ty', v', b', st₁, st₂, hty, hv, hb, rfl⟩ := replaceAllNested_letE h
    have hst₂ : ∀ q ∈ st₂.pins, q ∈ P := by
      intro q hq
      obtain ⟨new, hpins, -⟩ := replaceAllNested_grows b hb
      exact hst' q (by rw [hpins]; exact List.mem_append_left _ hq)
    have hst₁ : ∀ q ∈ st₁.pins, q ∈ P := by
      intro q hq
      obtain ⟨new, hpins, -⟩ := replaceAllNested_grows v hv
      exact hst₂ q (by rw [hpins]; exact List.mem_append_left _ hq)
    have ih₁ := restoreI_walk hR hnP hparC hP ty hty hst₁
      (fun n hn => (Expr.mentionsConstE_children.2.2.2.1 (he n hn)).1) xs t hxs hlen
    have ih₂ := restoreI_walk hR hnP hparC hP v hv hst₂
      (fun n hn => (Expr.mentionsConstE_children.2.2.2.1 (he n hn)).2.1) xs t hxs hlen
    have ih₃ := restoreI_walk hR hnP hparC hP b hb hst'
      (fun n hn => (Expr.mentionsConstE_children.2.2.2.1 (he n hn)).2.2) xs (t + 1) hxs (by omega)
    rw [instSeq_letE _ _ _ _ _ hlen, instSeq_letE _ _ _ _ _ hlen, restoreI_letE' hR]
    exact ⟨ih₁, ih₂, ih₃⟩
  | .proj s i x, st, st', e', h, hst', he, xs, t, hxs, hlen => by
    obtain ⟨x', hx, rfl⟩ := replaceAllNested_proj h
    have ih := restoreI_walk hR hnP hparC hP x hx hst'
      (fun n hn => Expr.mentionsConstE_children.2.2.2.2 (he n hn)) xs t hxs hlen
    rw [instSeq_proj, instSeq_proj, restoreI_proj' hR]
    exact ⟨rfl, rfl, ih⟩
  | .bvar i, st, st', e', h, _, he, xs, t, hxs, _ => by
    rw [replaceAllNested_bvar] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    rw [restoreI_eq_self hR _ (fun n hn => by
      rw [Expr.mentionsConstE_instSeq_fvars xs hxs]; exact he n hn)]
    exact Expr.ErasedEq.rfl _
  | .fvar i ty, st, st', e', h, _, he, xs, t, hxs, _ => by
    rw [replaceAllNested_fvar] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    rw [restoreI_eq_self hR _ (fun n hn => by
      rw [Expr.mentionsConstE_instSeq_fvars xs hxs]; exact he n hn)]
    exact Expr.ErasedEq.rfl _
  | .sort u, st, st', e', h, _, he, xs, t, hxs, _ => by
    rw [replaceAllNested_sort] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    rw [restoreI_eq_self hR _ (fun n hn => by
      rw [Expr.mentionsConstE_instSeq_fvars xs hxs]; exact he n hn)]
    exact Expr.ErasedEq.rfl _
  | .const c vs, st, st', e', h, _, he, xs, t, hxs, _ => by
    rw [replaceAllNested_const] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    rw [restoreI_eq_self hR _ (fun n hn => by
      rw [Expr.mentionsConstE_instSeq_fvars xs hxs]; exact he n hn)]
    exact Expr.ErasedEq.rfl _
  | .lit l, st, st', e', h, _, he, xs, t, hxs, _ => by
    rw [replaceAllNested_lit] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    rw [restoreI_eq_self hR _ (fun n hn => by
      rw [Expr.mentionsConstE_instSeq_fvars xs hxs]; exact he n hn)]
    exact Expr.ErasedEq.rfl _

/-! ## The pin round trip -/

/-- Peeling the OUTERMOST variable off a bulk abstraction: the shorter
range one variable higher, then one `abstract1` of the outermost at
the cursor past the range.  (`abstract1` shifts no bound variable, so
the two orders agree everywhere.) -/
theorem abstractRange_succ_outer :
    ∀ (e : Expr) (d k c : Nat),
      e.abstractRange d (k + 1) c = (e.abstractRange (d + 1) k c).abstract1 d (c + k) := by
  intro e
  induction e with
  | fvar idx ty _ih =>
    intro d k c
    by_cases hlo : idx = d
    · subst hlo
      have h1 : idx ≤ idx ∧ idx < idx + (k + 1) := by omega
      have h2 : ¬ (idx + 1 ≤ idx ∧ idx < idx + 1 + k) := by omega
      simp only [Expr.abstractRange, if_pos h1, if_neg h2, Expr.abstract1, if_true]
      congr 1
      omega
    · by_cases hin : d + 1 ≤ idx ∧ idx < d + 1 + k
      · have h1 : d ≤ idx ∧ idx < d + (k + 1) := by omega
        simp only [Expr.abstractRange, if_pos h1, if_pos hin, Expr.abstract1]
        congr 1
        omega
      · have h1 : ¬ (d ≤ idx ∧ idx < d + (k + 1)) := by omega
        simp [Expr.abstractRange, if_neg h1, if_neg hin, Expr.abstract1, hlo]
  | _ =>
    intro d k c <;>
    simp_all [Expr.abstractRange, Expr.abstract1] <;>
    rw [show c + 1 + k = c + k + 1 by omega]

/-- A variable outside the range keeps its leaves. -/
theorem fvarConsistent_abstractRange {d₀ : Nat} {ty : Expr} :
    ∀ (e : Expr) (d k c : Nat), d₀ < d → Expr.fvarConsistent d₀ ty e →
      Expr.fvarConsistent d₀ ty (e.abstractRange d k c) := by
  intro e
  induction e with
  | fvar idx ty' _ih =>
    intro d k c hd hc
    simp only [Expr.abstractRange]
    split
    · simp [Expr.fvarConsistent]
    · exact hc
  | _ =>
    intro d k c hd hc <;>
    simp_all [Expr.abstractRange, Expr.fvarConsistent]

/-- Abstraction stays below the cursor plus the range. -/
theorem looseBVarsBounded_abstractRange :
    ∀ (e : Expr) (d k c : Nat), e.looseBVarsBounded c = true →
      (e.abstractRange d k c).looseBVarsBounded (c + k) = true := by
  intro e
  induction e with
  | bvar i =>
    intro d k c hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb ⊢
    simp only [Expr.abstractRange, Expr.looseBVarsBounded, decide_eq_true_eq]
    omega
  | fvar idx ty _ih =>
    intro d k c _
    simp only [Expr.abstractRange]
    split
    · simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
      omega
    · rfl
  | app f a ihf iha =>
    intro d k c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf d k c hb.1, iha d k c hb.2⟩
  | lam ty b bm ihty ihb =>
    intro d k c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨ihty d k c hb.1, ?_⟩
    have := ihb d k (c + 1) hb.2
    rwa [show c + 1 + k = c + k + 1 by omega] at this
  | forallE ty b bm ihty ihb =>
    intro d k c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨ihty d k c hb.1, ?_⟩
    have := ihb d k (c + 1) hb.2
    rwa [show c + 1 + k = c + k + 1 by omega] at this
  | letE ty v b ihty ihv ihb =>
    intro d k c hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨⟨ihty d k c hb.1.1, ihv d k c hb.1.2⟩, ?_⟩
    have := ihb d k (c + 1) hb.2
    rwa [show c + 1 + k = c + k + 1 by omega] at this
  | proj s i x ih =>
    intro d k c hb
    simp only [Expr.looseBVarsBounded] at hb
    simp only [Expr.abstractRange, Expr.looseBVarsBounded]
    exact ih d k c hb
  | _ => intro d k c _; rfl

/-- **The pin round trip**: a bvar-closed term whose leaves at the
range's indices are the openers' annotations, abstracted over the range
and instantiated at the openers (outermost first, at descending
cuts), is itself. -/
theorem instSeq_abstractRange :
    ∀ (ps : List Expr) (d : Nat) {e : Expr},
      (∀ (j : Nat) (x : Expr), ps[j]? = some x →
        ∃ ty, x = .fvar (d + j) ty ∧ Expr.fvarConsistent (d + j) ty e) →
      e.looseBVarsBounded 0 = true →
      Expr.instSeq ps (ps.length - 1) (e.abstractRange d ps.length 0) = e
  | [], d, e, _, _ => by simp [abstractRange_zero, Expr.instSeq]
  | p :: ps, d, e, hps, hb => by
    obtain ⟨ty, rfl, hcons⟩ := hps 0 p rfl
    rw [Nat.add_zero] at hcons
    rw [List.length_cons, abstractRange_succ_outer, Nat.add_sub_cancel]
    show Expr.instSeq ps (ps.length + 1 - 1 - 1)
      (((e.abstractRange (d + 1) ps.length 0).abstract1 d (0 + ps.length)).instantiate1
        (.fvar d ty) ps.length) = e
    rw [Nat.zero_add, abstract1_instantiate1 _ _ (fvarConsistent_abstractRange e _ _ _ (by omega) hcons)
      (by have := looseBVarsBounded_abstractRange e (d + 1) ps.length 0 hb; simpa using this)]
    rw [show ps.length + 1 - 1 - 1 = ps.length - 1 by omega]
    exact instSeq_abstractRange ps (d + 1)
      (fun j x hx => by
        obtain ⟨ty', rfl, hc⟩ := hps (j + 1) x (by simpa using hx)
        exact ⟨ty', by rw [show d + 1 + j = d + (j + 1) by omega], by
          rw [show d + 1 + j = d + (j + 1) by omega]; exact hc⟩)
      hb

/-- Consistency at the openers from the leaves: a term whose every leaf
is an opener is consistent at every opener's index. -/
theorem fvarConsistent_of_leavesIn {params : List Expr}
    (hshape : ∀ (i : Nat) (x : Expr), params[i]? = some x → ∃ ty, x = .fvar i ty)
    {j : Nat} {ty : Expr} (hj : params[j]? = some (.fvar j ty)) :
    ∀ {e : Expr}, Expr.LeavesIn params e → Expr.fvarConsistent j ty e
  | .fvar idx ty', hl => by
    simp only [Expr.fvarConsistent]
    intro hidx
    subst hidx
    have hmem : Expr.fvar idx ty' ∈ params := hl (idx, ty') (by simp [Expr.fvarLeaves])
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
    obtain ⟨ty'', hty''⟩ := hshape i _ hi
    have hidx' : idx = i := (Expr.fvar.inj hty'').1
    subst hidx'
    exact (Expr.fvar.inj (Option.some.inj (hi.symm.trans hj))).2
  | .app f a, hl =>
    ⟨fvarConsistent_of_leavesIn hshape hj (Expr.leavesIn_app.mp hl).1,
      fvarConsistent_of_leavesIn hshape hj (Expr.leavesIn_app.mp hl).2⟩
  | .lam ty' b bm, hl =>
    ⟨fvarConsistent_of_leavesIn hshape hj (Expr.leavesIn_lam.mp hl).1,
      fvarConsistent_of_leavesIn hshape hj (Expr.leavesIn_lam.mp hl).2⟩
  | .forallE ty' b bm, hl =>
    ⟨fvarConsistent_of_leavesIn hshape hj (Expr.leavesIn_forallE.mp hl).1,
      fvarConsistent_of_leavesIn hshape hj (Expr.leavesIn_forallE.mp hl).2⟩
  | .letE ty' v b, hl =>
    ⟨fvarConsistent_of_leavesIn hshape hj (Expr.leavesIn_letE.mp hl).1,
      fvarConsistent_of_leavesIn hshape hj (Expr.leavesIn_letE.mp hl).2.1,
      fvarConsistent_of_leavesIn hshape hj (Expr.leavesIn_letE.mp hl).2.2⟩
  | .proj s i x, hl => fvarConsistent_of_leavesIn hshape hj (e := x) (Expr.leavesIn_proj.mp hl)
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => trivial

/-! ## The run's table, looked up -/

/-- `lookup` on a keyed map with distinct keys finds the entry. -/
theorem lookup_map_of_nodup {α β γ : Type} [BEq β] [LawfulBEq β] {f : α → β} {g : α → γ} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x : α}, x ∈ l →
      (l.map fun y => (f y, g y)).lookup (f x) = some (g x)
  | [], _, x, hx => nomatch hx
  | y :: l, hnd, x, hx => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.lookup_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp
    · have hne : (f x == f y) = false :=
        beq_eq_false_iff_ne.mpr fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hx')
      rw [hne]
      exact lookup_map_of_nodup hnd.2 hx'

/-- `lookup` misses a key no entry carries. -/
theorem lookup_eq_none_of_forall {α β : Type} [BEq α] [LawfulBEq α] {k : α} :
    ∀ {l : List (α × β)}, (∀ y ∈ l, y.1 ≠ k) → l.lookup k = none
  | [], _ => rfl
  | (k', v) :: l, h => by
    simp only [List.lookup_cons]
    have hne : (k == k') = false := beq_eq_false_iff_ne.mpr (h (k', v) List.mem_cons_self).symm
    rw [hne]
    exact lookup_eq_none_of_forall fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- **The run's table at the parameters finds every pin at itself**:
the copies' names are distinct, the pin's leaves are the openers, so
`instSeq` of `abstractRange` is the identity. -/
theorem restoreTbl_instAt_lookup {p : NestedParts} {st : ElimState} {params : List Expr}
    (hnodup : (st.pins.map (·.aux)).Nodup) (hlen : params.length = p.nP)
    (hshape : ∀ (i : Nat) (x : Expr), params[i]? = some x → ∃ ty, x = .fvar i ty)
    {q : NestedPin} (hq : q ∈ st.pins) (hleaves : Expr.LeavesIn params q.pin)
    (hclosed : q.pin.looseBVarsBounded 0 = true) :
    ((restoreTbl p st).instAt params).pins.lookup q.aux = some q.pin := by
  show ((st.pins.map fun q => (q.aux, Expr.abstractRange q.pin 0 p.nP 0)).map
      fun q => (q.1, Expr.instSeq params (params.length - 1) q.2)).lookup q.aux = some q.pin
  rw [List.lookup_map_snd, lookup_map_of_nodup hnodup hq]
  simp only [Option.map_some, Option.some.injEq]
  rw [← hlen]
  exact instSeq_abstractRange params 0 (fun j x hx => by
    obtain ⟨ty, rfl⟩ := hshape j x hx
    exact ⟨ty, by rw [Nat.zero_add], by
      rw [Nat.zero_add]; exact fvarConsistent_of_leavesIn hshape hx hleaves⟩) hclosed

/-- The recursor map holds no pin's name. -/
theorem restoreTbl_instAt_recMap {p : NestedParts} {st : ElimState} {params : List Expr}
    {q : NestedPin} (hne : ∀ q' ∈ st.pins, q'.aux.str "rec" ≠ q.aux) :
    ((restoreTbl p st).instAt params).recMap.lookup q.aux = none := by
  show ((st.pins.zipIdx.map fun (q, j) => (q.aux.str "rec", p.mimicRecName j)).lookup q.aux) = none
  refine lookup_eq_none_of_forall fun y hy => ?_
  obtain ⟨⟨q', j⟩, hqj, rfl⟩ := List.mem_map.mp hy
  obtain ⟨-, hjlt, hq'⟩ := List.mem_zipIdx hqj
  refine hne q' ?_
  rw [hq']
  exact List.getElem_mem _

end ConLeche
