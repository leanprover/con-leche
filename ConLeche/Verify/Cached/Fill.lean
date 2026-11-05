module

public import ConLeche.Verify.Cached.Defer

public section

/-!
# The install does not look at a theorem's value (task #481)

`InstallRun.fill`: a run of phase A over records whose theorems hold one value is a run
over the same records holding any other, ending in the same environment, with the same
records of the check phase but for those values.  Phase A stores a theorem by its
statement and records the value raw (`installStepC`), so nothing in it depends on the
value; this is what lets an `.olean` run install a theorem while its value is
still in the file, and read it in the theorem's check.
-/

namespace ConLeche.Cached

open ConLeche

/-- A record with its theorem's value replaced by `F` of it. -/
@[expose] def fillDecl (F : Expr → Expr) : Declaration → Declaration
  | .thmDecl cv v => .thmDecl cv (F v)
  | d => d

/-- A recorded check with its theorem's value replaced by `F` of it. -/
@[expose] def fillPend (F : Expr → Expr) (pc : PendingCheck) : PendingCheck :=
  match pc.vg.kind with
  | .thm => { pc with vg := { pc.vg with jv := F pc.vg.jv } }
  | _ => pc

variable {mode : CheckMode} {pins : List NatOpPinSet} (F : Expr → Expr)

private theorem bind_okk {α β : Type} {m : CheckCM α} {k : α → CheckCM β} {s s' : CState} {b : β} :
    (m >>= k) s = .ok (b, s') ↔ ∃ a s₁, m s = .ok (a, s₁) ∧ k a s₁ = .ok (b, s') := by
  show (StateT.bind m k) s = _ ↔ _
  simp only [StateT.bind, bind, Except.bind]
  cases e : m s with
  | error x => simp
  | ok x =>
    obtain ⟨a, s₁⟩ := x
    simp only []
    constructor
    · intro h; exact ⟨a, s₁, rfl, h⟩
    · rintro ⟨a', s₂, h1, h2⟩
      cases h1
      exact h2

private theorem pure_okk {α : Type} {a b : α} {s s' : CState} :
    (pure a : CheckCM α) s = .ok (b, s') ↔ a = b ∧ s = s' := by
  show (Except.ok (a, s) : Except CheckError (α × CState)) = _ ↔ _
  simp

/-- **The body of a step of phase A, at any theorem's value.** -/
theorem installStepC_fill {i : Nat} {fe fe' : FEnv} {pend pend' : Array PendingCheck}
    {d : Declaration} {s s' : CState}
    (h : installStepC mode pins i fe pend d s = .ok ((fe', pend'), s')) :
    installStepC mode pins i fe (pend.map (fillPend F)) (fillDecl F d) s =
      .ok ((fe', pend'.map (fillPend F)), s') := by
  cases d with
  | thmDecl cv v =>
    simp only [installStepC, fillDecl, bind_okk, pure_okk, Prod.mk.injEq] at h ⊢
    obtain ⟨_, s₁, h1, _, s₂, h2, ⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨_, s₁, h1, _, s₂, h2, ⟨rfl, ?_⟩, rfl⟩
    simp [fillPend]
  | defnDecl cv v hint =>
    simp only [installStepC, fillDecl] at h ⊢
    split at h
    · rename_i hc
      simp only [hc, ↓reduceIte, bind_okk, pure_okk, Prod.mk.injEq] at h ⊢
      obtain ⟨_, s₁, h1, ⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨_, s₁, h1, ⟨rfl, rfl⟩, rfl⟩
    · rename_i hc
      simp only [eq_false hc, ↓reduceIte]
      simp only [bind_okk, pure_okk, Prod.mk.injEq] at h ⊢
      obtain ⟨_, s₁, h1, ⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨_, s₁, h1, ⟨rfl, ?_⟩, rfl⟩
      simp [fillPend]
  | opaqueDecl cv v =>
    simp only [installStepC, fillDecl] at h ⊢
    split at h
    · rename_i hc
      simp only [hc, ↓reduceIte, bind_okk, pure_okk, Prod.mk.injEq] at h ⊢
      obtain ⟨_, s₁, h1, ⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨_, s₁, h1, ⟨rfl, rfl⟩, rfl⟩
    · rename_i hc
      simp only [eq_false hc, ↓reduceIte]
      simp only [bind_okk, pure_okk, Prod.mk.injEq] at h ⊢
      obtain ⟨_, s₁, h1, ⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨_, s₁, h1, ⟨rfl, ?_⟩, rfl⟩
      simp [fillPend]
  | _ =>
    simp only [installStepC, fillDecl, bind_okk, pure_okk, Prod.mk.injEq] at h ⊢
    obtain ⟨_, s₁, h1, ⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨_, s₁, h1, ⟨rfl, rfl⟩, rfl⟩

/-- **One step of phase A, at any theorem's value.** -/
theorem installDeclStep_fill {i i' : Nat} {fe fe' : FEnv} {pend pend' : Array PendingCheck}
    {d : Declaration} (h : installDeclStep mode pins (i, fe, pend) d = .ok (i', fe', pend')) :
    installDeclStep mode pins (i, fe, pend.map (fillPend F)) (fillDecl F d) =
      .ok (i', fe', pend'.map (fillPend F)) := by
  obtain ⟨fe1, pend1, s1, hq, hrun⟩ := installDeclStep_ok h
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl, rfl⟩ := hq
  have hpin : andPinOk (fillDecl F d) = andPinOk d := by
    cases d <;> rfl
  have ha : andPinOk d = true := by
    unfold installDeclStep at h
    split at h
    · assumption
    · cases h
  unfold installDeclStep
  simp only [hpin, ha, ↓reduceIte]
  have := installStepC_fill F hrun
  simp only at this
  rw [this]

/-- **Phase A, at any theorems' values.** -/
theorem InstallRun.fill {ds : List Declaration} {p p' : Nat × FEnv × Array PendingCheck}
    (h : InstallRun mode pins ds p p') :
    InstallRun mode pins (ds.map (fillDecl F)) (p.1, p.2.1, p.2.2.map (fillPend F))
      (p'.1, p'.2.1, p'.2.2.map (fillPend F)) := by
  induction h with
  | nil p => exact .nil _
  | @cons pd ds p p₁ p' hs _ ih =>
    exact .cons (installDeclStep_fill F hs) ih

/-! ## Every record and every block is a job -/

private theorem jobOrder_go_mem {pend : Array PendingCheck} {D : Array BlockCheck} :
    ∀ (a b : Nat) (acc : Array Job) (j : Job),
      (j ∈ acc ∨ (j.1 = false ∧ a ≤ j.2 ∧ j.2 < pend.size) ∨ (j.1 = true ∧ b ≤ j.2 ∧ j.2 < D.size)) →
      j ∈ jobOrder.go pend D a b acc := by
  intro a b acc j
  induction a, b, acc using jobOrder.go.induct pend D with
  | case1 a b acc ha hb hlt ih =>
    intro h
    rw [jobOrder.go]
    simp only [ha, ↓reduceDIte, hb, hlt, ↓reduceIte]
    apply ih
    rcases h with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact .inl (by simp [h])
    · exact .inr (.inl ⟨h1, h2, h3⟩)
    · by_cases he : j.2 = b
      · refine .inl ?_
        have : j = (true, b) := by rw [Prod.ext_iff]; exact ⟨h1, he⟩
        simp [this]
      · exact .inr (.inr ⟨h1, by omega, h3⟩)
  | case2 a b acc ha hb hlt ih =>
    intro h
    rw [jobOrder.go]
    simp only [ha, ↓reduceDIte, hb, hlt, ↓reduceIte]
    apply ih
    rcases h with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact .inl (by simp [h])
    · by_cases he : j.2 = a
      · refine .inl ?_
        have : j = (false, a) := by rw [Prod.ext_iff]; exact ⟨h1, he⟩
        simp [this]
      · exact .inr (.inl ⟨h1, by omega, h3⟩)
    · exact .inr (.inr ⟨h1, h2, h3⟩)
  | case3 a b acc ha hb ih =>
    intro h
    rw [jobOrder.go]
    simp only [ha, ↓reduceDIte, hb]
    apply ih
    rcases h with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact .inl (by simp [h])
    · by_cases he : j.2 = a
      · refine .inl ?_
        have : j = (false, a) := by rw [Prod.ext_iff]; exact ⟨h1, he⟩
        simp [this]
      · exact .inr (.inl ⟨h1, by omega, h3⟩)
    · exact .inr (.inr ⟨h1, h2, h3⟩)
  | case4 a b acc ha hb ih =>
    intro h
    rw [jobOrder.go]
    simp only [ha, ↓reduceDIte, hb, ↓reduceIte]
    apply ih
    rcases h with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact .inl (by simp [h])
    · omega
    · by_cases he : j.2 = b
      · refine .inl ?_
        have : j = (true, b) := by rw [Prod.ext_iff]; exact ⟨h1, he⟩
        simp [this]
      · exact .inr (.inr ⟨h1, by omega, h3⟩)
  | case5 a b acc ha hb =>
    intro h
    rw [jobOrder.go]
    simp only [ha, ↓reduceDIte, hb, ↓reduceIte]
    rcases h with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact h
    · omega
    · omega

/-- **Every record is a job.** -/
theorem jobOrder_pend {pend : Array PendingCheck} {D : Array BlockCheck} {k : Nat}
    (hk : k < pend.size) : ∃ t, t < (jobOrder pend D).size ∧ (jobOrder pend D)[t]? = some (false, k) := by
  have := jobOrder_go_mem (pend := pend) (D := D) 0 0 (Array.mkEmpty (pend.size + D.size))
    (false, k) (.inr (.inl ⟨rfl, Nat.zero_le _, hk⟩))
  obtain ⟨t, ht, h⟩ := Array.getElem_of_mem this
  exact ⟨t, ht, by unfold jobOrder; rw [Array.getElem?_eq_getElem ht, h]⟩

/-- **Every block check is a job.** -/
theorem jobOrder_block {pend : Array PendingCheck} {D : Array BlockCheck} {k : Nat}
    (hk : k < D.size) : ∃ t, t < (jobOrder pend D).size ∧ (jobOrder pend D)[t]? = some (true, k) := by
  have := jobOrder_go_mem (pend := pend) (D := D) 0 0 (Array.mkEmpty (pend.size + D.size))
    (true, k) (.inr (.inr ⟨rfl, Nat.zero_le _, hk⟩))
  obtain ⟨t, ht, h⟩ := Array.getElem_of_mem this
  exact ⟨t, ht, by unfold jobOrder; rw [Array.getElem?_eq_getElem ht, h]⟩

end ConLeche.Cached
