module

public import ConLeche.Cached.Installed
public import ConLeche.Verify.Frontend.Lazy

public section

/-!
# The install does not read theorem values (task #329)

Phase A installs a theorem by its statement: the record's value only
reaches the theorem's `PendingCheck` (`annotStepC`,
`ConLeche/Cached/Installed.lean`).  So the install of records that
differ only in theorem values is the same index with pending checks
that differ only in their values.  This is what lets the lazy driver
install records whose theorem values are placeholders and check each
theorem against its value built later.
-/

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-- `annotStepC` with any accumulator is the step with the empty one,
its records appended. -/
theorem annotStepC_pend (pins : List NatOpPinSet) (i : Nat) (fe : FEnv)
    (pend : Array PendingCheck) (pd : Declaration) (s : CState) :
    annotStepC mode pins i fe pend pd s =
      (match annotStepC mode pins i fe #[] pd s with
       | .ok ((fe', p), s') => .ok ((fe', pend ++ p), s')
       | .error e => .error e) := by
  cases pd with
  | defnDecl cv value hint =>
    simp only [annotStepC]
    split
    · simp only [bind, StateT.bind, pure, StateT.pure, Except.bind]
      cases checkDeclStepC mode pins fe (.defnDecl cv value hint) s <;> simp [Except.pure]
    · simp only [bind, StateT.bind, pure, StateT.pure, Except.bind]
      cases annotValueC mode fe cv value s <;> simp [Except.pure]
  | thmDecl cv value =>
    simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind]
    cases flushC s with
    | error e => simp
    | ok r =>
      simp only
      cases annotConstantValC mode fe cv r.2 <;> simp [Except.pure]
  | opaqueDecl cv value =>
    simp only [annotStepC]
    split
    · simp only [bind, StateT.bind, pure, StateT.pure, Except.bind]
      cases checkDeclStepC mode pins fe (.opaqueDecl cv value) s <;> simp [Except.pure]
    · simp only [bind, StateT.bind, pure, StateT.pure, Except.bind]
      cases annotValueC mode fe cv value s <;> simp [Except.pure]
  | axiomDecl cv =>
    simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind]
    cases checkDeclStepC mode pins fe (.axiomDecl cv) s <;> simp [Except.pure]
  | basisDecl b =>
    simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind]
    cases checkDeclStepC mode pins fe (.basisDecl b) s <;> simp [Except.pure]
  | quotDecl k cv =>
    simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind]
    cases checkDeclStepC mode pins fe (.quotDecl k cv) s <;> simp [Except.pure]
  | indDecl b n =>
    simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind]
    cases checkDeclStepC mode pins fe (.indDecl b n) s <;> simp [Except.pure]

/-- A run-time record and a serial one: equal, except a theorem's
value, related by `R`. -/
@[expose] def DR (R : Expr → Expr → Prop) (d' d : Declaration) : Prop :=
  match d with
  | .thmDecl cv w => ∃ w', d' = .thmDecl cv w' ∧ R w' w
  | _ => d' = d

/-- A run-time pending check and a serial one: equal, except a
theorem's value, related by `R`. -/
@[expose] def PRel (R : Expr → Expr → Prop) (pc' pc : PendingCheck) : Prop :=
  pc'.pos = pc.pos ∧ pc'.vis = pc.vis ∧ pc'.vg.kind = pc.vg.kind ∧ pc'.vg.cvA = pc.vg.cvA ∧
    (pc.vg.kind = .thm → R pc'.vg.jv pc.vg.jv) ∧ (pc.vg.kind ≠ .thm → pc'.vg.jv = pc.vg.jv)

/-- Two accumulators related entry by entry. -/
@[expose] def PendsRel (R : Expr → Expr → Prop) (a b : Array PendingCheck) : Prop :=
  a.size = b.size ∧ ∀ k (h₁ : k < a.size) (h₂ : k < b.size), PRel R a[k] b[k]

theorem PendsRel.append {R : Expr → Expr → Prop} {a b p q : Array PendingCheck}
    (h : PendsRel R a b) (hpq : PendsRel R p q) : PendsRel R (a ++ p) (b ++ q) := by
  refine ⟨by simp [h.1, hpq.1], fun k h₁ h₂ => ?_⟩
  simp only [Array.size_append] at h₁ h₂
  by_cases hk : k < a.size
  · rw [Array.getElem_append_left hk, Array.getElem_append_left (by rw [← h.1]; exact hk)]
    exact h.2 k hk _
  · obtain ⟨j, rfl⟩ : ∃ j, k = a.size + j := ⟨k - a.size, by omega⟩
    have hb : b.size = a.size := h.1.symm
    have hj1 : j < p.size := by omega
    have hj2 : j < q.size := by omega
    have e1 : (a ++ p)[a.size + j]'(by simp; omega) = p[j] := by
      simp [Array.getElem_append_right]
    have e2 : (b ++ q)[a.size + j]'(by simp; omega) = q[j] := by
      simp [Array.getElem_append_right, hb]
    rw [e1, e2]
    exact hpq.2 j hj1 hj2

/-- A non-theorem record's step pushes no theorem check. -/
theorem annotStepC_noThm (pins : List NatOpPinSet) (i : Nat) (fe : FEnv) (pd : Declaration)
    (hpd : ∀ cv w, pd ≠ .thmDecl cv w) {s : CState} {fe' : FEnv} {p : Array PendingCheck}
    {s' : CState} (h : annotStepC mode pins i fe #[] pd s = .ok ((fe', p), s')) :
    ∀ k (hk : k < p.size), p[k].vg.kind ≠ .thm := by
  cases pd with
  | defnDecl cv value hint =>
    simp only [annotStepC] at h
    split at h
    · simp only [bind, StateT.bind, pure, StateT.pure, Except.bind] at h
      cases hc : checkDeclStepC mode pins fe (.defnDecl cv value hint) s <;>
        simp [hc, Except.pure] at h
      obtain ⟨⟨-, rfl⟩, -⟩ := h; intro k hk; simp at hk
    · simp only [bind, StateT.bind, pure, StateT.pure, Except.bind] at h
      cases hc : annotValueC mode fe cv value s <;> simp [hc, Except.pure] at h
      obtain ⟨⟨-, rfl⟩, -⟩ := h; intro k hk; simp at hk; subst hk; simp
  | thmDecl cv value => exact absurd rfl (hpd cv value)
  | opaqueDecl cv value =>
    simp only [annotStepC] at h
    split at h
    · simp only [bind, StateT.bind, pure, StateT.pure, Except.bind] at h
      cases hc : checkDeclStepC mode pins fe (.opaqueDecl cv value) s <;>
        simp [hc, Except.pure] at h
      obtain ⟨⟨-, rfl⟩, -⟩ := h; intro k hk; simp at hk
    · simp only [bind, StateT.bind, pure, StateT.pure, Except.bind] at h
      cases hc : annotValueC mode fe cv value s <;> simp [hc, Except.pure] at h
      obtain ⟨⟨-, rfl⟩, -⟩ := h; intro k hk; simp at hk; subst hk; simp
  | axiomDecl cv =>
    simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind] at h
    cases hc : checkDeclStepC mode pins fe (.axiomDecl cv) s <;> simp [hc, Except.pure] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h; intro k hk; simp at hk
  | basisDecl b =>
    simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind] at h
    cases hc : checkDeclStepC mode pins fe (.basisDecl b) s <;> simp [hc, Except.pure] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h; intro k hk; simp at hk
  | quotDecl k cv =>
    simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind] at h
    cases hc : checkDeclStepC mode pins fe (.quotDecl k cv) s <;> simp [hc, Except.pure] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h; intro k hk; simp at hk
  | indDecl b n =>
    simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind] at h
    cases hc : checkDeclStepC mode pins fe (.indDecl b n) s <;> simp [hc, Except.pure] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h; intro k hk; simp at hk

/-- A theorem's step at two values: the same index, the same state, the
pending check with the other value. -/
theorem annotStepC_thm (pins : List NatOpPinSet) (i : Nat) (fe : FEnv) (cv : ConstantVal)
    (w' w : Expr) (s : CState) :
    annotStepC mode pins i fe #[] (.thmDecl cv w) s =
      (match annotStepC mode pins i fe #[] (.thmDecl cv w') s with
       | .ok ((fe', p), s') => .ok ((fe', p.map fun pc => { pc with vg := { pc.vg with jv := w } }), s')
       | .error e => .error e) := by
  simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind]
  cases flushC s with
  | error e => simp
  | ok r =>
    simp only
    cases annotConstantValC mode fe cv r.2 <;> simp [Except.pure]

/-- **One step at related records and accumulators**: the same index,
related accumulators. -/
theorem annotDeclStep_rel {R : Expr → Expr → Prop} (pins : List NatOpPinSet) {i : Nat}
    {fe : FEnv} {pend' pend : Array PendingCheck} {d' d : Declaration} (hd : DR R d' d)
    (hp : PendsRel R pend' pend) {i₂ : Nat} {fe₂ : FEnv} {P' : Array PendingCheck}
    (h : annotDeclStep mode pins (i, fe, pend') d' = .ok (i₂, fe₂, P')) :
    ∃ P, annotDeclStep mode pins (i, fe, pend) d = .ok (i₂, fe₂, P) ∧ PendsRel R P' P := by
  have hand : andPinOk d' = andPinOk d := by
    cases d with
    | thmDecl cv w => obtain ⟨w', rfl, -⟩ := hd; rfl
    | _ => subst hd; rfl
  unfold annotDeclStep at h ⊢
  rw [← hand]
  split at h
  · rename_i hok
    simp only [hok, ↓reduceIte]
    rw [annotStepC_pend] at h ⊢
    cases d with
    | thmDecl cv w =>
      obtain ⟨w', rfl, hw⟩ := hd
      rw [annotStepC_thm mode pins i fe cv w' w]
      cases hs : annotStepC mode pins i fe #[] (.thmDecl cv w') {} with
      | error e => simp [hs] at h
      | ok r =>
        obtain ⟨⟨fe', p⟩, s'⟩ := r
        simp only [hs, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨_, rfl, hp.append ⟨by simp, fun k h₁ h₂ => ?_⟩⟩
        simp only [Array.getElem_map]
        refine ⟨rfl, rfl, rfl, rfl, fun hk => ?_, fun hk => absurd hk ?_⟩
        · -- the pushed check's value is the record's
          have : p[k].vg.jv = w' := by
            simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind] at hs
            revert hs
            cases flushC ({} : CState) with
            | error e => simp
            | ok r =>
              simp only
              cases annotConstantValC mode fe cv r.2 <;> simp [Except.pure]
              intro _ hp _; subst hp; simp at h₁; subst h₁; rfl
          simpa [this] using hw
        · simp only
          simp only [annotStepC, bind, StateT.bind, pure, StateT.pure, Except.bind] at hs
          revert hs
          cases flushC ({} : CState) with
          | error e => simp
          | ok r =>
            simp only
            cases annotConstantValC mode fe cv r.2 <;> simp [Except.pure]
            intro _ hp _; subst hp; simp at h₁; subst h₁; rfl
    | _ =>
      subst hd
      cases hs : annotStepC mode pins i fe #[] _ {} with
      | error e => simp [hs] at h
      | ok r =>
        obtain ⟨⟨fe', p⟩, s'⟩ := r
        simp only [hs, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hno := annotStepC_noThm mode pins i fe _ (by intro _ _ h; cases h) hs
        refine ⟨_, rfl, hp.append ⟨rfl, fun k h₁ h₂ => ?_⟩⟩
        exact ⟨rfl, rfl, rfl, rfl, fun hk => absurd hk (hno k h₁), fun _ => rfl⟩
  · exact nomatch h

/-- **Phase A at related records**: the same index, related records. -/
theorem InstallRun.rel {R : Expr → Expr → Prop} {pins : List NatOpPinSet} :
    ∀ {ds' : List Declaration} {p q : Nat × FEnv × Array PendingCheck},
    InstallRun mode pins ds' p q → ∀ {ds : List Declaration} {pend : Array PendingCheck},
    Frontend.Pw (DR R) ds' ds → PendsRel R p.2.2 pend →
    ∃ P, InstallRun mode pins ds (p.1, p.2.1, pend) (q.1, q.2.1, P) ∧ PendsRel R q.2.2 P := by
  intro ds' p q h
  induction h with
  | nil p =>
    intro ds pend hds hp
    cases ds with
    | nil => exact ⟨pend, .nil _, hp⟩
    | cons _ _ => exact hds.elim
  | cons hstep rest ih =>
    rename_i pd ds₀ p₀ p₁ p'
    intro ds pend hds hp
    cases ds with
    | nil => exact hds.elim
    | cons d ds =>
      obtain ⟨hd, hds⟩ := hds
      obtain ⟨i, fe, pend₀⟩ := p₀
      obtain ⟨fe₁, pend₁, s₁, rfl, -⟩ := annotDeclStep_ok hstep
      obtain ⟨P₁, hP₁, hrel₁⟩ := annotDeclStep_rel mode pins hd hp hstep
      obtain ⟨P, hP, hrel⟩ := ih hds hrel₁
      exact ⟨P, .cons hP₁ hP, hrel⟩

/-- **Record `k` checked at every serial check related to it.** -/
@[expose] def LChecked (R : Expr → Expr → Prop) {pins : List NatOpPinSet}
    {ds : List Declaration} (e : InstalledEnv mode pins ds) (k : Nat) : Prop :=
  ∀ (hk : k < e.pend.size) (pc : PendingCheck), PRel R e.pend[k] pc →
    ∃ s', checkPending mode e.fe pc {} = .ok ((), s')

/-- **The fold accepts the serial records** when the run-time records,
related to them, installed and every record checked at every related
serial check. -/
theorem lazy_checkDecls {R : Expr → Expr → Prop} {pins : List NatOpPinSet}
    {ds' gds : Array Declaration} (hrel : Frontend.Pw (DR R) ds'.toList gds.toList)
    (e : InstalledEnv mode pins ds'.toList) (hall : ∀ k, k < e.pend.size → LChecked mode R e k) :
    checkDecls mode pins gds = .ok e.fe.env := by
  obtain ⟨n, hrun⟩ := e.run
  obtain ⟨P, hP, hrelP⟩ := InstallRun.rel mode hrun hrel (pend := #[]) ⟨rfl, fun k h => by simp at h⟩
  let e₂ : InstalledEnv mode pins gds.toList := ⟨e.fe, P, n, hP⟩
  have hchk : ∀ i, GroupChecked mode e₂ i := by
    intro i
    by_cases hi : i < P.size
    · have hi' : i < e.pend.size := by rw [hrelP.1]; exact hi
      obtain ⟨s', hs⟩ := hall i hi' hi' P[i] (hrelP.2 i hi' hi)
      exact groupChecked_of_run mode e₂ hi hs
    · exact groupChecked_of_ge mode e₂ (Nat.le_of_not_lt hi)
  exact fullyChecked_checkDecls mode ⟨e₂, hchk⟩

end ConLeche.Cached
