module

public import ConLeche.Verify.Modular.View
public import ConLeche.Cached.ModIso

public section

/-!
# The fold at a view is the fold at an environment with its lookups (task #373)

A modular run checks module `M` by the declaration fold started at `M`'s
view of the store (`checkAtView`); the isolated specification starts the
same fold at the canonical index of an environment `C` built from `M`'s
imports' units (`checkModuleIsolated`).  This file proves, for ANY
environment `C` whose lookups are the view's base lookups (`BaseLike`),
that the two folds are one: every step fails with the same error at the
same position or pushes the same constants and records the same check,
every record check gives the same verdict, and the results are the
module's own constants and tables, over `C` or alone
(`checkDeclsAt_over`).  Nothing here needs the run to accept.

* `installDeclStep_twin_full` — at twin indices the fold's step fails
  alike or succeeds alike (`installDeclStep_twin` covers the success);
* `restrict_find?_over` — the canonical index of `own ++ C` restricted
  past `C` answers as the view restricted to the same own prefix;
* `foldlM_over`, `checkPendingList_over`, `checkDeclsAt_over`.
-/

namespace ConLeche.Cached.Mod

open ConLeche

variable {mode : CheckMode} {pins : List NatOpPinSet}

/-! ## The step, both ways -/

theorem _root_.ConLeche.Cached.Twin.symm {fe₁ fe₂ : FEnv} (h : Twin fe₁ fe₂) : Twin fe₂ fe₁ :=
  ⟨h.find.symm, h.raw.symm, h.idx₂, h.idx₁⟩

/-- **The fold's step at twin indices, failing or not**: the same error
at the same position, or the same constants and tables pushed onto each
and the same check recorded (at each index's own counter). -/
theorem installDeclStep_twin_full {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (i : Nat)
    (pend₁ pend₂ : Array PendingCheck) (d : Declaration) :
    (∃ e, installDeclStep mode pins (i, fe₁, pend₁) d = .error e ∧
        installDeclStep mode pins (i, fe₂, pend₂) d = .error e) ∨
    ∃ L Q vg?, installDeclStep mode pins (i, fe₁, pend₁) d =
        .ok (i + 1, FEnv.pushDelta L Q fe₁, pushPending pend₁ i fe₁.visibleBelow vg?) ∧
      installDeclStep mode pins (i, fe₂, pend₂) d =
        .ok (i + 1, FEnv.pushDelta L Q fe₂, pushPending pend₂ i fe₂.visibleBelow vg?) := by
  cases h₁ : installDeclStep mode pins (i, fe₁, pend₁) d with
  | ok q =>
    obtain ⟨L, Q, vg?, rfl, h₂, -⟩ := installDeclStep_twin (pend₂ := pend₂) ht h₁
    exact .inr ⟨L, Q, vg?, rfl, h₂⟩
  | error e =>
    refine .inl ⟨e, rfl, ?_⟩
    cases h₂ : installDeclStep mode pins (i, fe₂, pend₂) d with
    | ok q =>
      obtain ⟨L, Q, vg?, rfl, h₁', -⟩ := installDeclStep_twin (pend₂ := pend₁) ht.symm h₂
      rw [h₁] at h₁'; exact nomatch h₁'
    | error e₂ =>
      -- both fail: the same error
      unfold installDeclStep at h₁ h₂
      split at h₁
      case isFalse =>
        rename_i hand
        simp only [hand, Bool.false_eq_true, ↓reduceIte] at h₂
        rw [← h₁, ← h₂]
      rename_i hand
      simp only [hand, ↓reduceIte] at h₂
      cases hv : valueStep fe₁ d with
      | some r =>
        have k₁ := installStepC_value (mode := mode) (pins := pins) (i := i) (pend := pend₁)
          (fe := fe₁) rfl hv
        have k₂ := installStepC_value (mode := mode) (pins := pins) (i := i) (pend := pend₂)
          (fe := fe₂) ht.find hv
        revert h₁ h₂ k₁ k₂
        cases installStepC mode pins i fe₁ pend₁ d {} with
        | ok p => intro h₁; exact nomatch h₁
        | error x₁ =>
          cases installStepC mode pins i fe₂ pend₂ d {} with
          | ok p => intro _ h₂; exact nomatch h₂
          | error x₂ =>
            intro h₁ h₂ k₁ k₂
            simp only [Except.error.injEq] at h₁ h₂
            cases r with
            | ok v => simp [Except.map] at k₁
            | error e' =>
              simp only [Except.map, Except.error.injEq] at k₁ k₂
              rw [← h₁, ← h₂, k₁, k₂]
      | none =>
        have hs₁ := installStepC_of_valueStep_none (mode := mode) (pins := pins) (i := i)
          (fe := fe₁) (pend := pend₁) hv
        have hs₂ := installStepC_of_valueStep_none (mode := mode) (pins := pins) (i := i)
          (fe := fe₂) (pend := pend₂) hv
        rw [hs₁] at h₁
        rw [hs₂] at h₂
        rcases checkDeclStepC_twin (mode := mode) pins ht d {} with
          ⟨x, k₁, k₂⟩ | ⟨a₁, a₂, s', k₁, k₂, -⟩
        · have e₁ : (match (checkDeclStepC mode pins fe₁ d {}).bind
              (fun v => (pure (v.1, pend₁) : CheckCM _) v.2) with
            | .ok ((fe', pend'), _) => Except.ok (i + 1, fe', pend')
            | .error e => .error (e, i)) = Except.error e := h₁
          have e₂' : (match (checkDeclStepC mode pins fe₂ d {}).bind
              (fun v => (pure (v.1, pend₂) : CheckCM _) v.2) with
            | .ok ((fe', pend'), _) => Except.ok (i + 1, fe', pend')
            | .error e => .error (e, i)) = Except.error e₂ := h₂
          rw [k₁] at e₁
          rw [k₂] at e₂'
          simp only [Except.bind, Except.error.injEq] at e₁ e₂'
          rw [← e₁, ← e₂']
        · have e₁ : (match (checkDeclStepC mode pins fe₁ d {}).bind
              (fun v => (pure (v.1, pend₁) : CheckCM _) v.2) with
            | .ok ((fe', pend'), _) => Except.ok (i + 1, fe', pend')
            | .error e => .error (e, i)) = Except.error e := h₁
          rw [k₁] at e₁
          simp only [Except.bind, pure, StateT.pure, Except.pure] at e₁
          exact nomatch e₁

/-! ## An environment with the base's lookups -/

/-- **`C` has the lookups of the store `mb`**: the same constant and the
same table under every name. -/
structure BaseLike (C : Env) (mb : MBase) : Prop where
  find : ∀ n, C.find? n = mb.find? n
  tbl : ∀ T, C.tables.find? (·.structName == T) = mb.findTable? T

/-- The store's own context has its lookups. -/
theorem baseLike_ctxOf (mb : MBase) : BaseLike (ctxOf mb) mb :=
  ⟨ctxOf_find? mb, ctxOf_tables_find? mb⟩

/-- **A view is the twin of the canonical index of its constants over
any environment with its base's lookups.** -/
theorem CanonB.twin_over {fe : FEnv} {mb : MBase} {C : Env} (h : CanonB fe { mb := some mb })
    (hC : BaseLike C mb) : Twin fe (ConLeche.mkFEnv (envAt fe C)) := by
  refine ⟨?_, ?_, h.idxBelow, IdxBelow.mkFEnv _⟩
  · funext n
    rw [h.find? n, mkFEnv_find?]
    unfold envAt Env.find?
    simp only
    rw [List.find?_append]
    have hb : ({ mb := some mb } : FBase).find? n = mb.find? n := rfl
    rw [hb, ← hC.find]
    rfl
  · funext T
    rw [h.rawTable? T, mkFEnv_rawTable?]
    unfold envAt
    simp only
    rw [List.find?_append]
    have hb : ({ mb := some mb } : FBase).findTable? T = mb.findTable? T := rfl
    rw [hb, ← hC.tbl]

/-! ## Prefix views -/

theorem idxSpec_append {n : Name} : ∀ (X Y : List ConstantInfo),
    idxSpec (X ++ Y) n = match idxSpec X n with
      | some (c, ci) => some (c + Y.length, ci)
      | none => idxSpec Y n
  | [], _ => rfl
  | ci :: X, Y => by
    rw [List.cons_append, idxSpec, idxSpec]
    split
    · simp [List.length_append]
    · exact idxSpec_append X Y

/-- **The canonical index over `C`, restricted past `C`, is the view
restricted to the same own prefix.** -/
theorem restrict_find?_over {fe : FEnv} {mb : MBase} {C : Env} (h : CanonB fe { mb := some mb })
    (hC : BaseLike C mb) (k : Nat) (n : Name) :
    ((ConLeche.mkFEnv (envAt fe C)).restrictTo (k + C.consts.length)).find? n =
      (fe.restrictTo k).find? n := by
  have hov₂ : (fe.restrictTo k).ovl = [] := h.ovl
  unfold FEnv.find?
  rw [hov₂]
  show (match (ConLeche.mkFEnv (envAt fe C)).idx[n]? with
      | some (c, ci) => if c < k + C.consts.length then some ci else none
      | none => (ConLeche.mkFEnv (envAt fe C)).base.find? n) =
    (match fe.idx[n]? with
      | some (c, ci) => if c < k then some ci else none
      | none => fe.base.find? n)
  rw [mkFEnv_idx, h.idx n, h.base]
  unfold envAt
  simp only
  rw [idxSpec_append]
  cases hs : idxSpec fe.env.consts n with
  | some p =>
    obtain ⟨c, ci⟩ := p
    simp only [Nat.add_lt_add_iff_right]
  | none =>
    simp only
    have hb : ({ mb := some mb } : FBase).find? n = mb.find? n := rfl
    rw [hb, ← hC.find]
    cases hc : idxSpec C.consts n with
    | some p =>
      obtain ⟨c, ci⟩ := p
      simp only
      rw [ite_eq_left (Nat.lt_of_lt_of_le (idxSpec_lt hc) (Nat.le_add_left _ _))]
      unfold Env.find?
      rw [idxSpec_some hc]
    | none =>
      show ({} : FBase).find? n = _
      rw [FBase.find?_empty]
      unfold Env.find?
      rw [idxSpec_none hc]

/-! ## The fold -/

/-- A record's check, its visibility bound past a context of `k`
constants. -/
@[expose] def shiftPC (k : Nat) (pc : PendingCheck) : PendingCheck := { pc with vis := pc.vis + k }

/-- **The state of the fold over `C`** for the state of the fold at the
view. -/
@[expose] def overState (C : Env) (p : Nat × FEnv × Array PendingCheck) :
    Nat × FEnv × Array PendingCheck :=
  (p.1, ConLeche.mkFEnv (envAt p.2.1 C), p.2.2.map (shiftPC C.consts.length))

theorem pushPending_shift (pend : Array PendingCheck) (i v k : Nat) (vg? : Option ValueGroup) :
    pushPending (pend.map (shiftPC k)) i (v + k) vg? = (pushPending pend i v vg?).map (shiftPC k) := by
  cases vg? with
  | none => rfl
  | some vg => simp [pushPending, shiftPC, Array.map_push]

/-- **The step over `C` is the step at the view**, for a view canonical
over the store. -/
theorem installDeclStep_over {mb : MBase} {C : Env} (hC : BaseLike C mb)
    {p : Nat × FEnv × Array PendingCheck} (hp : CanonB p.2.1 { mb := some mb }) (d : Declaration) :
    (∃ e, installDeclStep mode pins p d = .error e ∧
        installDeclStep mode pins (overState C p) d = .error e) ∨
    ∃ q, installDeclStep mode pins p d = .ok q ∧
      installDeclStep mode pins (overState C p) d = .ok (overState C q) ∧
      CanonB q.2.1 { mb := some mb } := by
  obtain ⟨i, fe, pend⟩ := p
  rcases installDeclStep_twin_full (mode := mode) (pins := pins) (hp.twin_over hC) i pend
      (pend.map (shiftPC C.consts.length)) d with
    ⟨e, h₁, h₂⟩ | ⟨L, Q, vg?, h₁, h₂⟩
  · exact .inl ⟨e, h₁, h₂⟩
  · refine .inr ⟨_, h₁, ?_, hp.pushDelta L Q⟩
    show installDeclStep mode pins (i, ConLeche.mkFEnv (envAt fe C),
      pend.map (shiftPC C.consts.length)) d = _
    rw [h₂]
    unfold overState
    simp only
    have hv : (ConLeche.mkFEnv (envAt fe C)).visibleBelow = fe.visibleBelow + C.consts.length := by
      rw [mkFEnv_visibleBelow, hp.visibleBelow]
      unfold envAt
      simp
    rw [hv, pushPending_shift, mkFEnv_pushDelta, envAt_pushDelta]

/-- **The fold over `C` is the fold at the view**: it fails with the same
error, or ends in the state over `C` of the view's final state, which is
still canonical over the store. -/
theorem foldlM_over {mb : MBase} {C : Env} (hC : BaseLike C mb) :
    ∀ (ds : List Declaration) (p : Nat × FEnv × Array PendingCheck),
      CanonB p.2.1 { mb := some mb } →
      ds.foldlM (installDeclStep mode pins) (overState C p) =
          (ds.foldlM (installDeclStep mode pins) p).map (overState C) ∧
        ∀ q, ds.foldlM (installDeclStep mode pins) p = .ok q → CanonB q.2.1 { mb := some mb }
  | [], p, hp => ⟨rfl, fun q hq => by cases hq; exact hp⟩
  | d :: ds, p, hp => by
    rw [List.foldlM_cons, List.foldlM_cons]
    rcases installDeclStep_over (mode := mode) (pins := pins) hC hp d with
      ⟨e, h₁, h₂⟩ | ⟨q, h₁, h₂, hq⟩
    · simp only [bind, Except.bind, h₁, h₂]
      exact ⟨rfl, fun _ h => nomatch h⟩
    · simp only [bind, Except.bind, h₁, h₂]
      exact foldlM_over hC ds q hq

/-- **Every record's check over `C` is its check at the view.** -/
theorem checkPending_over {mb : MBase} {C : Env} (hC : BaseLike C mb) {fe : FEnv}
    (hfe : CanonB fe { mb := some mb }) (pc : PendingCheck) (s : CState) :
    checkPending mode (ConLeche.mkFEnv (envAt fe C)) (shiftPC C.consts.length pc) s =
      checkPending mode fe pc s := by
  have hf : ((ConLeche.mkFEnv (envAt fe C)).restrictTo (shiftPC C.consts.length pc).vis).find? =
      (fe.restrictTo pc.vis).find? := funext (restrict_find?_over hfe hC pc.vis)
  refine checkPending_congr hf ?_ rfl s
  funext T
  unfold FEnv.findTable?
  rw [hf]
  have hr₁ : ((ConLeche.mkFEnv (envAt fe C)).restrictTo (shiftPC C.consts.length pc).vis).rawTable?
      T = (ConLeche.mkFEnv (envAt fe C)).rawTable? T := rfl
  have hr₂ : (fe.restrictTo pc.vis).rawTable? T = fe.rawTable? T := rfl
  rw [hr₁, hr₂, (hfe.twin_over hC).raw]

theorem checkPendingList_over {mb : MBase} {C : Env} (hC : BaseLike C mb) {fe : FEnv}
    (hfe : CanonB fe { mb := some mb }) :
    ∀ l : List PendingCheck,
      checkPendingList mode (ConLeche.mkFEnv (envAt fe C)) (l.map (shiftPC C.consts.length)) =
        checkPendingList mode fe l
  | [] => rfl
  | pc :: l => by
    rw [List.map_cons]
    unfold checkPendingList
    rw [checkPending_over hC hfe pc {}, checkPendingList_over hC hfe l]
    rfl

theorem envAt_viewOf_over (mb : MBase) (C : Env) : envAt (viewOf mb) C = C := by
  cases C; rfl

/-- **The module's check over `C` is its check at the view**: the same
verdict — the same error at the same position, or the module's own
constants and tables, over `C`. -/
theorem checkDeclsAt_over {mb : MBase} {C : Env} (hC : BaseLike C mb) (ds : Array Declaration) :
    checkDeclsAt mode pins (ConLeche.mkFEnv C) ds =
      (checkDeclsAt mode pins (viewOf mb) ds).map (Env.over · C) := by
  have h0 : overState C (0, viewOf mb, #[]) = (0, ConLeche.mkFEnv C, #[]) := by
    unfold overState
    rw [envAt_viewOf_over]
    simp
  obtain ⟨hf, hq⟩ := foldlM_over (mode := mode) (pins := pins) hC ds.toList (0, viewOf mb, #[])
    (canonB_viewOf mb)
  rw [h0] at hf
  unfold checkDeclsAt
  rw [← Array.foldlM_toList, ← Array.foldlM_toList, hf]
  cases hr : ds.toList.foldlM (installDeclStep mode pins) (0, viewOf mb, #[]) with
  | error e => rfl
  | ok q =>
    have hcq := hq q hr
    show (do checkPendingList mode (overState C q).2.1 (overState C q).2.2.toList
             pure (overState C q).2.1.env) =
      Except.map (Env.over · C) (do checkPendingList mode q.2.1 q.2.2.toList; pure q.2.1.env)
    unfold overState
    simp only [Array.toList_map]
    rw [checkPendingList_over hC hcq]
    cases checkPendingList mode q.2.1 q.2.2.toList with
    | error e => rfl
    | ok u => rfl

end ConLeche.Cached.Mod
