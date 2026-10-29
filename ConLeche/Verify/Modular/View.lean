module

public import ConLeche.Verify.Modular.Store
public import ConLeche.Verify.Cached.ViewCongr
public import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.InstalledC
import ConLeche.Verify.EnvBound
import ConLeche.Verify.CheckerF
import ConLeche.Verify.Cached.KnotCongr

public section

/-!
# A module's install at its view is the fold's step at its context (task #370)

A modular run installs module `i`'s records with the fold's own phase A
(`installDeclStep`) at the module's **view** (`Mod.Store.view`): an index
of the module's own constants over the store (`MBase`), counting from
zero.  This file proves that such a run is accepted at the module's
context in the sense of `Modular.AcceptedFrom`: every step is the fold's
step at the canonical index of the environment so far (the context with
the module's constants so far, `envAt`), and every record's check at
the view's end is the record's check at the step.

* `CanonB` — a view is canonical over its own constants with a base
  below; pushes keep it (`CanonB.pushDelta`), its lookups are its
  constants' then the base's (`CanonB.find?`, `CanonB.rawTable?`), and it
  is the twin of the canonical index of `envAt` (`CanonB.twin`).
* `installDeclStep_twin` — at twin indices the fold's step pushes the
  same constants and records the same check.
* `checkPending_congr` — a record's check reads its index through the
  prefix view's `find?` and `findTable?` only.
-/

namespace ConLeche.Cached.Mod

open ConLeche

variable {mode : CheckMode} {pins : List NatOpPinSet}

/-! ## Views -/

/-- The environment a view stands for over a context `C`: its own
constants and tables, then the context's. -/
@[expose] def envAt (fe : FEnv) (C : Env) : Env :=
  ⟨fe.env.consts ++ C.consts, fe.env.tables ++ C.tables⟩

/-- **A view is canonical over its own constants**, with the base `B`
below. -/
@[expose] def CanonB (fe : FEnv) (B : FBase) : Prop := fe = { mkFEnv fe.env with base := B }

theorem canonB_viewOf (mb : MBase) : CanonB (viewOf mb) { mb := some mb } := by
  unfold CanonB; rfl

theorem CanonB.push {fe : FEnv} {B : FBase} (h : CanonB fe B) (ci : ConstantInfo) :
    CanonB (fe.push ci) B := by
  unfold CanonB at h ⊢
  rw [h]
  rfl

theorem CanonB.pushTable {fe : FEnv} {B : FBase} (h : CanonB fe B) (t : ProjTable) :
    CanonB (fe.pushTable t) B := by
  unfold CanonB at h ⊢
  rw [h]
  rfl

theorem CanonB.pushAll {B : FBase} :
    ∀ (L : List ConstantInfo) {fe : FEnv}, CanonB fe B → CanonB (FEnv.pushAll L fe) B
  | [], _, h => h
  | ci :: L, _, h => CanonB.pushAll L (h.push ci)

theorem CanonB.pushTables {B : FBase} :
    ∀ (Q : List ProjTable) {fe : FEnv}, CanonB fe B → CanonB (FEnv.pushTables Q fe) B
  | [], _, h => h
  | t :: Q, _, h => CanonB.pushTables Q (h.pushTable t)

theorem CanonB.pushDelta {fe : FEnv} {B : FBase} (h : CanonB fe B) (L : List ConstantInfo)
    (Q : List ProjTable) : CanonB (FEnv.pushDelta L Q fe) B :=
  CanonB.pushTables Q (CanonB.pushAll L h)

theorem CanonB.ovl {fe : FEnv} {B : FBase} (h : CanonB fe B) : fe.ovl = [] := by
  rw [h]; rfl

theorem CanonB.idx {fe : FEnv} {B : FBase} (h : CanonB fe B) (n : Name) :
    fe.idx[n]? = idxSpec fe.env.consts n := by
  rw [h]
  exact mkFEnv_idx fe.env n

theorem CanonB.visibleBelow {fe : FEnv} {B : FBase} (h : CanonB fe B) :
    fe.visibleBelow = fe.env.consts.length := by
  rw [h]
  exact mkFEnv_visibleBelow fe.env

theorem CanonB.base {fe : FEnv} {B : FBase} (h : CanonB fe B) : fe.base = B := by
  rw [h]

theorem CanonB.tbls {fe : FEnv} {B : FBase} (h : CanonB fe B) (T : Name) :
    fe.tbls[T]? = fe.env.tables.find? (·.structName == T) := by
  rw [h]
  exact mkTblsGo_getElem? T fe.env.tables

theorem idxSpec_none {n : Name} : ∀ {l : List ConstantInfo}, idxSpec l n = none →
    l.find? (·.name == n) = none
  | [], _ => rfl
  | ci :: cs, h => by
    rw [idxSpec] at h
    by_cases hn : ci.name == n
    · rw [ite_eq_left hn] at h; cases h
    · rw [ite_eq_right hn] at h
      rw [List.find?_cons, Bool.of_not_eq_true hn]
      exact idxSpec_none h

theorem idxSpec_some {n : Name} {l : List ConstantInfo} {c : Nat} {ci : ConstantInfo}
    (h : idxSpec l n = some (c, ci)) : l.find? (·.name == n) = some ci := by
  have := idxSpec_snd n l
  rw [h] at this
  exact this.symm

/-- **A view's lookup**: its own constants, then the base. -/
theorem CanonB.find? {fe : FEnv} {B : FBase} (h : CanonB fe B) (n : Name) :
    fe.find? n = (fe.env.find? n).or (B.find? n) := by
  unfold FEnv.find?
  rw [h.ovl]
  simp only
  rw [h.idx n, h.base]
  unfold Env.find?
  cases hs : idxSpec fe.env.consts n with
  | none => rw [idxSpec_none hs]; rfl
  | some p =>
    obtain ⟨c, ci⟩ := p
    simp only
    rw [h.visibleBelow, ite_eq_left (idxSpec_lt hs), idxSpec_some hs]
    rfl

/-- **A view's raw table lookup**: its own tables, then the base's. -/
theorem CanonB.rawTable? {fe : FEnv} {B : FBase} (h : CanonB fe B) (T : Name) :
    fe.rawTable? T = (fe.env.tables.find? (·.structName == T)).or (B.findTable? T) := by
  unfold FEnv.rawTable?
  rw [h.tbls T, h.base]
  cases fe.env.tables.find? (·.structName == T) <;> rfl

theorem CanonB.idxBelow {fe : FEnv} {B : FBase} (h : CanonB fe B) : IdxBelow fe := by
  refine ⟨h.ovl, fun n c ci hl => ?_⟩
  rw [h.idx n] at hl
  rw [h.visibleBelow]
  exact idxSpec_lt hl

theorem IdxBelow.mkFEnv (env : Env) : IdxBelow (ConLeche.mkFEnv env) := by
  refine ⟨rfl, fun n c ci hl => ?_⟩
  rw [mkFEnv_idx] at hl
  rw [mkFEnv_visibleBelow]
  exact idxSpec_lt hl

/-- **A view over the store is the twin of the canonical index of the
environment it stands for.** -/
theorem CanonB.twin {fe : FEnv} {mb : MBase} (h : CanonB fe { mb := some mb }) :
    Twin fe (ConLeche.mkFEnv (envAt fe (ctxOf mb))) := by
  refine ⟨?_, ?_, h.idxBelow, IdxBelow.mkFEnv _⟩
  · funext n
    rw [h.find? n, mkFEnv_find?]
    show _ = (envAt fe (ctxOf mb)).find? n
    unfold envAt Env.find?
    simp only
    rw [List.find?_append]
    have hb : ({ mb := some mb } : FBase).find? n = mb.find? n := rfl
    rw [hb, ← ctxOf_find?]
    rfl
  · funext T
    rw [h.rawTable? T, mkFEnv_rawTable?]
    unfold envAt
    simp only
    rw [List.find?_append]
    have hb : ({ mb := some mb } : FBase).findTable? T = mb.findTable? T := rfl
    rw [hb, ← ctxOf_tables_find?]

/-- What a view's run leaves behind, over its context. -/
theorem envAt_pushDelta (fe : FEnv) (C : Env) (L : List ConstantInfo) (Q : List ProjTable) :
    envAt (FEnv.pushDelta L Q fe) C = ⟨L.reverse ++ (envAt fe C).consts,
      Q.reverse ++ (envAt fe C).tables⟩ := by
  unfold envAt
  rw [pushDelta_env]
  simp

theorem mkFEnv_pushAll (E : Env) :
    ∀ L : List ConstantInfo, FEnv.pushAll L (ConLeche.mkFEnv E) =
      ConLeche.mkFEnv ⟨L.reverse ++ E.consts, E.tables⟩
  | [] => rfl
  | ci :: L => by
    show FEnv.pushAll L ((ConLeche.mkFEnv E).push ci) = _
    rw [push_mkFEnv, mkFEnv_pushAll _ L]
    simp

theorem mkFEnv_pushTables (E : Env) :
    ∀ Q : List ProjTable, FEnv.pushTables Q (ConLeche.mkFEnv E) =
      ConLeche.mkFEnv ⟨E.consts, Q.reverse ++ E.tables⟩
  | [] => rfl
  | t :: Q => by
    show FEnv.pushTables Q ((ConLeche.mkFEnv E).pushTable t) = _
    rw [pushTable_mkFEnv, mkFEnv_pushTables _ Q]
    simp

theorem mkFEnv_pushDelta (E : Env) (L : List ConstantInfo) (Q : List ProjTable) :
    FEnv.pushDelta L Q (ConLeche.mkFEnv E) =
      ConLeche.mkFEnv ⟨L.reverse ++ E.consts, Q.reverse ++ E.tables⟩ := by
  unfold FEnv.pushDelta
  rw [mkFEnv_pushAll, mkFEnv_pushTables]

/-! ## The step at twin indices -/

/-- A value record's constant is named, and typed, by the record. -/
theorem valueStep_cv {W : FEnv} {d : Declaration} {ci : ConstantInfo} {vg : ValueGroup}
    (h : valueStep W d = some (.ok (ci, vg))) :
    ci.toConstantVal = vg.cv ∧
      ((∃ v hint, d = .defnDecl vg.cv v hint ∧ vg.kind = .defn ∧ vg.jv = v) ∨
       (∃ v, d = .thmDecl vg.cv v ∧ vg.kind = .thm ∧ vg.jv = v) ∨
       (∃ v, d = .opaqueDecl vg.cv v ∧ vg.kind = .opaque ∧ vg.jv = v)) := by
  cases d with
  | defnDecl cv value hint =>
    unfold valueStep at h
    simp only at h
    split at h
    · cases h
    · split at h
      · simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, .inl ⟨value, hint, rfl, rfl, rfl⟩⟩
      · cases h
  | thmDecl cv value =>
    unfold valueStep at h
    simp only at h
    split at h
    · simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, .inr (.inl ⟨value, rfl, rfl, rfl⟩)⟩
    · cases h
  | opaqueDecl cv value =>
    unfold valueStep at h
    simp only at h
    split at h
    · cases h
    · split at h
      · simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, .inr (.inr ⟨value, rfl, rfl, rfl⟩)⟩
      · cases h
  | axiomDecl _ => cases h
  | basisDecl _ => cases h
  | quotDecl _ _ => cases h
  | indDecl _ _ => cases h

/-- **The fold's step at twin indices**: it pushes the same constants and
tables onto each and records the same check (at each index's own
counter), whatever the records before. -/
theorem installDeclStep_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) {i : Nat}
    {pend₁ pend₂ : Array PendingCheck} {d : Declaration} {q : Nat × FEnv × Array PendingCheck}
    (h : installDeclStep mode pins (i, fe₁, pend₁) d = .ok q) :
    ∃ L Q vg?, q = (i + 1, FEnv.pushDelta L Q fe₁, pushPending pend₁ i fe₁.visibleBelow vg?) ∧
      installDeclStep mode pins (i, fe₂, pend₂) d =
        .ok (i + 1, FEnv.pushDelta L Q fe₂, pushPending pend₂ i fe₂.visibleBelow vg?) ∧
      ∀ vg, vg? = some vg → ∃ ci, L = [ci] ∧ Q = [] ∧ valueStep fe₁ d = some (.ok (ci, vg)) := by
  unfold installDeclStep at h ⊢
  split at h
  case isFalse => exact nomatch h
  rename_i hand
  simp only [hand, ↓reduceIte]
  cases hv : valueStep fe₁ d with
  | some r =>
    have h₁ := installStepC_value (mode := mode) (pins := pins) (i := i) (pend := pend₁)
      (fe := fe₁) rfl hv
    have h₂ := installStepC_value (mode := mode) (pins := pins) (i := i) (pend := pend₂)
      (fe := fe₂) ht.find hv
    cases r with
    | error e =>
      revert h h₁
      cases installStepC mode pins i fe₁ pend₁ d {} with
      | error e' => intro h _; exact nomatch h
      | ok p => intro _ h₁; simp [Except.map] at h₁
    | ok cv =>
      obtain ⟨ci, vg⟩ := cv
      revert h h₁ h₂
      cases installStepC mode pins i fe₁ pend₁ d {} with
      | error e' => intro h _; exact nomatch h
      | ok p =>
        obtain ⟨⟨fe₁', pend₁'⟩, s₁⟩ := p
        intro h h₁ h₂
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h₁
        obtain ⟨rfl, rfl⟩ := h₁
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨[ci], [], some vg, rfl, ?_, fun vg' hvg => ⟨ci, rfl, rfl, by cases hvg; rfl⟩⟩
        revert h₂
        cases installStepC mode pins i fe₂ pend₂ d {} with
        | error e' => intro h₂; simp [Except.map] at h₂
        | ok p₂ =>
          obtain ⟨⟨fe₂', pend₂'⟩, s₂⟩ := p₂
          intro h₂
          simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h₂
          obtain ⟨rfl, rfl⟩ := h₂
          rfl
  | none =>
    have hs₁ := installStepC_of_valueStep_none (mode := mode) (pins := pins) (i := i)
      (fe := fe₁) (pend := pend₁) hv
    have hs₂ := installStepC_of_valueStep_none (mode := mode) (pins := pins) (i := i)
      (fe := fe₂) (pend := pend₂) hv
    rw [hs₁] at h
    rw [hs₂]
    have h' : (match (checkDeclStepC mode pins fe₁ d {}).bind
        (fun v => (pure (v.1, pend₁) : CheckCM _) v.2) with
      | .ok ((fe', pend'), _) => Except.ok (i + 1, fe', pend')
      | .error e => .error (e, i)) = Except.ok q := h
    rcases checkDeclStepC_twin (mode := mode) pins ht d {} with
      ⟨e, h₁, h₂⟩ | ⟨a₁, a₂, s', h₁, h₂, L, Q, ha₁, ha₂⟩
    · rw [h₁] at h'
      exact nomatch h'
    · refine ⟨L, Q, none, ?_, ?_, fun _ h => nomatch h⟩
      · rw [h₁] at h'
        simp only [Except.bind, pure, StateT.pure, Except.pure, Except.ok.injEq] at h'
        rw [← h', ha₁]
        rfl
      · show (match (checkDeclStepC mode pins fe₂ d {}).bind
            (fun v => (pure (v.1, pend₂) : CheckCM _) v.2) with
          | .ok ((fe', pend'), _) => Except.ok (i + 1, fe', pend')
          | .error e => .error (e, i)) = _
        rw [h₂, ha₂]
        rfl

/-! ## The record checks -/

/-- **A record's check reads its index through the prefix view's
lookups only.** -/
theorem checkPending_congr {fe₁ fe₂ : FEnv} {pc₁ pc₂ : PendingCheck}
    (hf : (fe₁.restrictTo pc₁.vis).find? = (fe₂.restrictTo pc₂.vis).find?)
    (ht : (fe₁.restrictTo pc₁.vis).findTable? = (fe₂.restrictTo pc₂.vis).findTable?)
    (hv : pc₁.vg = pc₂.vg) (s : CState) :
    checkPending mode fe₁ pc₁ s = checkPending mode fe₂ pc₂ s := by
  unfold checkPending
  simp only [coreKnotI_congr hf ht, opSIxC_congr hf ht, installValueGuardsC_congr hf, hv]

/-! ## The view's prefix -/

theorem idxSpec_append_not_mem {n : Name} : ∀ (new old : List ConstantInfo),
    n ∉ new.map (·.name) → idxSpec (new ++ old) n = idxSpec old n
  | [], _, _ => rfl
  | ci :: new, old, hn => by
    rw [List.cons_append, idxSpec]
    have hne : (ci.name == n) = false := by
      refine beq_false_of_ne fun he => hn ?_
      rw [← he]; exact List.mem_cons_self
    rw [hne]
    exact idxSpec_append_not_mem new old (fun h => hn (List.mem_cons_of_mem _ h))

theorem idxSpec_append_mem {n : Name} : ∀ (new old : List ConstantInfo),
    n ∈ new.map (·.name) → ∃ c ci, idxSpec (new ++ old) n = some (c, ci) ∧ old.length ≤ c
  | [], _, h => by simp at h
  | ci :: new, old, hn => by
    rw [List.cons_append, idxSpec]
    by_cases he : ci.name == n
    · rw [ite_eq_left he]
      exact ⟨_, ci, rfl, by simp⟩
    · rw [ite_eq_right he]
      have hn' : n ∈ new.map (·.name) := by
        rcases List.mem_cons.mp hn with h | h
        · exact absurd (beq_iff_eq.mpr h.symm) he
        · exact h
      exact idxSpec_append_mem new old hn'

theorem find?_none_of_not_mem {l : List ConstantInfo} {n : Name} (h : n ∉ l.map (·.name)) :
    l.find? (·.name == n) = none := by
  rw [List.find?_eq_none]
  intro c hc hcn
  exact h (List.mem_map.mpr ⟨c, hc, beq_iff_eq.mp hcn⟩)

/-- **The view's prefix at an earlier counter is the environment of
then**: a view `feF` that extends `fe` by constants `new`, name-unique over
the context. -/
theorem CanonB.restrict_find? {fe feF : FEnv} {mb : MBase}
    (hF : CanonB feF { mb := some mb }) (hfe : CanonB fe { mb := some mb })
    {new : List ConstantInfo} (hext : feF.env.consts = new ++ fe.env.consts)
    (hnd : NodupNames (envAt feF (ctxOf mb))) (n : Name) :
    (feF.restrictTo fe.visibleBelow).find? n = (envAt fe (ctxOf mb)).find? n := by
  have hnd' : ((new ++ fe.env.consts ++ (ctxOf mb).consts).map (·.name)).Nodup := by
    have := hnd; unfold NodupNames envAt at this; rw [hext] at this; exact this
  rw [List.map_append, List.map_append] at hnd'
  have hov : (feF.restrictTo fe.visibleBelow).ovl = [] := hF.ovl
  unfold FEnv.find?
  rw [hov]
  simp only
  have hidx : (feF.restrictTo fe.visibleBelow).idx[n]? = idxSpec feF.env.consts n := hF.idx n
  have hbase : (feF.restrictTo fe.visibleBelow).base = { mb := some mb } := hF.base
  have hvis : (feF.restrictTo fe.visibleBelow).visibleBelow = fe.env.consts.length := by
    show fe.visibleBelow = _; exact hfe.visibleBelow
  rw [hidx, hbase, hvis, hext]
  unfold envAt Env.find?
  simp only
  rw [List.find?_append]
  by_cases hn : n ∈ new.map (·.name)
  · obtain ⟨c, ci, hs, hc⟩ := idxSpec_append_mem new fe.env.consts hn
    rw [hs]
    simp only [show ¬ c < fe.env.consts.length from Nat.not_lt.mpr hc, ↓reduceIte]
    have h1 : n ∉ fe.env.consts.map (·.name) := fun h =>
      (List.nodup_append.mp (List.nodup_append.mp hnd').1).2.2 n hn n h rfl
    have h2 : n ∉ (ctxOf mb).consts.map (·.name) := fun h =>
      (List.nodup_append.mp hnd').2.2 n (List.mem_append_left _ hn) n h rfl
    rw [find?_none_of_not_mem h1, find?_none_of_not_mem h2]
    rfl
  · rw [idxSpec_append_not_mem new fe.env.consts hn]
    cases hs : idxSpec fe.env.consts n with
    | none =>
      rw [idxSpec_none hs]
      show mb.find? n = _
      rw [← ctxOf_find?]
      rfl
    | some p =>
      obtain ⟨c, ci⟩ := p
      simp only
      rw [ite_eq_left (idxSpec_lt hs), idxSpec_some hs]
      rfl

/-- The view's prefix's table lookup, likewise, when the tables `newQ`
installed since are of structures not stored then. -/
theorem CanonB.restrict_findTable? {fe feF : FEnv} {mb : MBase}
    (hF : CanonB feF { mb := some mb }) (hfe : CanonB fe { mb := some mb })
    {new : List ConstantInfo} (hext : feF.env.consts = new ++ fe.env.consts)
    {newQ : List ProjTable} (hextT : feF.env.tables = newQ ++ fe.env.tables)
    (hfresh : ∀ t ∈ newQ, (envAt fe (ctxOf mb)).find? t.structName = none)
    (hnd : NodupNames (envAt feF (ctxOf mb))) (T : Name) :
    (feF.restrictTo fe.visibleBelow).findTable? T = (envAt fe (ctxOf mb)).findTable? T := by
  unfold FEnv.findTable? Env.findTable?
  rw [CanonB.restrict_find? hF hfe hext hnd T]
  split
  · rename_i hT
    have hraw : (feF.restrictTo fe.visibleBelow).rawTable? T = feF.rawTable? T := rfl
    rw [hraw, hF.rawTable? T, hextT, List.find?_append]
    have hq : newQ.find? (·.structName == T) = none := by
      rw [List.find?_eq_none]
      intro t ht htT
      have := hfresh t ht
      rw [beq_iff_eq.mp htT] at this
      rw [this] at hT
      cases hT
    rw [hq]
    unfold envAt
    simp only
    rw [List.find?_append]
    have hb : ({ mb := some mb } : FBase).findTable? T = mb.findTable? T := rfl
    simp only [Option.none_or]
    rw [hb, ← ctxOf_tables_find?]
  · rfl

/-! ## The run at a view -/

/-- **What a run at a view leaves behind**: still a view; its constants,
tables and records extend the start's, every new record named by a new
constant at or above the start's counter; and the canonical indices of
the environments it stands for form a fresh chain. -/
theorem viewRun_trace {mb : MBase} {ds : List Declaration} {p q : Nat × FEnv × Array PendingCheck}
    (hrun : InstallRun mode pins ds p q) (hc : CanonB p.2.1 { mb := some mb }) :
    CanonB q.2.1 { mb := some mb } ∧
    (∃ new newQ newR, q.2.1.env.consts = new ++ p.2.1.env.consts ∧
      q.2.1.env.tables = newQ ++ p.2.1.env.tables ∧ q.2.2.toList = p.2.2.toList ++ newR ∧
      ∀ pc ∈ newR, pc.vg.cv.name ∈ new.map (·.name)) ∧
    (∀ env, PushChain env (ConLeche.mkFEnv (envAt p.2.1 (ctxOf mb))) →
      PushChain env (ConLeche.mkFEnv (envAt q.2.1 (ctxOf mb)))) := by
  induction hrun with
  | nil p => exact ⟨hc, ⟨[], [], [], rfl, rfl, by simp, by simp⟩, fun _ h => h⟩
  | @cons d ds p p₁ q hstep rest ih =>
    obtain ⟨i, fe, pend⟩ := p
    have ht := hc.twin
    obtain ⟨L, Q, vg?, rfl, hcan, hvg⟩ := installDeclStep_twin (pend₂ := #[]) ht hstep
    have hc₁ : CanonB (FEnv.pushDelta L Q fe) { mb := some mb } := hc.pushDelta L Q
    obtain ⟨hcq, ⟨new, newQ, newR, hn, hq, hr, hrn⟩, hch⟩ := ih hc₁
    have hE₁ : envAt (FEnv.pushDelta L Q fe) (ctxOf mb) =
        (FEnv.pushDelta L Q (ConLeche.mkFEnv (envAt fe (ctxOf mb)))).env := by
      rw [mkFEnv_pushDelta, envAt_pushDelta]; rfl
    refine ⟨hcq, ⟨new ++ L.reverse, newQ ++ Q.reverse,
      (pushPending #[] i fe.visibleBelow vg?).toList ++ newR, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hn, pushDelta_env]; simp
    · rw [hq, pushDelta_env]; simp
    · rw [hr]
      cases vg? with
      | none => simp [pushPending]
      | some vg => simp [pushPending]
    · intro pc hpc
      rcases List.mem_append.mp hpc with h | h
      · cases hv : vg? with
        | none => rw [hv] at h; simp [pushPending] at h
        | some vg =>
          rw [hv] at h
          simp only [pushPending, List.push_toArray, List.nil_append, List.mem_singleton] at h
          subst h
          obtain ⟨ci, rfl, rfl, hval⟩ := hvg vg hv
          have := (valueStep_cv hval).1
          simp only [List.map_append, List.reverse_cons, List.reverse_nil, List.nil_append,
            List.map_cons, List.map_nil]
          refine List.mem_append_right _ (List.mem_singleton.mpr ?_)
          rw [← this]; rfl
      · rw [List.map_append]; exact List.mem_append_left _ (hrn pc h)
    · intro env hp
      obtain ⟨fe', pend', s', heq, hstepC⟩ := installDeclStep_ok hcan
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl, rfl⟩ := heq
      obtain ⟨hpush, -⟩ := installStepC_push mode i hp #[] d {} _ s' hstepC
      apply hch env
      rw [hE₁]
      rw [mkFEnv_pushDelta] at hpush ⊢
      exact hpush

/-! ## Acceptance from the context -/

/-- A found name stays found when constants are consed on. -/
theorem find?_isSome_append {E : Env} {l : List ConstantInfo} {T : List ProjTable} {n : Name}
    (h : (E.find? n).isSome = true) : ((⟨l ++ E.consts, T⟩ : Env).find? n).isSome = true := by
  unfold Env.find? at h ⊢
  rw [List.find?_append]
  cases l.find? (·.name == n) with
  | some _ => rfl
  | none => exact h

/-- **The proofs a run's records attest**: a flagged name is the name of a
record at the end of the run — a theorem's, or a definition's or opaque
constant's whose value also passes the theorem record's check there — at
a name that is not pinned. -/
@[expose] def ProofsAttested (mode : CheckMode) (proofs : Name → Bool) (feF : FEnv)
    (pendF : Array PendingCheck) : Prop :=
  ∀ n, proofs n = true → ∃ pc ∈ pendF.toList, pc.vg.cv.name = n ∧ n ∉ ConLeche.Modular.pinnedNames ∧
    (pc.vg.kind = .thm ∨ (pc.vg.kind ≠ .thm ∧
      ∃ s, checkPending mode feF { pc with vg := { pc.vg with kind := .thm } } {} = .ok ((), s)))

/-- **A run at a view is accepted from the module's context**
(`Modular.AcceptedFrom`): every step is the fold's step at the canonical
index of the environment so far, its record's check is the run's at the
end, and a flagged name the step newly stores is a proof of the step's
declaration.  From any point of the run whose records are named in the
environment so far. -/
theorem accepted_of_run {mb : MBase} {proofs : Name → Bool} {nF : Nat} {feF : FEnv}
    {pendF : Array PendingCheck}
    (hchk : ∀ pc ∈ pendF.toList, ∃ s, checkPending mode feF pc {} = .ok ((), s))
    (hndF : NodupNames (envAt feF (ctxOf mb)))
    (hprf : ProofsAttested mode proofs feF pendF) :
    ∀ {ds : List Declaration} {p q : Nat × FEnv × Array PendingCheck},
      InstallRun mode pins ds p q → q = (nF, feF, pendF) →
      CanonB p.2.1 { mb := some mb } →
      (∀ pc ∈ p.2.2.toList, ((envAt p.2.1 (ctxOf mb)).find? pc.vg.cv.name).isSome = true) →
      ConLeche.Modular.AcceptedFrom mode pins proofs (envAt p.2.1 (ctxOf mb)) ds
        (envAt feF (ctxOf mb)) := by
  intro ds p q hrun
  induction hrun with
  | nil p => intro hq _ _; rw [hq]; exact .nil _
  | @cons d ds p p₁ q hstep rest ih =>
    intro hq hc hrecs
    subst hq
    obtain ⟨i, fe, pend⟩ := p
    simp only at hc hrecs
    have ht := hc.twin
    obtain ⟨L, Q, vg?, rfl, hcan, hvg⟩ := installDeclStep_twin (pend₂ := #[]) ht hstep
    have hc₁ : CanonB (FEnv.pushDelta L Q fe) { mb := some mb } := hc.pushDelta L Q
    -- the run from here
    obtain ⟨hcF₀, ⟨new₀, newQ₀, newR₀, hn₀, hq₀, hr₀, hrn₀⟩, hch₀⟩ :=
      viewRun_trace (.cons hstep rest) hc
    obtain ⟨-, ⟨new₁, newQ₁, newR₁, hn₁, hq₁, hr₁, hrn₁⟩, -⟩ := viewRun_trace rest hc₁
    simp only at hcF₀ hn₀ hq₀ hr₀ hn₁ hq₁ hr₁ hch₀
    -- the environments
    let E := envAt fe (ctxOf mb)
    have hE₁ : envAt (FEnv.pushDelta L Q fe) (ctxOf mb) =
        (FEnv.pushDelta L Q (ConLeche.mkFEnv E)).env := by
      rw [mkFEnv_pushDelta, envAt_pushDelta]; rfl
    have hcanE : FEnv.pushDelta L Q (ConLeche.mkFEnv E) =
        ConLeche.mkFEnv (FEnv.pushDelta L Q (ConLeche.mkFEnv E)).env := by
      rw [mkFEnv_pushDelta]; rfl
    -- the chain from `E` to the end: fresh constants and tables
    have hchainF := hch₀ E (PushChain.refl E)
    obtain ⟨-, -, -, ⟨newQF, hQF, hQFf⟩⟩ := hchainF
    have hndE₁ : NodupNames (FEnv.pushDelta L Q (ConLeche.mkFEnv E)).env := by
      rw [← hE₁]
      have := hndF
      unfold NodupNames envAt at this ⊢
      rw [hn₁] at this
      rw [List.map_append, List.map_append] at this
      rw [List.map_append]
      exact (List.nodup_append.mp (by simpa only [List.append_assoc] using this)).2.1
    have hndE : NodupNames (ConLeche.mkFEnv E).env := by
      have := hndE₁; unfold NodupNames at this ⊢
      rw [mkFEnv_pushDelta] at this
      change ((L.reverse ++ E.consts).map (·.name)).Nodup at this
      change (E.consts.map (·.name)).Nodup
      rw [List.map_append] at this
      exact (List.nodup_append.mp this).2.1
    have hQFc : feF.env.tables = newQF ++ fe.env.tables := by
      have h1 := hQF
      change feF.env.tables ++ (ctxOf mb).tables = newQF ++ (fe.env.tables ++ (ctxOf mb).tables)
        at h1
      rw [← List.append_assoc] at h1
      exact List.append_cancel_right h1
    -- the canonical step's chain, for the freshness of its tables
    obtain ⟨fe', pend', s', heq, hstepC⟩ := installDeclStep_ok hcan
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, hfe', hpend'⟩ := heq
    obtain ⟨hpush, -⟩ := installStepC_push mode i (PushChain.refl E) #[] d {} _ s' hstepC
    simp only at hpush
    rw [← hfe'] at hpush
    obtain ⟨-, -, -, ⟨newQ₂, hQ₂, hQ₂f⟩⟩ := hpush
    refine .cons (i := i) hcan ?_ ?_ ?_
    · -- the step's record, checked
      intro pc hpc
      cases hv : vg? with
      | none => rw [hv] at hpc; simp [pushPending] at hpc
      | some vg =>
        rw [hv] at hpc
        simp only [pushPending, List.push_toArray, List.nil_append, List.mem_singleton] at hpc
        subst hpc
        have hmem : (⟨vg, i, fe.visibleBelow⟩ : PendingCheck) ∈ pendF.toList := by
          rw [hv] at hr₁
          rw [hr₁]
          exact List.mem_append_left _ (by simp [pushPending])
        obtain ⟨sB, hB⟩ := hchk _ hmem
        refine ⟨sB, ?_⟩
        rw [← hB]
        refine checkPending_congr (mode := mode)
          (fe₁ := FEnv.pushDelta L Q (ConLeche.mkFEnv E)) (fe₂ := feF)
          (pc₁ := ⟨vg, i, (ConLeche.mkFEnv E).visibleBelow⟩) (pc₂ := ⟨vg, i, fe.visibleBelow⟩)
          ?_ ?_ rfl {}
        · funext n
          rw [CanonB.restrict_find? hcF₀ hc hn₀ hndF n]
          show ((FEnv.pushDelta L Q (ConLeche.mkFEnv E)).restrictTo
            (ConLeche.mkFEnv E).visibleBelow).find? n = _
          rw [mkFEnv_visibleBelow]
          rw [restrictTo_find?_of_extends hcanE hndE₁ (new := L.reverse)
            (by rw [mkFEnv_pushDelta]; rfl)]
        · funext T
          rw [CanonB.restrict_findTable? hcF₀ hc hn₀ (newQ := newQF) hQFc hQFf hndF T]
          · show ((FEnv.pushDelta L Q (ConLeche.mkFEnv E)).restrictTo
              (ConLeche.mkFEnv E).visibleBelow).findTable? T = _
            rw [mkFEnv_visibleBelow]
            rw [restrictTo_findTable?_of_extends hcanE hndE₁ (new := L.reverse)
              (by rw [mkFEnv_pushDelta]; rfl) (newQ := newQ₂) hQ₂ hQ₂f]
    · -- a flagged name the step newly stores is a proof of its declaration
      intro n hpn hnE hnE'
      obtain ⟨pc, hpc, hpcn, hpin, hkind⟩ := hprf n hpn
      rw [hr₁] at hpc
      have hold_or : pc ∈ pend.toList ∨ (∃ vg, vg? = some vg ∧ pc = ⟨vg, i, fe.visibleBelow⟩) ∨
          pc ∈ newR₁ := by
        rcases List.mem_append.mp hpc with h | h
        · cases hv : vg? with
          | none => rw [hv] at h; exact .inl (by simpa [pushPending] using h)
          | some vg =>
            rw [hv] at h
            simp only [pushPending, Array.toList_push, List.mem_append, List.mem_singleton] at h
            rcases h with h | h
            · exact .inl h
            · exact .inr (.inl ⟨vg, rfl, h⟩)
        · exact .inr (.inr h)
      rcases hold_or with hold | ⟨vg, hv, hthis⟩ | hlater
      · -- an earlier record: its name was stored already
        have := hrecs pc hold
        rw [hpcn, hnE] at this
        cases this
      · -- the step's own record
        subst hthis
        obtain ⟨ci, rfl, rfl, hval⟩ := hvg vg hv
        obtain ⟨-, hd⟩ := valueStep_cv hval
        simp only at hpcn hkind
        rcases hd with ⟨v, hint, rfl, hk, hjv⟩ | ⟨v, rfl, hk, hjv⟩ | ⟨v, rfl, hk, hjv⟩
        · rcases hkind with hk' | ⟨-, sT, hT⟩
          · rw [hk] at hk'; cases hk'
          · refine ⟨(by rw [hpcn]; exact hpin), sT, ?_⟩
            rw [← hT]
            refine checkPending_congr ?_ ?_ ?_ {}
            · funext m
              rw [CanonB.restrict_find? hcF₀ hc hn₀ hndF m]
              show ((ConLeche.mkFEnv E).restrictTo (ConLeche.mkFEnv E).visibleBelow).find? m = _
              rw [mkFEnv_visibleBelow]
              exact restrictTo_find?_of_extends rfl hndE (new := []) rfl m
            · funext T
              rw [CanonB.restrict_findTable? hcF₀ hc hn₀ (newQ := newQF) hQFc hQFf hndF T]
              show ((ConLeche.mkFEnv E).restrictTo
                (ConLeche.mkFEnv E).visibleBelow).findTable? T = _
              rw [mkFEnv_visibleBelow]
              exact restrictTo_findTable?_of_extends rfl hndE (new := []) rfl (newQ := []) rfl
                (fun _ h => nomatch h) T
            · simp only [hjv]
        · exact (show vg.cv.name ∉ ConLeche.Modular.pinnedNames by rw [hpcn]; exact hpin)
        · rcases hkind with hk' | ⟨-, sT, hT⟩
          · rw [hk] at hk'; cases hk'
          · refine ⟨(by rw [hpcn]; exact hpin), sT, ?_⟩
            rw [← hT]
            refine checkPending_congr ?_ ?_ ?_ {}
            · funext m
              rw [CanonB.restrict_find? hcF₀ hc hn₀ hndF m]
              show ((ConLeche.mkFEnv E).restrictTo (ConLeche.mkFEnv E).visibleBelow).find? m = _
              rw [mkFEnv_visibleBelow]
              exact restrictTo_find?_of_extends rfl hndE (new := []) rfl m
            · funext T
              rw [CanonB.restrict_findTable? hcF₀ hc hn₀ (newQ := newQF) hQFc hQFf hndF T]
              show ((ConLeche.mkFEnv E).restrictTo
                (ConLeche.mkFEnv E).visibleBelow).findTable? T = _
              rw [mkFEnv_visibleBelow]
              exact restrictTo_findTable?_of_extends rfl hndE (new := []) rfl (newQ := []) rfl
                (fun _ h => nomatch h) T
            · simp only [hjv]
      · -- a later record: its name is stored only later
        have hlat := hrn₁ pc hlater
        rw [hpcn] at hlat
        exfalso
        have hnd := hndF
        unfold NodupNames envAt at hnd
        rw [hn₁] at hnd
        simp only [List.map_append] at hnd
        have hin : n ∈ ((FEnv.pushDelta L Q fe).env.consts ++ (ctxOf mb).consts).map (·.name) := by
          have : ((envAt (FEnv.pushDelta L Q fe) (ctxOf mb)).find? n).isSome = true := by
            rw [hE₁]; exact hnE'
          obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp this
          unfold Env.find? at hc'
          have hp := List.find?_some hc'
          exact List.mem_map.mpr ⟨c, List.mem_of_find?_eq_some hc', beq_iff_eq.mp hp⟩
        rw [List.map_append] at hin
        exact (List.nodup_append.mp (by simpa only [List.append_assoc] using hnd)).2.2 n hlat n
          hin rfl
    · -- the rest, from the environment the step produced
      rw [← hE₁]
      refine ih rfl hc₁ ?_
      intro pc hpc
      cases hv : vg? with
      | none =>
        rw [hv] at hpc
        simp only [pushPending] at hpc
        exact find?_isSome_append (E := E) (hrecs pc hpc) |> fun h => by
          rw [envAt_pushDelta]; exact h
      | some vg =>
        rw [hv] at hpc
        simp only [pushPending, Array.toList_push, List.mem_append, List.mem_singleton] at hpc
        rw [envAt_pushDelta]
        rcases hpc with hpc | rfl
        · exact find?_isSome_append (hrecs pc hpc)
        · obtain ⟨ci, rfl, rfl, hval⟩ := hvg vg hv
          have := (valueStep_cv hval).1
          show (Env.find? ⟨[ci].reverse ++ E.consts, _⟩ vg.cv.name).isSome = true
          unfold Env.find?
          simp [← this, ConstantInfo.name]

end ConLeche.Cached.Mod
