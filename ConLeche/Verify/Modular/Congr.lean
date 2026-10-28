module

public import ConLeche.Verify.Modular.IsoFold

public section

/-!
# The local checks read environments through their lookups (task #373)

`ConLeche.Modular.LocalOk` is stated about a module's context and own
environment as lists, but it reads them only through their lookups —
`find?` and the table lookup — except for two list facts (each name
once, every table found under its structure) and the acceptance
(`AcceptedFrom`), which runs the fold from their canonical indices.
This file makes that a theorem:

* `AcceptedFrom.over_congr` — declarations accepted over a context `C₁`
  are accepted over any `C₂` with the same lookups, with the same own
  constants and tables (the steps push the same constants: the indices
  are twins; the record checks read the prefixes through lookups);
* `LocalOk.congr` — the local checks of a development carry over to one
  whose contexts and own environments have the same lookups, given the
  two list facts and the acceptance there.

The isolated development (`isoDevOf`, `ConLeche/Verify/Modular/IsoRun.lean`)
gets its local checks this way from the store run's (`devOf`).
-/

namespace ConLeche.Cached.Mod

open ConLeche ConLeche.Modular

variable {mode : CheckMode} {pins : List NatOpPinSet}

/-! ## Environments with the same lookups -/

/-- **Two environments with the same lookups**: the same constant and the
same table (before the constant gate) under every name. -/
structure EnvLike (E₁ E₂ : Env) : Prop where
  find : ∀ n, E₁.find? n = E₂.find? n
  tbl : ∀ T, E₁.tables.find? (·.structName == T) = E₂.tables.find? (·.structName == T)

theorem EnvLike.refl (E : Env) : EnvLike E E := ⟨fun _ => rfl, fun _ => rfl⟩

theorem EnvLike.symm {E₁ E₂ : Env} (h : EnvLike E₁ E₂) : EnvLike E₂ E₁ :=
  ⟨fun n => (h.find n).symm, fun T => (h.tbl T).symm⟩

theorem EnvLike.of_base {C₁ C₂ : Env} {mb : MBase} (h₁ : BaseLike C₁ mb) (h₂ : BaseLike C₂ mb) :
    EnvLike C₁ C₂ :=
  ⟨fun n => (h₁.find n).trans (h₂.find n).symm, fun T => (h₁.tbl T).trans (h₂.tbl T).symm⟩

theorem EnvLike.findTable {E₁ E₂ : Env} (h : EnvLike E₁ E₂) (T : Name) :
    E₁.findTable? T = E₂.findTable? T := by
  unfold Env.findTable?
  rw [h.find, h.tbl]

theorem Env.over_find? (X C : Env) (n : Name) :
    (Env.over X C).find? n = (X.find? n).or (C.find? n) := by
  unfold Env.over Env.find?
  rw [List.find?_append]

theorem EnvLike.over {C₁ C₂ : Env} (h : EnvLike C₁ C₂) (X : Env) :
    EnvLike (Env.over X C₁) (Env.over X C₂) := by
  refine ⟨fun n => ?_, fun T => ?_⟩
  · rw [Env.over_find?, Env.over_find?, h.find]
  · unfold Env.over
    simp only
    rw [List.find?_append, List.find?_append, h.tbl]

/-- Environments with the same lookups have twin canonical indices. -/
theorem EnvLike.twin {E₁ E₂ : Env} (h : EnvLike E₁ E₂) : Twin (mkFEnv E₁) (mkFEnv E₂) := by
  refine ⟨?_, ?_, IdxBelow.mkFEnv _, IdxBelow.mkFEnv _⟩
  · funext n; rw [mkFEnv_find?, mkFEnv_find?, h.find]
  · funext T; rw [mkFEnv_rawTable?, mkFEnv_rawTable?, h.tbl]

/-- **The canonical index over a context, restricted past it**: the own
constants below the bound, then the context. -/
theorem mkFEnv_over_restrict_find? (X C : Env) (k : Nat) (n : Name) :
    ((mkFEnv (Env.over X C)).restrictTo (k + C.consts.length)).find? n =
      match idxSpec X.consts n with
      | some (c, ci) => if c < k then some ci else none
      | none => C.find? n := by
  unfold FEnv.find?
  show (match (mkFEnv (Env.over X C)).idx[n]? with
      | some (c, ci) => if c < k + C.consts.length then some ci else none
      | none => (mkFEnv (Env.over X C)).base.find? n) = _
  rw [mkFEnv_idx]
  unfold Env.over
  simp only
  rw [idxSpec_append]
  cases hs : idxSpec X.consts n with
  | some p =>
    obtain ⟨c, ci⟩ := p
    simp only [Nat.add_lt_add_iff_right]
  | none =>
    simp only
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

theorem mkFEnv_over_restrict_congr {C₁ C₂ : Env} (h : EnvLike C₁ C₂) (X : Env) (k : Nat) :
    ((mkFEnv (Env.over X C₁)).restrictTo (k + C₁.consts.length)).find? =
      ((mkFEnv (Env.over X C₂)).restrictTo (k + C₂.consts.length)).find? := by
  funext n
  rw [mkFEnv_over_restrict_find?, mkFEnv_over_restrict_find?, h.find]

theorem mkFEnv_over_restrict_table {C₁ C₂ : Env} (h : EnvLike C₁ C₂) (X : Env) (k : Nat) :
    ((mkFEnv (Env.over X C₁)).restrictTo (k + C₁.consts.length)).findTable? =
      ((mkFEnv (Env.over X C₂)).restrictTo (k + C₂.consts.length)).findTable? := by
  funext T
  unfold FEnv.findTable?
  rw [mkFEnv_over_restrict_congr h X k]
  show (if _ then (mkFEnv (Env.over X C₁)).rawTable? T else none) =
    (if _ then (mkFEnv (Env.over X C₂)).rawTable? T else none)
  rw [(h.over X).twin.raw]

/-! ## Acceptance over a context -/

theorem mkFEnv_over_visibleBelow (X C : Env) :
    (mkFEnv (Env.over X C)).visibleBelow = X.consts.length + C.consts.length := by
  rw [mkFEnv_visibleBelow]; unfold Env.over; simp

theorem pushDelta_over (L : List ConstantInfo) (Q : List ProjTable) (X C : Env) :
    (FEnv.pushDelta L Q (mkFEnv (Env.over X C))).env =
      Env.over ⟨L.reverse ++ X.consts, Q.reverse ++ X.tables⟩ C := by
  rw [pushDelta_env]
  show (⟨L.reverse ++ (X.consts ++ C.consts), Q.reverse ++ (X.tables ++ C.tables)⟩ : Env) = _
  unfold Env.over
  simp

theorem Env.over_eta (E C : Env) (X : Env) (h : E = Env.over X C) :
    E.consts = X.consts ++ C.consts ∧ E.tables = X.tables ++ C.tables := by
  subst h; exact ⟨rfl, rfl⟩

/-- **Acceptance over a context depends on the context's lookups only**:
declarations accepted over `C₁` are accepted over `C₂` with the same
own constants and tables. -/
theorem AcceptedFrom.over_congr {C₁ C₂ : Env} (hC : EnvLike C₁ C₂) {proofs : Name → Bool} :
    ∀ {E E' : Env} {ds : List Declaration}, AcceptedFrom mode pins proofs E ds E' →
      ∀ X Y, E = Env.over X C₁ → E' = Env.over Y C₁ →
      AcceptedFrom mode pins proofs (Env.over X C₂) ds (Env.over Y C₂) := by
  intro E E' ds hacc
  induction hacc with
  | nil E =>
    intro X Y hX hY
    have h1 := Env.over_eta E C₁ X hX
    have h2 := Env.over_eta E C₁ Y hY
    have hc : X.consts = Y.consts := List.append_cancel_right (h1.1.symm.trans h2.1)
    have ht : X.tables = Y.tables := List.append_cancel_right (h1.2.symm.trans h2.2)
    have : X = Y := by cases X; cases Y; simp_all
    subst this
    exact .nil _
  | @cons E E' d ds i fe pend hstep hrec hflag rest ih =>
    intro X Y hX hY
    subst hX
    have ht := (hC.over X).twin
    obtain ⟨L, Q, vg?, hq, h₂, -⟩ := installDeclStep_twin (pend₂ := #[]) ht hstep
    simp only [Prod.mk.injEq] at hq
    obtain ⟨-, rfl, rfl⟩ := hq
    have hfe₁ := pushDelta_over L Q X C₁
    have hfe₂ := pushDelta_over L Q X C₂
    refine .cons h₂ ?_ ?_ ?_
    · -- the record checks, through the prefix lookups
      intro pc hpc
      cases hv : vg? with
      | none => rw [hv] at hpc; simp [pushPending] at hpc
      | some vg =>
        rw [hv] at hpc
        simp only [pushPending, List.push_toArray, List.nil_append, List.mem_singleton] at hpc
        subst hpc
        have hpc₁ : (⟨vg, i, (mkFEnv (Env.over X C₁)).visibleBelow⟩ : PendingCheck) ∈
            (pushPending #[] i (mkFEnv (Env.over X C₁)).visibleBelow vg?).toList := by
          rw [hv]; simp [pushPending]
        obtain ⟨s, hs⟩ := hrec _ hpc₁
        refine ⟨s, ?_⟩
        rw [← hs]
        symm
        apply checkPending_congr
        · show ((FEnv.pushDelta L Q (mkFEnv (Env.over X C₁))).restrictTo
              (mkFEnv (Env.over X C₁)).visibleBelow).find? =
            ((FEnv.pushDelta L Q (mkFEnv (Env.over X C₂))).restrictTo
              (mkFEnv (Env.over X C₂)).visibleBelow).find?
          rw [mkFEnv_pushDelta, mkFEnv_pushDelta, mkFEnv_over_visibleBelow,
            mkFEnv_over_visibleBelow]
          have e₁ : (⟨L.reverse ++ (Env.over X C₁).consts, Q.reverse ++ (Env.over X C₁).tables⟩
              : Env) = Env.over ⟨L.reverse ++ X.consts, Q.reverse ++ X.tables⟩ C₁ := by
            unfold Env.over; simp
          have e₂ : (⟨L.reverse ++ (Env.over X C₂).consts, Q.reverse ++ (Env.over X C₂).tables⟩
              : Env) = Env.over ⟨L.reverse ++ X.consts, Q.reverse ++ X.tables⟩ C₂ := by
            unfold Env.over; simp
          rw [e₁, e₂]
          funext n
          rw [mkFEnv_over_restrict_find?, mkFEnv_over_restrict_find?, hC.find]
        · show ((FEnv.pushDelta L Q (mkFEnv (Env.over X C₁))).restrictTo
              (mkFEnv (Env.over X C₁)).visibleBelow).findTable? =
            ((FEnv.pushDelta L Q (mkFEnv (Env.over X C₂))).restrictTo
              (mkFEnv (Env.over X C₂)).visibleBelow).findTable?
          rw [mkFEnv_pushDelta, mkFEnv_pushDelta, mkFEnv_over_visibleBelow,
            mkFEnv_over_visibleBelow]
          have e₁ : (⟨L.reverse ++ (Env.over X C₁).consts, Q.reverse ++ (Env.over X C₁).tables⟩
              : Env) = Env.over ⟨L.reverse ++ X.consts, Q.reverse ++ X.tables⟩ C₁ := by
            unfold Env.over; simp
          have e₂ : (⟨L.reverse ++ (Env.over X C₂).consts, Q.reverse ++ (Env.over X C₂).tables⟩
              : Env) = Env.over ⟨L.reverse ++ X.consts, Q.reverse ++ X.tables⟩ C₂ := by
            unfold Env.over; simp
          rw [e₁, e₂]
          exact mkFEnv_over_restrict_table hC _ _
        · rfl
    · -- a flagged name
      intro n hp hnone hsome
      rw [← (hC.over X).find] at hnone
      rw [hfe₂, ← (hC.over _).find, ← hfe₁] at hsome
      have hpd := hflag n hp hnone hsome
      cases d with
      | thmDecl cv v => exact hpd
      | defnDecl cv v hint =>
        obtain ⟨hpin, s, hs⟩ := hpd
        refine ⟨hpin, s, ?_⟩
        rw [← hs]
        symm
        apply checkPending_congr
        · show ((mkFEnv (Env.over X C₁)).restrictTo (mkFEnv (Env.over X C₁)).visibleBelow).find? =
            ((mkFEnv (Env.over X C₂)).restrictTo (mkFEnv (Env.over X C₂)).visibleBelow).find?
          rw [mkFEnv_over_visibleBelow, mkFEnv_over_visibleBelow]
          exact mkFEnv_over_restrict_congr hC X _
        · show ((mkFEnv (Env.over X C₁)).restrictTo
              (mkFEnv (Env.over X C₁)).visibleBelow).findTable? =
            ((mkFEnv (Env.over X C₂)).restrictTo
              (mkFEnv (Env.over X C₂)).visibleBelow).findTable?
          rw [mkFEnv_over_visibleBelow, mkFEnv_over_visibleBelow]
          exact mkFEnv_over_restrict_table hC X _
        · rfl
      | opaqueDecl cv v =>
        obtain ⟨hpin, s, hs⟩ := hpd
        refine ⟨hpin, s, ?_⟩
        rw [← hs]
        symm
        apply checkPending_congr
        · show ((mkFEnv (Env.over X C₁)).restrictTo (mkFEnv (Env.over X C₁)).visibleBelow).find? =
            ((mkFEnv (Env.over X C₂)).restrictTo (mkFEnv (Env.over X C₂)).visibleBelow).find?
          rw [mkFEnv_over_visibleBelow, mkFEnv_over_visibleBelow]
          exact mkFEnv_over_restrict_congr hC X _
        · show ((mkFEnv (Env.over X C₁)).restrictTo
              (mkFEnv (Env.over X C₁)).visibleBelow).findTable? =
            ((mkFEnv (Env.over X C₂)).restrictTo
              (mkFEnv (Env.over X C₂)).visibleBelow).findTable?
          rw [mkFEnv_over_visibleBelow, mkFEnv_over_visibleBelow]
          exact mkFEnv_over_restrict_table hC X _
        · rfl
      | axiomDecl _ => exact hpd.elim
      | basisDecl _ => exact hpd.elim
      | quotDecl _ _ => exact hpd.elim
      | indDecl _ _ => exact hpd.elim
    · rw [hfe₂]
      exact ih _ Y hfe₁ hY

/-! ## What a context entry's laws read, through lookups -/

theorem constsResolve_congr {R₁ R₂ : Env} (h : ∀ n, R₁.find? n = R₂.find? n) :
    ∀ e : Expr, e.constsResolve R₁ = e.constsResolve R₂ := by
  intro e
  induction e with
  | bvar _ => rfl
  | sort _ => rfl
  | lit l => cases l <;> simp only [Expr.constsResolve, h]
  | const n _ => simp only [Expr.constsResolve, h]
  | fvar _ ty ih => exact ih
  | app f a ihf iha => simp only [Expr.constsResolve, ihf, iha]
  | lam ty b iht ihb => simp only [Expr.constsResolve, iht, ihb]
  | forallE ty b iht ihb => simp only [Expr.constsResolve, iht, ihb]
  | letE ty v b iht ihv ihb => simp only [Expr.constsResolve, iht, ihv, ihb]
  | proj s _ e ih => simp only [Expr.constsResolve, h, ih]

theorem projsFormer_congr {C₁ C₂ : Env} (h : ∀ n, C₁.find? n = C₂.find? n) :
    ∀ e : Expr, Modular.Expr.projsFormer C₁ e = Modular.Expr.projsFormer C₂ e := by
  intro e
  induction e with
  | proj s _ e ih => simp only [Modular.Expr.projsFormer, h, ih]
  | app f a ihf iha => simp only [Modular.Expr.projsFormer, ihf, iha]
  | lam ty b iht ihb => simp only [Modular.Expr.projsFormer, iht, ihb]
  | forallE ty b iht ihb => simp only [Modular.Expr.projsFormer, iht, ihb]
  | letE ty v b iht ihv ihb => simp only [Modular.Expr.projsFormer, iht, ihv, ihb]
  | _ => rfl

theorem EntryScoped.congr {R₁ R₂ C₁ C₂ : Env} (hR : ∀ n, R₁.find? n = R₂.find? n)
    (hC : ∀ T, C₁.findTable? T = C₂.findTable? T) {n : Name} {ci : ConstantInfo}
    (h : EntryScoped R₁ C₁ n ci) : EntryScoped R₂ C₂ n ci := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have cr := constsResolve_congr hR
  refine ⟨by rw [← cr]; exact h1, fun cv v hh hc => by rw [← cr]; exact h2 cv v hh hc,
    fun cv mI rP rules hc r hr => ?_, fun cv caps hc => ?_, fun d hd => by rw [← hR]; exact h5 d hd⟩
  · obtain ⟨a, b, c⟩ := h3 cv mI rP rules hc r hr
    exact ⟨by rw [← cr]; exact a, by rw [← hR]; exact b,
      fun lvls pins hf p hp => by rw [← cr]; exact c lvls pins hf p hp⟩
  · obtain ⟨a, b, c, d⟩ := h4 cv caps hc
    refine ⟨fun m hm => by rw [← hR]; exact a m hm, fun c' hc' => by rw [← hR]; exact b c' hc',
      fun he => by rw [← hR]; exact c he, fun t ht => ?_⟩
    rw [← hC] at ht
    obtain ⟨d1, d2⟩ := d t ht
    exact ⟨by rw [← hR]; exact d1, fun b hb => by rw [← cr]; exact d2 b hb⟩

theorem EntryProjs.congr {C₁ C₂ : Env} (hC : EnvLike C₁ C₂) {n : Name} {ci : ConstantInfo}
    (h : EntryProjs C₁ n ci) : EntryProjs C₂ n ci := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have pf := projsFormer_congr hC.find
  refine ⟨by rw [← pf]; exact h1, fun cv v hh hc => by rw [← pf]; exact h2 cv v hh hc,
    fun cv mI rP rules hc r hr => ?_, fun cv caps hc t ht b hb => ?_⟩
  · obtain ⟨a, c⟩ := h3 cv mI rP rules hc r hr
    exact ⟨by rw [← pf]; exact a, fun lvls pins hf p hp => by rw [← pf]; exact c lvls pins hf p hp⟩
  · rw [← hC.findTable] at ht
    rw [← pf]; exact h4 cv caps hc t ht b hb

theorem BlockIn.congr {C₁ C₂ : Env} (hC : EnvLike C₁ C₂) {n : Name} {ci : ConstantInfo}
    (h : BlockIn C₁ n ci) : BlockIn C₂ n ci := by
  cases ci with
  | indInfo cv caps =>
    obtain ⟨a, b, c, d⟩ := h
    refine ⟨fun m hm => by rw [← hC.find]; exact a m hm, fun c' hc => by rw [← hC.find]; exact b c' hc,
      fun he => by rw [← hC.find]; exact c he, fun t ht => ?_⟩
    rw [← hC.findTable] at ht
    rw [← hC.find]; exact d t ht
  | ctorInfo cv _ _ => exact fun T us hT => by rw [← hC.find]; exact h T us hT
  | recInfo _ _ _ rules => exact fun r hr => by rw [← hC.find]; exact h r hr
  | _ => trivial

theorem find?_filter_name (l : List ConstantInfo) (q : Name → Bool) (m : Name) :
    (l.filter fun c => q c.name).find? (·.name == m) = if q m then l.find? (·.name == m) else none := by
  induction l with
  | nil => split <;> rfl
  | cons c l ih =>
    rw [List.filter_cons, List.find?_cons]
    by_cases hcm : c.name = m
    · subst hcm
      by_cases hq : q c.name = true
      · simp [hq]
      · simp only [hq, Bool.false_eq_true, ↓reduceIte]
        rw [ih]; simp [hq]
    · have hne : (c.name == m) = false := beq_false_of_ne hcm
      by_cases hq : q c.name = true
      · simp only [hq, ↓reduceIte, List.find?_cons, hne]; exact ih
      · simp only [hq, Bool.false_eq_true, ↓reduceIte, hne]; exact ih

theorem readsAlike_lookup (dev : Nat → Module) (i b : Nat) (m : Name) :
    (readsAlike dev i b).find? m =
      if ((dev i).context.find? m).isSome && (dev i).res m == (dev b).res m then
        (dev b).own.find? m else none := by
  unfold readsAlike
  exact find?_filter_name _ (fun m => ((dev i).context.find? m).isSome && (dev i).res m == (dev b).res m) m

/-! ## The local checks -/

/-- **The local checks carry over to a development with the same
lookups**: `dev₂` is `dev₁` with other contexts and own environments,
each with the same lookups; the context of `i` stores each name once
and finds every table of it under its structure, and its declarations
are accepted from it (its own environment its context, if compared). -/
theorem LocalOk.congr {dev₁ dev₂ : Nat → Module} {i : Nat} (Cx Ow : Nat → Env)
    (hdev : ∀ k, dev₂ k = { dev₁ k with context := Cx k, own := Ow k })
    (hctx : ∀ k, EnvLike (dev₁ k).context (dev₂ k).context)
    (hown : ∀ k, EnvLike (dev₁ k).own (dev₂ k).own)
    (hnd : ((dev₂ i).context.consts.map (·.name)).Nodup)
    (htm : ∀ t ∈ (dev₂ i).context.tables, (dev₂ i).context.findTable? t.structName = some t)
    (hacc : AcceptedFrom mode pins (dev₁ i).proofs (dev₁ i).context (dev₁ i).decls (dev₁ i).own →
      AcceptedFrom mode pins (dev₂ i).proofs (dev₂ i).context (dev₂ i).decls (dev₂ i).own)
    (hcmp : (dev₂ i).compared = true → (dev₂ i).own = (dev₂ i).context)
    (h : LocalOk mode pins dev₁ i) : LocalOk mode pins dev₂ i := by
  have e_imp : ∀ k, (dev₂ k).imports = (dev₁ k).imports := fun k => by rw [hdev]
  have e_dec : ∀ k, (dev₂ k).decls = (dev₁ k).decls := fun k => by rw [hdev]
  have e_src : ∀ k, (dev₂ k).src = (dev₁ k).src := fun k => by rw [hdev]
  have e_prf : ∀ k, (dev₂ k).proofs = (dev₁ k).proofs := fun k => by rw [hdev]
  have e_res : ∀ k, (dev₂ k).res = (dev₁ k).res := fun k => by rw [hdev]
  have e_cmp : ∀ k, (dev₂ k).compared = (dev₁ k).compared := fun k => by rw [hdev]
  have e_ok : ∀ k n, (dev₂ k).ownKey k n = (dev₁ k).ownKey k n := fun k n => by
    funext ci; unfold Module.ownKey; rw [e_prf]
  have hra : ∀ b m, (readsAlike dev₂ i b).find? m = (readsAlike dev₁ i b).find? m := by
    intro b m
    rw [readsAlike_lookup, readsAlike_lookup]
    simp only [(hctx i).find, e_res]
    split
    · exact ((hown b).find m).symm
    · rfl
  refine ⟨?_, ?_, hnd, ?_, hcmp, ?_, ?_, ?_, ?_, ?_, ?_, htm, ?_, ?_⟩
  · rw [e_imp]; exact h.below
  · intro n hn; rw [e_src]; rw [← (hctx i).find] at hn; exact h.src_lt n hn
  · intro hc; rw [e_cmp] at hc; exact hacc (h.accepted hc)
  · intro n ci hf
    rw [← (hctx i).find] at hf
    obtain ⟨ci', h1, h2⟩ := h.context_le n ci hf
    refine ⟨ci', ?_, h2⟩
    rw [e_src, ← (hown _).find]; exact h1
  · intro n ci hf
    rw [← (hctx i).find] at hf
    have := h.scoping n ci hf
    rw [e_src]
    exact EntryScoped.congr (fun m => (hra _ m).symm) (hctx i).findTable this
  · intro T ci hf
    rw [← (hctx i).find] at hf
    rw [← (hctx i).findTable, h.tables T ci hf, e_src]
    cases ci <;> simp only [(hown _).findTable]
  · intro n ci hf
    rw [← (hctx i).find] at hf
    exact EntryProjs.congr (hctx i) (h.projs n ci hf)
  · intro n ci hf
    rw [← (hctx i).find] at hf
    exact BlockIn.congr (hctx i) (h.blocks n ci hf)
  · intro n cv mI rP rules hf r hr cvj nP nF hc T us hT
    rw [← (hctx i).find] at hf
    rw [e_src, ← (hown _).find] at hc ⊢
    exact h.recFam n cv mI rP rules hf r hr cvj nP nF hc T us hT
  · intro n hn
    rw [← (hctx i).find] at hn
    rw [e_res, e_res, e_src]; exact h.res_context n hn
  · intro n ci ho hc
    rw [← (hown i).find] at ho
    rw [← (hctx i).find] at hc
    rw [e_res, e_ok]; exact h.res_own n ci ho hc

end ConLeche.Cached.Mod
