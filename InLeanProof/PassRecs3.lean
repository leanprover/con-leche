module

public import InLeanProof.PassRecs2
import ConLeche.Verify.Denote.IndFrame

/-!
# O7-recursors: the erased comparison and the classes' constructors (task #451, lane O7-recursors)

The recursor stage (`genRecCheck`) against master's, continued bottom-up:

* `eraseFVarTysI_run`: InLean's `eraseFVarTys` (a `for` over `fvarIds` filling
  a `HashMap` of interned `Sort 0`-typed variables, then `EO.replace`) is
  master's pure `Expr.eraseFVarTys` on the reading.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-! ## Erasing the variables' annotations -/

/-- The erasing map's entries: each read as master's variable at the id's
depth, annotated `Sort 0`. -/
@[expose] def EraseMapOk (s : InLean.CState) (m : Std.HashMap FVarId Lean.Expr) : Prop :=
  ∀ id y, m[id]? = some y → ∃ d, EO.fvDepth? id = some d ∧ OkS s y = true ∧
    TrS s y = .fvar d (.sort .zero)

theorem EraseMapOk.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {m : Std.HashMap FVarId Lean.Expr}
    (hm : EraseMapOk s₀ m) : EraseMapOk s₁ m := by
  intro id y hy
  obtain ⟨d, hd, ho, ht⟩ := hm id y hy
  exact ⟨d, hd, okS_of_tabLe h ho, by rw [TrS_of_tabLe h ho, ht]⟩

/-- The callback of InLean's `eraseFVarTys`. -/
@[expose] def efF (m : Std.HashMap FVarId Lean.Expr) (x : Lean.Expr) : Option Lean.Expr :=
  match x with
  | .fvar id => m[id]?
  | _ => none

theorem efF_nonfvar {m : Std.HashMap FVarId Lean.Expr} {x : Lean.Expr} (hx : ∀ id, x ≠ .fvar id) :
    efF m x = none := by
  cases x <;> simp_all [efF]

/-- **The erasing replacement, read**: at a map holding every variable of
the term, master's `eraseFVarTys` of the reading. -/
theorem mapSpec_efF_tr {s : InLean.CState} {m : Std.HashMap FVarId Lean.Expr}
    (hm : EraseMapOk s m) :
    ∀ (e : Lean.Expr) (k : Nat), OkS s e = true →
      (∀ id, OccF id e → (EO.fvDepth? id).isSome → (m[id]?).isSome) →
      OkS s (mapSpec (fun x _ => efF m x) e k) = true ∧
        TrS s (mapSpec (fun x _ => efF m x) e k) = (TrS s e).eraseFVarTys := by
  intro e
  induction e with
  | fvar id =>
    intro k h hc
    obtain ⟨d', ty, ht, hd'⟩ := TrS_stripTop_fvar (id := id) h rfl
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (hc id rfl (by rw [hd']; rfl))
    obtain ⟨d, hd, hyo, hyt⟩ := hm id y hy
    rw [hd] at hd'; cases hd'
    rw [mapSpec_eq_of_some (f := fun x _ => efF m x) (by simpa [efF] using hy)]
    refine ⟨hyo, ?_⟩
    rw [hyt, ht]
    rfl
  | app f a ihf iha =>
    intro k h hc
    simp only [OkS_app, Bool.and_eq_true] at h
    have h1 := ihf k h.1 (fun id hi => hc id (.inl hi))
    have h2 := iha k h.2 (fun id hi => hc id (.inr hi))
    simp only [mapSpec, efF_nonfvar (m := m) (x := .app f a) (by simp), Option.getD_none,
      OkS_app, TrS_app, ConLeche.Expr.eraseFVarTys, ConLeche.Expr.replaceFVars, h1.1, h2.1,
      Bool.and_self, true_and]
    rw [h1.2, h2.2]; rfl
  | lam nm t b bi iht ihb =>
    intro k h hc
    simp only [OkS_lam, Bool.and_eq_true] at h
    have h1 := iht k h.1 (fun id hi => hc id (.inl hi))
    have h2 := ihb (k + 1) h.2 (fun id hi => hc id (.inr hi))
    simp only [mapSpec, efF_nonfvar (m := m) (x := .lam nm t b bi) (by simp), Option.getD_none,
      OkS_lam, TrS_lam, ConLeche.Expr.eraseFVarTys, ConLeche.Expr.replaceFVars, h1.1, h2.1,
      Bool.and_self, true_and]
    rw [h1.2, h2.2]; rfl
  | forallE nm t b bi iht ihb =>
    intro k h hc
    simp only [OkS_forallE, Bool.and_eq_true] at h
    have h1 := iht k h.1 (fun id hi => hc id (.inl hi))
    have h2 := ihb (k + 1) h.2 (fun id hi => hc id (.inr hi))
    simp only [mapSpec, efF_nonfvar (m := m) (x := .forallE nm t b bi) (by simp),
      Option.getD_none, OkS_forallE, TrS_forallE, ConLeche.Expr.eraseFVarTys,
      ConLeche.Expr.replaceFVars, h1.1, h2.1, Bool.and_self, true_and]
    rw [h1.2, h2.2]; rfl
  | letE nm t v b nd iht ihv ihb =>
    intro k h hc
    simp only [OkS_letE, Bool.and_eq_true] at h
    have h1 := iht k h.1.1 (fun id hi => hc id (.inl hi))
    have h2 := ihv k h.1.2 (fun id hi => hc id (.inr (.inl hi)))
    have h3 := ihb (k + 1) h.2 (fun id hi => hc id (.inr (.inr hi)))
    simp only [mapSpec, efF_nonfvar (m := m) (x := .letE nm t v b nd) (by simp),
      Option.getD_none, OkS_letE, TrS_letE, ConLeche.Expr.eraseFVarTys,
      ConLeche.Expr.replaceFVars, h1.1, h2.1, h3.1, Bool.and_self, true_and]
    rw [h1.2, h2.2, h3.2]; rfl
  | proj sn i x ih =>
    intro k h hc
    rw [OkS_proj] at h
    have h1 := ih k h hc
    simp only [mapSpec, efF_nonfvar (m := m) (x := .proj sn i x) (by simp), Option.getD_none,
      OkS_proj, TrS_proj, ConLeche.Expr.eraseFVarTys, ConLeche.Expr.replaceFVars, h1.1, true_and]
    rw [h1.2]; rfl
  | mdata md x ih =>
    intro k h hc
    rw [OkS_mdata] at h
    simp only [mapSpec, efF_nonfvar (m := m) (x := .mdata md x) (by simp), Option.getD_none,
      OkS_mdata, TrS_mdata]
    exact ih k h hc
  | bvar i =>
    intro k h _
    simp only [mapSpec, efF_nonfvar (m := m) (x := .bvar i) (by simp), Option.getD_none]
    exact ⟨h, by simp [TrS, trE, ConLeche.Expr.eraseFVarTys, ConLeche.Expr.replaceFVars]⟩
  | sort u =>
    intro k h _
    simp only [mapSpec, efF_nonfvar (m := m) (x := .sort u) (by simp), Option.getD_none]
    exact ⟨h, by simp [TrS, trE, ConLeche.Expr.eraseFVarTys, ConLeche.Expr.replaceFVars]⟩
  | const c us =>
    intro k h _
    simp only [mapSpec, efF_nonfvar (m := m) (x := .const c us) (by simp), Option.getD_none]
    exact ⟨h, by simp [TrS, trE, ConLeche.Expr.eraseFVarTys, ConLeche.Expr.replaceFVars]⟩
  | lit l =>
    intro k h _
    simp only [mapSpec, efF_nonfvar (m := m) (x := .lit l) (by simp), Option.getD_none]
    exact ⟨h, by simp [TrS, trE, ConLeche.Expr.eraseFVarTys, ConLeche.Expr.replaceFVars]⟩
  | mvar i => intro k h; simp [OkS, okE] at h

/-- The body of InLean's `eraseFVarTys` loop. -/
@[expose] def efBody (id : FVarId) (m : Std.HashMap FVarId Lean.Expr) :
    InLean.CheckCM (ForInStep (Std.HashMap FVarId Lean.Expr)) :=
  match EO.fvDepth? id with
  | some i => (do
    let y ← mkFVarM i (.sort .zero)
    pure (ForInStep.yield (m.insert id y)))
  | _ => pure (ForInStep.yield m)

theorem eraseFVarTys_eq (e : Lean.Expr) :
    InLean.eraseFVarTys e = if !e.hasFVar then pure e else (do
      let m ← forIn (EO.fvarIds e).toList ({} : Std.HashMap FVarId Lean.Expr) efBody
      pure (EO.replace (efF m) e)) := by
  rw [Array.forIn_toList]
  unfold InLean.eraseFVarTys efBody efF
  rfl

/-- The erasing loop: every variable met with a depth gets its entry. -/
theorem efLoop_run {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env} :
    ∀ (l : List FVarId) (m : Std.HashMap FVarId Lean.Expr) {t t' : InLean.CState}
      {m' : Std.HashMap FVarId Lean.Expr},
      CSOKI mode eager env t → EraseMapOk t m → forIn l m efBody t = .ok (m', t') →
      CSOKI mode eager env t' ∧ TabLe t t' ∧ EraseMapOk t' m' ∧
        ∀ id, (id ∈ l ∧ (EO.fvDepth? id).isSome) ∨ m.contains id → m'.contains id
  | [], m, t, t', m', hs, hm, h => by
    rw [List.forIn_nil] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, hm, fun id hid => by simpa using hid⟩
  | id :: l, m, t, t', m', hs, hm, h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, t₂, h1, h⟩ := bind_run h
    unfold efBody at h1
    cases hd : EO.fvDepth? id with
    | none =>
      rw [hd] at h1
      obtain ⟨rfl, rfl⟩ := pure_run h1
      obtain ⟨hs', ht', hm', hc⟩ := efLoop_run l m hs hm h
      refine ⟨hs', ht', hm', fun id' hid => hc id' ?_⟩
      rcases hid with ⟨hmem, hds⟩ | hmc
      · rcases List.mem_cons.1 hmem with rfl | hmem
        · rw [hd] at hds; cases hds
        · exact .inl ⟨hmem, hds⟩
      · exact .inr hmc
    | some i =>
      rw [hd] at h1
      obtain ⟨y, t₂, h3, h1⟩ := bind_run h1
      obtain ⟨rfl, rfl⟩ := pure_run h1
      obtain ⟨hs₃, ht₃, hyo, hyt⟩ := tripleI_iff_run.1
        (mkFVarM_specI hs i (ty := .sort .zero) (by simp [OkS, okE, okLv, okL, depthS]) rfl) y t₂ h3
      have hm₃ : EraseMapOk t₂ (m.insert id y) := by
        intro id' y' hy'
        rw [Std.HashMap.getElem?_insert] at hy'
        split at hy'
        · rename_i heq
          cases hy'
          have : id = id' := eq_of_beq heq
          subst this
          exact ⟨i, hd, hyo, by rw [hyt]; rfl⟩
        · exact (hm.mono ht₃) id' y' hy'
      obtain ⟨hs', ht', hm', hc⟩ := efLoop_run l _ hs₃ hm₃ h
      refine ⟨hs', ht₃.trans ht', hm', fun id' hid => hc id' ?_⟩
      rcases hid with ⟨hmem, hds⟩ | hmc
      · rcases List.mem_cons.1 hmem with rfl | hmem
        · exact .inr (by simp)
        · exact .inl ⟨hmem, hds⟩
      · exact .inr (by simp [hmc])

/-- **InLean's `eraseFVarTys`, read**: master's pure `Expr.eraseFVarTys` of
the reading. -/
theorem eraseFVarTysI_run {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}
    {s₀ s' : InLean.CState} {e r : Lean.Expr} (hs : CSOKI mode eager env s₀)
    (he : OkS s₀ e = true) (h : InLean.eraseFVarTys e s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' r = true ∧
      TrS s' r = (TrS s₀ e).eraseFVarTys := by
  rw [eraseFVarTys_eq] at h
  cases hf : e.hasFVar with
  | false =>
    simp only [hf, Bool.not_false, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, he, (cReplaceFVars_noFvar _ ?_).symm⟩
    rw [← hasFVar_TrS (s := s₀) he, hf]
  | true =>
    simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨m, s₁, h1, h⟩ := bind_run h
    obtain ⟨rfl, rfl⟩ := pure_run h
    obtain ⟨hs₁, ht₁, hm, hc⟩ := efLoop_run _ _ hs (fun _ _ hy => by simp at hy) h1
    have he₁ := okS_of_tabLe ht₁ he
    have hocc : ∀ id, OccF id e → (EO.fvDepth? id).isSome → (m[id]?).isSome := by
      intro id hid hds
      have hmem : id ∈ EO.fvarIds e := (mem_fvarIds (RangeOk_of_OkS he) id).2 hid
      have := hc id (.inl ⟨Array.mem_toList_iff.2 hmem, hds⟩)
      rwa [Std.HashMap.contains_eq_isSome_getElem?] at this
    unfold EO.replace
    rw [mapOff_fresh, ← TrS_of_tabLe ht₁ he]
    exact ⟨hs₁, ht₁, mapSpec_efF_tr hm e 0 he₁ hocc⟩

/-- **A list's erasure, read** (`mapM eraseFVarTys`). -/
theorem mapM_eraseFVarTysI_run {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env} :
    ∀ (l : List Lean.Expr) {s₀ s' : InLean.CState} {r : List Lean.Expr},
      CSOKI mode eager env s₀ → OkSL s₀ l = true →
      l.mapM InLean.eraseFVarTys s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkSL s' r = true ∧
        TrSL s' r = (TrSL s₀ l).map ConLeche.Expr.eraseFVarTys
  | [], s₀, s', r, hs, _, h => by
    rw [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, rfl, rfl⟩
  | a :: l, s₀, s', r, hs, hl, h => by
    simp only [OkSL_cons, Bool.and_eq_true] at hl
    rw [List.mapM_cons] at h
    obtain ⟨x, s₁, h1, h⟩ := bind_run h
    obtain ⟨xs, s₂, h2, h⟩ := bind_run h
    obtain ⟨rfl, rfl⟩ := pure_run h
    obtain ⟨hs₁, ht₁, hxo, hxt⟩ := eraseFVarTysI_run hs hl.1 h1
    obtain ⟨hs₂, ht₂, hxso, hxst⟩ := mapM_eraseFVarTysI_run l hs₁ (okSL_of_tabLe ht₁ hl.2) h2
    refine ⟨hs₂, ht₁.trans ht₂, by simp [OkSL_cons, okS_of_tabLe ht₂ hxo, hxso], ?_⟩
    rw [TrSL_cons, TrSL_cons, List.map_cons, TrS_of_tabLe ht₂ hxo, hxt, hxst,
      TrSL_of_tabLe ht₁ hl.2]

/-! ## The node agreement's comparison (K.53′) -/

/-- `stripPis` commutes with the reading. -/
theorem stripPis_TrS {s : InLean.CState} :
    ∀ (n : Nat) (e : Lean.Expr), OkS s e = true →
      (∀ ds r, InLean.stripPis n e = some (ds, r) → OkSL s ds = true ∧ OkS s r = true) ∧
        ConLeche.Expr.stripPis n (TrS s e) =
          (InLean.stripPis n e).map fun (ds, r) => (TrSL s ds, TrS s r)
  | 0, e, h => by
    refine ⟨fun ds r hs => ?_, by simp [InLean.stripPis, ConLeche.Expr.stripPis, TrSL]⟩
    simp only [InLean.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨rfl, h⟩
  | n + 1, .forallE nm d b bi, h => by
    simp only [OkS_forallE, Bool.and_eq_true] at h
    obtain ⟨ih1, ih2⟩ := stripPis_TrS n b h.2
    refine ⟨fun ds r hs => ?_, ?_⟩
    · simp only [InLean.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨ds', r'⟩, h1, h2⟩ := hs
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨h3, h4⟩ := ih1 ds' r' h1
      exact ⟨by simp [OkSL_cons, h.1, h3], h4⟩
    · rw [TrS_forallE]
      simp only [InLean.stripPis, ConLeche.Expr.stripPis, ih2]
      cases InLean.stripPis n b <;> simp [TrSL_cons]
  | n + 1, .mdata m e, h => by
    rw [OkS_mdata] at h
    rw [TrS_mdata]
    simp only [InLean.stripPis]
    exact stripPis_TrS (n + 1) e h
  | n + 1, .mvar _, h => by simp [OkS, okE] at h
  | n + 1, .fvar id, h => by
    refine ⟨fun ds r hs => by simp [InLean.stripPis] at hs, ?_⟩
    rw [TrS_fvar h]
    simp [InLean.stripPis, ConLeche.Expr.stripPis]
  | _ + 1, .bvar _, _ | _ + 1, .sort _, _ | _ + 1, .const _ _, _
  | _ + 1, .app _ _, _ | _ + 1, .lam _ _ _ _, _ | _ + 1, .letE _ _ _ _ _, _ | _ + 1, .lit _, _
  | _ + 1, .proj _ _ _, _ => by
    refine ⟨fun ds r hs => by simp [InLean.stripPis] at hs, ?_⟩
    simp [InLean.stripPis, ConLeche.Expr.stripPis, TrS_bvar, TrS_sort, TrS_const, TrS_app,
      TrS_lam, TrS_letE, TrS_lit, TrS_proj]

theorem getAppNumArgsT_TrS {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) :
    Expr.getAppNumArgsT e = (TrS s e).getAppArgs.length :=
  getAppNumArgsT_eq (FVarTable.trans_fvarsOnly _) e _ (TransS_of_ok h)

/-- **The node agreement's comparison** (`targetK53`): InLean's `true` is
master's on the readings, in the class's frame `FrameOk`. -/
theorem targetK53I_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {p : InLean.BlockShape} {formerTys tele : List Lean.Expr} {Mc : InLean.TargetMajor}
    {majDom f : Lean.Expr} {s₀ s' : InLean.CState} (hs : CSOKI .verified false L s₀)
    (hfo : OkSL s₀ formerTys = true) (hM : OkTMN s₀ Mc)
    (hF : FrameOk (TrSL s₀ Mc.pfvs) (TrSL s₀ formerTys))
    (htele : OkSL s₀ tele = true) (hmaj : OkS s₀ majDom = true) (hf : OkS s₀ f = true)
    (h : InLean.targetK53 (sharedOpsC .verified fe) fe p formerTys Mc tele majDom f s₀ =
      .ok (true, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.targetK53 (ConLeche.fueledOpsM .verified) L (trShape p)
        (TrSL s₀ formerTys) (trTM s₀ Mc) (TrSL s₀ tele) (TrS s₀ majDom) (TrS s₀ f)) true := by
  obtain ⟨hlv, hds, hpf, -⟩ := hM
  unfold InLean.targetK53 at h
  unfold ConLeche.targetK53
  have hlen : (TrSL s₀ tele).length = tele.length := by simp [TrSL]
  obtain ⟨hsp1, hsp2⟩ := stripPis_TrS tele.length f hf
  rw [hlen, hsp2]
  cases hsp : InLean.stripPis tele.length f with
  | none => rw [hsp] at h; exact absurd (pure_run h).1 (by simp)
  | some q =>
    obtain ⟨teleW, leafW⟩ := q
    obtain ⟨htwo, hlwo⟩ := hsp1 teleW leafW hsp
    rw [hsp] at h
    simp only [Option.map_some]
    obtain ⟨r1, s₁, h1, h⟩ := bind_run h
    obtain ⟨r2, s₂, h2, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hr1o, hr1t⟩ := mapM_eraseFVarTysI_run teleW hs htwo h1
    obtain ⟨hs₂, ht₂, hr2o, hr2t⟩ := mapM_eraseFVarTysI_run tele hs₁ (okSL_of_tabLe ht₁ htele) h2
    have ht₀₂ := ht₁.trans ht₂
    cases hne : (r1 != r2) with
    | true => rw [hne] at h; exact absurd (pure_run h).1 (by simp)
    | false =>
      rw [hne] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have heq : (r1 == r2) = true := by simpa [bne] using hne
      have hTr : TrSL s₂ r1 = TrSL s₂ r2 :=
        TrSL_of_beq (okSL_of_tabLe ht₂ hr1o) (fun b _ => TransS_of_ok (by
          simp only [OkSL, List.all_eq_true] at hr2o; exact hr2o b ‹_›)) heq
      rw [TrSL_of_tabLe ht₂ hr1o, hr1t, hr2t, TrSL_of_tabLe ht₁ htele] at hTr
      rw [hTr]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [← TrS_getAppFnT, ← TrS_getAppFnT]
      generalize hdL : leafW.getAppFnT = hL at h
      generalize hdM : majDom.getAppFnT = hM at h
      cases hL <;> try (simp only at h; exact absurd (pure_run h).1 (by simp))
      rename_i I' us'
      cases hM <;> try (simp only at h; exact absurd (pure_run h).1 (by simp))
      rename_i I u
      simp only at h
      rw [TrS_const, TrS_const]
      simp only
      have hus' := okLv_of_getAppFnT hlwo hdL
      have hlo₂ := okS_of_tabLe ht₀₂ hlwo
      have hmo₂ := okS_of_tabLe ht₀₂ hmaj
      obtain ⟨r3, s₃, h3, h⟩ := bind_run h
      obtain ⟨r4, s₄, h4, h⟩ := bind_run h
      have hA1 : OkSL s₂ ((appArgs leafW).drop Mc.nPc) = true :=
        OkSL_drop s₂ (OkSL_appArgs s₂ hlo₂) _
      obtain ⟨hs₃, ht₃, hr3o, hr3t⟩ := mapM_eraseFVarTysI_run _ hs₂ hA1 h3
      have hA2 : OkSL s₃ ((appArgs majDom).drop Mc.nPc) = true :=
        OkSL_drop s₃ (OkSL_appArgs s₃ (okS_of_tabLe ht₃ hmo₂)) _
      obtain ⟨hs₄, ht₄, hr4o, hr4t⟩ := mapM_eraseFVarTysI_run _ hs₃ hA2 h4
      have ht₀₄ := ht₀₂.trans (ht₃.trans ht₄)
      cases hc : (I' == I && leafW.getAppNumArgsT == majDom.getAppNumArgsT && r3 == r4 &&
          nestOcc p.memberNames 0 0 (mkAppL (Expr.const I' us') (List.take Mc.nPc (appArgs leafW))))
      with
      | false =>
        rw [hc] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact absurd (pure_run h).1 (by simp)
      | true =>
        rw [hc] at h
        simp only [↓reduceIte] at h
        have hTCM := h
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨⟨hI, hn⟩, hr⟩, hocc⟩ := hc
        obtain rfl : I' = I := by simpa using hI
        -- the erased indices agree on the readings
        have hTr4 : TrSL s₄ r3 = TrSL s₄ r4 :=
          TrSL_of_beq (okSL_of_tabLe ht₄ hr3o) (fun b hb => TransS_of_ok (by
            simp only [OkSL, List.all_eq_true] at hr4o; exact hr4o b hb)) hr
        rw [TrSL_of_tabLe ht₄ hr3o, hr3t, hr4t, TrSL_of_tabLe ht₀₂ (OkSL_drop s₀ (OkSL_appArgs s₀ hlwo) _),
          TrSL_of_tabLe (ht₀₂.trans ht₃) (OkSL_drop s₀ (OkSL_appArgs s₀ hmaj) _), TrSL_drop, TrSL_drop,
          TrSL_appArgs, TrSL_appArgs] at hTr4
        have hok₀ : OkS s₀ (InLean.mkAppL (Expr.const I' us') (List.take Mc.nPc (appArgs leafW))) = true := by
          unfold InLean.mkAppL
          rw [OkS_mkAppN, OkS_const, hus', OkSL_take s₀ (OkSL_appArgs s₀ hlwo)]; rfl
        rw [nestOccI_tr _ 0 0 hok₀, TrS_mkAppL_const, TrSL_take, TrSL_appArgs] at hocc
        have hcC : ((toName I' == toName I' &&
            (TrS s₀ leafW).getAppArgs.length == (TrS s₀ majDom).getAppArgs.length &&
            ((TrS s₀ leafW).getAppArgs.drop Mc.nPc).map ConLeche.Expr.eraseFVarTys ==
              ((TrS s₀ majDom).getAppArgs.drop Mc.nPc).map ConLeche.Expr.eraseFVarTys &&
            ConLeche.Expr.nestOcc (trShape p).memberNames 0 0
              ((ConLeche.Expr.const (toName I') (us'.map trL)).mkAppN
                ((TrS s₀ leafW).getAppArgs.take Mc.nPc))) = true) := by
          rw [← getAppNumArgsT_TrS hlwo, ← getAppNumArgsT_TrS hmaj, hTr4, trShape_memberNames]
          simp only [beq_self_eq_true, Bool.true_and, hocc, Bool.and_true]
          exact hn
        simp only [trTM] at hcC ⊢
        simp only [hcC]
        simp only [↓reduceIte]
        have hds₄ := okSL_of_tabLe ht₀₄ hds
        have hpf₄ := okSL_of_tabLe ht₀₄ hpf
        have hfo₄ := okSL_of_tabLe ht₀₄ hfo
        have heds : OkSL s₀ (List.take Mc.nPc (appArgs leafW)) = true :=
          OkSL_take s₀ (OkSL_appArgs s₀ hlwo) _
        have hF₄ : FrameOk (TrSL s₄ Mc.pfvs) (TrSL s₄ formerTys) := by
          rw [TrSL_of_tabLe ht₀₄ hpf, TrSL_of_tabLe ht₀₄ hfo]; exact hF
        obtain ⟨hs', ht', hR⟩ := targetClassMatchI_run hO hs₄ hfo₄ hpf₄ hF₄ hlv hus' hds₄
          (okSL_of_tabLe ht₀₄ heds) hTCM
        refine ⟨hs', ht₀₄.trans ht', ?_⟩
        rw [TrSL_of_tabLe ht₀₄ hpf, TrSL_of_tabLe ht₀₄ hfo, TrSL_of_tabLe ht₀₄ hds,
          TrSL_of_tabLe ht₀₄ heds, TrSL_take, TrSL_appArgs] at hR
        exact hR

/-! ## Node agreement -/

/-- A recorded form's field domain `i`, read. -/
theorem piDomAt_tr {s : InLean.CState} {fvs : List Lean.Expr} {ty f : Lean.Expr} {i : Nat}
    (hfv : OkSL s fvs = true) (hfc : ∀ x ∈ fvs, (TrS s x).looseBVarsBounded 0 = true)
    (hty : OkS s ty = true)
    (h : ((InLean.targetPiDomsWith fvs ty).getD [])[i]? = some f) :
    OkS s f = true ∧
      ((ConLeche.targetPiDomsWith (TrSL s fvs) (TrS s ty)).getD [])[i]? = some (TrS s f) := by
  obtain ⟨h1, h2⟩ := targetPiDomsWith_tr fvs ty hfv hfc hty
  rw [h2]
  cases hd : InLean.targetPiDomsWith fvs ty with
  | none => rw [hd] at h; simp at h
  | some ds =>
    rw [hd] at h
    simp only [Option.getD_some] at h
    refine ⟨okS_getElem? (h1 ds hd) h, ?_⟩
    simp [TrSL, h]

/-- **Node agreement at one recursive field** (`classNodesAgree`): InLean's
pass is master's on the readings. -/
theorem classNodesAgreeI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {p : InLean.BlockShape} {formerTys tele fvs : List Lean.Expr} {Mc : InLean.TargetMajor}
    {leaf : Lean.Expr} {i : Nat} {ctor : Lean.Name} :
    ∀ (es : List InLean.NestCtorNf) {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ → OkSL s₀ formerTys = true → OkTMN s₀ Mc →
      FrameOk (TrSL s₀ Mc.pfvs) (TrSL s₀ formerTys) →
      OkSL s₀ tele = true → OkS s₀ leaf = true → OkSL s₀ fvs = true →
      (∀ x ∈ fvs, (TrS s₀ x).looseBVarsBounded 0 = true) → (∀ e ∈ es, OkNf s₀ e) →
      InLean.classNodesAgree (sharedOpsC .verified fe) fe p formerTys Mc tele leaf fvs i ctor es
        s₀ = .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.classNodesAgree (ConLeche.fueledOpsM .verified) L (trShape p)
          (TrSL s₀ formerTys) (trTM s₀ Mc) (TrSL s₀ tele) (TrS s₀ leaf) (TrSL s₀ fvs) i
          (toName ctor) (es.map (trNf s₀))) ()
  | [], s₀, s', u, hs, _, _, _, _, _, _, _, _, h => by
    unfold InLean.classNodesAgree at h
    obtain ⟨-, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by unfold ConLeche.classNodesAgree; exact Runs.pure _⟩
  | e :: es, s₀, s', u, hs, hfo, hM, hF, hte, hle, hfv, hfc, hes, h => by
    unfold InLean.classNodesAgree at h
    unfold ConLeche.classNodesAgree
    obtain ⟨-, -, hty⟩ := hes e List.mem_cons_self
    cases hd : ((InLean.targetPiDomsWith fvs e.ty).getD [])[i]? with
    | none => rw [hd] at h; exact (throw_run h).elim
    | some f =>
      rw [hd] at h
      obtain ⟨hfo', hfC⟩ := piDomAt_tr hfv hfc hty hd
      simp only [List.map_cons, trNf]
      rw [hfC]
      simp only
      obtain ⟨b, s₁, h1, h⟩ := bind_run h
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨_, _, h2, -⟩ := bind_run h; exact (throw_run h2).elim
      | true =>
        obtain ⟨hs₁, ht₁, hK⟩ := targetK53I_run hO hs hfo hM hF hte hle hfo' h1
        simp only [↓reduceIte] at h
        have hM₁ := OkTMN.mono ht₁ hM
        have hes₁ : ∀ e ∈ es, OkNf s₁ e := fun e he => (OkNf.mono ht₁ (hes e (List.mem_cons_of_mem _ he))).1
        obtain ⟨hs', ht', hR⟩ := classNodesAgreeI_run hO es hs₁ (okSL_of_tabLe ht₁ hfo) hM₁.1
          (by rw [TrSL_of_tabLe ht₁ hM.2.2.1, TrSL_of_tabLe ht₁ hfo]; exact hF) (okSL_of_tabLe ht₁ hte)
          (okS_of_tabLe ht₁ hle) (okSL_of_tabLe ht₁ hfv)
          (fun x hx => by
            rw [TrS_of_tabLe ht₁ (by simp only [OkSL, List.all_eq_true] at hfv; exact hfv x hx)]
            exact hfc x hx) hes₁ h
        rw [hM₁.2, TrSL_of_tabLe ht₁ hfo, TrSL_of_tabLe ht₁ hte, TrS_of_tabLe ht₁ hle,
          TrSL_of_tabLe ht₁ hfv, map_trNf_mono ht₁ (fun e he => hes e (List.mem_cons_of_mem _ he))] at hR
        refine ⟨hs', ht₁.trans ht', Runs.bind hK ?_⟩
        simpa using hR

/-! ## Node agreement at every recursive field -/

theorem unwrapOr_run {α : Type} {o : Option α} {err : InLean.CheckError} {s₀ s' : InLean.CState}
    {v : α} (h : InLean.unwrapOr o err s₀ = .ok (v, s')) : o = some v ∧ s' = s₀ := by
  unfold InLean.unwrapOr at h
  cases o with
  | none => exact (throw_run h).elim
  | some a => obtain ⟨rfl, rfl⟩ := pure_run h; exact ⟨rfl, rfl⟩

theorem trTM_default (s : InLean.CState) : trTM s default = default := rfl

theorem getD_map_trTM (s : InLean.CState) (Ms : List InLean.TargetMajor) (t : Nat) :
    (Ms.map (trTM s)).getD t default = trTM s (Ms.getD t default) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Ms[t]? <;> rfl

theorem getD_of_all {α : Type} [Inhabited α] {P : α → Prop} {l : List α} (h : ∀ a ∈ l, P a)
    (hd : P default) (t : Nat) : P (l.getD t default) := by
  rw [List.getD_eq_getElem?_getD]
  cases ht : l[t]? with
  | none => exact hd
  | some a => exact h a (List.mem_of_getElem? ht)

theorem okTMN_default (s : InLean.CState) : OkTMN s default :=
  ⟨rfl, rfl, rfl, fun _ h => by cases h⟩

/-- A field's leaf class test, read. -/
theorem classLeafAt_tr {s : InLean.CState} (M : InLean.TargetMajor) {leaf : Lean.Expr} :
    InLean.classLeafAt M leaf = ConLeche.classLeafAt (trTM s M) (TrS s leaf) := by
  unfold InLean.classLeafAt ConLeche.classLeafAt
  rw [← TrS_getAppFnT]
  have hm : ∀ m y, leaf.getAppFnT ≠ .mdata m y := fun _ _ h => getAppFnT_ne_mdata h
  generalize leaf.getAppFnT = x at hm
  cases x with
  | const I us => simp [TrS_const, trTM, toName_beq]
  | mdata m y => exact (hm m y rfl).elim
  | fvar id =>
    cases hc : FVarTable.trans (tableOf s) id with
    | none => simp only [TrS, trE, hc]; rfl
    | some c =>
      obtain ⟨_, _, rfl⟩ := FVarTable.trans_fvarsOnly _ id _ hc
      simp only [TrS, trE, hc]; rfl
  | _ => simp [TrS, trE]

/-- The datum's opened fields: readable, read as variables. -/
@[expose] def FvsOk (s : InLean.CState) (fvs : List Lean.Expr) : Prop :=
  ∀ f ∈ fvs, OkS s f = true ∧ ∃ j ty, TrS s f = .fvar j ty

theorem FvsOk.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {fvs : List Lean.Expr}
    (hf : FvsOk s₀ fvs) : FvsOk s₁ fvs ∧ TrSL s₁ fvs = TrSL s₀ fvs := by
  refine ⟨fun f hf' => ?_, ?_⟩
  · obtain ⟨ho, j, ty, ht⟩ := hf f hf'
    exact ⟨okS_of_tabLe h ho, j, ty, by rw [TrS_of_tabLe h ho, ht]⟩
  · exact TrSL_of_tabLe h (by simp only [OkSL, List.all_eq_true]; exact fun f hf' => (hf f hf').1)

theorem FvsOk.okSL {s : InLean.CState} {fvs : List Lean.Expr} (hf : FvsOk s fvs) :
    OkSL s fvs = true := by
  simp only [OkSL, List.all_eq_true]; exact fun f hf' => (hf f hf').1

theorem FvsOk.lbb {s : InLean.CState} {fvs : List Lean.Expr} (hf : FvsOk s fvs) :
    ∀ x ∈ fvs, (TrS s x).looseBVarsBounded 0 = true := by
  intro x hx
  obtain ⟨-, j, ty, ht⟩ := hf x hx
  rw [ht]; rfl

/-- **Node agreement at every recursive field** (`classFieldsAgree`):
InLean's pass is master's on the readings, the kinds as `trCF`. -/
theorem classFieldsAgreeI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {p : InLean.BlockShape} {formerTys fvs : List Lean.Expr} {Ms : List InLean.TargetMajor}
    {ctor : Lean.Name} {E : List InLean.NestCtorNf} :
    ∀ (ks : List InLean.ClassField) (i : Nat) {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ → OkSL s₀ formerTys = true →
      (∀ t, OkTMN s₀ (Ms.getD t default)) →
      (∀ t, FrameOk (TrSL s₀ (Ms.getD t default).pfvs) (TrSL s₀ formerTys)) →
      FvsOk s₀ fvs → i + ks.length ≤ fvs.length → (∀ e ∈ E, OkNf s₀ e) →
      InLean.classFieldsAgree (sharedOpsC .verified fe) fe p formerTys Ms fvs ctor E i ks s₀ =
        .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.classFieldsAgree (ConLeche.fueledOpsM .verified) L (trShape p)
          (TrSL s₀ formerTys) (Ms.map (trTM s₀)) (TrSL s₀ fvs) (toName ctor) (E.map (trNf s₀)) i
          (ks.map trCF)) ()
  | [], i, s₀, s', u, hs, _, _, _, _, _, _, h => by
    unfold InLean.classFieldsAgree at h
    obtain ⟨-, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by unfold ConLeche.classFieldsAgree; exact Runs.pure _⟩
  | .ordinary :: ks, i, s₀, s', u, hs, hfo, hMs, hFr, hfv, hlen, hE, h => by
    unfold InLean.classFieldsAgree at h
    simp only [List.map_cons, trCF]
    unfold ConLeche.classFieldsAgree
    exact classFieldsAgreeI_run hO ks (i + 1) hs hfo hMs hFr hfv
      (by simp only [List.length_cons] at hlen; omega) hE h
  | .recursive t tele :: ks, i, s₀, s', u, hs, hfo, hMs, hFr, hfv, hlen, hE, h => by
    unfold InLean.classFieldsAgree at h
    simp only [List.map_cons, trCF]
    unfold ConLeche.classFieldsAgree
    simp only [List.length_cons] at hlen
    have hi : i < fvs.length := by omega
    have hget : fvs.getD i default = fvs[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    have hgetC : (TrSL s₀ fvs).getD i default = TrS s₀ fvs[i] := by
      rw [List.getD_eq_getElem?_getD, TrSL, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
    rw [hget] at h
    rw [hgetC]
    obtain ⟨hxo, j, ty, hxt⟩ := hfv _ (List.getElem_mem hi)
    obtain ⟨w, s₁, h1, hA⟩ := bind_run h
    obtain ⟨rfl, hwo, hwt, -⟩ := fvarTypeDI_run hs hxo hxt h1
    obtain ⟨q, s₂, h2, h⟩ := bind_run hA
    obtain ⟨hsp, rfl⟩ := unwrapOr_run h2
    obtain ⟨teleB, leaf⟩ := q
    obtain ⟨hsp1, hsp2⟩ := stripPis_TrS tele w hwo
    obtain ⟨htbo, hlo⟩ := hsp1 teleB leaf hsp
    rw [hxt]
    simp only [ConLeche.Expr.fvarTypeD]
    rw [← hwt, hsp2, hsp]
    simp only [Option.map_some, ConLeche.unwrapOr]
    have hM := hMs t
    rw [Runs.pure_bind_eq]
    simp only [getD_map_trTM, ← classLeafAt_tr]
    cases hcl : InLean.classLeafAt (Ms.getD t default) leaf with
    | false =>
      simp only [hcl] at h
      obtain ⟨_, _, h3, -⟩ := bind_run h; exact (throw_run h3).elim
    | true =>
      simp only [hcl, ↓reduceIte] at h
      obtain ⟨_, s₃, h3, h⟩ := bind_run h
      obtain ⟨hs₃, ht₃, hN⟩ := classNodesAgreeI_run hO E hs hfo hM (hFr t) htbo hlo hfv.okSL
        hfv.lbb hE h3
      have hfv₃ := hfv.mono ht₃
      obtain ⟨hs', ht', hR⟩ := classFieldsAgreeI_run hO ks (i + 1) hs₃ (okSL_of_tabLe ht₃ hfo)
        (fun t' => (OkTMN.mono ht₃ (hMs t')).1)
        (fun t' => by
          rw [TrSL_of_tabLe ht₃ (hMs t').2.2.1, TrSL_of_tabLe ht₃ hfo]; exact hFr t')
        hfv₃.1 (by omega) (fun e he => (OkNf.mono ht₃ (hE e he)).1) h
      rw [TrSL_of_tabLe ht₃ hfo, hfv₃.2, map_trNf_mono ht₃ hE,
        map_trTM_mono ht₃ (Ms := Ms) ?_] at hR
      · refine ⟨hs', ht₃.trans ht', ?_⟩
        simp only [↓reduceIte]
        exact Runs.bind hN hR
      · intro M hM'
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hM'
        have := hMs k
        rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at this

/-! ## One constructor of a class -/

/-- A class's constructor at the class's levels (`targetCtorAt`), read. -/
theorem targetCtorAtI_run {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}
    {s₀ s' : InLean.CState} {M : InLean.TargetMajor} {c : Lean.ConstantVal} {r : Lean.Expr}
    (hs : CSOKI mode eager env s₀) (hlv : M.lvls.all okLv = true) (hc : okC c.type = true)
    (h : InLean.targetCtorAt M c s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' r = true ∧
      TrS s' r = ConLeche.targetCtorAt (trTM s₀ M) (trCV c) := by
  unfold InLean.targetCtorAt at h
  unfold ConLeche.targetCtorAt
  simp only [trTM]
  cases hm : M.member with
  | some t =>
    rw [hm] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, OkS_of_okC s₀ hc, by rw [TrS_of_okC _ hc]; rfl⟩
  | none =>
    rw [hm] at h
    obtain ⟨hs', ht', hok, htr⟩ := tripleI_iff_run.1
      (instLevelParamsM_specI hs (OkS_of_okC s₀ hc) (fvarS_of_okC hc) hlv) r s' h
    refine ⟨hs', ht', hok, ?_⟩
    rw [htr, TrS_of_okC _ hc]
    rfl

theorem classFieldsOf_length {p : InLean.BlockShape} {ctor : Lean.Name} {ihs : List (Nat × Nat)} :
    ∀ (fvs : List Lean.Expr) (i : Nat) {s₀ s' : InLean.CState} {v : List InLean.ClassField},
      InLean.classFieldsOf p ctor ihs i fvs s₀ = .ok (v, s') → v.length = fvs.length
  | [], i, s₀, s', v, h => by
    unfold InLean.classFieldsOf at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    rfl
  | f :: fs, i, s₀, s', v, h => by
    unfold InLean.classFieldsOf at h
    obtain ⟨w, s₁, -, h⟩ := bind_run h
    simp only at h
    have hrest : ∀ {α : Type} (x : InLean.CheckCM InLean.ClassField) {t : InLean.CState},
        (x >>= fun k' => do let ks' ← InLean.classFieldsOf p ctor ihs (i + 1) fs; pure (k' :: ks'))
          t = .ok (v, s') → v.length = (f :: fs).length := by
      intro _ x t h
      obtain ⟨k, s₂, -, h⟩ := bind_run h
      obtain ⟨ks, s₃, h3, h⟩ := bind_run h
      obtain ⟨rfl, rfl⟩ := pure_run h
      simp only [List.length_cons, classFieldsOf_length fs (i + 1) h3]
    revert h
    generalize InLean.nestOcc p.memberNames 0 0 w = b
    generalize List.filter (fun x => x.fst == i) ihs = l
    intro h
    cases b <;> rcases l with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> (try simp only at h) <;>
      first | exact hrest (α := Unit) _ h | exact (throw_run h).elim

/-- A class's constructor, read at a state. -/
@[expose] def trCC (s : InLean.CState) (x : InLean.ClassCtor) : ConLeche.ClassCtor :=
  ⟨trCV x.cv, x.nF, x.kinds.map trCF, TrS s x.tyD, TrS s x.tyN⟩

/-- A class's constructor has readings. -/
@[expose] def OkCC (s : InLean.CState) (x : InLean.ClassCtor) : Prop :=
  okC x.cv.type = true ∧ OkS s x.tyD = true ∧ OkS s x.tyN = true

theorem OkCC.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {x : InLean.ClassCtor}
    (hx : OkCC s₀ x) : OkCC s₁ x ∧ trCC s₁ x = trCC s₀ x := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨⟨h1, okS_of_tabLe h h2, okS_of_tabLe h h3⟩, ?_⟩
  unfold trCC
  rw [TrS_of_tabLe h h2, TrS_of_tabLe h h3]

/-- A class's facts the constructor stage reads: its entries closed, its
parameters closed, its constructors' types closed. -/
@[expose] def ClassOk (s : InLean.CState) (M : InLean.TargetMajor) : Prop :=
  OkTMN s M ∧ (∀ e ∈ M.nfs, (TrS s e.ty).looseBVarsBounded 0 = true) ∧
    (∀ a ∈ M.ds, (TrS s a).looseBVarsBounded 0 = true) ∧ ∀ c ∈ M.ctors, okC c.1.type = true

theorem ClassOk.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {M : InLean.TargetMajor}
    (hM : ClassOk s₀ M) : ClassOk s₁ M := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  refine ⟨(OkTMN.mono h h1).1, fun e he => ?_, fun a ha => ?_, h4⟩
  · rw [TrS_of_tabLe h (h1.2.2.2 e he).2.2]; exact h2 e he
  · have hds := h1.2.1
    simp only [OkSL, List.all_eq_true] at hds
    rw [TrS_of_tabLe h (hds a ha)]
    exact h3 a ha

theorem classOk_default (s : InLean.CState) : ClassOk s default := by
  refine ⟨okTMN_default s, ?_, ?_, ?_⟩ <;> intro _ h <;> cases h

theorem filter_ctor_trNf (s : InLean.CState) (nfs : List InLean.NestCtorNf) (n : Lean.Name) :
    (nfs.map (trNf s)).filter (·.ctor == toName n) = (nfs.filter (·.ctor == n)).map (trNf s) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  simp [trNf, toName_beq]

/-- **One constructor of a class** (`classCtorOf`): InLean's reading is
master's on the readings, the constructor read as `trCC`. -/
theorem classCtorOfI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {p : InLean.BlockShape} {formerTys : List Lean.Expr} {rd : InLean.ClassRead}
    {Ms : List InLean.TargetMajor} {c : Nat} {ctor : Lean.ConstantVal × Nat}
    {sr s₀ s' : InLean.CState} {x : InLean.ClassCtor} (hs : CSOKI .verified false L s₀)
    (hfo : OkSL s₀ formerTys = true) (hMs : ∀ t, ClassOk s₀ (Ms.getD t default))
    (hFr : ∀ t, FrameOk (TrSL s₀ (Ms.getD t default).pfvs) (TrSL s₀ formerTys))
    (hct : okC ctor.1.type = true)
    (h : InLean.classCtorOf (sharedOpsC .verified fe) fe p formerTys rd Ms c ctor s₀ = .ok (x, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ OkCC s' x ∧
      Runs (ConLeche.classCtorOf (ConLeche.fueledOpsM .verified) L (trShape p) (TrSL s₀ formerTys)
        (trCR sr rd) (Ms.map (trTM s₀)) c (trCtor ctor)) (trCC s' x) := by
  unfold InLean.classCtorOf at h
  unfold ConLeche.classCtorOf
  obtain ⟨hMc, hnfc, hdsc, -⟩ := hMs c
  simp only [getD_map_trTM, trCtor, trCV_name]
  simp only [trTM]
  rw [filter_ctor_trNf]
  obtain ⟨e0, s₁, h1, h⟩ := bind_run h
  obtain ⟨he0, hst⟩ := unwrapOr_run h1
  subst s₁
  have he0m : e0 ∈ (Ms.getD c default).nfs := by
    have := List.mem_of_mem_head? he0
    exact (List.mem_filter.1 this).1
  obtain ⟨-, -, he0o⟩ := hMc.2.2.2 e0 he0m
  have he0c := hnfc e0 he0m
  rw [List.head?_map, he0, Option.map_some]
  simp only [ConLeche.unwrapOr]
  rw [Runs.pure_bind_eq]
  obtain ⟨q, s₂, h2, h⟩ := bind_run h
  obtain ⟨hst, hq⟩ := classMinorSlotI_run (s := sr) h2
  subst s₂
  obtain ⟨_, ihs⟩ := q
  rw [Runs.bind_eq _ hq]
  simp only
  obtain ⟨r, s₃, h3, h⟩ := bind_run h
  unfold InLean.openPisAtFvars at h3
  obtain ⟨hs₃, ht₃, hop⟩ := openPisAtFvarsI_run ctor.2 (p.nP + p.k) hs he0o he0c h3
  obtain ⟨q, s₄, h4, h⟩ := bind_run h
  obtain ⟨hr, hst⟩ := unwrapOr_run h4
  subst s₄
  obtain ⟨fvs, b⟩ := q
  obtain ⟨hfvo, hbo, hopC⟩ := hop fvs b hr
  simp only [trNf]
  rw [trShape_nP, trShape_k, hopC]
  rw [Runs.pure_bind_eq]
  simp only
  have hfv : FvsOk s₃ fvs := by
    intro f hf
    obtain ⟨j, hj⟩ := List.getElem_of_mem hf
    obtain ⟨hjl, rfl⟩ := hj
    refine ⟨okS_getElem? hfvo (List.getElem?_eq_getElem hjl), ?_⟩
    obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ hopC j (TrS s₃ fvs[j])
      (by simp [TrSL, List.getElem?_eq_getElem hjl])
    exact ⟨_, ty, hty⟩
  obtain ⟨kinds, s₅, h5, h⟩ := bind_run h
  have hklen := classFieldsOf_length fvs 0 h5
  obtain ⟨hst, hK⟩ := classFieldsOfI_run fvs 0 hs₃ hfv h5
  subst s₅
  rw [Runs.bind_eq _ hK]
  obtain ⟨_, s₆, h6, h⟩ := bind_run h
  have hMs₃ : ∀ t, ClassOk s₃ (Ms.getD t default) := fun t => (hMs t).mono ht₃
  obtain ⟨hs₆, ht₆, hA⟩ := classFieldsAgreeI_run hO kinds 0 hs₃ (okSL_of_tabLe ht₃ hfo)
    (fun t => (hMs₃ t).1)
    (fun t => by
      rw [TrSL_of_tabLe ht₃ (hMs t).1.2.2.1, TrSL_of_tabLe ht₃ hfo]; exact hFr t)
    hfv (by omega) (fun e he => (OkNf.mono ht₃ (hMc.2.2.2 e (List.mem_filter.1 he).1)).1) h6
  rw [TrSL_of_tabLe ht₃ hfo, map_trTM_mono ht₃ (fun M hM => ?_),
    map_trNf_mono ht₃ (fun e he => hMc.2.2.2 e (List.mem_filter.1 he).1)] at hA
  rotate_left
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hM
    have := (hMs k).1
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at this
  simp only at h
  obtain ⟨ty, s₇, h7, h⟩ := bind_run h
  have hMc₆ := (OkTMN.mono (ht₃.trans ht₆) hMc)
  obtain ⟨hs₇, ht₇, htyo, htyt⟩ := targetCtorAtI_run hs₆ hMc.1 hct h7
  obtain ⟨tyD, s₈, h8, h⟩ := bind_run h
  obtain ⟨hpw, hst⟩ := unwrapOr_run h8
  subst s₈
  obtain ⟨rfl, rfl⟩ := pure_run h
  have ht₀₇ := ht₃.trans (ht₆.trans ht₇)
  have hds₇ : OkSL s₇ (Ms.getD c default).ds = true := okSL_of_tabLe ht₀₇ hMc.2.1
  obtain ⟨htDo, htDC⟩ := instPisWithI_tr _ _ htyo hds₇
    (fun a ha => by
      have hds := hMc.2.1
      simp only [OkSL, List.all_eq_true] at hds
      rw [TrS_of_tabLe ht₀₇ (hds a ha)]; exact hdsc a ha) hpw
  rw [TrSL_of_tabLe ht₀₇ hMc.2.1, htyt, hMc₆.2] at htDC
  refine ⟨hs₇, ht₀₇, ⟨hct, htDo, okS_of_tabLe ht₀₇ he0o⟩, ?_⟩
  refine Runs.bind hA ?_
  simp only [trTM] at htDC
  rw [htDC]
  simp only
  rw [Runs.pure_bind_eq]
  unfold trCC
  rw [TrS_of_tabLe ht₀₇ he0o]
  exact Runs.pure _

/-! ## Every constructor of every class -/

theorem map_trCC_mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) :
    ∀ {xs : List InLean.ClassCtor}, (∀ x ∈ xs, OkCC s₀ x) → xs.map (trCC s₁) = xs.map (trCC s₀)
  | [], _ => rfl
  | x :: xs, hx => by
    rw [List.map_cons, List.map_cons, (OkCC.mono h (hx x List.mem_cons_self)).2,
      map_trCC_mono h (fun y hy => hx y (List.mem_cons_of_mem _ hy))]

theorem okTMN_all_of_getD {s : InLean.CState} {Ms : List InLean.TargetMajor}
    (h : ∀ t, ClassOk s (Ms.getD t default)) : ∀ M ∈ Ms, OkTMN s M := by
  intro M hM
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hM
  have := (h k).1
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at this

/-- **Every constructor of class `c`** (`classCtorsOf`). -/
theorem classCtorsOfI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {p : InLean.BlockShape} {formerTys : List Lean.Expr} {rd : InLean.ClassRead}
    {Ms : List InLean.TargetMajor} {c : Nat} {sr : InLean.CState} :
    ∀ (ctors : List (Lean.ConstantVal × Nat)) {s₀ s' : InLean.CState} {xs : List InLean.ClassCtor},
      CSOKI .verified false L s₀ → OkSL s₀ formerTys = true →
      (∀ t, ClassOk s₀ (Ms.getD t default)) →
      (∀ t, FrameOk (TrSL s₀ (Ms.getD t default).pfvs) (TrSL s₀ formerTys)) →
      (∀ ctor ∈ ctors, okC ctor.1.type = true) →
      InLean.classCtorsOf (sharedOpsC .verified fe) fe p formerTys rd Ms c ctors s₀ = .ok (xs, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ (∀ x ∈ xs, OkCC s' x) ∧
        Runs (ConLeche.classCtorsOf (ConLeche.fueledOpsM .verified) L (trShape p) (TrSL s₀ formerTys)
          (trCR sr rd) (Ms.map (trTM s₀)) c (ctors.map trCtor)) (xs.map (trCC s'))
  | [], s₀, s', xs, hs, _, _, _, _, h => by
    unfold InLean.classCtorsOf at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, (fun _ h => by cases h), by unfold ConLeche.classCtorsOf; exact Runs.pure _⟩
  | ctor :: cs, s₀, s', xs, hs, hfo, hMs, hFr, hct, h => by
    unfold InLean.classCtorsOf at h
    unfold ConLeche.classCtorsOf
    obtain ⟨x, s₁, h1, h⟩ := bind_run h
    obtain ⟨xs', s₂, h2, h⟩ := bind_run h
    obtain ⟨rfl, rfl⟩ := pure_run h
    obtain ⟨hs₁, ht₁, hx, hR1⟩ := classCtorOfI_run (sr := sr) hO hs hfo hMs hFr
      (hct ctor List.mem_cons_self) h1
    have hMs₁ : ∀ t, ClassOk s₁ (Ms.getD t default) := fun t => (hMs t).mono ht₁
    obtain ⟨hs₂, ht₂, hxs, hR2⟩ := classCtorsOfI_run hO cs hs₁ (okSL_of_tabLe ht₁ hfo) hMs₁
      (fun t => by
        rw [TrSL_of_tabLe ht₁ (hMs t).1.2.2.1, TrSL_of_tabLe ht₁ hfo]; exact hFr t)
      (fun c' hc' => hct c' (List.mem_cons_of_mem _ hc')) h2
    rw [TrSL_of_tabLe ht₁ hfo, map_trTM_mono ht₁ (okTMN_all_of_getD hMs)] at hR2
    have hoc := OkCC.mono ht₂ hx
    refine ⟨hs₂, ht₁.trans ht₂, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hoc.1
      · exact hxs y hy
    · rw [List.map_cons, List.map_cons, hoc.2]
      exact Runs.bind hR1 (Runs.bind hR2 (Runs.pure _))

/-- **Every class's constructors** (`classesCtors`), from class `c` on. -/
theorem classesCtorsI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {p : InLean.BlockShape} {formerTys : List Lean.Expr} {rd : InLean.ClassRead}
    {Ms : List InLean.TargetMajor} {sr : InLean.CState} :
    ∀ (rest : List InLean.TargetMajor) (c : Nat) {s₀ s' : InLean.CState}
      {xss : List (List InLean.ClassCtor)},
      CSOKI .verified false L s₀ → OkSL s₀ formerTys = true →
      (∀ t, ClassOk s₀ (Ms.getD t default)) →
      (∀ t, FrameOk (TrSL s₀ (Ms.getD t default).pfvs) (TrSL s₀ formerTys)) →
      (∀ M ∈ rest, ClassOk s₀ M) →
      InLean.classesCtors (sharedOpsC .verified fe) fe p formerTys rd Ms c rest s₀ = .ok (xss, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ (∀ xs ∈ xss, ∀ x ∈ xs, OkCC s' x) ∧
        Runs (ConLeche.classesCtors (ConLeche.fueledOpsM .verified) L (trShape p) (TrSL s₀ formerTys)
          (trCR sr rd) (Ms.map (trTM s₀)) c (rest.map (trTM s₀))) (xss.map (·.map (trCC s')))
  | [], c, s₀, s', xss, hs, _, _, _, _, h => by
    unfold InLean.classesCtors at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, (fun _ h => by cases h), by unfold ConLeche.classesCtors; exact Runs.pure _⟩
  | M :: rest, c, s₀, s', xss, hs, hfo, hMs, hFr, hrest, h => by
    unfold InLean.classesCtors at h
    simp only [List.map_cons]
    unfold ConLeche.classesCtors
    obtain ⟨xs, s₁, h1, h⟩ := bind_run h
    obtain ⟨xss', s₂, h2, h⟩ := bind_run h
    obtain ⟨rfl, rfl⟩ := pure_run h
    have hM := hrest M List.mem_cons_self
    obtain ⟨hs₁, ht₁, hxs, hR1⟩ := classCtorsOfI_run (sr := sr) hO M.ctors hs hfo hMs hFr
      hM.2.2.2 h1
    have hMs₁ : ∀ t, ClassOk s₁ (Ms.getD t default) := fun t => (hMs t).mono ht₁
    obtain ⟨hs₂, ht₂, hxss, hR2⟩ := classesCtorsI_run hO rest (c + 1) hs₁ (okSL_of_tabLe ht₁ hfo)
      hMs₁
      (fun t => by
        rw [TrSL_of_tabLe ht₁ (hMs t).1.2.2.1, TrSL_of_tabLe ht₁ hfo]; exact hFr t)
      (fun M' hM' => (hrest M' (List.mem_cons_of_mem _ hM')).mono ht₁) h2
    rw [TrSL_of_tabLe ht₁ hfo, map_trTM_mono ht₁ (okTMN_all_of_getD hMs),
      map_trTM_mono ht₁ (fun M' hM' => (hrest M' (List.mem_cons_of_mem _ hM')).1)] at hR2
    refine ⟨hs₂, ht₁.trans ht₂, ?_, ?_⟩
    · intro ys hys
      rcases List.mem_cons.1 hys with rfl | hys
      · exact fun x hx => (OkCC.mono ht₂ (hxs x hx)).1
      · exact hxss ys hys
    · rw [List.map_cons, map_trCC_mono ht₂ hxs]
      exact Runs.bind hR1 (Runs.bind hR2 (Runs.pure _))

/-! ## The generator's record and its `OptionT` steps -/

/-- The generator's record, read at a state. -/
@[expose] def trCG (s : InLean.CState) (g : InLean.ClassGen) : ConLeche.ClassGen :=
  ⟨g.nP, TrSL s g.params, g.cls.map (trTM s), TrSL s g.formerTys, g.slots.map (trSlot s),
    g.ctors.map (·.map (trCC s)), trL g.elim, TrSL s g.pre⟩

theorem optT_bind_run {α β : Type} {x : OptionT InLean.CheckCM α} {f : α → OptionT InLean.CheckCM β}
    {s₀ s' : InLean.CState} {r : Option β} (h : (x >>= f).run s₀ = .ok (r, s')) :
    ∃ a s₁, x.run s₀ = .ok (a, s₁) ∧
      match a with
      | none => r = none ∧ s' = s₁
      | some a => (f a).run s₁ = .ok (r, s') := by
  simp only [OptionT.run, bind, OptionT.bind, OptionT.mk] at h
  obtain ⟨a, s₁, h1, h⟩ := bind_run h
  refine ⟨a, s₁, h1, ?_⟩
  cases a with
  | none => obtain ⟨rfl, rfl⟩ := pure_run h; exact ⟨rfl, rfl⟩
  | some a => exact h

theorem optT_pure_run {α : Type} {a : α} {s₀ s' : InLean.CState} {r : Option α}
    (h : (pure a : OptionT InLean.CheckCM α).run s₀ = .ok (r, s')) : r = some a ∧ s' = s₀ := by
  simp only [OptionT.run, pure, OptionT.pure, OptionT.mk] at h
  obtain ⟨rfl, rfl⟩ := pure_run h
  exact ⟨rfl, rfl⟩

theorem liftOpt_run {α : Type} {o : Option α} {s₀ s' : InLean.CState} {r : Option α}
    (h : (InLean.liftOpt o).run s₀ = .ok (r, s')) : r = o ∧ s' = s₀ := by
  simp only [InLean.liftOpt, OptionT.run, OptionT.mk] at h
  obtain ⟨rfl, rfl⟩ := pure_run h
  exact ⟨rfl, rfl⟩

theorem liftM_run {α : Type} {x : InLean.CheckCM α} {s₀ s' : InLean.CState} {r : Option α}
    (h : (liftM x : OptionT InLean.CheckCM α).run s₀ = .ok (r, s')) :
    ∃ a, r = some a ∧ x s₀ = .ok (a, s') := by
  simp only [liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.run, OptionT.mk] at h
  obtain ⟨a, s₁, h1, h⟩ := bind_run h
  obtain ⟨rfl, rfl⟩ := pure_run h
  exact ⟨a, rfl, h1⟩

/-- `instPisWith` keeps a closed term closed at closed arguments. -/
theorem lbb_instPisWith :
    ∀ (as : List ConLeche.Expr) (e : ConLeche.Expr) {r : ConLeche.Expr},
      (∀ a ∈ as, a.looseBVarsBounded 0 = true) → e.looseBVarsBounded 0 = true →
      ConLeche.instPisWith as e = some r → r.looseBVarsBounded 0 = true
  | [], e, r, _, he, h => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at h; subst h; exact he
  | a :: as, .forallE d b, r, ha, he, h => by
    simp only [ConLeche.instPisWith] at h
    simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at he
    exact lbb_instPisWith as _ (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (lbb_instantiate1 (ha a List.mem_cons_self) he.2) h
  | _ :: _, .bvar _, _, _, _, h | _ :: _, .fvar _ _, _, _, _, h | _ :: _, .sort _, _, _, _, h
  | _ :: _, .const _ _, _, _, _, h | _ :: _, .app _ _, _, _, _, h | _ :: _, .lam _ _, _, _, _, h
  | _ :: _, .letE _ _ _, _, _, _, h | _ :: _, .lit _, _, _, _, h | _ :: _, .proj _ _ _, _, _, _, h => by
    simp [ConLeche.instPisWith] at h

/-- Opened variables read as variables (`openPisAtFvars_index` on the reading). -/
theorem fvsOk_of_open {s : InLean.CState} {n i : Nat} {e : ConLeche.Expr} {fvs : List Lean.Expr}
    {b : ConLeche.Expr} (ho : OkSL s fvs = true)
    (h : ConLeche.openPisAtFvars n e i = some (TrSL s fvs, b)) : FvsOk s fvs := by
  intro f hf
  obtain ⟨j, hjl, rfl⟩ := List.getElem_of_mem hf
  refine ⟨okS_getElem? ho (List.getElem?_eq_getElem hjl), ?_⟩
  obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ h j (TrS s fvs[j])
    (by simp [TrSL, List.getElem?_eq_getElem hjl])
  exact ⟨_, ty, hty⟩

/-- **A class's index telescope and major domain** (`ClassGen.major`), read. -/
theorem majorI_run {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}
    {s₀ s' : InLean.CState} {g : InLean.ClassGen} {c d : Nat}
    {r : Option (List Lean.Expr × Lean.Expr)} (hs : CSOKI mode eager env s₀)
    (hM : ClassOk s₀ (g.cls.getD c default)) (hft : OkS s₀ (g.formerTys.getD c default) = true)
    (hftc : (TrS s₀ (g.formerTys.getD c default)).looseBVarsBounded 0 = true)
    (hc : c < g.formerTys.length) (h : (g.major c d).run s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ ifs maj, r = some (ifs, maj) →
      FvsOk s' ifs ∧ OkS s' maj = true ∧
        (trCG s₀ g).major c d = some (TrSL s' ifs, TrS s' maj) := by
  obtain ⟨hMn, -, hdsc, -⟩ := hM
  unfold InLean.ClassGen.major at h
  unfold ConLeche.ClassGen.major
  simp only [trCG, getD_map_trTM]
  have hgf : (TrSL s₀ g.formerTys).getD c default = TrS s₀ (g.formerTys.getD c default) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, TrSL, List.getElem?_map]
    rw [List.getElem?_eq_getElem hc]; rfl
  rw [hgf]
  simp only at h
  obtain ⟨o, s₁, h1, h⟩ := optT_bind_run h
  obtain ⟨rfl, hst⟩ := liftOpt_run h1
  subst s₁
  cases hpw : InLean.instPisWith (g.cls.getD c default).ds (g.formerTys.getD c default) with
  | none =>
    rw [hpw] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs, TabLe.refl _, fun _ _ h => by cases h⟩
  | some ty =>
    rw [hpw] at h
    simp only at h
    obtain ⟨htyo, htyC⟩ := instPisWithI_tr _ _ hft hMn.2.1 hdsc hpw
    have htyc : (TrS s₀ ty).looseBVarsBounded 0 = true :=
      lbb_instPisWith _ _ (fun a ha => by
        simp only [TrSL, List.mem_map] at ha
        obtain ⟨a', ha', rfl⟩ := ha
        exact hdsc a' ha') hftc htyC
    simp only [trTM]
    rw [htyC]
    simp only [Option.bind_eq_bind, Option.bind_some]
    obtain ⟨o, s₂, h2, h⟩ := optT_bind_run h
    simp only [InLean.openPisO, OptionT.run, OptionT.mk] at h2
    unfold InLean.openPisAtFvars at h2
    obtain ⟨hs₂, ht₂, hop⟩ := openPisAtFvarsI_run _ d hs htyo htyc h2
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hs₂, ht₂, fun _ _ h => by cases h⟩
    | some q =>
      obtain ⟨ifs, b⟩ := q
      simp only at h
      obtain ⟨rfl, rfl⟩ := optT_pure_run h
      obtain ⟨hifo, -, hopC⟩ := hop ifs b rfl
      refine ⟨hs₂, ht₂, fun ifs' maj h => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hds₂ := okSL_of_tabLe ht₂ hMn.2.1
      refine ⟨fvsOk_of_open hifo hopC, ?_, ?_⟩
      · unfold InLean.mkAppL
        rw [OkS_mkAppN, OkS_const, hMn.1, OkSL]
        simp only [OkSL, List.all_append, Bool.and_eq_true] at hds₂ hifo ⊢
        exact ⟨trivial, hds₂, hifo⟩
      · rw [hopC]
        simp only [Option.bind_some, Option.pure_def]
        rw [TrS_mkAppL_const, TrSL_append, TrSL_of_tabLe ht₂ hMn.2.1]

/-- **A recursive field's inductive hypothesis parts** (`ClassGen.ihParts`), read. -/
theorem ihPartsI_run {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}
    {s₀ s' : InLean.CState} {g : InLean.ClassGen} {t tele d : Nat} {w : Lean.Expr}
    {r : Option (List Lean.Expr × List Lean.Expr)} (hs : CSOKI mode eager env s₀)
    (hw : OkS s₀ w = true) (hwc : (TrS s₀ w).looseBVarsBounded 0 = true)
    (h : (g.ihParts t tele w d).run s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ xs idx, r = some (xs, idx) →
      FvsOk s' xs ∧ OkSL s' idx = true ∧
        (trCG sg g).ihParts t tele (TrS s₀ w) d = some (TrSL s' xs, TrSL s' idx) := by
  unfold InLean.ClassGen.ihParts at h
  unfold ConLeche.ClassGen.ihParts
  obtain ⟨o, s₁, h1, h⟩ := optT_bind_run h
  simp only [InLean.openPisO, OptionT.run, OptionT.mk] at h1
  unfold InLean.openPisAtFvars at h1
  obtain ⟨hs₁, ht₁, hop⟩ := openPisAtFvarsI_run _ d hs hw hwc h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs₁, ht₁, fun _ _ h => by cases h⟩
  | some q =>
    obtain ⟨xs, leaf⟩ := q
    simp only at h
    obtain ⟨rfl, hst⟩ := optT_pure_run h
    subst s'
    obtain ⟨hxo, hlo, hopC⟩ := hop xs leaf rfl
    refine ⟨hs₁, ht₁, fun xs' idx h => ?_⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fvsOk_of_open hxo hopC, OkSL_drop s₁ (OkSL_appArgs s₁ hlo) _, ?_⟩
    rw [hopC]
    simp only [Option.pure_def, trCG, getD_map_trTM, trTM, TrSL_drop,
      TrSL_appArgs]
    rfl

/-- The binders of opened variables (`mapM fvarTypeD` in `OptionT`), read. -/
theorem mapM_binder_run {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) :
    ∀ (xs : List Lean.Expr) {r : Option (List Lean.Expr)} {s' : InLean.CState}, FvsOk s₀ xs →
      (xs.mapM fun x => (liftM (InLean.fvarTypeD x) : OptionT InLean.CheckCM Lean.Expr)).run s₀ =
        .ok (r, s') →
      s' = s₀ ∧ ∃ bs, r = some bs ∧ OkSL s₀ bs = true ∧
        TrSL s₀ bs = (TrSL s₀ xs).map ConLeche.Expr.fvarTypeD
  | [], r, s', _, h => by
    rw [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := optT_pure_run h
    exact ⟨rfl, [], rfl, rfl, rfl⟩
  | x :: xs, r, s', hx, h => by
    rw [List.mapM_cons] at h
    obtain ⟨o, s₁, h1, h⟩ := optT_bind_run h
    obtain ⟨b, rfl, hfb⟩ := liftM_run h1
    obtain ⟨hxo, j, ty, hxt⟩ := hx x List.mem_cons_self
    obtain ⟨hst, hbo, hbt, -⟩ := fvarTypeDI_run hs hxo hxt hfb
    subst s₁
    simp only at h
    obtain ⟨o', s₂, h2, h⟩ := optT_bind_run h
    obtain ⟨hst, bs, rfl, hbso, hbst⟩ := mapM_binder_run hs xs
      (fun y hy => hx y (List.mem_cons_of_mem _ hy)) h2
    subst s₂
    simp only at h
    obtain ⟨rfl, rfl⟩ := optT_pure_run h
    refine ⟨rfl, b :: bs, rfl, by simp [OkSL_cons, hbo, hbso], ?_⟩
    rw [TrSL_cons, TrSL_cons, List.map_cons, hbt, hbst, hxt]
    rfl

/-- **A class's motive type** (`ClassGen.motiveTy`), read where InLean's
closing wrote no out-of-range marker. -/
theorem motiveTyI_run {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}
    {s₀ s' : InLean.CState} {g : InLean.ClassGen} {c d : Nat} {r : Option Lean.Expr}
    (hs : CSOKI mode eager env s₀)
    (hM : ClassOk s₀ (g.cls.getD c default)) (hft : OkS s₀ (g.formerTys.getD c default) = true)
    (hftc : (TrS s₀ (g.formerTys.getD c default)).looseBVarsBounded 0 = true)
    (hc : c < g.formerTys.length) (hel : okLv g.elim = true)
    (h : (g.motiveTy c d).run s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ ∀ e, r = some e → emvarS e = false →
      OkS s' e = true ∧ (trCG s₀ g).motiveTy c d = some (TrS s' e) := by
  unfold InLean.ClassGen.motiveTy at h
  unfold ConLeche.ClassGen.motiveTy
  obtain ⟨o, s₁, h1, h⟩ := optT_bind_run h
  obtain ⟨hs₁, ht₁, hmj⟩ := majorI_run hs hM hft hftc hc h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs₁, ht₁, fun _ h => by cases h⟩
  | some q =>
    obtain ⟨ifs, maj⟩ := q
    obtain ⟨hfv, hmo, hmC⟩ := hmj ifs maj rfl
    rw [hmC]
    simp only at h ⊢
    obtain ⟨o', s₂, h2, h⟩ := optT_bind_run h
    obtain ⟨hst, bs, rfl, hbso, hbst⟩ := mapM_binder_run hs₁ ifs hfv h2
    subst s₂
    simp only at h
    obtain ⟨rfl, hst⟩ := optT_pure_run h
    subst s'
    refine ⟨hs₁, ht₁, fun e he hem => ?_⟩
    simp only [Option.some.injEq] at he
    subst he
    have hbo : OkS s₁ (Lean.Expr.forallE .anonymous maj (.sort g.elim) .default) = true := by
      simp only [OkS_forallE, hmo, OkS_sort, hel, Bool.and_self]
    obtain ⟨ho, ht⟩ := closeTelescope_tr s₁ bs d _ hbso hbo hem
    refine ⟨ho, ?_⟩
    rw [ht, hbst]
    rfl


end InLeanProof
