module

public import InLeanProof.PassNestPos
public import InLeanProof.NestDepth
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Cached.NestPosC
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.Cached.IndPositivityC
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Inductives.NestCallSyn
/- `Expr.isFVar`'s body (`nestResHead_tr`). -/
import all Lean.Expr

/-!
# O7-positivity: the positivity walk's frames against master's (task #451, lane O7-positivity)

The walk's frame-level steps, each master's on the readings of
`PassNestPos0.lean`, functional (`bind_run`, `pure_run`) as O7's:

* `structUsedLater_tr`: U4's occurrence test, read.
* `nestContainer_ctorOk`, `nestGroupCtors_ctorOk`: a container's
  constructors are stored constants (closed, in range).
* `nestCtorsI_run`: a frame's constructors through the recursion.
* `nestFrameI_run`, `nestContNewI_run`, `nestContKeyI_run`, `nestContI_run`:
  a container instantiation's frame, met, cached or new.
* `nestPosI_run`: the walk at every fuel (induction on the fuel), and
  `nestRootI_run`: the root frame at each constructor's own fuel
  (`whnfWalkFuel_TrS`).
-/

public section

namespace InLeanProof

open Lean InLean ConLeche.Cached

/-! ## U4's test -/

/-- InLean's `peelPis` through the reading: master's `stripPis`' rest. -/
theorem peelPis_tr (s : InLean.CState) : ∀ (n : Nat) (t : Lean.Expr), OkS s t = true →
    (∀ r, InLean.peelPis n t = some r → OkS s r = true) ∧
      (ConLeche.Expr.stripPis n (TrS s t)).map (·.2) = (InLean.peelPis n t).map (TrS s)
  | 0, t, h => by
    refine ⟨fun r hr => ?_, by simp [ConLeche.Expr.stripPis, InLean.peelPis]⟩
    simp only [InLean.peelPis, Option.some.injEq] at hr
    exact hr ▸ h
  | n + 1, .forallE _ _ b _, h => by
    simp only [OkS_forallE, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := peelPis_tr s n b h.2
    refine ⟨fun r hr => h1 r hr, ?_⟩
    rw [TrS_forallE, ConLeche.Expr.stripPis, InLean.peelPis, ← h2, Option.map_map]
    rfl
  | n + 1, .mdata _ e, h => by
    rw [OkS_mdata] at h
    rw [TrS_mdata, InLean.peelPis]
    exact peelPis_tr s (n + 1) e h
  | n + 1, .fvar id, _ => by
    refine ⟨fun r hr => by simp [InLean.peelPis] at hr, ?_⟩
    simp only [InLean.peelPis, TrS, trE]
    cases hf : FVarTable.trans (tableOf s) id with
    | none => rfl
    | some c => obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf; rfl
  | n + 1, .bvar _, _ | n + 1, .mvar _, _ | n + 1, .sort _, _ | n + 1, .const .., _
  | n + 1, .app .., _ | n + 1, .lam .., _ | n + 1, .letE .., _ | n + 1, .lit _, _
  | n + 1, .proj .., _ => ⟨fun r hr => by simp [InLean.peelPis] at hr, rfl⟩

/-- **U4's occurrence test** (`structUsedLater`), read. -/
theorem structUsedLater_tr {s : InLean.CState} {t : Lean.Expr} (h : OkS s t = true) (nP j : Nat) :
    InLean.structUsedLater t nP j = ConLeche.Cached.structUsedLaterC (TrS s t) nP j := by
  obtain ⟨h1, h2⟩ := peelPis_tr s (nP + j + 1) t h
  unfold InLean.structUsedLater ConLeche.Cached.structUsedLaterC
  cases hp : InLean.peelPis (nP + j + 1) t with
  | none =>
    rw [hp] at h2
    cases hc : ConLeche.Expr.stripPis (nP + j + 1) (TrS s t) with
    | none => rfl
    | some p => rw [hc] at h2; cases h2
  | some r =>
    rw [hp] at h2
    cases hc : ConLeche.Expr.stripPis (nP + j + 1) (TrS s t) with
    | none => rw [hc] at h2; cases h2
    | some p =>
      rw [hc] at h2
      simp only [Option.map_some, Option.some.injEq] at h2
      simp only
      rw [h2, hasLooseBVarI_TrS (h1 r hp), ConLeche.Cached.hasLooseBVarBC_spec]

/-! ## The out-of-range marker of a closed telescope -/

theorem RangeOk_closeTelescopeFrom : ∀ (bs : List Lean.Expr) (i j : Nat) (body : Lean.Expr),
    (∀ b ∈ bs, Expr.RangeOk b) → Expr.RangeOk body →
      Expr.RangeOk (InLean.closeTelescopeFrom bs i j body)
  | [], _, _, _, _, hb => RangeOk_abstractDepthsFrom hb _ _ _
  | dom :: bs, i, j, body, hbs, hb => by
    simp only [InLean.closeTelescopeFrom, Expr.RangeOk]
    exact ⟨RangeOk_abstractDepthsFrom (hbs dom List.mem_cons_self) _ _ _,
      RangeOk_closeTelescopeFrom bs i (j + 1) body
        (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb⟩

theorem RangeOk_closeTelescope (bs : List Lean.Expr) (i : Nat) (body : Lean.Expr)
    (hbs : ∀ b ∈ bs, Expr.RangeOk b) (hb : Expr.RangeOk body) :
    Expr.RangeOk (InLean.closeTelescope bs i body) :=
  RangeOk_closeTelescopeFrom bs i 0 body hbs hb

/-- A closed telescope of readable parts the walk did not refuse has no
marker. -/
theorem emvarS_closeTelescope {s : InLean.CState} {bs : List Lean.Expr} {i : Nat}
    {body : Lean.Expr} (hbs : OkSL s bs = true) (hb : OkS s body = true)
    (hm : (InLean.closeTelescope bs i body).hasExprMVar = false) :
    emvarS (InLean.closeTelescope bs i body) = false := by
  rw [← Expr.hasExprMVar_eq (RangeOk_closeTelescope bs i body (fun b hb' => RangeOk_of_OkS
    (by simp only [OkSL, List.all_eq_true] at hbs; exact hbs b hb')) (RangeOk_of_OkS hb))]
  exact hm

/-! ## A container's constructors are stored constants -/

/-- A constructor record of a stored constant: its type closed, in range. -/
@[expose] def CtorOkI (c : Lean.ConstantVal × Nat) : Prop :=
  okC c.1.type = true ∧ (trC c.1.type).hasFvar = false ∧ (trC c.1.type).looseBVarsBounded 0 = true

theorem nestContainer_ctorOk {fe : InLean.FEnv} {L : ConLeche.Env} {s : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L)
    (hW : WalkRel fe L s ctx cctx) {C : Lean.Name} {q : Nat × List (Lean.ConstantVal × Nat)}
    (h : InLean.nestContainer ctx C = some q) : ∀ c ∈ q.2, CtorOkI c := by
  unfold InLean.nestContainer at h
  rw [hW.fe] at h
  split at h
  · rename_i cv caps _
    have hall : ∀ x ∈ caps.ctors.filterMap (fun n =>
        (fe.ctorView? n).bind fun (cv, nPc, nF, _) => InLean.nestCtorEntry C cv nPc nF),
        CtorOkI (x.1, x.2.2) := by
      intro x hx
      obtain ⟨n, -, hn⟩ := List.mem_filterMap.1 hx
      cases hv : fe.ctorView? n with
      | none => rw [hv] at hn; cases hn
      | some p =>
        obtain ⟨cv', nPc, nF⟩ := p
        rw [hv] at hn
        simp only [Option.bind_some] at hn
        have hx1 : x.1 = cv' := by
          unfold InLean.nestCtorEntry at hn
          split at hn
          · split at hn
            · split at hn
              · simp only [Option.some.injEq] at hn; rw [← hn]
              · cases hn
            · cases hn
          · cases hn
        obtain ⟨ccv, hcv, hL⟩ := ctorView_rel hJ.pres hv
        have he := hcv.eq_trCV
        subst he
        have hwf := hJ.wf.consts _ (ConLeche.Env.find?_mem hL)
        rw [hx1]
        exact ⟨(trC_of_toExprC hcv.2.2.2.2 hcv.2.2.2.1).1, hwf.1, hwf.2.2.2.1⟩
    simp only at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp
    · simp only [Option.some.injEq] at h
      subst h
      rename_i heq
      intro c hc
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
      exact hall x (by simpa [heq] using hx)
  · cases h

theorem nestGroupCtors_ctorOk {fe : InLean.FEnv} {L : ConLeche.Env} {s : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L)
    (hW : WalkRel fe L s ctx cctx) (nPc : Nat) :
    ∀ (cs : List Lean.Name) {s₀ s' : InLean.CState} {v : List (Lean.ConstantVal × Nat)},
      InLean.nestGroupCtors ctx nPc cs s₀ = .ok (v, s') → ∀ c ∈ v, CtorOkI c
  | [], s₀, s', v, h => by
    unfold InLean.nestGroupCtors at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    simp
  | c :: cs, s₀, s', v, h => by
    unfold InLean.nestGroupCtors at h
    obtain ⟨q, s₁, h1, h⟩ := bind_run h
    cases hq : InLean.nestContainer ctx c with
    | none => rw [hq] at h1; exact (throw_run h1).elim
    | some q' =>
    rw [hq] at h1
    obtain ⟨rfl, rfl⟩ := pure_run h1
    have hq' := nestContainer_ctorOk hJ hW hq
    obtain ⟨nPc', ctors⟩ := q'
    simp only at h
    split at h
    · obtain ⟨rest, s₃, h3, h⟩ := bind_run h
      obtain ⟨rfl, rfl⟩ := pure_run h
      have ih := nestGroupCtors_ctorOk hJ hW nPc cs h3
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hq' x hx
      · exact ih x hx
    · obtain ⟨_, _, h2, -⟩ := bind_run h
      exact (throw_run h2).elim

/-! ## A frame's constructors -/

/-- A frame output's normal form: readable, scoped at the frame, closed. -/
@[expose] def OutOk (s : InLean.CState) (hi : Nat) (o : List InLean.NestFieldKind × Lean.Expr) :
    Prop :=
  OkS s o.2 = true ∧ ConLeche.Expr.WScoped hi (TrS s o.2) ∧ (TrS s o.2).looseBVarsBounded 0 = true

/-- A frame's outputs, read. -/
@[expose] def trOuts (s : InLean.CState) (os : List (List InLean.NestFieldKind × Lean.Expr)) :
    List (List ConLeche.NestFieldKind × ConLeche.Expr) :=
  os.map fun o => (o.1.map trNK, TrS s o.2)

theorem OutOk.mono {s₀ s₁ : InLean.CState} (ht : TabLe s₀ s₁) {hi : Nat}
    {os : List (List InLean.NestFieldKind × Lean.Expr)} (h : ∀ o ∈ os, OutOk s₀ hi o) :
    (∀ o ∈ os, OutOk s₁ hi o) ∧ trOuts s₁ os = trOuts s₀ os := by
  refine ⟨fun o ho => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := h o ho
    exact ⟨okS_of_tabLe ht h1, by rw [TrS_of_tabLe ht h1]; exact h2,
      by rw [TrS_of_tabLe ht h1]; exact h3⟩
  · simp only [trOuts]
    apply List.map_congr_left
    intro o ho
    rw [TrS_of_tabLe ht (h o ho).1]

theorem getD_trNK (ks : List InLean.NestFieldKind) (i : Nat) :
    ((ks.map trNK).getD i .ordinary != .ordinary) = (ks.getD i .ordinary != .ordinary) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ks[i]? with
  | none => rfl
  | some k => exact trNK_ne_ordinary k

theorem nestResHead_tr {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) :
    InLean.nestResHead e = ConLeche.nestResHead (TrS s e) := by
  unfold InLean.nestResHead ConLeche.nestResHead
  rw [← TrS_getAppFnT]
  have hok := OkS_getAppFnT s h
  have hs := getAppFnT_shape e
  generalize Expr.getAppFnT e = x at hok hs
  cases x with
  | fvar id =>
    obtain ⟨d, ty, hT, -⟩ := TrS_stripTop_fvar (x := .fvar id) hok rfl
    rw [hT]; rfl
  | mdata m b => exact (hs.1 m b rfl).elim
  | app f a => exact (hs.2 f a rfl).elim
  | mvar _ => simp [OkS, okE] at hok
  | _ => simp [Expr.isFVar, TrS, trE]

theorem all_nestOcc_tr {s : InLean.CState} (names : List Lean.Name) (lo hi : Nat) :
    ∀ {l : List Lean.Expr}, OkSL s l = true →
      (TrSL s l).all (fun x => !x.nestOcc (names.map toName) lo hi) =
        l.all (fun x => !InLean.nestOcc names lo hi x)
  | [], _ => rfl
  | a :: l, h => by
    simp only [OkSL_cons, Bool.and_eq_true] at h
    simp only [TrSL_cons, List.all_cons, nestOccI_tr names lo hi h.1, all_nestOcc_tr names lo hi h.2]

theorem allWS_TrSL {s : InLean.CState} {d : Nat} {l : List Lean.Expr} (h : ∀ a ∈ l, TOk s d a) :
    ConLeche.Cached.AllWS d (TrSL s l) := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  exact (h a ha).2.1

theorem closed_TrSL {s : InLean.CState} {d : Nat} {l : List Lean.Expr} (h : ∀ a ∈ l, TOk s d a) :
    ∀ x ∈ TrSL s l, x.looseBVarsBounded 0 = true := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  exact (h a ha).2.2

theorem TOk_all_mono {s₀ s₁ : InLean.CState} (ht : TabLe s₀ s₁) {d : Nat} {l : List Lean.Expr}
    (h : ∀ a ∈ l, TOk s₀ d a) : ∀ a ∈ l, TOk s₁ d a :=
  fun a ha => (TOk.mono ht (h a ha)).1

/-- **A frame's constructors** (`nestCtors`): each constructor at the key,
typed, its fields through the recursion, U4, its result, its normal form
recorded; master's on the readings. -/
theorem nestCtorsI_run {fe : InLean.FEnv} {L : ConLeche.Env} {ctx : InLean.NestCtx}
    {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L) {fuelOf : Lean.Expr → Nat}
    {rec : Nat → InLean.NestRec}
    {rec' : ConLeche.Expr → List ConLeche.NestHole → Nat → Nat → ConLeche.Expr →
      ConLeche.NestState →
      ConLeche.FueledM (ConLeche.NestFieldKind × ConLeche.Expr × ConLeche.NestState)}
    (hrec : ∀ (s : InLean.CState) (x : Lean.Expr), OkS s x = true →
      RecSpecI fe L ctx cctx (rec (fuelOf x)) (rec' (TrS s x)))
    (prog : List InLean.NestHole) (hi : Nat) (us : List Lean.Level) (ds : List Lean.Expr)
    (names : List Lean.Name) (holes : List Lean.Expr) (hus : us.all okLv = true)
    (hlen : names.length ≤ holes.length) :
    ∀ (cs : List (Lean.ConstantVal × Nat)) (st : InLean.NestState) {s₀ s' : InLean.CState}
      {v : List (List InLean.NestFieldKind × Lean.Expr) × InLean.NestState},
      CSOKI .verified false L s₀ → WalkRel fe L s₀ ctx cctx → ProgOk s₀ prog → StOk s₀ st →
      OkSL s₀ ds = true → (∀ a ∈ ds, TOk s₀ hi a) →
      OkSL s₀ holes = true → (∀ a ∈ holes, TOk s₀ hi a) → (∀ c ∈ cs, CtorOkI c) →
      InLean.nestCtors .verified ctx fe fuelOf rec prog hi us ds names holes cs st
        s₀ =
        .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ (∀ o ∈ v.1, OutOk s' hi o) ∧ StOk s' v.2 ∧
        Runs (ConLeche.nestCtors cctx (ConLeche.fueledOpsM .verified) L rec'
          (prog.map (trHole s₀)) hi (us.map trL) (TrSL s₀ ds) (names.map toName)
          (TrSL s₀ holes) (trCtorL cs) (trSt s₀ st)) (trOuts s' v.1, trSt s' v.2)
  | [], st, s₀, s', v, hs, _, _, hst, _, _, _, _, _, h => by
    unfold InLean.nestCtors at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, by simp, hst, ?_⟩
    unfold ConLeche.nestCtors
    exact Runs.pure _
  | (cv, nF) :: cs, st, s₀, s', v, hs, hW, hp, hst, hds, hdsT, hh, hhT, hcs, h => by
    obtain ⟨hcOk, hcF, hcB⟩ := hcs (cv, nF) List.mem_cons_self
    unfold InLean.nestCtors at h
    unfold ConLeche.nestCtors
    simp only [trCtorL, List.map_cons]
    simp only [trCV, nodup_tr]
    by_cases hnd : InLean.namesNodup cv.levelParams = true
    · simp only [hnd, ↓reduceIte] at h ⊢
      obtain ⟨r, s₁, h1, h⟩ := bind_run h
      obtain ⟨hs₁, ht₁, hokr, htrr⟩ := tripleI_iff_run.1
        (instLevelParamsM_specI hs (OkS_of_okC s₀ hcOk) (fvarS_of_okC hcOk) hus) r s₁ h1
      rw [TrS_of_okC s₀ hcOk] at htrr
      obtain ⟨c, s₂, h2, h⟩ := bind_run h
      obtain ⟨hs₂, ht₂, hokc, htrc⟩ := nestCrestI_run hs₁ hus hokr (okSL_of_tabLe ht₁ hds)
        (okSL_of_tabLe ht₁ hh) h2
      rw [TrSL_of_tabLe ht₁ hds, TrSL_of_tabLe ht₁ hh, htrr] at htrc
      obtain ⟨crest, s₂', h2', h⟩ := bind_run h
      cases c with
      | none => simp only [InLean.unwrapOr] at h2'; exact (throw_run h2').elim
      | some c0 =>
      simp only [InLean.unwrapOr] at h2'
      obtain ⟨rfl, rfl⟩ := pure_run h2'
      have hokC0 := hokc c0 rfl
      simp only [Option.map_some] at htrc
      rw [← htrc]
      have ht02 := ht₁.trans ht₂
      have hwC : ConLeche.Expr.WScoped hi (TrS s₂ c0) :=
        ConLeche.Cached.wscoped_nestCrest (cv := trCV cv) hcF (by simp [TrSL]; exact hlen)
          (allWS_TrSL hdsT) (allWS_TrSL hhT) htrc.symm
      have hcC : (TrS s₂ c0).looseBVarsBounded 0 = true :=
        lbb_nestCrest (by rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hcB)
          (closed_TrSL hdsT) (closed_TrSL hhT) htrc.symm
      obtain ⟨ty, s₃, h3, h⟩ := bind_run h
      obtain ⟨hs₃, ht₃, hokty, hRty, hwty, hcty⟩ :=
        tripleI_iff_run.1 (hJ.ops.infer hs₂ hokC0 hwC hcC) ty s₃ h3
      obtain ⟨u, s₄, h4, h⟩ := bind_run h
      obtain ⟨hs₄, ht₄, -, hRu⟩ :=
        tripleI_iff_run.1 (hJ.ops.sort hs₃ hokty hwty hcty) u s₄ h4
      have ht24 := ht₃.trans ht₄
      have ht04 := ht02.trans ht24
      obtain ⟨⟨ks, nds, cur, st₁⟩, s₅, h5, h⟩ := bind_run h
      obtain ⟨hTc4, hTce⟩ := TOk.mono ht24 ⟨hokC0, hwC, hcC⟩
      obtain ⟨hs₅, ht₅, hnds, hcur, hst₁, hR5⟩ :=
        nestFieldsI_run (hrec s₂ c0 hokC0) prog hi _ (.invalid "nested positivity: invalid \
          nested inductive datatype, its constructor type does not bind its fields (official: \
          ill-formed constructor)") nF 0 c0 st hs₄ (hW.mono ht04) (hp.mono ht04).1
          (hst.mono ht04).1 (by simpa using hTc4) h5
      rw [hTce, (hp.mono ht04).2, (hst.mono ht04).2] at hR5
      simp only at hnds hcur hst₁ hR5
      have ht05 := ht04.trans ht₅
      simp only at h
      by_cases hm : (InLean.closeTelescope nds hi cur).hasExprMVar = true
      · simp only [hm, ↓reduceIte] at h
        obtain ⟨_, _, h6, -⟩ := bind_run h
        exact (throw_run h6).elim
      simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hokT, hTC⟩ := closeTelescope_tr s₅ nds hi cur hnds.1 hcur.1
        (emvarS_closeTelescope hnds.1 hcur.1 (by simpa using hm))
      rw [ConLeche.Expr.closeTelescopeC_eq] at hTC
      by_cases hu : ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
          InLean.structUsedLater (InLean.closeTelescope nds hi cur) 0 i) = true
      · simp only [hu, ↓reduceIte] at h
        obtain ⟨_, _, h6, -⟩ := bind_run h
        exact (throw_run h6).elim
      simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
      have hokArgs := OkSL_appArgs s₅ hcur.1
      by_cases hr : (InLean.nestResHead cur &&
          (appArgs cur).all fun x => !InLean.nestOcc ctx.names ctx.nP hi x) = false
      · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨_, _, h6, -⟩ := bind_run h
        exact (throw_run h6).elim
      simp only [Bool.not_eq_false] at hr
      simp only [hr, ↓reduceIte] at h
      obtain ⟨⟨os, st₃⟩, s₆, h6, h⟩ := bind_run h
      obtain ⟨rfl, rfl⟩ := pure_run h
      have hW₅ := hW.mono ht05
      obtain ⟨hp₅, hpe⟩ := hp.mono ht05
      have hF := nestHoleImg_sub hW₅ prog hp₅
      have hds₅ := okSL_of_tabLe ht05 hds
      obtain ⟨hokD, htrD⟩ := replaceFVarsI_trL hF hds₅
      obtain ⟨hokN, htrN⟩ := replaceFVarsI_tr hF hokT
      have hst₂ : StOk s₅ { st₁ with
          ctorNfs := (st₁.ctorNfs.push
            (InLean.nestCtorNf ctx prog us ds cv (InLean.closeTelescope nds hi cur))) } := by
        refine ⟨hst₁.1, hst₁.2.1, ?_⟩
        intro n hn
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hn
        rcases hn with hn | rfl
        · exact hst₁.2.2 n hn
        · exact ⟨hus, hokD, hokN⟩
      obtain ⟨hs₆, ht₆, hos, hst₃, hR6⟩ := nestCtorsI_run hJ hrec prog hi us ds names holes hus hlen
        cs _ hs₅ hW₅ hp₅ hst₂ hds₅ (TOk_all_mono ht05 hdsT) (okSL_of_tabLe ht05 hh)
        (TOk_all_mono ht05 hhT) (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) h6
      rw [hpe, TrSL_of_tabLe ht05 hds, TrSL_of_tabLe ht05 hh] at hR6
      have hwT : ConLeche.Expr.WScoped hi (TrS s₅ (InLean.closeTelescope nds hi cur)) := by
        rw [hTC]
        exact ConLeche.Cached.closeTelescope_wscopedA (by simpa using hnds.2.1)
          (by simpa [TrSL] using hcur.2.1)
      have hcT : (TrS s₅ (InLean.closeTelescope nds hi cur)).looseBVarsBounded 0 = true := by
        rw [hTC]
        exact ConLeche.closeTelescope_bounded _ _ _
          (fun x hx => by
            obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
            exact hnds.2.2 a ha) hcur.2.2
      have hTe := TrS_of_tabLe ht₆ hokT
      refine ⟨hs₆, ht05.trans ht₆, ?_, hst₃, ?_⟩
      · intro o ho
        rcases List.mem_cons.1 ho with rfl | ho
        · exact ⟨okS_of_tabLe ht₆ hokT, by rw [hTe]; exact hwT, by rw [hTe]; exact hcT⟩
        · exact hos o ho
      · refine Runs.bind (Runs.pure _) (Runs.bind hRty (Runs.bind hRu (Runs.bind hR5 ?_)))
        simp only
        rw [← hTC]
        simp only [getD_trNK, ← ConLeche.Cached.structUsedLaterC_eq, ← structUsedLater_tr hokT, hu,
          Bool.false_eq_true, ↓reduceIte]
        rw [← nestResHead_tr hcur.1, ← TrSL_appArgs, hW.canon.names, hW.canon.nP,
          all_nestOcc_tr _ _ _ hokArgs, hr]
        simp only [↓reduceIte]
        have hNf : trNf s₅ (InLean.nestCtorNf ctx prog us ds cv (InLean.closeTelescope nds hi cur)) =
            ConLeche.nestCtorNf cctx (prog.map (trHole s₀)) hi (us.map trL) (TrSL s₀ ds) (trCV cv)
              (TrSL s₅ nds) (TrS s₅ cur) := by
          simp only [trNf, InLean.nestCtorNf, ConLeche.nestCtorNf, htrD, htrN, hTC, hpe,
            TrSL_of_tabLe ht05 hds, trCV]
        simp only [trSt, Array.map_push, hNf, trCtorL, trCV] at hR6
        refine Runs.bind hR6 ?_
        simp only [trOuts, List.map_cons, hTe]
        exact Runs.pure _
    · simp only [hnd, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨_, _, h1, -⟩ := bind_run h
      exact (throw_run h1).elim

/-! ## A frame -/

/-- **Interned holes at given types** (`mapM mkFVarM`): master's free
variables, read at the final state. -/
theorem mapM_mkFVarM_tys {α : Type} {mode : ConLeche.CheckMode} {eager : Bool}
    {env : ConLeche.Env} (g : α → Nat) (t : α → Lean.Expr) :
    ∀ (l : List α) {s₀ s' : InLean.CState} {xs : List Lean.Expr},
      CSOKI mode eager env s₀ →
      (∀ i ∈ l, OkS s₀ (t i) = true ∧ (TrS s₀ (t i)).looseBVarsBounded 0 = true) →
      l.mapM (fun i => InLean.mkFVarM (g i) (t i)) s₀ = .ok (xs, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkSL s' xs = true ∧
        TrSL s' xs = l.map fun i => .fvar (g i) (TrS s₀ (t i))
  | [], s₀, s', xs, hs, _, h => by
    simp only [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, rfl, rfl⟩
  | i :: l, s₀, s', xs, hs, ht, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨x, s₁, h1, h⟩ := bind_run h
    obtain ⟨hok, hcl⟩ := ht i List.mem_cons_self
    obtain ⟨hs₁, ht₁, hokx, htx⟩ :=
      tripleI_iff_run.1 (mkFVarM_specI hs (g i) hok hcl) x s₁ h1
    obtain ⟨xs', s₂, h2, h⟩ := bind_run h
    have ht' : ∀ j ∈ l, OkS s₁ (t j) = true ∧ (TrS s₁ (t j)).looseBVarsBounded 0 = true := by
      intro j hj
      obtain ⟨a, b⟩ := ht j (List.mem_cons_of_mem _ hj)
      exact ⟨okS_of_tabLe ht₁ a, by rw [TrS_of_tabLe ht₁ a]; exact b⟩
    obtain ⟨hs₂, ht₂, hok₂, htr₂⟩ := mapM_mkFVarM_tys g t l hs₁ ht' h2
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs₂, ht₁.trans ht₂, ?_, ?_⟩
    · simp only [OkSL_cons, okS_of_tabLe ht₂ hokx, hok₂, Bool.and_self]
    · rw [TrSL_cons, htr₂, TrS_of_tabLe ht₂ hokx, htx, List.map_cons]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [TrS_of_tabLe ht₁ (ht j (List.mem_cons_of_mem _ hj)).1]

/-- **A frame** (`nestFrame`): the key typed, the group's constructors
through the walk at the frame's holes; master's on the readings. -/
theorem nestFrameI_run {fe : InLean.FEnv} {L : ConLeche.Env} {ctx : InLean.NestCtx}
    {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L) (hRF : ReducedFormerSimI)
    {rec : InLean.NestRec}
    {rec' : List ConLeche.NestHole → Nat → Nat → ConLeche.Expr → ConLeche.NestState →
      ConLeche.FueledM (ConLeche.NestFieldKind × ConLeche.Expr × ConLeche.NestState)}
    (hrec : RecSpecI fe L ctx cctx rec rec') (prog : List InLean.NestHole) (hi : Nat)
    (us : List Lean.Level) (ds : List Lean.Expr) (nPc : Nat) (grp : List (Lean.Name × Lean.Expr))
    (st : InLean.NestState) {s₀ s' : InLean.CState} {v : InLean.NestState}
    (hus : us.all okLv = true) (hs : CSOKI .verified false L s₀) (hW : WalkRel fe L s₀ ctx cctx)
    (hp : ProgOk s₀ prog) (hst : StOk s₀ st) (hds : OkSL s₀ ds = true)
    (hdsT : ∀ a ∈ ds, TOk s₀ hi a) (hg : GrpOk s₀ ds grp)
    (h : InLean.nestFrame .verified ctx fe rec prog hi us ds nPc grp st s₀ =
      .ok (v, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ StOk s' v ∧
      Runs (ConLeche.nestFrame cctx (ConLeche.fueledOpsM .verified) L rec' (prog.map (trHole s₀)) hi
        (us.map trL) (TrSL s₀ ds) nPc (trGrp s₀ grp) (trSt s₀ st)) (trSt s' v) := by
  unfold InLean.nestFrame at h
  unfold ConLeche.nestFrame
  obtain ⟨u, s₁, h1, h⟩ := bind_run h
  obtain ⟨hs₁, ht₁, hR1⟩ := familyKeyCheckI_run hJ hRF hs hus hds
    (fun a ha => ⟨(hdsT a ha).2.1, (hdsT a ha).2.2⟩) h1
  simp only at h
  obtain ⟨ctors, s₂, h2, hk⟩ := bind_run h
  have hW₁ := hW.mono ht₁
  have hcOk := nestGroupCtors_ctorOk hJ hW₁ nPc _ h2
  obtain ⟨rfl, hR2⟩ := nestGroupCtorsI_run hJ hW₁ nPc _ h2
  obtain ⟨holes, s₃, h3, h⟩ := bind_run hk
  have hg₁ := (hg.mono ht₁ hds).1
  obtain ⟨hs₃, ht₃, hokH, htrH⟩ := mapM_mkFVarM_tys (fun p : (Lean.Name × Lean.Expr) × Nat => hi + p.2)
    (fun p => p.1.2) _ hs₁ (by
      intro p hp'
      have hm : p.1 ∈ grp := List.fst_mem_of_mem_zipIdx hp'
      exact ⟨(hg₁ _ hm).1, (hg₁ _ hm).2.1⟩) h3
  obtain ⟨⟨os, st₁⟩, s₄, h4, h⟩ := bind_run h
  obtain ⟨rfl, rfl⟩ := pure_run h
  have ht03 := ht₁.trans ht₃
  obtain ⟨hg₃, hge₃⟩ := hg.mono ht03 hds
  have hge₁ := (hg.mono ht₁ hds).2
  have hlenH : holes.length = grp.length := by
    have := congrArg List.length htrH
    simpa [TrSL] using this
  have hholesT : TrSL s₃ holes = (trGrp s₀ grp).mapIdx fun i x => ConLeche.Expr.fvar (hi + i) x.2 := by
    rw [htrH]
    apply List.ext_getElem
    · simp [trGrp]
    · intro i h1 h2
      have hlt : i < grp.length := by simpa using h1
      simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_mapIdx, trGrp]
      rw [TrS_of_tabLe ht₁ (hg _ (List.getElem_mem hlt)).1]
      simp
  have hdsT₃ : ∀ a ∈ ds, TOk s₃ (hi + grp.length) a := by
    intro a ha
    obtain ⟨h1', h2'⟩ := TOk.mono ht03 (hdsT a ha)
    exact ⟨h1'.1, ConLeche.Expr.WScoped.mono (by omega) h1'.2.1, h1'.2.2⟩
  have hhT₃ : ∀ a ∈ holes, TOk s₃ (hi + grp.length) a := by
    intro a ha
    have hok : OkS s₃ a = true := by
      simp only [OkSL, List.all_eq_true] at hokH; exact hokH a ha
    refine ⟨hok, ?_, ?_⟩
    · have hm : TrS s₃ a ∈ TrSL s₃ holes := List.mem_map_of_mem ha
      rw [hholesT] at hm
      obtain ⟨i, hi', he⟩ := List.mem_mapIdx.1 hm
      rw [← he]
      simp only [ConLeche.Expr.WScoped]
      have hlt : i < grp.length := by simpa [trGrp] using hi'
      refine ⟨by omega, ConLeche.Expr.WScoped.mono (d := hi) (by omega) ?_⟩
      have hx := hg grp[i] (List.getElem_mem hlt)
      simp only [trGrp, List.getElem_map]
      exact hx.2.2 hi (fun b hb => (hdsT b hb).2.1)
    · have hm : TrS s₃ a ∈ TrSL s₃ holes := List.mem_map_of_mem ha
      rw [hholesT] at hm
      obtain ⟨i, hi', he⟩ := List.mem_mapIdx.1 hm
      rw [← he]; rfl
  have hKey : KeyOk s₃ ⟨(default : Lean.Name), us, ds⟩ :=
    ⟨hus, okSL_of_tabLe ht03 hds, closed_of_tabLe ht03 hds (fun a ha => (hdsT a ha).2.2)⟩
  have hp' : ProgOk s₃ ((grp.mapIdx fun _ x =>
      (⟨⟨x.1, us, ds⟩, hi, (InLean.piBinders x.2).1.length⟩ : InLean.NestHole)).reverse ++ prog) := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨i, -, rfl⟩ := List.mem_mapIdx.1 (List.mem_reverse.1 hx)
      exact hKey
    · exact (hp.mono ht03).1 x hx
  obtain ⟨hs₄, ht₄, -, hst₄, hR4⟩ := nestCtorsI_run hJ (fuelOf := fun _ => 0) (rec := fun _ => rec)
    (rec' := fun _ => rec')
    (fun _ _ _ => hrec) _ (hi + grp.length) us ds (grp.map (·.1)) holes hus (by simp [hlenH])
    ctors st hs₃ (hW.mono ht03) hp' (hst.mono ht03).1 (okSL_of_tabLe ht03 hds) hdsT₃ hokH hhT₃
    hcOk h4
  refine ⟨hs₄, ht03.trans ht₄, hst₄, ?_⟩
  have hhead : ((trGrp s₀ grp).headD default).fst = toName (grp.headD default).1 := by
    cases grp <;> rfl
  rw [hhead, hW.find]
  refine Runs.bind hR1 ?_
  simp only
  have hnames : (trGrp s₀ grp).map (·.1) = (grp.map (·.1)).map toName := by simp [trGrp]
  rw [hnames]
  refine Runs.bind hR2 ?_
  have hprog : ((grp.mapIdx fun _ x =>
      (⟨⟨x.1, us, ds⟩, hi, (InLean.piBinders x.2).1.length⟩ : InLean.NestHole)).reverse ++ prog).map
        (trHole s₃) =
      ((trGrp s₀ grp).mapIdx fun _ x =>
        (⟨⟨x.1, us.map trL, TrSL s₀ ds⟩, hi, x.2.piBinders.1.length⟩ : ConLeche.NestHole)).reverse ++
        prog.map (trHole s₀) := by
    rw [List.map_append, List.map_reverse, (hp.mono ht03).2]
    congr 2
    apply List.ext_getElem
    · simp [trGrp]
    · intro i h1 h2
      have hlt : i < grp.length := by simpa using h1
      simp only [List.getElem_map, List.getElem_mapIdx, trGrp, trHole, trKey,
        TrSL_of_tabLe ht03 hds, (piBinders_TrS _ (hg _ (List.getElem_mem hlt)).1).1,
        List.length_map]
  rw [hprog, TrSL_of_tabLe ht03 hds, hholesT, (hst.mono ht03).2] at hR4
  simp only [trGrp, List.length_map] at hR4 ⊢
  refine Runs.bind hR4 ?_
  exact Runs.pure _

/-! ## An instantiation's frame -/

theorem TOk_nestWalkStack {fe : InLean.FEnv} {L : ConLeche.Env} {s : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hW : WalkRel fe L s ctx cctx)
    {prog : List InLean.NestHole} {ds : List Lean.Expr} (hds : OkSL s ds = true)
    (hdsT : ∀ a ∈ ds, TOk s (ctx.hiAt prog.length) a) :
    ∀ a ∈ ds, TOk s (ctx.hiAt (InLean.nestWalkStack ctx prog ds).length) a := by
  have h := ConLeche.Cached.allWS_nestWalkStack (ctx := cctx) (prog := prog.map (trHole s))
    (ds := TrSL s ds) (by rw [List.length_map, hiAt_rel hW.canon]; exact allWS_TrSL hdsT)
  rw [nestWalkStack_tr hW prog hds, List.length_map, hiAt_rel hW.canon] at h
  intro a ha
  exact ⟨(hdsT a ha).1, h _ (List.mem_map_of_mem ha), (hdsT a ha).2.2⟩

theorem ProgOk_nestWalkStack {s : InLean.CState} {ctx : InLean.NestCtx}
    {prog : List InLean.NestHole} (hp : ProgOk s prog) (ds : List Lean.Expr) :
    ProgOk s (InLean.nestWalkStack ctx prog ds) := by
  unfold InLean.nestWalkStack
  split
  · intro x hx; cases hx
  · exact hp

/-- **A new instantiation's frame** (`nestContNew`): the group grown, the
frame walked with the group active, the group accepted; master's on the
readings. -/
theorem nestContNewI_run {fe : InLean.FEnv} {L : ConLeche.Env} {ctx : InLean.NestCtx}
    {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L) (hRF : ReducedFormerSimI)
    {rec : InLean.NestRec}
    {rec' : List ConLeche.NestHole → Nat → Nat → ConLeche.Expr → ConLeche.NestState →
      ConLeche.FueledM (ConLeche.NestFieldKind × ConLeche.Expr × ConLeche.NestState)}
    (hrec : RecSpecI fe L ctx cctx rec rec') (prog : List InLean.NestHole) (kb : Nat)
    (n : Lean.Name) (us : List Lean.Level) (ds : List Lean.Expr) (nPc : Nat) (cty : Lean.Expr)
    (st : InLean.NestState) {s₀ s' : InLean.CState} {v : InLean.NestFieldKind × InLean.NestState}
    (hus : us.all okLv = true) (hs : CSOKI .verified false L s₀) (hW : WalkRel fe L s₀ ctx cctx)
    (hp : ProgOk s₀ prog) (hst : StOk s₀ st) (hds : OkSL s₀ ds = true)
    (hdsT : ∀ a ∈ ds, TOk s₀ (ctx.hiAt prog.length) a) (hcty : GrpOk s₀ ds [(n, cty)])
    (h : InLean.nestContNew .verified ctx fe rec prog kb n us ds nPc cty st s₀ =
      .ok (v, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ StOk s' v.2 ∧
      Runs (ConLeche.nestContNew cctx (ConLeche.fueledOpsM .verified) L rec' (prog.map (trHole s₀))
        kb (toName n) (us.map trL) (TrSL s₀ ds) nPc (TrS s₀ cty) (trSt s₀ st))
        (trNK v.1, trSt s' v.2) := by
  unfold InLean.nestContNew at h
  unfold ConLeche.nestContNew
  simp only at h
  have hcl : ∀ a ∈ ds, (TrS s₀ a).looseBVarsBounded 0 = true := fun a ha => (hdsT a ha).2.2
  obtain ⟨grp, s₁, h1, h⟩ := bind_run h
  obtain ⟨hs₁, ht₁, hg₁, hR1⟩ := nestGrowGroupI_run hJ hRF hW hus _ _ hs hds hcl hcty h1
  obtain ⟨st₃, s₂, h2, h⟩ := bind_run h
  obtain ⟨rfl, rfl⟩ := pure_run h
  have hds₁ := okSL_of_tabLe ht₁ hds
  have hKey : ∀ c : Lean.Name, KeyOk s₁ ⟨c, us, ds⟩ :=
    fun _ => ⟨hus, hds₁, closed_of_tabLe ht₁ hds hcl⟩
  obtain ⟨hst₁, hste₁⟩ := hst.mono ht₁
  have hst₂ : StOk s₁ { st with active := grp.map (fun p => (⟨p.1, us, ds⟩ : InLean.NestKey)) ++
      st.active } := by
    refine ⟨hst₁.1, ?_, hst₁.2.2⟩
    intro k hk
    rcases List.mem_append.1 hk with hk | hk
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hk
      exact hKey p.1
    · exact hst₁.2.1 k hk
  obtain ⟨hdsW, -⟩ := (⟨TOk_nestWalkStack (hW.mono ht₁) hds₁ (TOk_all_mono ht₁ hdsT), trivial⟩ :
    (∀ a ∈ ds, TOk s₁ (ctx.hiAt (InLean.nestWalkStack ctx prog ds).length) a) ∧ True)
  obtain ⟨hs₂, ht₂, hst₃, hR2⟩ := nestFrameI_run hJ hRF hrec _ _ us ds nPc grp _ hus hs₁
    (hW.mono ht₁) (ProgOk_nestWalkStack (hp.mono ht₁).1 ds) hst₂ hds₁ hdsW hg₁ h2
  refine ⟨hs₂, ht₁.trans ht₂, ?_, ?_⟩
  · refine ⟨?_, (hst.mono (ht₁.trans ht₂)).1.2.1, hst₃.2.2⟩
    split
    · exact (nestAcceptGroup_tr hs₂.fv hus (okSL_of_tabLe (ht₁.trans ht₂) hds)
        (closed_of_tabLe (ht₁.trans ht₂) hds hcl) grp _ hst₃.1).1
    · exact hst₃.1
  · simp only
    rw [nestFrameMates_tr hJ hW, nestWalkStack_tr hW prog hds, List.length_map,
      hiAt_rel hW.canon]
    refine Runs.bind hR1 ?_
    have hwp := (ProgOk_nestWalkStack (ctx := ctx) hp ds).mono ht₁
    rw [hwp.2, TrSL_of_tabLe ht₁ hds] at hR2
    have hst₂e : trSt s₁ { st with active := grp.map (fun p => (⟨p.1, us, ds⟩ : InLean.NestKey)) ++
        st.active } = (⟨(trSt s₀ st).keys,
          (trGrp s₁ grp).map (fun p => (⟨p.1, us.map trL, TrSL s₀ ds⟩ : ConLeche.NestKey)) ++
            (trSt s₀ st).active, (trSt s₀ st).ctorNfs⟩ : ConLeche.NestState) := by
      rw [← hste₁]
      simp [trSt, trGrp, trKey, TrSL_of_tabLe ht₁ hds]
    rw [hst₂e] at hR2
    refine Runs.bind hR2 ?_
    have ht12 := ht₁.trans ht₂
    have hdsE : TrSL s₂ ds = TrSL s₀ ds := TrSL_of_tabLe ht12 hds
    have hgE : trGrp s₂ grp = trGrp s₁ grp := (hg₁.mono ht₂ hds₁).2
    have hactE : st.active.map (trKey s₂) = st.active.map (trKey s₀) :=
      map_trKey_of_tabLe ht12 hst.2.1
    have hacc := (nestAcceptGroup_tr hs₂.fv hus (okSL_of_tabLe ht12 hds)
      (closed_of_tabLe ht12 hds hcl) grp st₃.keys hst₃.1).2
    rw [hdsE, hgE] at hacc
    rw [hiAt_rel hW.canon, allFvarB_tr _ hds]
    by_cases hc : (ds.all fun x => decide (InLean.fvarB x ≤ ctx.hiAt 0)) = true
    · simp only [hc, ↓reduceIte, trSt, trNK, ← hacc, hactE]
      exact Runs.pure _
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, trSt, trNK, hactE]
      exact Runs.pure _

/-- **An instantiation met** (`nestContKey`): in progress, cached or new;
master's on the readings. -/
theorem nestContKeyI_run {fe : InLean.FEnv} {L : ConLeche.Env} {ctx : InLean.NestCtx}
    {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L) (hRF : ReducedFormerSimI)
    {rec : InLean.NestRec}
    {rec' : List ConLeche.NestHole → Nat → Nat → ConLeche.Expr → ConLeche.NestState →
      ConLeche.FueledM (ConLeche.NestFieldKind × ConLeche.Expr × ConLeche.NestState)}
    (hrec : RecSpecI fe L ctx cctx rec rec') (prog : List InLean.NestHole) (kb : Nat)
    (n : Lean.Name) (us : List Lean.Level) (ds : List Lean.Expr) (nPc : Nat) (cty : Lean.Expr)
    (st : InLean.NestState) {s₀ s' : InLean.CState} {v : InLean.NestFieldKind × InLean.NestState}
    (hus : us.all okLv = true) (hs : CSOKI .verified false L s₀) (hW : WalkRel fe L s₀ ctx cctx)
    (hp : ProgOk s₀ prog) (hst : StOk s₀ st) (hds : OkSL s₀ ds = true)
    (hdsT : ∀ a ∈ ds, TOk s₀ (ctx.hiAt prog.length) a) (hcty : GrpOk s₀ ds [(n, cty)])
    (h : InLean.nestContKey .verified ctx fe rec prog kb n us ds nPc cty st s₀ =
      .ok (v, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ StOk s' v.2 ∧
      Runs (ConLeche.nestContKey cctx (ConLeche.fueledOpsM .verified) L rec' (prog.map (trHole s₀))
        kb (toName n) (us.map trL) (TrSL s₀ ds) nPc (TrS s₀ cty) (trSt s₀ st))
        (trNK v.1, trSt s' v.2) := by
  have hk : KeyOk s₀ ⟨n, us, ds⟩ := ⟨hus, hds, fun a ha => (hdsT a ha).2.2⟩
  have htk : (⟨toName n, us.map trL, TrSL s₀ ds⟩ : ConLeche.NestKey) = trKey s₀ ⟨n, us, ds⟩ := rfl
  unfold InLean.nestContKey at h
  unfold ConLeche.nestContKey
  rw [htk]
  have hact : (trSt s₀ st).active.contains (trKey s₀ ⟨n, us, ds⟩) = st.active.contains ⟨n, us, ds⟩ :=
    contains_trKey_list hs.fv hk hst.2.1
  have hkeys : (trSt s₀ st).keys.contains (trKey s₀ ⟨n, us, ds⟩) = st.keys.contains ⟨n, us, ds⟩ :=
    contains_trKey hs.fv hk hst.1
  rw [hact, hkeys, hiAt_rel hW.canon, allFvarB_tr _ hds]
  by_cases h1 : st.active.contains ⟨n, us, ds⟩ = true
  · simp only [h1, ↓reduceIte] at h
    exact (throw_run h).elim
  simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h2 : ((ds.all fun x => decide (InLean.fvarB x ≤ ctx.hiAt 0)) &&
      st.keys.contains ⟨n, us, ds⟩) = true
  · simp only [h2, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, hst, Runs.pure _⟩
  · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact nestContNewI_run hJ hRF hrec prog kb n us ds nPc cty st hus hs hW hp hst hds hdsT hcty h

/-- InLean's loose-variable test, read: master's bound. -/
theorem hasLooseBVars_tr {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) :
    (!e.hasLooseBVars) = ((TrS s e).bvarB == 0) := by
  have hb : (TrS s e).bvarB = rangeS e := by
    rw [ConLeche.Expr.bvarB_eq]
    exact bvarBound_toExpr (FVarTable.trans_fvarsOnly _) e (TrS s e) (TransS_of_ok h)
  show (!decide (e.looseBVarRange > 0)) = _
  rw [Expr.looseBVarRange_eq (RangeOk_of_OkS h), hb]
  cases rangeS e <;> simp

theorem paramsCheck_tr {s : InLean.CState} (hi : Nat) :
    ∀ {l : List Lean.Expr}, OkSL s l = true →
      (TrSL s l).all (fun x => x.bvarB == 0 && decide (x.fvarB ≤ hi)) =
        l.all (fun x => !x.hasLooseBVars && decide (InLean.fvarB x ≤ hi))
  | [], _ => rfl
  | a :: l, h => by
    simp only [OkSL_cons, Bool.and_eq_true] at h
    simp only [TrSL_cons, List.all_cons, ← hasLooseBVars_tr h.1, fvarB_tr h.1, paramsCheck_tr hi h.2]

/-- **The container case** (`nestCont`): the container's checks, its
instantiation's type, the instantiation met; master's on the readings. -/
theorem nestContI_run {fe : InLean.FEnv} {L : ConLeche.Env} {ctx : InLean.NestCtx}
    {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L) (hRF : ReducedFormerSimI)
    {rec : InLean.NestRec}
    {rec' : List ConLeche.NestHole → Nat → Nat → ConLeche.Expr → ConLeche.NestState →
      ConLeche.FueledM (ConLeche.NestFieldKind × ConLeche.Expr × ConLeche.NestState)}
    (hrec : RecSpecI fe L ctx cctx rec rec') (prog : List InLean.NestHole) (kb : Nat)
    (n : Lean.Name) (us : List Lean.Level) (args : List Lean.Expr) (st : InLean.NestState)
    {dep : Nat} {s₀ s' : InLean.CState} {v : InLean.NestFieldKind × InLean.NestState}
    (hus : us.all okLv = true) (hs : CSOKI .verified false L s₀) (hW : WalkRel fe L s₀ ctx cctx)
    (hp : ProgOk s₀ prog) (hst : StOk s₀ st) (hargs : OkSL s₀ args = true)
    (hargsW : ∀ a ∈ args, ConLeche.Expr.WScoped dep (TrS s₀ a))
    (h : InLean.nestCont .verified ctx fe rec prog kb n us args st s₀ =
      .ok (v, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ StOk s' v.2 ∧
      Runs (ConLeche.nestCont cctx (ConLeche.fueledOpsM .verified) L rec' (prog.map (trHole s₀))
        kb (toName n) (us.map trL) (TrSL s₀ args) (trSt s₀ st)) (trNK v.1, trSt s' v.2) := by
  unfold InLean.nestCont at h
  unfold ConLeche.nestCont
  obtain ⟨q, s₁, h1, h⟩ := bind_run h
  rw [nestContainer_tr hJ hW]
  cases hq : InLean.nestContainer ctx n with
  | none => rw [hq] at h1; exact (throw_run h1).elim
  | some q' =>
  rw [hq] at h1
  obtain ⟨rfl, rfl⟩ := pure_run h1
  obtain ⟨nPc, ctors⟩ := q'
  simp only at h
  have hdrop : (TrSL s₀ args).drop nPc = TrSL s₀ (args.drop nPc) := by simp [TrSL, List.map_drop]
  have htake : (TrSL s₀ args).take nPc = TrSL s₀ (args.take nPc) := by simp [TrSL, List.map_take]
  have hokD : OkSL s₀ (args.drop nPc) = true := by
    simp only [OkSL, List.all_eq_true] at hargs ⊢
    exact fun x hx => hargs x (List.mem_of_mem_drop hx)
  have hokT : OkSL s₀ (args.take nPc) = true := by
    simp only [OkSL, List.all_eq_true] at hargs ⊢
    exact fun x hx => hargs x (List.mem_of_mem_take hx)
  have hlenA : (TrSL s₀ args).length = args.length := by simp [TrSL]
  have hquot : (toName n == ConLeche.quotName) = (n == InLean.quotName) := by
    rw [show ConLeche.quotName = toName InLean.quotName from rfl, ← nameBeq_tr]
  by_cases hc1 : (decide (args.length < nPc) || !(args.drop nPc).all fun x =>
      !InLean.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x) = true
  · simp only [hc1, ↓reduceIte] at h
    obtain ⟨_, _, h2, -⟩ := bind_run h
    exact (throw_run h2).elim
  simp only [hc1, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hc2 : (n == InLean.quotName) = true
  · simp only [hc2, ↓reduceIte] at h
    obtain ⟨_, _, h2, -⟩ := bind_run h
    exact (throw_run h2).elim
  simp only [hc2, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hc3 : ((args.take nPc).all fun x =>
      !x.hasLooseBVars && decide (InLean.fvarB x ≤ ctx.hiAt prog.length)) = false
  · simp only [hc3, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, _, h2, -⟩ := bind_run h
    exact (throw_run h2).elim
  simp only [Bool.not_eq_false] at hc3
  simp only [hc3, ↓reduceIte] at h
  have hpT : ∀ a ∈ args.take nPc, TOk s₀ (ctx.hiAt prog.length) a := by
    intro a ha
    have hoka : OkS s₀ a = true := by
      simp only [OkSL, List.all_eq_true] at hokT; exact hokT a ha
    have hca := List.all_eq_true.1 hc3 a ha
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hca
    have hb : (TrS s₀ a).bvarB = 0 := by
      have := hasLooseBVars_tr hoka
      rw [hca.1] at this
      simpa using this.symm
    refine ⟨hoka, ?_, ?_⟩
    · exact ConLeche.WScoped.of_fvarsBelow (hargsW a (List.mem_of_mem_take ha))
        (ConLeche.Expr.fvarB_le (by rw [← fvarB_tr hoka]; exact hca.2))
    · rw [ConLeche.Expr.looseBVarsBounded_iff, ← ConLeche.Expr.bvarB_eq, hb]; exact Nat.le_refl 0
  obtain ⟨⟨k, ty⟩, s₁, h3, h⟩ := bind_run h
  obtain ⟨hs₁, ht₁, hok₁, hcl₁, hws₁, hR1⟩ := nestInstTypeI_run (key := ⟨n, us, args.take nPc⟩)
    hJ hRF hW.canon hW.fe hW.find hW.sort hW.sortOk hs hus hokT (fun a ha => (hpT a ha).2.2) h3
  by_cases hc4 : (args.length == nPc + k) = false
  · simp only [hc4, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, _, h2, -⟩ := bind_run h
    exact (throw_run h2).elim
  simp only [Bool.not_eq_false] at hc4
  simp only [hc4, ↓reduceIte] at h
  have hcty : GrpOk s₁ (args.take nPc) [(n, ty)] := by
    intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    refine ⟨hok₁, hcl₁, fun d hd => hws₁ d ?_⟩
    intro a ha
    rw [← TrS_of_tabLe ht₁ (hpT a ha).1]
    exact hd a ha
  obtain ⟨hs', ht', hst', hR⟩ := nestContKeyI_run hJ hRF hrec prog kb n us (args.take nPc) nPc ty st
    hus hs₁ (hW.mono ht₁) (hp.mono ht₁).1 (hst.mono ht₁).1 (okSL_of_tabLe ht₁ hokT)
    (TOk_all_mono ht₁ hpT) hcty h
  refine ⟨hs', ht₁.trans ht', hst', ?_⟩
  rw [(hp.mono ht₁).2, TrSL_of_tabLe ht₁ hokT, (hst.mono ht₁).2] at hR
  simp only [Option.map_some, ConLeche.unwrapOr]
  refine Runs.bind (Runs.pure _) ?_
  simp only
  rw [hlenA, List.length_map, hiAt_rel hW.canon, hW.canon.names, hW.canon.nP, hdrop, htake,
    all_nestOcc_tr _ _ _ hokD, hquot, paramsCheck_tr _ hokT]
  simp only [hc1, hc2, hc3, Bool.false_eq_true, ↓reduceIte]
  refine Runs.bind hR1 ?_
  simp only [hc4, ↓reduceIte]
  exact hR

/-! ## The walk -/

theorem contains_toName (n : Lean.Name) : ∀ (l : List Lean.Name),
    (l.map toName).contains (toName n) = l.contains n
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.contains_cons, List.contains_cons, contains_toName n l, ← nameBeq_tr]

/-- InLean's re-abstraction of one variable, where it wrote no marker, reads
as master's. -/
theorem abstract1_tr {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) (d : Nat)
    (hm : (InLean.abstract1 e d 0).hasExprMVar = false) :
    OkS s (InLean.abstract1 e d 0) = true ∧
      TrS s (InLean.abstract1 e d 0) = (TrS s e).abstract1 d 0 := by
  unfold InLean.abstract1 at hm ⊢
  have hrr := RangeOk_abstractDepthsFrom (RangeOk_of_OkS h) d 1 0
  have hm' : emvarS (EO.abstractDepthsFrom e d 1 0) = false := by
    rw [← Expr.hasExprMVar_eq hrr]; exact hm
  obtain ⟨hok, htr⟩ := ok_of_TransS hrr (toExpr_abstractDepthsFrom (FVarTable.trans_depthOK _)
    (RangeOk_of_OkS h) (TransS_of_ok h) d 1 0 hm')
  exact ⟨hok, by rw [htr, abstractRange_one]⟩

/-- A reading that is a `Π` comes from one, under `mdata`. -/
theorem TrS_eq_forallE {s : InLean.CState} (x : Lean.Expr) : ∀ {a b : ConLeche.Expr},
    OkS s x = true → TrS s x = .forallE a b → ∃ n t u bi, EO.stripTop x = .forallE n t u bi := by
  induction x with
  | forallE n t u bi => intro _ _ _ _; exact ⟨n, t, u, bi, rfl⟩
  | mdata _ e ih =>
    intro a b h he
    rw [OkS_mdata] at h
    rw [TrS_mdata] at he
    exact ih h he
  | fvar id =>
    intro a b h he
    obtain ⟨d, ty, hT, -⟩ := TrS_stripTop_fvar (x := .fvar id) h rfl
    rw [hT] at he; cases he
  | mvar _ => intro _ _ h _; simp [OkS, okE] at h
  | _ => intro _ _ _ he; simp [TrS, trE] at he

/-- **The positivity walk** (`nestPos`), at every fuel: master's on the
readings (the twin of master's `RecSpec` for the walk itself). -/
theorem nestPosI_run {fe : InLean.FEnv} {L : ConLeche.Env} {ctx : InLean.NestCtx}
    {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L) (hRF : ReducedFormerSimI) :
    ∀ fuel : Nat, RecSpecI fe L ctx cctx (InLean.nestPos .verified fe ctx fuel)
      (ConLeche.nestPos (ConLeche.fueledOpsM .verified) L cctx fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro prog dep kb e st s₀ s' v _ _ _ _ _ h
    unfold InLean.nestPos at h
    exact (throw_run h).elim
  | succ fuel ih =>
    intro prog dep kb e st s₀ s' v hs hW hp hst he h
    unfold InLean.nestPos at h
    unfold ConLeche.nestPos
    simp only at h
    obtain ⟨w, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hokw, hRw, hww, hcw⟩ :=
      tripleI_iff_run.1 (hJ.ops.whnf hs he.1 he.2.1 he.2.2) w s₁ h1
    obtain ⟨he₁, hee⟩ := TOk.mono ht₁ he
    have hW₁ := hW.mono ht₁
    obtain ⟨hp₁, hpe⟩ := hp.mono ht₁
    obtain ⟨hst₁, hste⟩ := hst.mono ht₁
    have hocc : ∀ {x : Lean.Expr}, OkS s₁ x = true →
        ConLeche.Expr.nestOcc cctx.names cctx.nP (cctx.hiAt (prog.map (trHole s₀)).length) (TrS s₁ x) =
          InLean.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x := by
      intro x hx
      rw [List.length_map, hiAt_rel hW.canon, hW.canon.names, hW.canon.nP, nestOccI_tr _ _ _ hx]
    by_cases ho : InLean.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) w = false
    · simp only [ho, Bool.not_false, ↓reduceIte] at h
      obtain ⟨rfl, rfl⟩ := pure_run h
      by_cases hoe : InLean.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) e = true
      · simp only [hoe, ↓reduceIte]
        refine ⟨hs₁, ht₁, ⟨hokw, hww, hcw⟩, hst₁, Runs.bind hRw ?_⟩
        simp only [hocc hokw, ho, Bool.not_false, ↓reduceIte, ← hee, hocc he₁.1, hoe, trNK, hste]
        exact Runs.pure _
      · simp only [hoe, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hs₁, ht₁, he₁, hst₁, Runs.bind hRw ?_⟩
        simp only [hocc hokw, ho, Bool.not_false, ↓reduceIte, ← hee, hocc he₁.1, hoe,
          Bool.false_eq_true, trNK, hste]
        exact Runs.pure _
    simp only [Bool.not_eq_false] at ho
    simp only [ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    have hokx : OkS s₁ (EO.stripTop w) = true := by rw [OkS_stripTop]; exact hokw
    have hTx : TrS s₁ w = TrS s₁ (EO.stripTop w) := (TrS_stripTop s₁ w).symm
    have hnm : ∀ m b, EO.stripTop w ≠ .mdata m b := fun m b he => stripTop_ne_mdata he
    generalize hx : EO.stripTop w = x at h hokx hnm
    cases x with
    | forallE nm a b bi =>
      rw [hx] at hTx
      simp only at h
      simp only [OkS_forallE, Bool.and_eq_true] at hokx
      rw [TrS_forallE] at hTx
      have hwab := hww
      have hcab := hcw
      rw [hTx] at hwab hcab
      simp only [ConLeche.Expr.WScoped] at hwab
      rw [lbb_forallE, Bool.and_eq_true] at hcab
      by_cases hoa : InLean.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) a = true
      · simp only [hoa, ↓reduceIte] at h
        obtain ⟨_, _, h2, -⟩ := bind_run h
        exact (throw_run h2).elim
      simp only [hoa, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨r, s₂, h2, h⟩ := bind_run h
      obtain ⟨hs₂, ht₂, hokr, htrr⟩ := tripleI_iff_run.1
        (mkFVarM_specI hs₁ dep hokx.1 hcab.1) r s₂ h2
      obtain ⟨⟨k, nb, st₁⟩, s₃, h3, h⟩ := bind_run h
      have hokb := okS_of_tabLe ht₂ hokx.2
      have htb := TrS_of_tabLe ht₂ hokx.2
      have hrcl : (TrS s₂ r).looseBVarsBounded 0 = true := by rw [htrr]; rfl
      have hTI : TrS s₂ (b.inst1I r) = (TrS s₁ b).instantiate1 (.fvar dep (TrS s₁ a)) 0 := by
        rw [inst1I_eq, TrS_inst1_eq hokb hokr hrcl, htb, htrr]
      have hin : TOk s₂ (dep + 1) (b.inst1I r) := by
        refine ⟨OkS_inst1 hokb hokr hrcl, ?_, ?_⟩
        · rw [hTI]; exact ConLeche.Expr.WScoped.instantiate1 hwab.1 0 hwab.2
        · rw [hTI]; exact lbb_instantiate1 rfl hcab.2
      obtain ⟨hs₃, ht₃, hnb, hst₃, hR3⟩ := ih prog (dep + 1) (kb + 1) _ st hs₂ (hW₁.mono ht₂)
        (hp₁.mono ht₂).1 (hst₁.mono ht₂).1 hin h3
      simp only at h
      by_cases hm : (InLean.abstract1 nb dep 0).hasExprMVar = true
      · simp only [hm, ↓reduceIte] at h
        obtain ⟨_, _, h4, -⟩ := bind_run h
        exact (throw_run h4).elim
      simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rfl, rfl⟩ := pure_run h
      obtain ⟨hokA, htrA⟩ := abstract1_tr hnb.1 dep (by simpa using hm)
      have ht13 := ht₂.trans ht₃
      have hta₃ := TrS_of_tabLe ht13 hokx.1
      refine ⟨hs₃, ht₁.trans ht13, ⟨?_, ?_, ?_⟩, hst₃, Runs.bind hRw ?_⟩
      · simp only [OkS_forallE, okS_of_tabLe ht13 hokx.1, hokA, Bool.and_self]
      · simp only [TrS_forallE, ConLeche.Expr.WScoped, hta₃, htrA]
        exact ⟨hwab.1, ConLeche.WScoped.abstract1 0 hnb.2.1⟩
      · simp only [TrS_forallE, lbb_forallE, hta₃, htrA, hcab.1, Bool.true_and]
        exact ConLeche.looseBVarsBounded_abstract1 _ 0 hnb.2.2
      · rw [hocc hokw, ho, hTx]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [hocc hokx.1]
        simp only [hoa, Bool.false_eq_true, ↓reduceIte]
        rw [hTI, (hp₁.mono ht₂).2, hpe, (hst₁.mono ht₂).2, hste] at hR3
        refine Runs.bind hR3 ?_
        simp only [TrS_forallE, hta₃, htrA]
        exact Runs.pure _
    | mdata m b => exact (hnm m b rfl).elim
    | _ =>
      simp only at h
      have hnT : ∀ a' b', TrS s₁ w ≠ .forallE a' b' := by
        intro a' b' he
        obtain ⟨n, t, u, bi, hx'⟩ := TrS_eq_forallE w hokw he
        rw [hx] at hx'
        cases hx'
      have hfn := OkS_getAppFnT s₁ hokw
      have hshape := getAppFnT_shape w
      have hargs := OkSL_appArgs s₁ hokw
      have hargsW : ∀ a ∈ appArgs w, ConLeche.Expr.WScoped dep (TrS s₁ a) := by
        intro a ha
        have := ConLeche.Cached.allWS_getAppArgs hww
        rw [← TrSL_appArgs] at this
        exact this _ (List.mem_map_of_mem ha)
      have hfT := TrS_getAppFnT s₁ w
      have hall : ((TrS s₁ w).getAppArgs.all fun x =>
          !ConLeche.Expr.nestOcc cctx.names cctx.nP (cctx.hiAt (prog.map (trHole s₀)).length) x) =
          (appArgs w).all fun x => !InLean.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x := by
        rw [← TrSL_appArgs, List.length_map, hiAt_rel hW.canon, hW.canon.names, hW.canon.nP,
          all_nestOcc_tr _ _ _ hargs]
      have hlenA : (TrS s₁ w).getAppArgs.length = (appArgs w).length := by
        rw [← TrSL_appArgs]; simp [TrSL]
      generalize hf : Expr.getAppFnT w = f at h hfn hshape hfT
      cases f with
      | fvar id =>
        obtain ⟨d, ty, hT, hd⟩ := TrS_stripTop_fvar (x := .fvar id) hfn rfl
        rw [hT] at hfT
        simp only [hd, Option.getD_some] at h
        cases hh : InLean.nestHoleAt ctx prog d with
        | none => rw [hh] at h; exact (throw_run h).elim
        | some ho' =>
        rw [hh] at h
        simp only at h
        by_cases hc : (((appArgs w).all fun x => !InLean.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x) &&
            (appArgs w).length == ho'.nIdx) = true
        · simp only [hc, ↓reduceIte] at h
          obtain ⟨rfl, rfl⟩ := pure_run h
          refine ⟨hs₁, ht₁, ⟨hokw, hww, hcw⟩, hst₁, Runs.bind hRw ?_⟩
          rw [hocc hokw, ho]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          generalize TrS s₁ w = W at hnT hfT hall hlenA ⊢
          cases W
          case forallE a' b' => exact absurd rfl (hnT a' b')
          all_goals
            try simp only
            rw [← hfT]
            try simp only
            rw [nestHoleAt_tr hW prog d, hh]
            simp only [Option.map_some, hall, hlenA, trHole]
            simp only [hc, ↓reduceIte, hiAt_rel hW.canon, hW.canon.nP]
            rw [hste]
            split
            · split
              · exact Runs.pure _
              · exact Runs.pure _
            · exact Runs.pure _
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
          exact (throw_run h).elim
      | const n us =>
        simp only at h
        have hus : us.all okLv = true := by simpa [OkS_const] using hfn
        rw [TrS_const] at hfT
        by_cases hn : ctx.names.contains n = true
        · simp only [hn, ↓reduceIte] at h
          obtain ⟨_, _, h2, -⟩ := bind_run h
          exact (throw_run h2).elim
        simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨⟨k, st₂⟩, s₂, h2, h⟩ := bind_run h
        obtain ⟨rfl, rfl⟩ := pure_run h
        obtain ⟨hs₂, ht₂, hst₂, hR2⟩ := nestContI_run hJ hRF ih prog kb n us (appArgs w) st hus hs₁
          hW₁ hp₁ hst₁ hargs hargsW h2
        obtain ⟨hw₂, hwe⟩ := TOk.mono ht₂ ⟨hokw, hww, hcw⟩
        refine ⟨hs₂, ht₁.trans ht₂, hw₂, hst₂, Runs.bind hRw ?_⟩
        rw [hocc hokw, ho]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [hpe, hste, TrSL_appArgs] at hR2
        generalize TrS s₁ w = W at hnT hfT hR2 hwe ⊢
        cases W
        case forallE a' b' => exact absurd rfl (hnT a' b')
        all_goals
          try simp only
          rw [← hfT]
          try simp only
          rw [hW.canon.names, contains_toName]
          simp only [hn, Bool.false_eq_true, ↓reduceIte]
          refine Runs.bind hR2 ?_
          rw [hwe]
          exact Runs.pure _
      | mdata m b => exact (hshape.1 m b rfl).elim
      | app f a => exact (hshape.2 f a rfl).elim
      | _ => simp only at h; exact (throw_run h).elim

/-! ## The root -/

/-- **The root frame** (`nestRoot`): every member's constructors through the
walk at their own fuel; master's on the readings. -/
theorem nestRootI_run {fe : InLean.FEnv} {L : ConLeche.Env} {ctx : InLean.NestCtx}
    {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L) (hRF : ReducedFormerSimI)
    (holes : List Lean.Expr) :
    ∀ (css : List (List (Lean.ConstantVal × Nat))) (st : InLean.NestState) {s₀ s' : InLean.CState}
      {v : List (List (List InLean.NestFieldKind × Lean.Expr)) × InLean.NestState},
      CSOKI .verified false L s₀ → WalkRel fe L s₀ ctx cctx → StOk s₀ st →
      OkSL s₀ holes = true → (∀ a ∈ holes, TOk s₀ (ctx.hiAt 0) a) →
      (∀ a ∈ ctx.params, ConLeche.Expr.WScoped (ctx.hiAt 0) (TrS s₀ a)) →
      ctx.names.length ≤ holes.length → (∀ cs ∈ css, ∀ c ∈ cs, CtorOkI c) →
      InLean.nestRoot .verified fe ctx holes css st s₀ = .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ (∀ o ∈ v.1, ∀ x ∈ o, OutOk s' (ctx.hiAt 0) x) ∧
        StOk s' v.2 ∧
        Runs (ConLeche.nestRoot (ConLeche.fueledOpsM .verified) L cctx (TrSL s₀ holes)
          (css.map trCtorL) (trSt s₀ st)) (v.1.map (trOuts s'), trSt s' v.2)
  | [], st, s₀, s', v, hs, _, hst, _, _, _, _, _, h => by
    unfold InLean.nestRoot at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by simp, hst, by unfold ConLeche.nestRoot; exact Runs.pure _⟩
  | cs :: css, st, s₀, s', v, hs, hW, hst, hh, hhT, hpW, hlen, hcs, h => by
    unfold InLean.nestRoot at h
    unfold ConLeche.nestRoot
    obtain ⟨⟨o, st₁⟩, s₁, h1, h⟩ := bind_run h
    have hpT : ∀ a ∈ ctx.params, TOk s₀ (ctx.hiAt 0) a := by
      intro a ha
      have hok := hW.paramsOk
      simp only [OkSL, List.all_eq_true] at hok
      exact ⟨hok a ha, hpW a ha, hW.paramsCl a ha⟩
    have hrec : ∀ (s : InLean.CState) (x : Lean.Expr), OkS s x = true →
        RecSpecI fe L ctx cctx
          (InLean.nestPos .verified fe ctx (InLean.whnfWalkFuel x))
          ((fun crest => ConLeche.nestPos (ConLeche.fueledOpsM .verified) L cctx
            (ConLeche.whnfWalkFuel crest)) (TrS s x)) := by
      intro s x _
      simp only
      rw [← whnfWalkFuel_TrS s x]
      exact nestPosI_run hJ hRF _
    obtain ⟨hs₁, ht₁, ho, hst₁, hR1⟩ := nestCtorsI_run hJ
      (fuelOf := InLean.whnfWalkFuel) (rec := InLean.nestPos .verified fe ctx)
      (rec' := fun crest => ConLeche.nestPos (ConLeche.fueledOpsM .verified) L cctx
        (ConLeche.whnfWalkFuel crest)) hrec [] (ctx.hiAt 0) (ctx.lps.map .param)
      ctx.params ctx.names holes (params_okLv _) hlen cs st hs hW (fun _ h => nomatch h) hst
      hW.paramsOk hpT hh hhT (hcs cs List.mem_cons_self) h1
    obtain ⟨⟨os, st₂⟩, s₂, h2, h⟩ := bind_run h
    obtain ⟨rfl, rfl⟩ := pure_run h
    obtain ⟨hs₂, ht₂, hos, hst₂, hR2⟩ := nestRootI_run hJ hRF holes css st₁ hs₁ (hW.mono ht₁) hst₁
      (okSL_of_tabLe ht₁ hh) (TOk_all_mono ht₁ hhT)
      (fun a ha => by
        have hok := hW.paramsOk
        simp only [OkSL, List.all_eq_true] at hok
        rw [TrS_of_tabLe ht₁ (hok a ha)]; exact hpW a ha)
      hlen (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) h2
    refine ⟨hs₂, ht₁.trans ht₂, ?_, hst₂, ?_⟩
    · intro o' ho'
      rcases List.mem_cons.1 ho' with rfl | ho'
      · exact (OutOk.mono ht₂ ho).1
      · exact hos o' ho'
    · rw [TrSL_of_tabLe ht₁ hh] at hR2
      simp only [List.map_nil, params_trL] at hR1
      simp only [List.map_cons, hiAt_rel hW.canon, hW.canon.lps, hW.canon.names, hW.params]
      refine Runs.bind hR1 ?_
      refine Runs.bind hR2 ?_
      rw [(OutOk.mono ht₂ ho).2]
      exact Runs.pure _

end InLeanProof
