module

public import InLeanProof.PassNestPos0
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.ReplaceApps

/-!
# O7-positivity: the positivity walk against master's (task #451, lane O7-positivity)

The walk's monadic steps, each master's on the readings of
`PassNestPos0.lean`, functional (`bind_run`, `pure_run`) as O7's:

* `RecSpecI`: what a walk's recursive call provides (the twin of master's
  cached `RecSpec`, `Verify/Cached/NestPosC.lean`): at a readable input,
  well scoped at its depth and closed, a successful run answers master's
  on the readings, its normal form readable, scoped and closed, the state's
  records readable.
* `nestFieldsI_run`: a constructor's field telescope through the recursion.
* `nestCrestI_run`, `lbb_nestCrest`: a stored constructor at a key, and its
  closedness on master's side.
* `nestGroupCtorsI_run`, `nestGrowGroupI_run` (`GrpOk`: a group's hole types
  readable, closed, scoped wherever the key's parameters are): a frame's
  group.
* `nestWalkStack_tr`: the stack an instantiation is walked under.
-/

public section

namespace InLeanProof

open Lean InLean ConLeche.Cached

/-- A term with a reading at a state, well scoped at depth `d` and closed. -/
@[expose] def TOk (s : InLean.CState) (d : Nat) (e : Lean.Expr) : Prop :=
  OkS s e = true ∧ ConLeche.Expr.WScoped d (TrS s e) ∧ (TrS s e).looseBVarsBounded 0 = true

theorem TOk.mono {s₀ s₁ : InLean.CState} (ht : TabLe s₀ s₁) {d : Nat} {e : Lean.Expr}
    (h : TOk s₀ d e) : TOk s₁ d e ∧ TrS s₁ e = TrS s₀ e := by
  have he := TrS_of_tabLe ht h.1
  exact ⟨⟨okS_of_tabLe ht h.1, he ▸ h.2.1, he ▸ h.2.2⟩, he⟩

/-- **The triple a walk's recursive call provides** (master's `RecSpec`'s
twin). -/
@[expose] def RecSpecI (fe : InLean.FEnv) (L : ConLeche.Env) (ctx : InLean.NestCtx)
    (cctx : ConLeche.NestCtx) (rec : InLean.NestRec)
    (rec' : List ConLeche.NestHole → Nat → Nat → ConLeche.Expr → ConLeche.NestState →
      ConLeche.FueledM (ConLeche.NestFieldKind × ConLeche.Expr × ConLeche.NestState)) : Prop :=
  ∀ (prog : List InLean.NestHole) (dep kb : Nat) (e : Lean.Expr) (st : InLean.NestState)
    {s₀ s' : InLean.CState} {v : InLean.NestFieldKind × Lean.Expr × InLean.NestState},
    CSOKI .verified false L s₀ → WalkRel fe L s₀ ctx cctx → ProgOk s₀ prog → StOk s₀ st →
    TOk s₀ dep e → rec prog dep kb e st s₀ = .ok (v, s') →
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ TOk s' dep v.2.1 ∧ StOk s' v.2.2 ∧
      Runs (rec' (prog.map (trHole s₀)) dep kb (TrS s₀ e) (trSt s₀ st))
        (trNK v.1, TrS s' v.2.1, trSt s' v.2.2)

/-- A telescope of readable domains, the `k`-th scoped at `i + k`, all closed. -/
@[expose] def TeleOk (s : InLean.CState) (i : Nat) (nds : List Lean.Expr) : Prop :=
  OkSL s nds = true ∧ TeleWS i (TrSL s nds) ∧ ∀ nd ∈ nds, (TrS s nd).looseBVarsBounded 0 = true

theorem TeleOk.mono {s₀ s₁ : InLean.CState} (ht : TabLe s₀ s₁) {i : Nat} {nds : List Lean.Expr}
    (h : TeleOk s₀ i nds) : TeleOk s₁ i nds ∧ TrSL s₁ nds = TrSL s₀ nds := by
  have he := TrSL_of_tabLe ht h.1
  exact ⟨⟨okSL_of_tabLe ht h.1, he ▸ h.2.1, closed_of_tabLe ht h.1 h.2.2⟩, he⟩

/-- **A constructor's field telescope** (`nestFields`): each field through
the recursion at its depth, opened at an interned variable; master's on the
readings (at any error value: only the success is simulated). -/
theorem nestFieldsI_run {fe : InLean.FEnv} {L : ConLeche.Env} {ctx : InLean.NestCtx}
    {cctx : ConLeche.NestCtx} {rec : InLean.NestRec}
    {rec' : List ConLeche.NestHole → Nat → Nat → ConLeche.Expr → ConLeche.NestState →
      ConLeche.FueledM (ConLeche.NestFieldKind × ConLeche.Expr × ConLeche.NestState)}
    (hrec : RecSpecI fe L ctx cctx rec rec') (prog : List InLean.NestHole) (base : Nat)
    (err : InLean.CheckError) (err' : ConLeche.CheckError) :
    ∀ (nF j : Nat) (cur : Lean.Expr) (st : InLean.NestState) {s₀ s' : InLean.CState}
      {v : List InLean.NestFieldKind × List Lean.Expr × Lean.Expr × InLean.NestState},
      CSOKI .verified false L s₀ → WalkRel fe L s₀ ctx cctx → ProgOk s₀ prog → StOk s₀ st →
      TOk s₀ (base + j) cur →
      InLean.nestFields rec prog base err nF j cur st s₀ = .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ TeleOk s' (base + j) v.2.1 ∧
        TOk s' (base + j + v.2.1.length) v.2.2.1 ∧ StOk s' v.2.2.2 ∧
        Runs (ConLeche.nestFields rec' (prog.map (trHole s₀)) base err' nF j (TrS s₀ cur)
          (trSt s₀ st)) (v.1.map trNK, TrSL s' v.2.1, TrS s' v.2.2.1, trSt s' v.2.2.2)
  | 0, j, cur, st, s₀, s', v, hs, _, _, hst, hcur, h => by
    unfold InLean.nestFields at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, ⟨rfl, by simp [TrSL, TeleWS], by simp⟩, by simpa using hcur, hst, ?_⟩
    unfold ConLeche.nestFields
    exact Runs.pure _
  | nF + 1, j, cur, st, s₀, s', v, hs, hW, hp, hst, hcur, h => by
    unfold InLean.nestFields at h
    have hT : TrS s₀ cur = TrS s₀ (EO.stripTop cur) := (TrS_stripTop s₀ cur).symm
    have hOk : OkS s₀ (EO.stripTop cur) = true := by rw [OkS_stripTop]; exact hcur.1
    have hnm : ∀ m b, EO.stripTop cur ≠ .mdata m b := fun m b he => stripTop_ne_mdata he
    obtain ⟨-, hwc, hcc⟩ := hcur
    rw [hT] at hwc hcc ⊢
    generalize EO.stripTop cur = x at h hOk hnm hwc hcc
    cases x with
    | forallE nm a b bi =>
      simp only at h
      simp only [OkS_forallE, Bool.and_eq_true] at hOk
      rw [TrS_forallE] at hwc hcc ⊢
      rw [lbb_forallE, Bool.and_eq_true] at hcc
      simp only [ConLeche.Expr.WScoped] at hwc
      obtain ⟨⟨k, nd, st₁⟩, s₁, h1, h⟩ := bind_run h
      obtain ⟨hs₁, ht₁, hnd, hst₁, hR1⟩ :=
        hrec prog (base + j) 0 a st hs hW hp hst ⟨hOk.1, hwc.1, hcc.1⟩ h1
      obtain ⟨r, s₂, h2, h⟩ := bind_run h
      have hoka₁ := okS_of_tabLe ht₁ hOk.1
      have hta₁ := TrS_of_tabLe ht₁ hOk.1
      obtain ⟨hs₂, ht₂, hokr, htrr⟩ := tripleI_iff_run.1
        (mkFVarM_specI hs₁ (base + j) hoka₁ (by rw [hta₁]; exact hcc.1)) r s₂ h2
      rw [hta₁] at htrr
      obtain ⟨⟨ks, nds, res, st₂⟩, s₃, h3, h⟩ := bind_run h
      obtain ⟨rfl, rfl⟩ := pure_run h
      have ht12 := ht₁.trans ht₂
      have hokb := okS_of_tabLe ht12 hOk.2
      have htb := TrS_of_tabLe ht12 hOk.2
      have hrcl : (TrS s₂ r).looseBVarsBounded 0 = true := by
        rw [htrr]; rfl
      have hTI : TrS s₂ (b.inst1I r) =
          (TrS s₀ b).instantiate1 (.fvar (base + j) (TrS s₀ a)) 0 := by
        rw [inst1I_eq, TrS_inst1_eq hokb hokr hrcl, htb, htrr]
      have hcur₂ : TOk s₂ (base + (j + 1)) (b.inst1I r) := by
        refine ⟨OkS_inst1 hokb hokr hrcl, ?_, ?_⟩
        · rw [hTI, show base + (j + 1) = base + j + 1 by omega]
          exact ConLeche.Expr.WScoped.instantiate1 hwc.1 0 hwc.2
        · rw [hTI]; exact lbb_instantiate1 rfl hcc.2
      obtain ⟨hW₂, hp₂, hst₂⟩ : WalkRel fe L s₂ ctx cctx ∧ ProgOk s₂ prog ∧ StOk s₂ st₁ :=
        ⟨hW.mono ht12, (hp.mono ht12).1, (hst₁.mono ht₂).1⟩
      obtain ⟨hs₃, ht₃, hnds, hres, hst₃, hR3⟩ :=
        nestFieldsI_run hrec prog base err err' nF (j + 1) (b.inst1I r) st₁ hs₂ hW₂ hp₂ hst₂
          hcur₂ h3
      have ht23 := ht₂.trans ht₃
      obtain ⟨hnd₃, hndE⟩ := TOk.mono ht23 hnd
      refine ⟨hs₃, ht12.trans ht₃, ⟨?_, ?_, ?_⟩, ?_, hst₃, ?_⟩
      · simp only [OkSL_cons, hnd₃.1, hnds.1, Bool.and_self]
      · rw [TrSL_cons, TeleWS.cons_eq, hndE]
        exact ⟨hnd.2.1, by rw [show base + j + 1 = base + (j + 1) by omega]; exact hnds.2.1⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hnd₃.2.2
        · exact hnds.2.2 x hx
      · simp only [List.length_cons, show base + j + (nds.length + 1) = base + (j + 1) + nds.length
          by omega]
        exact hres
      · unfold ConLeche.nestFields
        simp only
        refine Runs.bind hR1 ?_
        rw [hTI, (hp.mono ht12).2] at hR3
        have hst12 : trSt s₂ st₁ = trSt s₁ st₁ := (hst₁.mono ht₂).2
        rw [hst12] at hR3
        simp only [List.map_cons, TrSL_cons, hndE]
        refine Runs.bind hR3 ?_
        exact Runs.pure _
    | mdata m b => exact (hnm m b rfl).elim
    | _ => simp only at h; exact (throw_run h).elim

/-! ## A constructor at a key -/

/-- **A stored constructor type at a key** (`nestCrest`): an answer reads, at
the final state, as master's on the readings. -/
theorem nestCrestI_run {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}
    {names : List Lean.Name} {us : List Lean.Level} {ds holes : List Lean.Expr}
    {cty : Lean.Expr} {s₀ s' : InLean.CState} {r : Option Lean.Expr}
    (hs : CSOKI mode eager env s₀) (hus : us.all okLv = true) (hok : OkS s₀ cty = true)
    (hds : OkSL s₀ ds = true) (hh : OkSL s₀ holes = true)
    (h : InLean.nestCrest names us ds holes cty s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ (∀ y, r = some y → OkS s' y = true) ∧
      r.map (TrS s') = ConLeche.nestCrest (names.map toName) (us.map trL) (TrSL s₀ ds)
        (TrSL s₀ holes) (TrS s₀ cty) := by
  unfold InLean.nestCrest at h
  obtain ⟨c, s₁, h1, h⟩ := bind_run h
  obtain ⟨rfl, rfl⟩ := pure_run h
  obtain ⟨hs₁, ht₁, hokc, htrc⟩ := nestCanonCrestI_run hs hus hok h1
  have hds₁ := okSL_of_tabLe ht₁ hds
  have hh₁ := okSL_of_tabLe ht₁ hh
  have hF := nestKeyMap_sub hds₁ hh₁
  rw [TrSL_of_tabLe ht₁ hds, TrSL_of_tabLe ht₁ hh] at hF
  refine ⟨hs₁, ht₁, ?_, ?_⟩
  · intro y hy
    obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.1 hy
    exact (replaceFVarsI_tr hF (hokc c0 hc0)).1
  · unfold ConLeche.nestCrest
    have hlen : (TrSL s₀ ds).length = ds.length := by simp [TrSL]
    rw [hlen, ← htrc]
    cases c with
    | none => rfl
    | some c0 =>
      simp only [Option.map_some]
      rw [(replaceFVarsI_tr hF (hokc c0 rfl)).2]

/-- A crest of a closed constructor type at closed variables is closed. -/
theorem lbb_nestCrest {names : List ConLeche.Name} {us : List ConLeche.Level}
    {ds holes : List ConLeche.Expr} {cty crest : ConLeche.Expr}
    (hb : cty.looseBVarsBounded 0 = true)
    (hds : ∀ x ∈ ds, x.looseBVarsBounded 0 = true)
    (hh : ∀ x ∈ holes, x.looseBVarsBounded 0 = true)
    (h : ConLeche.nestCrest names us ds holes cty = some crest) :
    crest.looseBVarsBounded 0 = true := by
  unfold ConLeche.nestCrest ConLeche.nestCanonCrest at h
  obtain ⟨c1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨c0, h0, rfl⟩ := Option.map_eq_some_iff.1 h1
  have hc0 : c0.looseBVarsBounded 0 = true := by
    refine ConLeche.looseBVarsBounded_instPisWith (as := ConLeche.nestPhs ds.length) ?_ hb h0
    intro a ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
    rfl
  have hc1 := ConLeche.Expr.looseBVarsBounded_replaceApps (f := ConLeche.nestCanonSub names us ds.length)
    (b := 0) (n := ds.length) (by
      intro c v hv hvs
      unfold ConLeche.nestCanonSub at hvs
      split at hvs
      · obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.1 hvs; rfl
      · cases hvs) c0 0 hc0
  refine ConLeche.looseBVarsBounded_replaceFVars (g := ConLeche.nestKeyMap ds holes) ?_ _ 0 hc1
  intro i r hr
  unfold ConLeche.nestKeyMap at hr
  split at hr
  · exact hds r (List.mem_of_getElem? hr)
  · exact hh r (List.mem_of_getElem? hr)

/-! ## A frame's group -/

/-- **A group's constructors** (`nestGroupCtors`): master's at the readings;
the state does not change. -/
theorem nestGroupCtorsI_run {fe : InLean.FEnv} {L : ConLeche.Env} {s : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L)
    (hW : WalkRel fe L s ctx cctx) (nPc : Nat) :
    ∀ (cs : List Lean.Name) {s₀ s' : InLean.CState} {v : List (Lean.ConstantVal × Nat)},
      InLean.nestGroupCtors ctx nPc cs s₀ = .ok (v, s') →
      s' = s₀ ∧ Runs (ConLeche.nestGroupCtors (m := ConLeche.FueledM) cctx nPc (cs.map toName))
        (trCtorL v)
  | [], s₀, s', v, h => by
    unfold InLean.nestGroupCtors at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨rfl, by unfold ConLeche.nestGroupCtors; exact Runs.pure _⟩
  | c :: cs, s₀, s', v, h => by
    unfold InLean.nestGroupCtors at h
    obtain ⟨q, s₁, h1, h⟩ := bind_run h
    have hc := nestContainer_tr hJ hW c
    unfold ConLeche.nestGroupCtors
    simp only [List.map_cons]
    rw [hc]
    cases hq : InLean.nestContainer ctx c with
    | none => rw [hq] at h1; exact (throw_run h1).elim
    | some q' =>
    rw [hq] at h1
    obtain ⟨rfl, rfl⟩ := pure_run h1
    obtain ⟨nPc', ctors⟩ := q'
    simp only [Option.map_some, ConLeche.unwrapOr] at h ⊢
    have hE : (trCtorL ctors).isEmpty = ctors.isEmpty := by
      cases ctors <;> rfl
    by_cases hb : (nPc' == nPc || ctors.isEmpty) = true
    · simp only [hb, ↓reduceIte] at h
      obtain ⟨rest, s₃, h3, h⟩ := bind_run h
      obtain ⟨rfl, rfl⟩ := pure_run h
      obtain ⟨rfl, hR⟩ := nestGroupCtorsI_run hJ hW nPc cs h3
      refine ⟨rfl, Runs.bind (Runs.pure _) ?_⟩
      simp only [hE, hb, ↓reduceIte]
      refine Runs.bind hR ?_
      rw [trCtorL_append]
      exact Runs.pure _
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨_, _, h2, -⟩ := bind_run h
      exact (throw_run h2).elim

/-- A list of terms readable, closed and scoped wherever `ds` is. -/
@[expose] def GrpOk (s : InLean.CState) (ds : List Lean.Expr) (grp : List (Lean.Name × Lean.Expr)) :
    Prop :=
  ∀ x ∈ grp, OkS s x.2 = true ∧ (TrS s x.2).looseBVarsBounded 0 = true ∧
    ∀ d, (∀ a ∈ ds, ConLeche.Expr.WScoped d (TrS s a)) → ConLeche.Expr.WScoped d (TrS s x.2)

theorem GrpOk.mono {s₀ s₁ : InLean.CState} (ht : TabLe s₀ s₁) {ds : List Lean.Expr}
    (hds : OkSL s₀ ds = true) {grp : List (Lean.Name × Lean.Expr)} (hg : GrpOk s₀ ds grp) :
    GrpOk s₁ ds grp ∧ trGrp s₁ grp = trGrp s₀ grp := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨a1, a2, a3⟩ := hg x hx
    have he := TrS_of_tabLe ht a1
    refine ⟨okS_of_tabLe ht a1, he ▸ a2, fun d hd => he ▸ a3 d ?_⟩
    intro a ha
    rw [← TrS_of_tabLe ht (by simp only [OkSL, List.all_eq_true] at hds; exact hds a ha)]
    exact hd a ha
  · simp only [trGrp]
    apply List.map_congr_left
    intro x hx
    rw [TrS_of_tabLe ht (hg x hx).1]

/-- **A frame's group grown** (`nestGrowGroup`): each mate's instantiated
former through `nestInstType`; master's on the readings, every entry's type
readable, closed and scoped wherever the key's parameters are. -/
theorem nestGrowGroupI_run {fe : InLean.FEnv} {L : ConLeche.Env} {sW : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L)
    (hRF : ReducedFormerSimI) (hW : WalkRel fe L sW ctx cctx) {hi : Nat} {us : List Lean.Level}
    {ds : List Lean.Expr} (hus : us.all okLv = true) :
    ∀ (cs : List Lean.Name) (grp : List (Lean.Name × Lean.Expr)) {s₀ s' : InLean.CState}
      {v : List (Lean.Name × Lean.Expr)},
      CSOKI .verified false L s₀ → OkSL s₀ ds = true →
      (∀ a ∈ ds, (TrS s₀ a).looseBVarsBounded 0 = true) → GrpOk s₀ ds grp →
      InLean.nestGrowGroup ctx (sharedOpsC .verified fe) fe hi us ds cs grp s₀ = .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ GrpOk s' ds v ∧
        Runs (ConLeche.nestGrowGroup cctx (ConLeche.fueledOpsM .verified) L hi (us.map trL)
          (TrSL s₀ ds) (cs.map toName) (trGrp s₀ grp)) (trGrp s' v)
  | [], grp, s₀, s', v, hs, _, _, hg, h => by
    unfold InLean.nestGrowGroup at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, hg, by unfold ConLeche.nestGrowGroup; exact Runs.pure _⟩
  | c :: cs, grp, s₀, s', v, hs, hds, hcl, hg, h => by
    unfold InLean.nestGrowGroup at h
    obtain ⟨⟨k, cty⟩, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hok₁, hcl₁, hws₁, hR1⟩ := nestInstTypeI_run (key := ⟨c, us, ds⟩) hJ hRF
      hW.canon hW.fe hW.find hW.sort hW.sortOk hs hus hds hcl h1
    have hds₁ := okSL_of_tabLe ht₁ hds
    obtain ⟨hgm, hge⟩ := hg.mono ht₁ hds
    have hg₁ : GrpOk s₁ ds (grp ++ [(c, cty)]) := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hgm x hx
      · rw [List.mem_singleton] at hx
        subst hx
        refine ⟨hok₁, hcl₁, fun d hd => hws₁ d ?_⟩
        intro a ha
        rw [← TrS_of_tabLe ht₁ (by simp only [OkSL, List.all_eq_true] at hds; exact hds a ha)]
        exact hd a ha
    obtain ⟨hs', ht', hv, hR⟩ := nestGrowGroupI_run hJ hRF hW hus cs (grp ++ [(c, cty)]) hs₁ hds₁
      (closed_of_tabLe ht₁ hds hcl) hg₁ h
    refine ⟨hs', ht₁.trans ht', hv, ?_⟩
    unfold ConLeche.nestGrowGroup
    simp only [List.map_cons]
    refine Runs.bind hR1 ?_
    rw [TrSL_of_tabLe ht₁ hds, trGrp_append, hge] at hR
    exact hR

/-! ## The walk stack -/

/-- The parameters' hole-freeness test, read. -/
theorem allFvarB_tr {s : InLean.CState} (D : Nat) : ∀ {ds : List Lean.Expr}, OkSL s ds = true →
    (TrSL s ds).all (fun x => decide (x.fvarB ≤ D)) = ds.all (fun x => decide (InLean.fvarB x ≤ D))
  | [], _ => rfl
  | a :: l, h => by
    simp only [OkSL_cons, Bool.and_eq_true] at h
    simp only [TrSL_cons, List.all_cons, fvarB_tr h.1, allFvarB_tr D h.2]

/-- **The stack an instantiation is walked under** (`nestWalkStack`), read. -/
theorem nestWalkStack_tr {fe : InLean.FEnv} {L : ConLeche.Env} {s : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hW : WalkRel fe L s ctx cctx)
    (prog : List InLean.NestHole) {ds : List Lean.Expr} (hds : OkSL s ds = true) :
    ConLeche.nestWalkStack cctx (prog.map (trHole s)) (TrSL s ds) =
      (InLean.nestWalkStack ctx prog ds).map (trHole s) := by
  unfold ConLeche.nestWalkStack InLean.nestWalkStack
  rw [hiAt_rel hW.canon, allFvarB_tr _ hds]
  split <;> rfl

end InLeanProof
