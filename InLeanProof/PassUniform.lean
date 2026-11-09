module

public import InLeanProof.PassNest
public import InLeanProof.QuotPres
import ConLeche.Verify.Cached.IndWalksC

/-!
# O7-stages: the canonical crest and the uniform-occurrence check (task #451, lane O7-stages)

`nestUniformI_run` (`nestUniform`'s twin): InLean's uniform-occurrence check
accepting the block's constructors means master's accepts their
translations.  Below it:

* `instLvlParamsI_params_tr`: a level instantiation parameters by
  parameters (`instLvlParamsI`, unchecked) on a term with a reading and no
  free variable has a reading, master's `instantiateLevelParams` on it: a
  parameter is `0` deep, so no level passes C's bound and no `rangePoison`
  is written (`emvarS_instantiateLevelParams` at `LvFits 0`).
* `instPisWithI_map`: InLean's `instPisWith` is master's `instPisWithC` on the reading, as
  an equation of options (`instPisWithI_tr` gives the `some` half).
* `mapM_mkFVarM_run`: a list of interned placeholders of type `Sort 0`
  (`nestPhs`, `nestCanonVars`) reads as master's free variables.
* `nestCanonSub_rel`: InLean's canonical substitution, over the interned
  placeholders, is related to master's (`SubRel`).
* `nestCanonCrestI_run`, `nestRootCanonI_run`, `nestUniformOkI_run`: the
  canonical crest, the root's crest of a constructor, and the per-constructor
  check, master's on the reading.

The proofs are functional (`bind_run`, `pure_run`), as O7's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Level instantiation at parameters -/

theorem LvFits_zero_of_RangeOk : ∀ {e : Lean.Expr}, Expr.RangeOk e → LvFits 0 e := by
  intro e
  induction e with
  | sort u => intro h; simpa [LvFits, Expr.RangeOk] using h
  | const n us => intro h; simpa [LvFits, Expr.RangeOk] using h
  | app f a ihf iha => intro h; exact ⟨ihf h.1, iha h.2⟩
  | lam _ t b _ iht ihb => intro h; exact ⟨iht h.1, ihb h.2⟩
  | forallE _ t b _ iht ihb => intro h; exact ⟨iht h.1, ihb h.2⟩
  | letE _ t v b _ iht ihv ihb => intro h; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | mdata _ x ih => intro h; exact ih h
  | proj _ _ x ih => intro h; exact ih h
  | bvar | fvar | mvar | lit => intro _; trivial

theorem maxDepthS_params : ∀ lps : List Lean.Name, maxDepthS (lps.map Level.param) = 0
  | [] => rfl
  | n :: lps => by
    have := maxDepthS_params lps
    simp only [maxDepthS, List.map_cons, List.foldr_cons] at this ⊢
    rw [this]; rfl

theorem params_okLv (lps : List Lean.Name) : (lps.map Level.param).all okLv = true := by
  simp [okLv, okL, depthS, maxLevelDepth]

theorem params_trL (lps : List Lean.Name) :
    (lps.map Level.param).map trL = (lps.map toName).map ConLeche.Level.param := by
  simp [trL]

/-- **Level instantiation parameters by parameters, read** (round 3's
finding 2): on a term with a reading and no free variable, InLean's
unchecked `instLvlParamsI` at level parameters has a reading, master's
`instantiateLevelParams` on it. -/
theorem instLvlParamsI_params_tr {s : InLean.CState} {e : Lean.Expr} (he : OkS s e = true)
    (hf : fvarS e = false) (ps lps : List Lean.Name) :
    OkS s (e.instLvlParamsI ps (lps.map Level.param)) = true ∧
      TrS s (e.instLvlParamsI ps (lps.map Level.param)) =
        (TrS s e).instantiateLevelParams (ps.map toName) ((lps.map toName).map ConLeche.Level.param) := by
  have hr := RangeOk_of_OkS he
  have hus : ∀ u ∈ lps.map Level.param, depthS u ≤ maxLevelDepth := by
    intro u hu
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hu
    simp [depthS, maxLevelDepth]
  have hm := emvarS_instantiateLevelParams ps (lps.map Level.param) hr
    (emvarS_of_toExpr (TransS_of_ok he)) hus (by rw [maxDepthS_params]; exact LvFits_zero_of_RangeOk hr)
  have h := toExpr_instantiateLevelParams (fv := FVarTable.trans (tableOf s)) hr hf (TransS_of_ok he)
    ps (toLevels_of_okLv (params_okLv lps)) hm
  rw [params_trL] at h
  exact ok_of_TransS (RangeOk_instantiateLevelParams ps _ hr hus) h

/-! ## Instantiating leading binders, as options -/

/-- **InLean's `instPisWith`, read, both answers**: master's on the
readings. -/
theorem instPisWithI_map {s : InLean.CState} :
    ∀ (as : List Lean.Expr) (e : Lean.Expr), OkS s e = true → OkSL s as = true →
      (∀ a ∈ as, (TrS s a).looseBVarsBounded 0 = true) →
      (InLean.instPisWith as e).map (TrS s) = ConLeche.Expr.instPisWithC (TrSL s as) (TrS s e)
  | [], e, _, _, _ => by simp [InLean.instPisWith, ConLeche.Expr.instPisWithC, TrSL]
  | a :: as, .forallE n t b bi, he, ha, hc => by
    simp only [OkS_forallE, Bool.and_eq_true] at he
    simp only [OkSL_cons, Bool.and_eq_true] at ha
    have hca := hc a List.mem_cons_self
    have hb' := OkS_inst1 he.2 ha.1 hca
    simp only [InLean.instPisWith]
    rw [TrS_forallE, TrSL_cons, ConLeche.Expr.instPisWithC, ConLeche.Expr.instantiate1C_spec,
      ← TrS_inst1_eq he.2 ha.1 hca, ← inst1I_eq]
    exact instPisWithI_map as _ hb' ha.2 (fun x hx => hc x (List.mem_cons_of_mem _ hx))
  | a :: as, .mdata m e, he, ha, hc => by
    rw [OkS_mdata] at he
    simp only [InLean.instPisWith]
    rw [TrS_mdata]
    exact instPisWithI_map (a :: as) e he ha hc
  | _ :: _, .fvar _, he, _, _ => by
    rw [TrS_fvar he]; simp [InLean.instPisWith, TrSL, ConLeche.Expr.instPisWithC]
  | _ :: _, .mvar _, he, _, _ => by simp [OkS, okE] at he
  | _ :: _, .bvar _, _, _, _ | _ :: _, .sort _, _, _, _
  | _ :: _, .const _ _, _, _, _ | _ :: _, .app _ _, _, _, _
  | _ :: _, .lam _ _ _ _, _, _, _ | _ :: _, .letE _ _ _ _ _, _, _, _
  | _ :: _, .lit _, _, _, _ | _ :: _, .proj _ _ _, _, _, _ => by
    simp [InLean.instPisWith, TrSL, TrS_bvar, TrS_sort, TrS_const, TrS_app, TrS_lam, TrS_letE,
      TrS_lit, TrS_proj, ConLeche.Expr.instPisWithC]

/-! ## Interned placeholders -/

/-- **A list of interned placeholders of type `Sort 0`** at depths `g i`:
master's free variables, read at the final state. -/
theorem mapM_mkFVarM_run (g : Nat → Nat) :
    ∀ (l : List Nat) {s₀ s' : InLean.CState} {xs : List Lean.Expr},
      CSOKI mode eager env s₀ →
      l.mapM (fun i => InLean.mkFVarM (g i) (.sort .zero)) s₀ = .ok (xs, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkSL s' xs = true ∧
        TrSL s' xs = l.map fun i => .fvar (g i) (.sort .zero)
  | [], s₀, s', xs, hs, h => by
    simp only [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, rfl, rfl⟩
  | i :: l, s₀, s', xs, hs, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨x, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hokx, htx⟩ :=
      tripleI_iff_run.1 (mkFVarM_specI hs (g i) (ty := .sort .zero) rfl rfl) x s₁ h1
    obtain ⟨xs', s₂, h2, h⟩ := bind_run h
    obtain ⟨hs₂, ht₂, hok₂, htr₂⟩ := mapM_mkFVarM_run g l hs₁ h2
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs₂, ht₁.trans ht₂, ?_, ?_⟩
    · simp only [OkSL_cons, okS_of_tabLe ht₂ hokx, hok₂, Bool.and_self]
    · rw [TrSL_cons, htr₂, TrS_of_tabLe ht₂ hokx, htx]
      rfl

/-! ## The canonical substitution -/

theorem map_trL_beq {v us : List Lean.Level} (hv : v.all okLv = true) (hus : us.all okLv = true) :
    (v.map trL == us.map trL) = (v == us) := by
  induction v generalizing us with
  | nil => cases us <;> rfl
  | cons a v ih =>
    cases us with
    | nil => rfl
    | cons b us =>
      simp only [List.all_cons, Bool.and_eq_true] at hv hus
      simp only [List.map_cons, List.cons_beq_cons, ih hv.2 hus.2]
      congr 1
      have ha : okL a = true := by simp only [okLv, Bool.and_eq_true] at hv; exact hv.1.1
      have hb : okL b = true := by simp only [okLv, Bool.and_eq_true] at hus; exact hus.1.1
      by_cases h : a = b
      · subst h; simp
      · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (fun he => h (trL_inj ha hb he))]

/-- **The canonical substitution, related** (`nestCanonSub`): over the
interned placeholders of the members, InLean's images read as master's. -/
theorem nestCanonSub_rel {s : InLean.CState} {names : List Lean.Name} {us : List Lean.Level}
    {vars : List Lean.Expr} (n : Nat) (hus : us.all okLv = true) (hok : OkSL s vars = true)
    (htr : TrSL s vars = (List.range names.length).map fun m => .fvar (n + m) (.sort .zero)) :
    SubRel s (InLean.nestCanonSub names us vars)
      (ConLeche.nestCanonSub (names.map toName) (us.map trL) n) := by
  intro c v hv
  simp only [InLean.nestCanonSub, ConLeche.nestCanonSub, map_trL_beq hv hus, findIdx?_map_toName]
  cases hb : v == us with
  | false => exact ⟨rfl, fun _ h => by simp at h⟩
  | true =>
    simp only [↓reduceIte]
    cases hi : names.findIdx? (· == c) with
    | none => exact ⟨rfl, fun _ h => by simp at h⟩
    | some m =>
      have hm : m < names.length := (List.findIdx?_eq_some_iff_getElem.1 hi).1
      have hlen : vars.length = names.length := by
        have := congrArg List.length htr
        simpa [TrSL] using this
      have hx : (TrSL s vars)[m]? = some (.fvar (n + m) (.sort .zero)) := by
        rw [htr]; simp [hm]
      obtain ⟨x, hxv⟩ : ∃ x, vars[m]? = some x := by
        exact ⟨vars[m]'(by omega), List.getElem?_eq_getElem _⟩
      rw [TrSL_getElem? hxv] at hx
      simp only [Option.bind_some, hxv, Option.map_some, Option.some.injEq]
      exact ⟨Option.some.inj hx, fun y hy => by cases hy; exact okS_getElem? hok hxv⟩

/-! ## The canonical crest -/

/-- **The canonical crest, read** (`nestCanonCrest`): an answer reads, at
the final state, as master's on the reading. -/
theorem nestCanonCrestI_run {names : List Lean.Name} {us : List Lean.Level} {n : Nat}
    {cty : Lean.Expr} {s₀ s' : InLean.CState} {r : Option Lean.Expr}
    (hs : CSOKI mode eager env s₀) (hus : us.all okLv = true) (hok : OkS s₀ cty = true)
    (h : InLean.nestCanonCrest names us n cty s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ (∀ y, r = some y → OkS s' y = true) ∧
      r.map (TrS s') = ConLeche.nestCanonCrest (names.map toName) (us.map trL) n (TrS s₀ cty) := by
  unfold InLean.nestCanonCrest at h
  obtain ⟨phs, s₁, h1, h⟩ := bind_run h
  unfold InLean.nestPhs at h1
  obtain ⟨hs₁, ht₁, hokp, htrp⟩ := mapM_mkFVarM_run (mode := mode) (eager := eager) (env := env)
    (fun i => i) (List.range n) hs h1
  obtain ⟨vars, s₂, h2, h⟩ := bind_run h
  unfold InLean.nestCanonVars at h2
  obtain ⟨hs₂, ht₂, hokv, htrv⟩ := mapM_mkFVarM_run (mode := mode) (eager := eager) (env := env)
    (fun m => n + m) (List.range names.length) hs₁ h2
  obtain ⟨rfl, rfl⟩ := pure_run h
  have ht12 := ht₁.trans ht₂
  have hokc := okS_of_tabLe ht12 hok
  have hokp₂ := okSL_of_tabLe ht₂ hokp
  have htrp₂ : TrSL s₂ phs = ConLeche.nestPhs n := by
    rw [TrSL_of_tabLe ht₂ hokp, htrp]; rfl
  have hclp : ∀ a ∈ phs, (TrS s₂ a).looseBVarsBounded 0 = true := by
    intro a ha
    have : TrS s₂ a ∈ TrSL s₂ phs := List.mem_map_of_mem ha
    rw [htrp₂] at this
    obtain ⟨i, -, he⟩ := List.mem_map.1 this
    rw [← he]; rfl
  have hR := nestCanonSub_rel (s := s₂) (names := names) n hus hokv htrv
  have hmap := instPisWithI_map phs cty hokc hokp₂ hclp
  rw [ConLeche.Expr.instPisWithC_eq] at hmap
  rw [htrp₂, TrS_of_tabLe ht12 hok] at hmap
  unfold ConLeche.nestCanonCrest
  rw [← hmap]
  refine ⟨hs₂, ht12, ?_, ?_⟩
  · intro y hy
    obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.1 hy
    obtain ⟨hok0, -⟩ := instPisWithI_tr phs cty hokc hokp₂ hclp hr0
    rw [replaceApps_eq]
    exact (replaceAppsI_tr hR 0 n r0 0 hok0).1
  · cases hr0 : InLean.instPisWith phs cty with
    | none => rfl
    | some r0 =>
      obtain ⟨hok0, -⟩ := instPisWithI_tr phs cty hokc hokp₂ hclp hr0
      simp only [Option.map_some, replaceApps_eq]
      rw [(replaceAppsI_tr hR 0 n r0 0 hok0).2]

/-! ## The root's crest and the uniform-occurrence check -/

/-- What the canonical crest and the uniform-occurrence check read of the
two contexts: the members' names, the level parameters, the parameter
count. -/
structure CanonRel (ctx : InLean.NestCtx) (cctx : ConLeche.NestCtx) : Prop where
  names : cctx.names = ctx.names.map toName
  lps : cctx.lps = ctx.lps.map toName
  nP : cctx.nP = ctx.nP

theorem hiAt_rel {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hR : CanonRel ctx cctx) (nf : Nat) :
    cctx.hiAt nf = ctx.hiAt nf := by
  simp [ConLeche.NestCtx.hiAt, InLean.NestCtx.hiAt, hR.names, hR.nP]

/-- **The root's crest of a stored constructor** (`nestRootCanon`): an answer
reads, at the final state, as master's at the translated constructor. -/
theorem nestRootCanonI_run {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hR : CanonRel ctx cctx)
    {cv : Lean.ConstantVal} (hok : okC cv.type = true) {s₀ s' : InLean.CState} {r : Option Lean.Expr}
    (hs : CSOKI mode eager env s₀) (h : InLean.nestRootCanon ctx cv s₀ = .ok (r, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ (∀ y, r = some y → OkS s' y = true) ∧
      r.map (TrS s') = ConLeche.nestRootCanon cctx (trCV cv) := by
  unfold InLean.nestRootCanon at h
  obtain ⟨hokI, htrI⟩ := instLvlParamsI_params_tr (OkS_of_okC s₀ hok) (fvarS_of_okC hok)
    cv.levelParams ctx.lps
  obtain ⟨hs', ht', hokr, htr⟩ := nestCanonCrestI_run hs (params_okLv ctx.lps) hokI h
  refine ⟨hs', ht', hokr, ?_⟩
  rw [htr, htrI, TrS_of_okC _ hok, params_trL]
  unfold ConLeche.nestRootCanon
  simp only [trCV, hR.names, hR.lps, hR.nP]

/-- **The uniform-occurrence check at one constructor** (`nestUniformOk`):
InLean's answer is master's at the translated constructor. -/
theorem nestUniformOkI_run {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hR : CanonRel ctx cctx)
    {cv : Lean.ConstantVal} (hok : okC cv.type = true) {s₀ s' : InLean.CState} {b : Bool}
    (hs : CSOKI mode eager env s₀) (h : InLean.nestUniformOk ctx cv s₀ = .ok (b, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ b = ConLeche.nestUniformOk cctx (trCV cv) := by
  have hpd := piDomsOccI_tr (s := s₀) ctx.names ctx.nP (ctx.hiAt 0) ctx.nP cv.type
    (OkS_of_okC s₀ hok)
  rw [TrS_of_okC _ hok] at hpd
  unfold ConLeche.nestUniformOk
  simp only [trCV_type, hR.names, hR.nP, hiAt_rel hR]
  rw [← hpd]
  unfold InLean.nestUniformOk at h
  cases hp : InLean.piDomsOcc ctx.names ctx.nP (ctx.hiAt 0) ctx.nP cv.type with
  | true =>
    simp only [hp, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, rfl⟩
  | false =>
    simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨o, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hoko, htro⟩ := nestRootCanonI_run hR hok hs h1
    simp only [Bool.not_false, Bool.true_and]
    rw [← htro]
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := pure_run h
      exact ⟨hs₁, ht₁, rfl⟩
    | some crest =>
      obtain ⟨rfl, rfl⟩ := pure_run h
      refine ⟨hs₁, ht₁, ?_⟩
      simp only [Option.map_some]
      rw [nestOccI_tr ctx.names 0 0 (hoko crest rfl)]

/-- **A `for` loop with no state and no early exit** (each iteration yields
or throws): a run from `CSOKI` ends in `CSOKI`, the table grows, and every
element met satisfies what its iteration establishes. -/
theorem forIn_unit_run {α : Type} :
    ∀ (l : List α) (f : α → PUnit → InLean.CheckCM (ForInStep PUnit)) (P : α → Prop),
      (∀ c ∈ l, ∀ (t t' : InLean.CState) (st : ForInStep PUnit), CSOKI mode eager env t →
        f c PUnit.unit t = .ok (st, t') →
        st = .yield PUnit.unit ∧ P c ∧ CSOKI mode eager env t' ∧ TabLe t t') →
      ∀ {t₀ t₁ : InLean.CState} {u : PUnit}, CSOKI mode eager env t₀ →
        forIn l PUnit.unit f t₀ = .ok (u, t₁) →
        CSOKI mode eager env t₁ ∧ TabLe t₀ t₁ ∧ ∀ c ∈ l, P c
  | [], _, _, _, t₀, t₁, u, ht, h => by
    rw [List.forIn_nil] at h
    obtain ⟨-, rfl⟩ := pure_run h
    exact ⟨ht, TabLe.refl _, by simp⟩
  | c :: l, f, P, hf, t₀, t₁, u, ht, h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, t₂, h1, h⟩ := bind_run h
    obtain ⟨rfl, hP, ht₂, htt⟩ := hf c List.mem_cons_self t₀ t₂ st ht h1
    obtain ⟨ht', htt', hall⟩ := forIn_unit_run l f P
      (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')) ht₂ h
    refine ⟨ht', htt.trans htt', ?_⟩
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact hP
    · exact hall c' hc'

/-- **The uniform-occurrence check** (`nestUniform`): InLean's check passing
means master's passes on the translated constructors. -/
theorem nestUniformI_run {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hR : CanonRel ctx cctx)
    {ctorss : List (List (Lean.ConstantVal × Nat))}
    (hok : ∀ cs ∈ ctorss, ∀ c ∈ cs, okC c.1.type = true) {s₀ s' : InLean.CState} {v : Unit}
    (hs : CSOKI mode eager env s₀) (h : InLean.nestUniform ctx ctorss s₀ = .ok (v, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.nestUniform (m := ConLeche.FueledM) cctx (ctorss.map (·.map trCtor))) () := by
  suffices H : CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      ∀ cs ∈ ctorss, ∀ c ∈ cs, ConLeche.nestUniformOk cctx (trCV c.1) = true by
    obtain ⟨hs', ht', hall⟩ := H
    refine ⟨hs', ht', ?_⟩
    unfold ConLeche.nestUniform
    have hn : (ctorss.map (·.map trCtor)).findSome? (·.find? (!ConLeche.nestUniformOk cctx ·.1)) =
        none := by
      rw [List.findSome?_eq_none_iff]
      intro cs hcs
      obtain ⟨cs0, hcs0, rfl⟩ := List.mem_map.1 hcs
      rw [List.find?_eq_none]
      intro c hc
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
      simp [trCtor, hall cs0 hcs0 c0 hc0]
    rw [hn]
    exact Runs.pure _
  unfold InLean.nestUniform at h
  obtain ⟨u, s₁, h1, h⟩ := bind_run h
  obtain ⟨-, rfl⟩ := pure_run h
  refine forIn_unit_run (mode := mode) (eager := eager) (env := env) ctorss _
    (fun cs => ∀ c ∈ cs, ConLeche.nestUniformOk cctx (trCV c.1) = true) ?_ hs h1
  intro cs hcs t t' st ht hrun
  obtain ⟨u, t₂, h2, hrun⟩ := bind_run hrun
  obtain ⟨rfl, rfl⟩ := pure_run hrun
  obtain ⟨ht', htt, hall⟩ := forIn_unit_run (mode := mode) (eager := eager) (env := env) cs _
    (fun c => ConLeche.nestUniformOk cctx (trCV c.1) = true) (fun c hc t t' st ht hrun => by
      obtain ⟨b, t₂, hb, hrun⟩ := bind_run hrun
      obtain ⟨ht₂, htt₂, rfl⟩ := nestUniformOkI_run hR (hok cs hcs c hc) ht hb
      cases hbv : ConLeche.nestUniformOk cctx (trCV c.1) with
      | false =>
        simp only [hbv, Bool.false_eq_true, ↓reduceIte] at hrun
        obtain ⟨_, _, h3, -⟩ := bind_run hrun
        exact (throw_run h3).elim
      | true =>
        simp only [hbv, ↓reduceIte] at hrun
        obtain ⟨rfl, rfl⟩ := pure_run hrun
        exact ⟨rfl, rfl, ht₂, htt₂⟩) ht h2
  exact ⟨rfl, hall, ht', htt⟩

end InLeanProof
