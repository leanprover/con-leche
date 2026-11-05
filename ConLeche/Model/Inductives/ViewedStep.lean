module

public import ConLeche.Model.Inductives.DeclBlockStep
public import ConLeche.Model.Inductives.FormerSwap
public import ConLeche.Verify.EnvExt
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Semantics.Inductives.DeclBlockEta
import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Model.Env.CanonCrest
import ConLeche.Verify.BridgeDecl
import ConLeche.Model.Inductives.GenRecExtra
import ConLeche.Semantics.Tower.TowerKit

public section

/-!
# The second path of the block's install (task #480)

`checkBlock`'s second path checks a block at its reduced group and its containers' views, and
stores the group as declared.  Against the model: the input's carrier moves to the views
(`EnvModelM.toViews`: a family's view IS the former its block read, a run not seeing an
extension), the ordinary step runs there (`declBlock`), and the carrier moves to the stored
environment (`EnvModelM.ofViews`).
-/

namespace ConLeche.Model

open ConLeche ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory

universe w
variable {V : Type w} [SetTheory V]

/-! ## Ownership and coverage across a swap -/

omit [SetTheory V] in
theorem ctorLook_formerSwap {env₀ env₃ : Env} (h : FormerSwap env₀ env₃) (C n : Name) :
    ctorLook env₃.find? C n = ctorLook env₀.find? C n := by
  simp only [ctorLook]
  rcases h.find n with he | ⟨cv, cv', caps, h₀, h₃, -⟩
  · rw [he]
  · rw [h₀, h₃]; rfl

omit [SetTheory V] in
theorem nestContainer_formerSwap {env₀ env₃ : Env} (h : FormerSwap env₀ env₃) (C : Name) :
    ConLeche.nestContainer (envCtx env₃) C = ConLeche.nestContainer (envCtx env₀) C := by
  rw [nestContainer_eq, nestContainer_eq]
  show (match env₃.find? C with
      | some (.indInfo _ caps) => nestPick caps (caps.ctors.filterMap (ctorLook env₃.find? C))
      | _ => none) = (match env₀.find? C with
      | some (.indInfo _ caps) => nestPick caps (caps.ctors.filterMap (ctorLook env₀.find? C))
      | _ => none)
  have hfm : ctorLook env₃.find? C = ctorLook env₀.find? C := funext (ctorLook_formerSwap h C)
  rcases h.find C with he | ⟨cv, cv', caps, h₀, h₃, -⟩
  · rw [he]
    cases env₀.find? C with
    | none => rfl
    | some ci => cases ci <;> first | rfl | simp only [hfm]
  · rw [h₀, h₃]
    simp only [hfm]

omit [SetTheory V] in
/-- Ownership across a swap of formers: it reads their level parameters alone. -/
theorem LfpOwn.formerSwap {env₀ env₃ : Env} (h : FormerSwap env₀ env₃) {D : LfpDatum V}
    (ho : LfpOwn env₀ D) : LfpOwn env₃ D where
  ctors := fun c hc => by
    obtain ⟨nP', L, hL, hlen, hj⟩ := ho.ctors c hc
    exact ⟨nP', L, (nestContainer_formerSwap h _).trans hL, hlen, fun j hjl =>
      (h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mpr (hj j hjl)⟩
  noCtors := fun c hc nP' hL => by
    obtain ⟨cv, caps, hf, hnd, hlen, hall⟩ :=
      ho.noCtors c hc nP' ((nestContainer_formerSwap h _).symm.trans hL)
    obtain ⟨cv', hf', hl'⟩ := h.find_ind hf
    refine ⟨cv', caps, hf', hl' ▸ hnd, hlen, fun mm hmm => ?_⟩
    obtain ⟨cvm, capsm, hfm, hlm⟩ := hall mm hmm
    obtain ⟨cvm', hfm', hlm'⟩ := h.find_ind hfm
    exact ⟨cvm', capsm, hfm', by rw [hlm', hlm, hl']⟩
  lvlNodup := fun c hc => by
    obtain ⟨cv, caps, hf, hnd⟩ := ho.lvlNodup c hc
    obtain ⟨cv', hf', hl'⟩ := h.find_ind hf
    exact ⟨cv', caps, hf', hl' ▸ hnd⟩
  ctorConcl := fun c hc j hj => by
    obtain ⟨cv, nPc, nF, hf, hrest⟩ := ho.ctorConcl c hc j hj
    exact ⟨cv, nPc, nF, (h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mpr hf, hrest⟩

/-- Coverage across a swap of formers, at the same records. -/
theorem LfpCover.formerSwap {env₀ env₃ : Env} (h : FormerSwap env₀ env₃)
    {mp : EnvModelM V env₀} {mp₃ : EnvModelM V env₃} (hL : mp₃.lfpBlocks = mp.lfpBlocks)
    (hc : LfpCover mp []) : LfpCover mp₃ [] where
  cover := fun n cv caps hf hn hq => by
    obtain ⟨cv₀, hf₀, -⟩ := h.find_ind_back hf
    rw [hL]; exact hc.cover n cv₀ caps hf₀ hn hq
  nodup := fun D hD => hc.nodup D (hL ▸ hD)
  len := fun D hD => hc.len D (hL ▸ hD)
  all := fun D hD mm hmm cv caps hf => by
    obtain ⟨cv₀, hf₀, -⟩ := h.find_ind_back hf
    exact hc.all D (hL ▸ hD) mm hmm cv₀ caps hf₀
  fresh := fun _ _ _ _ hin => absurd hin List.not_mem_nil
  own := fun D hD => LfpOwn.formerSwap h (hc.own D (hL ▸ hD))
  wid := fun D hD => hc.wid D (hL ▸ hD)

/-! ## What a shown former carries past the records -/

/-- A shown former types its structure's projections where its sort is not `Prop` as written. -/
@[expose] def TowerViewTyped {env : Env} (m : EnvModel V env) (φ : Name → Nat) (T : Name)
    (f : ConstantVal) : Prop :=
  ∀ (i : Nat) (entry : ProjEntry) (s : Level), env.findProj? T i = some entry →
    ConLeche.formerResSort f.type = some s → s.isAlwaysZero = false →
    ∀ (us : List Level) (Ta : Term), us.length = entry.levelParams.length →
      denote m.acval env φ 0 (ConLeche.projTele (entry.numParams + 1)
        (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta →
      ∀ (ρ : Nat → V) (vs : List Term) (x rest : Term),
        vs.length = entry.numParams →
        WellDenoted V ρ (Term.mkAppN (m.acval T (Level.substFn φ entry.levelParams us)) vs) →
        interp V ρ (Term.mkAppN (m.acval T (Level.substFn φ entry.levelParams us)) vs) ≠ pt →
        WellDenoted V ρ x →
        interp V ρ x ∈ˢ interp V ρ (Term.mkAppN (m.acval T (Level.substFn φ entry.levelParams us)) vs) →
        Term.peelPis Ta (vs ++ [x]) = some rest →
        WellDenoted V ρ (projNV (i + 1) x) ∧ WellDenotedTy V ρ rest ∧
          interp V ρ (projNV (i + 1) x) ∈ˢ interp V ρ rest

/-- **A carrier's shown formers**: each is the reduct of its stored former at a prefix, and the
laws the block proved at it stand: its fibres, its projections, its type's grading. -/
@[expose] def ShownFacts {env : Env} (mp : EnvModelM V env) : Prop :=
  ∀ D ∈ mp.lfpBlocks, ∀ (mm : Nat) (f : ConstantVal), mm < D.k → D.shown mm = some f →
    ∀ (cv : ConstantVal) (caps : IndCaps), env.find? (D.member mm) = some (.indInfo cv caps) →
    (∃ (envB : Env) (F : Nat), EnvWF envB ∧ EnvExt envB env ∧
      cv.type.constsResolve envB = true ∧
      reducedFormer (fueledOps .verified F) envB cv (caps.nparams + caps.nIdx) = .ok f) ∧
    IndStrictAt (V := V) mp.base2.acval env (D.member mm) f ∧
    (∀ φ, TowerViewTyped mp.base2 φ (D.member mm) f) ∧
    (∀ (ψ : Name → Nat) (ta : Term), denote mp.base2.acval env ψ 0 f.type = some ta →
      ∀ ρ : Nat → V, WellDenotedTy V ρ ta)

/-- A container's view, as `blockViews` made it. -/
structure ViewFacts (env : Env) (cv cvR : ConstantVal) (caps : IndCaps) : Prop where
  find : env.find? cv.name = some (.indInfo cv caps)
  name : cvR.name = cv.name
  lps : cvR.levelParams = cv.levelParams
  headed : ConLeche.formerDefHeaded cv = true
  guard : ConLeche.litGuardFamilies.contains cv.name = false
  closed : ConLeche.viewScoped (·.constsResolve env) cvR = true
  ran : ∃ F, reducedFormer (fueledOps .verified F) env cv (caps.nparams + caps.nIdx) = .ok cvR

/-- A list of views. -/
@[expose] def ViewOf (env : Env) (c : ConstantInfo) : Prop :=
  ∃ (cv cvR : ConstantVal) (caps : IndCaps), c = .indInfo cvR caps ∧ ViewFacts env cv cvR caps

omit [SetTheory V] in
theorem find_views {env : Env} : ∀ {vs : List ConstantInfo}, (∀ c ∈ vs, ViewOf env c) → ∀ n : Name,
    (⟨vs ++ env.consts, env.tables⟩ : Env).find? n = env.find? n ∨
    ∃ (cv cvR : ConstantVal) (caps : IndCaps), cv.name = n ∧ ViewFacts env cv cvR caps ∧
      (⟨vs ++ env.consts, env.tables⟩ : Env).find? n = some (.indInfo cvR caps)
  | [], _, n => .inl rfl
  | c :: vs, hv, n => by
    obtain ⟨cv, cvR, caps, rfl, hF⟩ := hv c List.mem_cons_self
    by_cases hn : cv.name = n
    · subst hn
      refine .inr ⟨cv, cvR, caps, rfl, hF, ?_⟩
      show List.find? _ (.indInfo cvR caps :: (vs ++ env.consts)) = _
      rw [List.find?_cons_of_pos (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, hF.name])]
    · have htail : (⟨ConstantInfo.indInfo cvR caps :: vs ++ env.consts, env.tables⟩ : Env).find? n =
          (⟨vs ++ env.consts, env.tables⟩ : Env).find? n := by
        show List.find? _ (.indInfo cvR caps :: (vs ++ env.consts)) = List.find? _ (vs ++ env.consts)
        rw [List.find?_cons_of_neg (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, hF.name, hn])]
      rcases find_views (vs := vs) (fun d hd => hv d (List.mem_cons_of_mem _ hd)) n with he |
        ⟨cv', cvR', caps', hn', hF', h₃⟩
      · exact .inl (htail.trans he)
      · exact .inr ⟨cv', cvR', caps', hn', hF', htail.trans h₃⟩

omit [SetTheory V] in
/-- The views over an environment are a swap of formers. -/
theorem formerSwap_views {env : Env} {vs : List ConstantInfo} (hv : ∀ c ∈ vs, ViewOf env c) :
    FormerSwap env ⟨vs ++ env.consts, env.tables⟩ where
  find := fun n => by
    rcases find_views hv n with he | ⟨cv, cvR, caps, rfl, hF, h₃⟩
    · exact .inl he
    · exact .inr ⟨cv, cvR, caps, hF.find, h₃, hF.name, hF.lps, hF.guard⟩
  mem := fun c hc hne => by
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨cv, cvR, caps, he, -⟩ := hv c hc
      exact absurd he (hne _ _)
    · exact hc
  tables := rfl

/-- **A family's view is the former its block read**: a run does not see an extension. -/
theorem shown_of_view {env : Env} {mp : EnvModelM V env} (hS : ShownFacts mp) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv cvR : ConstantVal} {caps : IndCaps}
    (hn : cv.name = D.member mm) (hF : ViewFacts env cv cvR caps) : D.shown mm = some cvR := by
  obtain ⟨-, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', caps', hf', ⟨-, hsh⟩, -⟩ := hrd mm hmm
  have hf := hF.find
  rw [hn, hf'] at hf
  obtain ⟨rfl, rfl⟩ : cv' = cv ∧ caps' = caps := by simpa using hf
  rcases hsh with ⟨-, hfl⟩ | ⟨f, hs, -⟩
  · rw [hF.headed] at hfl; exact nomatch hfl
  · obtain ⟨⟨envB, F, hwf, hx, hr, hrun⟩, -⟩ := hS D hD mm f hmm hs cv' caps' hf'
    obtain ⟨F₁, h₁⟩ := reducedFormer_ext hwf hx hr hrun
    obtain ⟨F₂, h₂⟩ := hF.ran
    have g₁ : reducedFormer (fueledOps .verified (max F₁ F₂)) env cv' (caps'.nparams + caps'.nIdx)
        = .ok f := by
      rw [← reducedFormer_datF]
      exact ConLeche.Cached.FueledM.up (Nat.le_max_left _ _) (by rw [reducedFormer_datF]; exact h₁)
    have g₂ : reducedFormer (fueledOps .verified (max F₁ F₂)) env cv' (caps'.nparams + caps'.nIdx)
        = .ok cvR := by
      rw [← reducedFormer_datF]
      exact ConLeche.Cached.FueledM.up (Nat.le_max_right _ _) (by rw [reducedFormer_datF]; exact h₂)
    rw [g₁] at g₂
    rw [hs]
    injection g₂ with g₂
    rw [g₂]

/-- A view's family is a recorded block's member, read at the view. -/
theorem view_member {env : Env} {mp : EnvModelM V env} (hS : ShownFacts mp)
    (hcov : LfpCover mp []) {cv cvR : ConstantVal} {caps : IndCaps}
    (hF : ViewFacts env cv cvR caps) :
    ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = cv.name ∧ D.shown mm = some cvR := by
  have hq : cv.name ≠ ConLeche.quotName := fun he => by
    have := hF.guard
    rw [he] at this
    exact absurd this (by decide)
  obtain ⟨D, hD, mm, hmm, hn⟩ := hcov.cover cv.name cv caps hF.find List.not_mem_nil hq
  exact ⟨D, hD, mm, hmm, hn, shown_of_view hS hD hmm hn.symm hF⟩

/-- A view's two readings: the view's own, and the stored former's, of one value, the family
inhabiting it. -/
theorem view_read {env : Env} {mp : EnvModelM V env} (hS : ShownFacts mp)
    (hcov : LfpCover mp []) {cv cvR : ConstantVal} {caps : IndCaps}
    (hF : ViewFacts env cv cvR caps) (ψ : Name → Nat) :
    ∃ ta ta₀ : Term, denote mp.base2.acval env ψ 0 cvR.type = some ta ∧
      denote mp.base2.acval env ψ 0 cv.type = some ta₀ ∧
      ∀ ρ : Nat → V, interp V ρ ta₀ = interp V ρ ta ∧
        interp V ρ (mp.base2.acval cv.name ψ) ∈ˢ interp V ρ ta := by
  obtain ⟨D, hD, mm, hmm, hn, hs⟩ := view_member hS hcov hF
  obtain ⟨-, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv', caps', hf', ⟨-, hsh⟩, -⟩ := hrd mm hmm
  have hf := hF.find
  rw [← hn, hf'] at hf
  obtain ⟨rfl, rfl⟩ : cv' = cv ∧ caps' = caps := by simpa using hf
  rcases hsh with ⟨hn', -⟩ | ⟨f, hs', -, -, -, -, -, -, hm⟩
  · rw [hs] at hn'; exact nomatch hn'
  · rw [hs] at hs'
    obtain rfl := Option.some.inj hs'
    rw [hn] at hm
    exact hm ψ

/-! ## To the views -/

/-- A stack of views over a well-formed environment is well formed. -/
theorem envWF_ofViews {env : Env} (henv : EnvWF env) :
    ∀ {vs : List ConstantInfo}, (∀ c ∈ vs, ViewOf env c) → EnvWF ⟨vs ++ env.consts, env.tables⟩
  | [], _ => henv
  | c :: vs, hv => by
    have ih := envWF_ofViews henv (vs := vs) fun d hd => hv d (List.mem_cons_of_mem _ hd)
    obtain ⟨cv, cvR, caps, rfl, hF⟩ := hv c List.mem_cons_self
    have hsc := hF.closed
    simp only [ConLeche.viewScoped, Bool.and_eq_true, Bool.not_eq_true'] at hsc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hsc
    have hres : ∀ (vs : List ConstantInfo) {e : Expr}, e.constsResolve env = true →
        e.constsResolve ⟨vs ++ env.consts, env.tables⟩ = true := by
      intro vs e he
      induction vs with
      | nil => exact he
      | cons d vs ih => exact Expr.constsResolve_mono ih
    have hcaps : ConLeche.IndCapsWF (.indInfo cvR caps) := by
      obtain ⟨hu, he⟩ := (henv.consts _ (ConLeche.Env.find?_mem hF.find)).2.2.2.2.2.2 cv caps rfl
      exact ConLeche.IndCapsWF.of_caps hu he
    exact ih.cons (ConLeche.structConstWF h1 h2 (Expr.constsResolve_mono (hres vs h3)) h4
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq) hcaps)

set_option maxHeartbeats 1600000 in
/-- **The carrier at the views**: the same leaves and records. -/
theorem EnvModelM.toViews {env : Env} (mp : EnvModelM V env) (hS : ShownFacts mp)
    (hcov : LfpCover mp []) {vs : List ConstantInfo} (hv : ∀ c ∈ vs, ViewOf env c) :
    ∃ mpV : EnvModelM V ⟨vs ++ env.consts, env.tables⟩,
      mpV.base2.acval = mp.base2.acval ∧ mpV.lfpBlocks = mp.lfpBlocks ∧ LfpCover mpV [] := by
  have h := formerSwap_views hv
  have hwf := envWF_ofViews mp.base2.wf hv
  have hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denote mp.base2.acval env ψ d e
        = denote mp.base2.acval ⟨vs ++ env.consts, env.tables⟩ ψ d e :=
    fun ψ d e => denote_formerSwap h ψ d e
  have hbd : ∀ e, ConstsBound env e → ConstsBound ⟨vs ++ env.consts, env.tables⟩ e := fun _ =>
    ConstsBound.of_isSome fun n hn => by rw [← h.isSomeEq]; exact hn
  -- a member's former as read, on the two sides
  have hfa : ∀ {D : LfpDatum V}, D ∈ mp.lfpBlocks → ∀ {mm : Nat}, mm < D.k →
      ∀ {cv cv' : ConstantVal} {caps caps' : IndCaps},
      env.find? (D.member mm) = some (.indInfo cv caps) →
      (⟨vs ++ env.consts, env.tables⟩ : Env).find? (D.member mm) = some (.indInfo cv' caps') →
      D.formerAt mm cv' = D.formerAt mm cv := by
    intro D hD mm hmm cv cv' caps caps' hf hf'
    rcases find_views hv (D.member mm) with he | ⟨cvs, cvR, capsv, hn, hF, h₃⟩
    · rw [he, hf] at hf'
      obtain ⟨rfl, -⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
      rfl
    · have hs := shown_of_view hS hD hmm hn hF
      simp [LfpDatum.formerAt, hs]
  refine (mp.swapFormers h hwf ?_ ?_ ?_ ?_ ?_ ?_ mp.lfpBlocks ?_).imp fun mpV hV =>
    ⟨hV.1, hV.2, LfpCover.formerSwap h hV.2 hcov⟩
  · -- the recursors' constructors
    intro n cv mI rP isK rules hf r hr
    obtain ⟨cvj, cnP, cnF, hc⟩ := mp.base2.rec_ctors n cv mI rP isK rules
      ((h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mp hf) r hr
    exact ⟨cvj, cnP, cnF, (h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mpr hc⟩
  · -- the tables' discipline
    intro T tbl hf i hi
    have hf₀ : env.findTable? T = some tbl := by rw [h.tableEq]; exact hf
    obtain ⟨h2, h3, h4, h5, ⟨cvT, caps, hT, hlT⟩, ⟨cvC, hC, hlC, hstrip⟩⟩ := mp.base2.proj_ok T tbl hf₀ i hi
    obtain ⟨cvT', hT', hl'⟩ := h.find_ind hT
    exact ⟨h2, h3, h4, h5, ⟨cvT', caps, hT', hl'.trans hlT⟩,
      ⟨cvC, (h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mpr hC, hlC, hstrip⟩⟩
  · -- the recursors' laws
    intro m₃ hac φ n cv mI rP isK rules hf rl hrl
    have hl := mp.rec_rules φ n cv mI rP isK rules
      ((h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mp hf) rl hrl
    refine RecRuleLaw.formerSwap h hac (fun φ' cvj us hz => ?_) hl
    refine FamNZ.formerSwap h mp.base2.acval_params ?_ ?_ hz
    · intro T cv cv' caps φ'' us' h₀ h₃ hne hnv
      rcases find_views hv T with he | ⟨cvs, cvR, capsv, hn, hF, h₃'⟩
      · rw [he, h₀] at h₃
        obtain rfl : cv = cv' := by simpa using h₃
        exact absurd rfl hne
      · have hfs := hF.find
        rw [hn, h₀] at hfs
        obtain ⟨rfl, rfl⟩ : cv = cvs ∧ caps = capsv := by simpa using hfs
        rw [h₃] at h₃'
        obtain rfl : cv' = cvR := by simpa using h₃'
        obtain ⟨D, hD, mm, hmm, hnm, hs⟩ := view_member hS hcov hF
        obtain ⟨-, -, hrd, -, hcK, -⟩ := mp.lfp_ok D hD
        obtain ⟨cv₁, caps₁, hf₁, hz₁, hlen⟩ := hcK mm hmm
        rw [hnm, hn, h₀] at hf₁
        obtain ⟨rfl, rfl⟩ : cv = cv₁ ∧ caps = caps₁ := by simpa using hf₁
        have hfm : env.find? (D.member mm) = some (.indInfo cv caps) := by rw [hnm, hn]; exact h₀
        have hfaV : D.formerAt mm cv = cv' := by simp [LfpDatum.formerAt, hs]
        rw [hfaV] at hz₁
        generalize hψ : Level.substFn φ'' cv.levelParams us' = ψ
        have hfalse := holds_false_of_isNever hnv φ''
        rw [show cv'.levelParams = cv.levelParams from hF.lps, hψ] at hfalse
        refine ⟨D.w ψ, (fun h0 => by rw [hz₁ ψ h0] at hfalse; exact nomatch hfalse),
          fun ta hta ρ => ?_⟩
        rw [denote_instLevels mp.base2.acval_params φ'', hψ] at hta
        obtain ⟨cv₂, caps₂, hf₂, -, hab⟩ := hrd mm hmm
        rw [hfm] at hf₂
        obtain ⟨rfl, rfl⟩ : cv = cv₂ ∧ caps = caps₂ := by simpa using hf₂
        obtain ⟨ab, hab₁, hmap⟩ := hab ψ
        rw [mp.formerAt_interp hD hmm hfm hta hab₁ ρ, ← hlen ψ, ← hmap]
        exact (towerEnds_mkPisAV ab ρ (D.w ψ)).toPt
    · intro T cv cv' caps ψ ta _ h₀ h₃ hta ρ
      rcases find_views hv T with he | ⟨cvs, cvR, capsv, hn, hF, h₃'⟩
      · rw [he, h₀] at h₃
        obtain rfl : cv = cv' := by simpa using h₃
        exact ⟨ta, hta, rfl⟩
      · have hfs := hF.find
        rw [hn, h₀] at hfs
        obtain ⟨rfl, rfl⟩ : cv = cvs ∧ caps = capsv := by simpa using hfs
        rw [h₃] at h₃'
        obtain rfl : cv' = cvR := by simpa using h₃'
        obtain ⟨ta₁, ta₀, h₁, h₀', hin⟩ := view_read hS hcov hF ψ
        rw [hta] at h₀'
        obtain rfl := Option.some.inj h₀'
        exact ⟨ta₁, h₁, (hin ρ).1⟩
  · -- the projections' laws
    intro m₃ hac φ T i entry hf
    have hf₀ : env.findProj? T i = some entry := by rw [h.projEq]; exact hf
    have hl := mp.tower_ok φ T i entry hf₀
    refine TowerEntryLaw.formerSwap h hac (fun us cvC Ta hus hTa hgd => ?_) hl
    have hsn : entry.structName = T := hl.1
    rcases hgd with ⟨cvT, caps, s, hT, hs, hz⟩ | hr | ⟨cvT, caps, u, hT, ht, hu⟩
    · rcases find_views hv entry.structName with he | ⟨cvs, cvR, capsv, hn, hF, h₃⟩
      · exact .inl (.inl ⟨cvT, caps, s, by rw [← he]; exact hT, hs, hz⟩)
      · rw [hT] at h₃
        obtain ⟨rfl, -⟩ : cvT = cvR ∧ caps = capsv := by simpa using h₃
        obtain ⟨D, hD, mm, hmm, hnm, hs'⟩ := view_member hS hcov hF
        have hfm : env.find? (D.member mm) = some (.indInfo cvs capsv) := by
          rw [hnm]; exact hF.find
        obtain ⟨-, -, htv, -⟩ := hS D hD mm cvT hmm hs' cvs capsv hfm
        have hmT : D.member mm = T := by rw [hnm, hn, hsn]
        rw [hmT] at htv
        exact .inr (htv φ i entry s hf₀ hs hz us Ta hus hTa)
    · refine .inl (.inr (.inl fun ds b hrd hl' => hr ds b ?_ hl'))
      rw [hac, ← hde]; exact hrd
    · obtain ⟨cv₀, hT₀, hlp⟩ := h.find_ind_back hT
      refine .inl (.inr (.inr ⟨cv₀, caps, u, hT₀, fun ta hta ρ => ?_, hu.imp id fun hr ds b hrd hl' =>
        hr ds b (by rw [hac, ← hde]; exact hrd) hl'⟩))
      rw [denote_instLevels mp.base2.acval_params φ] at hta
      rcases find_views hv entry.structName with he | ⟨cvs, cvR, capsv, hn, hF, h₃⟩
      · rw [he, hT₀] at hT
        obtain rfl : cv₀ = cvT := by simpa using hT
        refine ht ta ?_ ρ
        rw [hac, ← hde, denote_instLevels mp.base2.acval_params φ]
        exact hta
      · have hfs := hF.find
        rw [hn, hT₀] at hfs
        obtain ⟨rfl, rfl⟩ : cv₀ = cvs ∧ caps = capsv := by simpa using hfs
        rw [hT] at h₃
        obtain rfl : cvT = cvR := by simpa using h₃
        obtain ⟨ta₁, ta₀, h₁, h₀', hin⟩ := view_read hS hcov hF
          (Level.substFn φ cv₀.levelParams us)
        rw [hta] at h₀'
        obtain rfl := Option.some.inj h₀'
        rw [(hin ρ).1]
        refine ht ta₁ ?_ ρ
        rw [hac, ← hde, denote_instLevels mp.base2.acval_params φ, hlp]
        exact h₁
  · -- the fibres
    intro m₃ hac I cv caps hf hfl ψ ab n hread hn ρ vs' hsp
    rw [hac] at hread ⊢
    rw [← hde] at hread
    rcases find_views hv I with he | ⟨cvs, cvR, capsv, hnm, hF, h₃⟩
    · exact mp.ind_strict I cv caps (by rw [← he]; exact hf) hfl ψ ab n hread hn ρ vs' hsp
    · rw [hf] at h₃
      obtain ⟨rfl, -⟩ : cv = cvR ∧ caps = capsv := by simpa using h₃
      obtain ⟨D, hD, mm, hmm, hnm', hs'⟩ := view_member hS hcov hF
      have hfm : env.find? (D.member mm) = some (.indInfo cvs capsv) := by
        rw [hnm']; exact hF.find
      obtain ⟨-, his, -⟩ := hS D hD mm cv hmm hs' cvs capsv hfm
      have hmT : D.member mm = I := by rw [hnm', hnm]
      rw [hmT] at his
      exact his ψ ab n hread hn ρ vs' hsp
  · -- the views' types
    intro c hc hnot
    have hc' : c ∈ vs := (List.mem_append.mp hc).resolve_right hnot
    obtain ⟨cv, cvR, caps, rfl, hF⟩ := hv c hc'
    obtain ⟨D, hD, mm, hmm, hnm, hs'⟩ := view_member hS hcov hF
    have hfm : env.find? (D.member mm) = some (.indInfo cv caps) := by rw [hnm]; exact hF.find
    obtain ⟨-, -, -, hwd⟩ := hS D hD mm cvR hmm hs' cv caps hfm
    refine ⟨fun ψ => ?_, fun ψ ta hta ρ => ?_, fun ψ ta hta ρ => ?_⟩
    · obtain ⟨ta, -, h₁, -⟩ := view_read hS hcov hF ψ
      exact ⟨ta, by rw [← hde]; exact h₁⟩
    · rw [← hde] at hta
      exact hwd ψ ta hta ρ
    · rw [← hde] at hta
      change denote mp.base2.acval env ψ 0 cvR.type = some ta at hta
      obtain ⟨ta₁, _, h₁, _, hin⟩ := view_read hS hcov hF ψ
      rw [hta] at h₁
      obtain rfl := Option.some.inj h₁
      show interp V ρ (mp.base2.acval cvR.name ψ) ∈ˢ _
      rw [hF.name]
      exact (hin ρ).2
  · -- the records
    intro D hD
    obtain ⟨hc, ⟨hst, hstC⟩, hrd, ⟨hnk, hrdC⟩, ⟨hcK, hcC⟩⟩ := mp.lfp_ok D hD
    refine ⟨hc, ⟨fun mm hmm => ?_, fun c hc' j hj => ?_⟩, fun mm hmm => ?_, ⟨hnk, fun c hc' j hj => ?_⟩,
      ⟨fun mm hmm => ?_, fun c hc' j hj => ?_⟩⟩
    · obtain ⟨cv, caps, hf⟩ := hst mm hmm
      obtain ⟨cv', hf', -⟩ := h.find_ind hf
      exact ⟨cv', caps, hf'⟩
    · obtain ⟨cv, a, b, hf⟩ := hstC c hc' j hj
      exact ⟨cv, a, b, (h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mpr hf⟩
    · obtain ⟨cv, caps, hf, ⟨hfl, hsh⟩, hab⟩ := hrd mm hmm
      obtain ⟨cv', hf', hl'⟩ := h.find_ind hf
      have hq := hfa hD hmm hf hf'
      refine ⟨cv', caps, hf', ⟨?_, ?_⟩, fun ψ => ?_⟩
      · intro hfl'
        rcases find_views hv (D.member mm) with he | ⟨cvs, cvR, capsv, hn, hF, h₃⟩
        · rw [he, hf] at hf'
          obtain rfl : cv = cv' := by simpa using hf'
          exact hfl hfl'
        · rw [hf'] at h₃
          obtain ⟨rfl, -⟩ : cv' = cvR ∧ caps = capsv := by simpa using h₃
          have hs := shown_of_view hS hD hmm hn hF
          simp [LfpDatum.formerAt, hs]
      · rcases find_views hv (D.member mm) with he | ⟨cvs, cvR, capsv, hn, hF, h₃⟩
        · rw [he, hf] at hf'
          obtain rfl : cv = cv' := by simpa using hf'
          rcases hsh with ⟨h₁, h₂⟩ | ⟨f, hs, h₁, h₂, h₃', h₄, hb, hdl, hm⟩
          · exact .inl ⟨h₁, h₂⟩
          · refine .inr ⟨f, hs, h₁, h₂, h₃', h₄, hbd _ hb, hdl, fun ψ => ?_⟩
            obtain ⟨ta, ta₀, hta, hta₀, hin⟩ := hm ψ
            exact ⟨ta, ta₀, by rw [← hde]; exact hta, by rw [← hde]; exact hta₀, hin⟩
        · rw [hf'] at h₃
          obtain ⟨rfl, -⟩ : cv' = cvR ∧ caps = capsv := by simpa using h₃
          have hs := shown_of_view hS hD hmm hn hF
          rcases hsh with ⟨h₁, -⟩ | ⟨f, hs', h₁, h₂, h₃', h₄, hb, hdl, hm⟩
          · rw [hs] at h₁; exact nomatch h₁
          · rw [hs] at hs'
            obtain rfl := Option.some.inj hs'
            refine .inr ⟨cv', hs, rfl, rfl, h₃', h₄, hbd _ hb, hdl, fun ψ => ?_⟩
            obtain ⟨ta, ta₀, hta, -, hin⟩ := hm ψ
            exact ⟨ta, ta, by rw [← hde]; exact hta, by rw [← hde]; exact hta, fun ρ =>
              ⟨rfl, (hin ρ).2⟩⟩
      · rw [hq]
        obtain ⟨ab, hta, hmap⟩ := hab ψ
        exact ⟨ab, by rw [← hde]; exact hta, hmap⟩
    · obtain ⟨cv, nPc, nF, hf, hcf, hlps, hpars, A, hA, hocc, hrdA⟩ := hrdC c hc' j hj
      refine ⟨cv, nPc, nF, (h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mpr hf, hcf,
        fun mm hmm => ?_, fun ψ dsC bodyC hrd' hle => ?_, A, hA, hocc, fun ψ => ?_⟩
      · obtain ⟨cvm, caps, hfm, hl⟩ := hlps mm hmm
        obtain ⟨cvm', hfm', hl'⟩ := h.find_ind hfm
        exact ⟨cvm', caps, hfm', hl'.trans hl⟩
      · rw [← hde] at hrd'
        exact hpars ψ dsC bodyC hrd' hle
      · obtain ⟨h1, h2, ab, Tys, hta, hlab, hlT, hTys, hab⟩ := hrdA ψ
        refine ⟨h1, h2, ab, Tys, by rw [← hde]; exact hta, hlab, hlT, fun mm hmm => ?_, hab⟩
        obtain ⟨cvm, caps, ty, hfm, hty, hr⟩ := hTys mm hmm
        obtain ⟨cvm', hfm', -⟩ := h.find_ind hfm
        refine ⟨cvm', caps, ty, hfm', by rw [hfa hD hmm hfm hfm']; exact hty, ?_⟩
        rw [← hde]; exact hr
    · obtain ⟨cv, caps, hf, hz, hlen⟩ := hcK mm hmm
      obtain ⟨cv', hf', -⟩ := h.find_ind hf
      exact ⟨cv', caps, hf', by rw [hfa hD hmm hf hf']; exact hz, hlen⟩
    · obtain ⟨cv, nPc, nF, hf, hshape⟩ := hcC c hc' j hj
      exact ⟨cv, nPc, nF, (h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mpr hf, hshape⟩

/-! ## The block's install, against its input -/

omit [SetTheory V] in
theorem checkBlockTeles_formers {env : Env} {nP F : Nat} :
    ∀ {mss : List MemberShape} {cvs : List (ConstantVal × Level)},
      ConLeche.checkBlockTeles (fueledOps .verified F) env nP mss = .ok cvs →
      cvs.map (·.1) = mss.map (·.cvT)
  | [], cvs, h => by
    simp only [ConLeche.checkBlockTeles, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | ms :: rest, cvs, h => by
    unfold ConLeche.checkBlockTeles at h
    obtain ⟨r, hr, h⟩ := exceptBind_ok h
    obtain ⟨rs, hrs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨cvTa, s⟩ := r
    simp only [List.map_cons, ConLeche.checkBlockTele_former hr, checkBlockTeles_formers hrs]

omit [SetTheory V] in
/-- The tables' stage stores no constant. -/
theorem checkBlockTables_consts {q : BlockShape} :
    ∀ {l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))} {env env₂ : Env},
      ConLeche.checkBlockTables (m := CheckM) q l env = .ok env₂ → env₂.consts = env.consts
  | [], env, env₂, h => by
    simp only [ConLeche.checkBlockTables, pure, Except.pure, Except.ok.injEq] at h
    rw [h]
  | (ms, ctorsA, sortss) :: rest, env, env₂, h => by
    unfold ConLeche.checkBlockTables at h
    obtain ⟨env', henv', h⟩ := exceptBind_ok h
    rw [checkBlockTables_consts h]
    revert henv'
    split
    · split
      · intro hh
        obtain ⟨tbl, -, rfl⟩ := ConLeche.Semantics.checkStructProjTable_shape hh
        rfl
      · intro hh
        simp only [pure, Except.pure, Except.ok.injEq] at hh
        rw [hh]
    · intro hh
      simp only [pure, Except.pure, Except.ok.injEq] at hh
      rw [hh]

omit [SetTheory V] in
/-- **What the ordinary install stores**: its members as the group has them, and no other
former. -/
theorem declBlockRun_consts {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    {p₀ : BlockParts} (hrun : ConLeche.Semantics.DeclBlockRun F env block p₀ env₂) :
    ∃ new : List ConstantInfo, env₂.consts = new ++ env.consts ∧
      ∀ c ∈ new, ∀ cv caps, c = .indInfo cv caps → ∃ ms ∈ p₀.members, cv = ms.cvT := by
  obtain ⟨-, -, isRec, env₁, cvTas, p₁, p, ctorsAs, sortsss, ctx, holes, rd, Ms, kinds,
    nfs, nodes, st, isorts, outR, hInd, hp, -, -, -, -, -, -, -, -, -, hTbl⟩ := hrun
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, hmem0, hcvTas, hq, hcons, htele0, hteles, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  have hcv : ∀ cv ∈ cvTas, ∃ ms ∈ p₀.members, cv = ms.cvT := by
    intro cv hcvm
    have hall : cvTas = p₀.members.map (·.cvT) := by
      rw [hcvTas, hmem0, List.map_cons, checkBlockTeles_formers hteles,
        ConLeche.checkBlockTele_former htele0]
    rw [hall] at hcvm
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hcvm
    exact ⟨ms, hms, rfl⟩
  obtain ⟨newI, hnewI, hnewIall⟩ := consBlockInds_consts (p₁ := p₁) (isRec := isRec) cvTas 0 env
  obtain ⟨newR, hnewR, hnewRall⟩ := consBlockRecsT_consts
    (q := p.toBlockShape) 0 (ConLeche.storedOut p.recs outR)
    (ConLeche.consBlockCtors p.nP ctorsAs env₁)
  have hctor := consBlockCtors_consts p.nP ctorsAs env₁
  refine ⟨newR ++ (ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 p.nP c.2).reverse ++ newI,
    ?_, fun c hc cv caps he => ?_⟩
  · rw [checkBlockTables_consts hTbl, hnewR, hctor, hcons, hnewI]
    simp
  · simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · obtain ⟨o, -, mI, rP, isK, rules, rfl⟩ := hnewRall c hc
      exact nomatch he
    · obtain ⟨cA, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
      exact nomatch he
    · obtain ⟨cv', hcv', j, rfl⟩ := hnewIall c hc
      obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj he
      exact hcv _ hcv'

end ConLeche.Model
