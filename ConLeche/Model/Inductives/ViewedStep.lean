module

public import ConLeche.Model.Inductives.DeclBlockStep
public import ConLeche.Model.Inductives.FormerSwap
public import ConLeche.Verify.EnvExt
import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Model.Env.CanonCrest
import ConLeche.Verify.BridgeDecl

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

end ConLeche.Model
