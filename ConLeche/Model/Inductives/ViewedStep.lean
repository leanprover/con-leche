module

public import ConLeche.Model.Inductives.DeclBlockStep
public import ConLeche.Model.Inductives.FormerSwap
public import ConLeche.Verify.EnvExt
import ConLeche.Model.Inductives.StoredSem
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Semantics.Inductives.DeclBlockEta
import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.GenRecC
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

omit [SetTheory V] in
/-- A stored projection's type mentions what is stored. -/
theorem constsBound_entry {env : Env} (hwf : EnvWF env) {T : Name} {i : Nat} {entry : ProjEntry}
    (hfp : env.findProj? T i = some entry) (k : Nat) (us : List Level) :
    ConstsBound env (ConLeche.projTele k
      (entry.body.instantiateLevelParams entry.levelParams us)) := by
  obtain ⟨tbl, ht, hi, rfl⟩ := ConLeche.Env.findProj?_some hfp
  obtain ⟨-, hsz, hb⟩ := hwf.table ht
  have hlt : i < tbl.bodies.size := hsz ▸ hi
  have hget : tbl.bodies[i]? = some (tbl.bodies.getD i default) := by
    simp [Array.getD, hlt]
  have hres := (hb i _ hget).2.2.1
  refine constsBound_of_constsResolve _ ?_
  rw [ConLeche.projTele_constsResolve, Expr.constsResolve_instantiateLevelParams]
  exact hres

omit [SetTheory V] in
/-- An extension of an extension. -/
theorem envExt_trans {env₁ env₂ env₃ : Env} (h₁ : EnvExt env₁ env₂)
    (hf : ∀ n ci, env₂.find? n = some ci → env₃.find? n = some ci)
    (ht : ∀ T, (env₂.find? T).isSome = true → env₃.findTable? T = env₂.findTable? T) :
    EnvExt env₁ env₃ where
  find := fun n ci h => hf n ci (h₁.find n ci h)
  table := fun T hT => by
    have hs : (env₂.find? T).isSome = true := by
      cases hc : env₁.find? T with
      | none => rw [hc] at hT; exact nomatch hT
      | some ci => rw [h₁.find T ci hc]; rfl
    rw [ht T hs]; exact h₁.table T hT
  natTrio := h₁.natTrio

/-- **A shown former's facts across an extension.** -/
theorem shownFacts_keep {env env' : Env} {mp : EnvModelM V env} {m' : EnvModel V env'}
    (hS : ShownFacts mp) (hfd : ∀ n ci, env.find? n = some ci → env'.find? n = some ci)
    (htb : ∀ T, (env.find? T).isSome = true → env'.findTable? T = env.findTable? T)
    (hleaf : ∀ n, (env.find? n).isSome = true → m'.acval n = mp.base2.acval n)
    (hread : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr) (ta : Term), ConstsBound env e →
      denote mp.base2.acval env ψ d e = some ta → denote m'.acval env' ψ d e = some ta)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} {f : ConstantVal} (hmm : mm < D.k)
    (hs : D.shown mm = some f) {cv : ConstantVal} {caps : IndCaps}
    (hf : env'.find? (D.member mm) = some (.indInfo cv caps)) :
    (∃ (envB : Env) (F : Nat), EnvWF envB ∧ EnvExt envB env' ∧
      cv.type.constsResolve envB = true ∧
      reducedFormer (fueledOps .verified F) envB cv (caps.nparams + caps.nIdx) = .ok f) ∧
    IndStrictAt (V := V) m'.acval env' (D.member mm) f ∧
    (∀ φ, TowerViewTyped m' φ (D.member mm) f) ∧
    (∀ (ψ : Name → Nat) (ta : Term), denote m'.acval env' ψ 0 f.type = some ta →
      ∀ ρ : Nat → V, WellDenotedTy V ρ ta) := by
  obtain ⟨-, ⟨hst, -⟩, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv₀, caps₀, hf₀⟩ := hst mm hmm
  rw [hfd _ _ hf₀] at hf
  obtain ⟨rfl, rfl⟩ : cv₀ = cv ∧ caps₀ = caps := by simpa using hf
  obtain ⟨hrun, his, htv, hwd⟩ := hS D hD mm f hmm hs cv₀ caps₀ hf₀
  have hsm : (env.find? (D.member mm)).isSome = true := by rw [hf₀]; rfl
  have hlf := hleaf _ hsm
  obtain ⟨cv₁, caps₁, hf₁, ⟨-, hsh⟩, -⟩ := hrd mm hmm
  rw [hf₀] at hf₁
  obtain ⟨rfl, rfl⟩ : cv₀ = cv₁ ∧ caps₀ = caps₁ := by simpa using hf₁
  obtain ⟨hbf, hrf⟩ : ConstsBound env f.type ∧ ∀ ψ, ∃ ta, denote mp.base2.acval env ψ 0 f.type = some ta := by
    rcases hsh with ⟨h₀, -⟩ | ⟨f', hs', -, -, -, -, hb, -, hm⟩
    · rw [hs] at h₀; exact nomatch h₀
    · rw [hs] at hs'
      obtain rfl := Option.some.inj hs'
      exact ⟨hb, fun ψ => (hm ψ).elim fun ta h => ⟨ta, h.elim fun _ h => h.1⟩⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨envB, F, hwf, hxB, hr, hrn⟩ := hrun
    exact ⟨envB, F, hwf, envExt_trans hxB hfd htb, hr, hrn⟩
  · intro ψ ab n hta hn ρ vs hsp
    obtain ⟨ta, hta₀⟩ := hrf ψ
    have h₁ := hread ψ 0 _ _ hbf hta₀
    rw [hta] at h₁
    obtain rfl := Option.some.inj h₁
    rw [hlf]
    exact his ψ ab n hta₀ hn ρ vs hsp
  · intro φ i entry s' hfp hs₁ hz us Ta hus hTa ρ vs x rest h₁ h₂ h₃ h₄ h₅ h₆
    have hfp₀ : env.findProj? (D.member mm) i = some entry := by
      have := htb _ hsm
      unfold Env.findProj? at hfp ⊢
      rw [← this]; exact hfp
    obtain ⟨_, _, _, _, _, _, _, hlaw, _⟩ := mp.tower_ok φ _ i entry hfp₀
    obtain ⟨⟨Ta₀, hTa₀, -⟩, -⟩ := hlaw us hus
    have h₁' := hread φ 0 _ _ (constsBound_entry mp.base2.wf hfp₀ _ us) hTa₀
    rw [hTa] at h₁'
    obtain rfl := Option.some.inj h₁'
    rw [hlf] at h₂ h₃ h₅
    exact htv φ i entry s' hfp₀ hs₁ hz us Ta hus hTa₀ ρ vs x rest h₁ h₂ h₃ h₄ h₅ h₆
  · intro ψ ta hta ρ
    obtain ⟨ta₀, hta₀⟩ := hrf ψ
    have h₁ := hread ψ 0 _ _ hbf hta₀
    rw [hta] at h₁
    obtain rfl := Option.some.inj h₁
    exact hwd ψ ta hta₀ ρ

/-- **Shown formers across a step.** -/
theorem ShownFacts.step {env env' : Env} {mp : EnvModelM V env} {mp' : EnvModelM V env'}
    (hS : ShownFacts mp) (r : CoverRel mp mp')
    (htb : ∀ T, (env.find? T).isSome = true → env'.findTable? T = env.findTable? T) :
    ShownFacts mp' := by
  intro D hD mm f hmm hs cv caps hf
  rcases r.blocks D hD with h₀ | h₀
  · exact shownFacts_keep hS r.find htb r.leaf r.read h₀ hmm hs hf
  · rw [h₀] at hs; exact nomatch hs

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
theorem blockCapsAt_nIdx (p : BlockShape) (mi : Nat) (isRec : Bool) :
    (ConLeche.blockCapsAt p mi isRec).nIdx = (p.members.getD mi default).nIdx := by
  unfold ConLeche.blockCapsAt; split <;> rfl

omit [SetTheory V] in
theorem consBlockInds_indexed {p₁ : BlockShape} {isRec : Bool} :
    ∀ (cvs : List ConstantVal) (i : Nat) (env : Env), ∃ new : List ConstantInfo,
      (ConLeche.consBlockInds p₁ isRec cvs i env).consts = new ++ env.consts ∧
      ∀ c ∈ new, ∃ j cv, cvs[j]? = some cv ∧ c = .indInfo cv (ConLeche.blockCapsAt p₁ (i + j) isRec)
  | [], _, _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | cv :: rest, i, env => by
    obtain ⟨new, hnew, hall⟩ := consBlockInds_indexed (p₁ := p₁) (isRec := isRec) rest (i + 1)
      ⟨.indInfo cv (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩
    refine ⟨new ++ [.indInfo cv (ConLeche.blockCapsAt p₁ i isRec)], ?_, fun c hc => ?_⟩
    · show (ConLeche.consBlockInds p₁ isRec rest (i + 1) _).consts = _
      rw [hnew]; simp
    · rcases List.mem_append.mp hc with h | h
      · obtain ⟨j, cv', hj, rfl⟩ := hall c h
        exact ⟨j + 1, cv', by simpa using hj, by
          rw [show i + (j + 1) = i + 1 + j by omega]⟩
      · rw [List.mem_singleton.mp h]
        exact ⟨0, cv, rfl, rfl⟩

omit [SetTheory V] in
/-- A stored recursor is named as the generated one. -/
theorem storedOut_mem_name :
    ∀ (recs : List RecShape) (out : List (ConstantVal × ConLeche.TargetMajor × List Expr)),
      ∀ o ∈ ConLeche.storedOut recs out, ∃ g ∈ out, o.1.name = g.1.name
  | [], _, _, h => by simp [ConLeche.storedOut] at h
  | _ :: _, [], _, h => by simp [ConLeche.storedOut] at h
  | rc :: recs, g :: out, o, h => by
    simp only [ConLeche.storedOut, List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨g, List.mem_cons_self, rfl⟩
    · obtain ⟨g', hg', hn⟩ := storedOut_mem_name recs out o h
      exact ⟨g', List.mem_cons_of_mem _ hg', hn⟩

omit [SetTheory V] in
/-- **What the ordinary install stores**: its members as the group has them, and no other
former. -/
theorem declBlockRun_consts {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    {p₀ : BlockParts} (hrun : ConLeche.Semantics.DeclBlockRun F env block p₀ env₂) :
    ∃ new : List ConstantInfo, env₂.consts = new ++ env.consts ∧
      (∀ c ∈ new, ∀ cv caps, c = .indInfo cv caps → ∃ ms ∈ p₀.members, cv = ms.cvT ∧
        caps.nparams + caps.nIdx = p₀.nP + ms.nIdx) ∧
      ((∀ c ∈ p₀.allCtors, ConLeche.reservedBasisNames.contains c.1.name = false) →
        ∀ c ∈ new, ConLeche.reservedBasisNames.contains c.name = false) := by
  obtain ⟨-, -, isRec, env₁, cvTas, p₁, p, ctorsAs, sortsss, ctx, holes, rd, Ms, kinds,
    nfs, nodes, st, isorts, outR, hInd, hp, hCtors, -, -, -, -, -, -, hRec, -, hTbl⟩ := hrun
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, hmem0, hcvTas, hq, hcons, htele0, hteles, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  have hall : cvTas = p₀.members.map (·.cvT) := by
    rw [hcvTas, hmem0, List.map_cons, checkBlockTeles_formers hteles,
      ConLeche.checkBlockTele_former htele0]
  obtain ⟨newI, hnewI, hnewIall⟩ := consBlockInds_indexed (p₁ := p₁) (isRec := isRec) cvTas 0 env
  obtain ⟨newR, hnewR, hnewRall⟩ := consBlockRecsT_consts
    (q := p.toBlockShape) 0 (ConLeche.storedOut p.recs outR)
    (ConLeche.consBlockCtors p.nP ctorsAs env₁)
  have hctor := consBlockCtors_consts p.nP ctorsAs env₁
  refine ⟨newR ++ (ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 p.nP c.2).reverse ++ newI,
    ?_, fun c hc cv caps he => ?_, fun hCres c hc => ?_⟩
  · rw [checkBlockTables_consts hTbl, hnewR, hctor, hcons, hnewI]
    simp
  rotate_left
  · simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · obtain ⟨o, ho, mI, rP, isK, rules, rfl⟩ := hnewRall c hc
      obtain ⟨g, hg, hn⟩ := storedOut_mem_name _ _ o ho
      subst hp
      have hRec' : ConLeche.genRecCheck (ConLeche.ShadowOps.fueled .verified F)
          (mkFEnv (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)) (p₀.complete p₁).toBlockShape
          (ConLeche.blockNestedBit (p₀.complete p₁).toBlockShape kinds) ctx.params st.ctorNfs.toList
          rd Ms cvTas block = .ok outR := hRec
      have hr := ConLeche.Cached.genRecCheck_out_unreserved hRec' g hg
      have hn' : (ConstantInfo.recInfo o.1 mI rP isK rules).name = g.1.name := hn
      rw [hn']
      simp only [ConLeche.reservedRecName, Bool.or_eq_false_iff] at hr
      exact hr.1.1.1.1.1.1
    · obtain ⟨cA, hcA, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
      obtain ⟨ctorsA, hctorsA, hcAm⟩ := List.mem_flatten.mp hcA
      obtain ⟨hnames, -⟩ := checkBlockCtors_names hCtors
      have h₁ : (cA.1.name, cA.2) ∈ (ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))).flatten :=
        List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨ctorsA, hctorsA, rfl⟩,
          List.mem_map.mpr ⟨cA, hcAm, rfl⟩⟩
      rw [hnames] at h₁
      obtain ⟨l, hl, hin⟩ := List.mem_flatten.mp h₁
      obtain ⟨mc, hmc, rfl⟩ := List.mem_map.mp hl
      obtain ⟨c₀, hc₀, hc₀e⟩ := List.mem_map.mp hin
      have hmm : mc.1 ∈ p₀.members := by
        have h := (List.of_mem_zip hmc).1
        subst hp
        have : (p₀.complete p₁).toBlockShape.members = p₀.members := by rw [hq]; rfl
        rw [← this]; exact h
      have hmem₀ : c₀ ∈ p₀.allCtors :=
        List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨mc.1, hmm, rfl⟩, hc₀⟩
      have hne : c₀.1.name = cA.1.name := (Prod.mk.inj hc₀e).1
      show ConLeche.reservedBasisNames.contains cA.1.name = false
      rw [← hne]
      exact hCres c₀ hmem₀
    · obtain ⟨j, cv', hj, rfl⟩ := hnewIall c hc
      rw [hall, List.getElem?_map] at hj
      cases hmsj : p₀.members[j]? with
      | none => rw [hmsj] at hj; exact nomatch hj
      | some ms =>
        rw [hmsj] at hj
        obtain rfl : ms.cvT = cv' := by simpa using hj
        have hms := List.mem_of_getElem? hmsj
        have hrun₁ : ∃ q, ConLeche.checkBlockTele (fueledOps .verified F) env p₀.nP ms = .ok q := by
          rw [hmem0] at hms
          rcases List.mem_cons.mp hms with rfl | hms'
          · exact ⟨_, htele0⟩
          · obtain ⟨i, hi⟩ := List.getElem?_of_mem hms'
            obtain ⟨q, -, hq'⟩ := (ConLeche.checkBlockTeles_inv hteles).2 i ms hi
            exact ⟨q, hq'⟩
        obtain ⟨q, hq'⟩ := hrun₁
        unfold ConLeche.checkBlockTele at hq'
        obtain ⟨u, hc', -⟩ := exceptBind_ok hq'
        cases u
        exact (ConLeche.checkConstantVal_inv hc').2.1
  · simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · obtain ⟨o, -, mI, rP, isK, rules, rfl⟩ := hnewRall c hc
      exact nomatch he
    · obtain ⟨cA, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
      exact nomatch he
    · obtain ⟨j, cv', hj, rfl⟩ := hnewIall c hc
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj he
      rw [hall, List.getElem?_map] at hj
      cases hmsj : p₀.members[j]? with
      | none => rw [hmsj] at hj; exact nomatch hj
      | some ms =>
        rw [hmsj] at hj
        obtain rfl : ms.cvT = cv' := by simpa using hj
        refine ⟨ms, List.mem_of_getElem? hmsj, rfl, ?_⟩
        have hm' : p₁.members.getD (0 + j) default = ms := by
          rw [hq, Nat.zero_add, List.getD_eq_getElem?_getD]
          show (p₀.members[j]?).getD default = ms
          rw [hmsj]; rfl
        rw [blockCapsAt_nparams, blockCapsAt_nIdx, hm', hq]
        rfl

omit [SetTheory V] in
/-- The tables' stage adds its members' tables. -/
theorem checkBlockTables_tables {q : BlockShape} :
    ∀ {l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))} {env env₂ : Env},
      ConLeche.checkBlockTables (m := CheckM) q l env = .ok env₂ →
      ∃ newQ : List ProjTable, env₂.tables = newQ ++ env.tables ∧
        ∀ t ∈ newQ, ∃ e ∈ l, t.structName = e.1.cvT.name
  | [], env, env₂, h => by
    simp only [ConLeche.checkBlockTables, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨[], by rw [h]; rfl, fun _ h => nomatch h⟩
  | (ms, ctorsA, sortss) :: rest, env, env₂, h => by
    unfold ConLeche.checkBlockTables at h
    obtain ⟨env', henv', h⟩ := exceptBind_ok h
    obtain ⟨newQ, hQ, hall⟩ := checkBlockTables_tables h
    have hlift : ∀ t ∈ newQ, ∃ e ∈ (ms, ctorsA, sortss) :: rest, t.structName = e.1.cvT.name :=
      fun t ht => by
        obtain ⟨e, he, hn⟩ := hall t ht
        exact ⟨e, List.mem_cons_of_mem _ he, hn⟩
    have hsame : env' = env → ∃ newQ : List ProjTable, env₂.tables = newQ ++ env.tables ∧
        ∀ t ∈ newQ, ∃ e ∈ (ms, ctorsA, sortss) :: rest, t.structName = e.1.cvT.name := fun he =>
      ⟨newQ, by rw [hQ, he], hlift⟩
    revert henv'
    split
    · split
      · intro hh
        obtain ⟨tbl, htn, rfl⟩ := ConLeche.Semantics.checkStructProjTable_shape hh
        refine ⟨newQ ++ [tbl], by rw [hQ]; simp, fun t ht => ?_⟩
        rcases List.mem_append.mp ht with ht | ht
        · exact hlift t ht
        · rw [List.mem_singleton.mp ht]
          exact ⟨_, List.mem_cons_self, htn⟩
      · intro hh
        simp only [pure, Except.pure, Except.ok.injEq] at hh
        exact hsame hh.symm
    · intro hh
      simp only [pure, Except.pure, Except.ok.injEq] at hh
      exact hsame hh.symm

omit [SetTheory V] in
/-- **The ordinary install's tables and its fresh members.** -/
theorem declBlockRun_tables {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    {p₀ : BlockParts} (hrun : ConLeche.Semantics.DeclBlockRun F env block p₀ env₂) :
    (∀ ms ∈ p₀.members, env.find? ms.cvT.name = none) ∧
    ∃ newQ : List ProjTable, env₂.tables = newQ ++ env.tables ∧
      ∀ t ∈ newQ, ∃ ms ∈ p₀.members, t.structName = ms.cvT.name := by
  obtain ⟨-, -, isRec, env₁, cvTas, p₁, p, ctorsAs, sortsss, ctx, holes, rd, Ms, kinds,
    nfs, nodes, st, isorts, outR, hInd, hp, -, -, -, -, -, -, -, -, -, hTbl⟩ := hrun
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, hmem0, hcvTas, hq, hcons, htele0, hteles, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  refine ⟨?_, ?_⟩
  · intro ms hms
    have hrun₁ : ∃ q, ConLeche.checkBlockTele (fueledOps .verified F) env p₀.nP ms = .ok q := by
      rw [hmem0] at hms
      rcases List.mem_cons.mp hms with rfl | hms'
      · exact ⟨_, htele0⟩
      · obtain ⟨i, hi⟩ := List.getElem?_of_mem hms'
        obtain ⟨q, -, hq'⟩ := (ConLeche.checkBlockTeles_inv hteles).2 i ms hi
        exact ⟨q, hq'⟩
    obtain ⟨q, hq'⟩ := hrun₁
    unfold ConLeche.checkBlockTele at hq'
    obtain ⟨u, hc, -⟩ := exceptBind_ok hq'
    cases u
    exact (ConLeche.checkConstantVal_inv hc).1
  · obtain ⟨newQ, hQ, hall⟩ := checkBlockTables_tables hTbl
    refine ⟨newQ, ?_, fun t ht => ?_⟩
    · rw [hQ, consBlockRecsT_tables 0, consBlockCtors_tables, hcons, consBlockInds_tables]
    · obtain ⟨e, he, hn⟩ := hall t ht
      have hm := (List.of_mem_zip he).1
      subst hp
      refine ⟨e.1, ?_, hn⟩
      have : (p₀.complete p₁).toBlockShape.members = p₀.members := by rw [hq]; rfl
      rw [← this]; exact hm

/-! ## A member's reduct -/

/-- A member against its reduction. -/
structure MemberReduct (F : Nat) (env : Env) (nP : Nat) (m₀ m : MemberShape) : Prop where
  name : m.cvT.name = m₀.cvT.name
  lps : m.cvT.levelParams = m₀.cvT.levelParams
  nIdx : m.nIdx = m₀.nIdx
  ctors : m.ctors = m₀.ctors
  how : (ConLeche.formerDefHeaded m₀.cvT = false ∧ m = m₀) ∨
    (ConLeche.formerDefHeaded m₀.cvT = true ∧ ConLeche.litGuardFamilies.contains m₀.cvT.name = false ∧
      ConLeche.checkConstantVal (fueledOps .verified F) env m₀.cvT = .ok () ∧
      ConLeche.checkConstantVal (fueledOps .verified F) env m.cvT = .ok () ∧
      (fueledOps .verified F).isDefEq env 0 m₀.cvT.type m.cvT.type = .ok true ∧
      reducedFormer (fueledOps .verified F) env m₀.cvT (nP + m₀.nIdx) = .ok m.cvT)

omit [SetTheory V] in
theorem reduceMember_inv {F : Nat} {env : Env} {nP : Nat} {m₀ m : MemberShape}
    (h : reduceMember (m := CheckM) (fueledOps .verified F) env nP m₀ = .ok m) :
    MemberReduct F env nP m₀ m := by
  unfold reduceMember at h
  by_cases hd : ConLeche.formerDefHeaded m₀.cvT = true
  · rw [ite_eq_left hd] at h
    by_cases hg : ConLeche.litGuardFamilies.contains m₀.cvT.name = true
    · rw [ite_eq_left hg] at h
      exact nomatch h
    rw [ite_eq_right hg] at h
    obtain ⟨u₁, h₁, h⟩ := exceptBind_ok h
    cases u₁
    obtain ⟨cvR, hR, h⟩ := exceptBind_ok h
    obtain ⟨u₂, h₂, h⟩ := exceptBind_ok h
    cases u₂
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    cases b with
    | false => simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
    | true =>
      simp only [pure, Except.pure, Except.ok.injEq, ↓reduceIte] at h
      subst h
      have hrf : cvR = { m₀.cvT with type := cvR.type } := by
        simp only [reducedFormer, Bind.bind, Except.bind] at hR
        split at hR
        · exact nomatch hR
        · cases hR; rfl
      refine ⟨by rw [hrf], by rw [hrf], rfl, rfl, .inr ⟨hd, by simpa using hg, h₁, h₂, hb, hR⟩⟩
  · rw [ite_eq_right hd] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, .inl ⟨by simpa using hd, rfl⟩⟩

omit [SetTheory V] in
theorem reduceMembers_mem {F : Nat} {env : Env} {nP : Nat} :
    ∀ {l l' : List MemberShape},
      reduceMembers (m := CheckM) (fueledOps .verified F) env nP l = .ok l' →
      ∀ m ∈ l', ∃ m₀ ∈ l, MemberReduct F env nP m₀ m
  | [], l', h, m, hm => by
    simp only [reduceMembers, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact nomatch hm
  | m₀ :: rest, l', h, m, hm => by
    unfold reduceMembers at h
    obtain ⟨m', hm', h⟩ := exceptBind_ok h
    obtain ⟨r', hr', h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨m₀, List.mem_cons_self, reduceMember_inv hm'⟩
    · obtain ⟨x, hx, hr⟩ := reduceMembers_mem hr' m hm
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

omit [SetTheory V] in
theorem find_member_of_nodup : ∀ {l : List MemberShape} {x : MemberShape},
    (l.map (·.cvT.name)).Nodup → x ∈ l → l.find? (·.cvT.name == x.cvT.name) = some x
  | [], _, _, hx => nomatch hx
  | y :: l, x, hn, hx => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp
    · have hne : y.cvT.name ≠ x.cvT.name := by
        have := (List.nodup_cons.mp hn).1
        intro he
        exact this (List.mem_map.mpr ⟨x, hx', he.symm⟩)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact find_member_of_nodup (List.nodup_cons.mp hn).2 hx'

/-! ## Back to what the group stores -/

omit [SetTheory V] in
theorem restoreBlock_eq {p₀ : BlockParts} {env env₃ : Env} {vs new : List ConstantInfo}
    (hnew : env₃.consts = new ++ (vs ++ env.consts)) :
    restoreBlock p₀ vs.length env env₃ =
      ⟨new.map (storedFormerOf p₀) ++ env.consts, env₃.tables⟩ := by
  unfold restoreBlock
  have hlen : env₃.consts.length - (vs.length + env.consts.length) = new.length := by
    rw [hnew]; simp
  have htake : env₃.consts.take new.length = new := by
    rw [hnew]; exact List.take_left' rfl
  rw [hlen, htake]

omit [SetTheory V] in
/-- **Where the stored environment differs from the job's**: at a member reduced, or a view. -/
theorem restore_find {F : Nat} {p₀ : BlockParts} {env env₃ : Env} {vs new : List ConstantInfo}
    {ms : List MemberShape} (hnew : env₃.consts = new ++ (vs ++ env.consts))
    (hnewI : ∀ c ∈ new, ∀ cv caps, c = .indInfo cv caps → ∃ m ∈ ms, cv = m.cvT ∧
      caps.nparams + caps.nIdx = p₀.nP + m.nIdx)
    (hmr : ∀ m ∈ ms, ∃ m₀ ∈ p₀.members, MemberReduct F env p₀.nP m₀ m)
    (hnd : (p₀.members.map (·.cvT.name)).Nodup)
    (hv : ∀ c ∈ vs, ViewOf env c) (n : Name) :
    (restoreBlock p₀ vs.length env env₃).find? n = env₃.find? n ∨
    (∃ (m₀ m : MemberShape) (caps : IndCaps), MemberReduct F env p₀.nP m₀ m ∧
      ConLeche.formerDefHeaded m₀.cvT = true ∧ caps.nparams + caps.nIdx = p₀.nP + m₀.nIdx ∧
      m₀.cvT.name = n ∧ env₃.find? n = some (.indInfo m.cvT caps) ∧
      (restoreBlock p₀ vs.length env env₃).find? n = some (.indInfo m₀.cvT caps)) ∨
    (∃ (cv cvR : ConstantVal) (caps : IndCaps), ViewFacts env cv cvR caps ∧ cv.name = n ∧
      env₃.find? n = some (.indInfo cvR caps) ∧
      (restoreBlock p₀ vs.length env env₃).find? n = some (.indInfo cv caps)) := by
  rw [restoreBlock_eq hnew]
  have h₃ : env₃.find? n = (new.find? (·.name == n)).or
      ((⟨vs ++ env.consts, env.tables⟩ : Env).find? n) := by
    show env₃.consts.find? (·.name == n) = _
    rw [hnew, List.find?_append]; rfl
  have h₂ : (⟨new.map (storedFormerOf p₀) ++ env.consts, env₃.tables⟩ : Env).find? n =
      ((new.find? (·.name == n)).map (storedFormerOf p₀)).or (env.find? n) := by
    show (new.map (storedFormerOf p₀) ++ env.consts).find? (·.name == n) = _
    rw [List.find?_append, List.find?_map]
    have hcomp : ((fun x : ConstantInfo => x.name == n) ∘ storedFormerOf p₀)
        = (fun x => x.name == n) := funext fun c => by
      simp only [Function.comp, ConLeche.Cached.storedFormerOf_name]
    rw [hcomp]; rfl
  rw [h₂, h₃]
  cases hfn : new.find? (·.name == n) with
  | some c =>
    simp only [Option.map_some]
    have hcm := List.mem_of_find?_eq_some hfn
    have hcn : c.name = n := by simpa using List.find?_some hfn
    cases c
    case indInfo cv caps =>
      obtain ⟨m, hm, rfl, hsum⟩ := hnewI _ hcm cv caps rfl
      obtain ⟨m₀, hm₀, hr⟩ := hmr m hm
      have hfind : p₀.members.find? (·.cvT.name == m.cvT.name) = some m₀ := by
        rw [hr.name]; exact find_member_of_nodup hnd hm₀
      have hf : storedFormerOf p₀ (.indInfo m.cvT caps) = .indInfo m₀.cvT caps := by
        simp only [storedFormerOf, hfind]
      rw [hf]
      rcases hr.how with ⟨-, rfl⟩ | ⟨hd, -⟩
      · exact .inl rfl
      · refine .inr (.inl ⟨m₀, m, caps, hr, hd, by rw [hsum, hr.nIdx], ?_, rfl, rfl⟩)
        rw [← hr.name]; exact hcn
    all_goals
      exact .inl rfl
  | none =>
    simp only [Option.map_none, Option.none_or]
    rcases find_views hv n with he | ⟨cv, cvR, caps, hn, hF, hV⟩
    · exact .inl he.symm
    · refine .inr (.inr ⟨cv, cvR, caps, hF, hn, hV, ?_⟩)
      rw [← hn]; exact hF.find

/-- **A former the stored environment has where the job's has its reduct.** -/
structure Swapped (env env₃ env₂ : Env) (n : Name) (cvR cvS : ConstantVal) (caps : IndCaps) : Prop where
  find₃ : env₃.find? n = some (.indInfo cvR caps)
  find₂ : env₂.find? n = some (.indInfo cvS caps)
  nameS : cvS.name = n
  nameR : cvR.name = n
  lps : cvR.levelParams = cvS.levelParams
  headed : ConLeche.formerDefHeaded cvS = true
  guard : ConLeche.litGuardFamilies.contains n = false
  resolve : cvS.type.constsResolve env = true
  boundR : cvR.type.constsResolve env = true
  ran : ∃ F, reducedFormer (fueledOps .verified F) env cvS (caps.nparams + caps.nIdx) = .ok cvR

/-- The two readings of a swapped former, at the input's carrier. -/
theorem Swapped_read {env : Env} {mp : EnvModelM V env} (hS : ShownFacts mp) (hcov : LfpCover mp [])
    {F nP : Nat} {m₀ m : MemberShape}
    (cases_ : (MemberReduct F env nP m₀ m ∧ ConLeche.formerDefHeaded m₀.cvT = true) ∨
      ∃ caps, ViewFacts env m₀.cvT m.cvT caps) (ψ : Name → Nat) :
    ∃ Ts Tr : Term, denote mp.base2.acval env ψ 0 m₀.cvT.type = some Ts ∧
      denote mp.base2.acval env ψ 0 m.cvT.type = some Tr ∧
      ∀ ρ : Nat → V, interp V ρ Ts = interp V ρ Tr := by
  rcases cases_ with ⟨hr, hd⟩ | ⟨caps, hF⟩
  · rcases hr.how with ⟨hd', -⟩ | ⟨-, -, h₁, h₂, hb, -⟩
    · rw [hd] at hd'; exact nomatch hd'
    · obtain ⟨Ts, Tr, h₃, h₄, -, -, heq⟩ := storedFormer_sem mp h₁ h₂ hb ψ
      exact ⟨Ts, Tr, h₃, h₄, heq⟩
  · obtain ⟨Tr, Ts, h₁, h₂, h₃⟩ := view_read hS hcov hF ψ
    exact ⟨Ts, Tr, h₂, h₁, fun ρ => (h₃ ρ).1⟩

omit [SetTheory V] in
/-- What `blockViews` returns are views. -/
theorem blockViews_views {F : Nat} {env : Env} :
    ∀ {cs : List Name} {vs : List ConstantInfo},
      blockViews (m := CheckM) (fueledOps .verified F) env cs = .ok vs → ∀ c ∈ vs, ViewOf env c
  | [], vs, h, c, hc => by
    simp only [blockViews, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact nomatch hc
  | n :: cs, vs, h, c, hc => by
    unfold blockViews at h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    have ih := blockViews_views hrest
    split at h
    · next cv caps hf =>
      by_cases hd : ConLeche.formerDefHeaded cv = true
      · rw [ite_eq_left hd] at h
        by_cases hg : ConLeche.litGuardFamilies.contains n = true
        · rw [ite_eq_left hg] at h
          exact nomatch h
        rw [ite_eq_right hg] at h
        obtain ⟨cvR, hR, h⟩ := exceptBind_ok h
        by_cases hsc : ConLeche.viewScoped (·.constsResolve env) cvR = true
        · simp only [hsc, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
          subst h
          rcases List.mem_cons.mp hc with rfl | hc'
          · have hnm : cv.name = n := ConLeche.Env.find?_name hf
            have hrf : cvR = { cv with type := cvR.type } := by
              simp only [reducedFormer, Bind.bind, Except.bind] at hR
              split at hR
              · exact nomatch hR
              · cases hR; rfl
            refine ⟨cv, cvR, caps, rfl, ⟨by rw [hnm]; exact hf, by rw [hrf], by rw [hrf], hd,
              by rw [hnm]; simpa using hg, hsc, F, hR⟩⟩
          · exact ih c hc'
        · simp [hsc, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      · rw [ite_eq_right hd] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ih c hc
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ih c hc

/-- A clause does not read which formers its block showed. -/
theorem LfpClause.withShown {acval : Name → (Name → Nat) → Term} {D : LfpDatum V}
    (h : LfpClause (V := V) acval D) (s : Nat → Option ConstantVal) :
    LfpClause (V := V) acval { D with shown := s } where
  kN := h.kN
  idxOk := h.idxOk
  maps := h.maps
  fitAcc := h.fitAcc
  fibre := h.fibre
  leaf := h.leaf
  mkZero := h.mkZero
  mkInj := h.mkInj
  ctor := h.ctor
  parsLen := h.parsLen
  parsSat := h.parsSat
  parsSatInv := h.parsSatInv
  resIdxFit := h.resIdxFit
  injNePt := h.injNePt
  injFrame := h.injFrame
  fieldsOk := h.fieldsOk

/-! ### Across the swap back -/

section Back

variable {env env₃ env₂ : Env}

open Classical in
/-- Where the stored former differs from the one the job read, that one. -/
noncomputable def shownAt (env₃ env₂ : Env) (D : LfpDatum V) (mm : Nat) : Option ConstantVal :=
  match env₃.find? (D.member mm), env₂.find? (D.member mm) with
  | some (.indInfo c₃ _), some (.indInfo c₂ _) => if c₃ = c₂ then none else some c₃
  | _, _ => none

/-- A new block's record at the stored environment. -/
noncomputable def reshown (env₃ env₂ : Env) (D : LfpDatum V) : LfpDatum V :=
  { D with shown := shownAt env₃ env₂ D }

open Classical in
/-- A block's record at the stored environment. -/
noncomputable def reshow (mp : EnvModelM V env) (env₃ env₂ : Env) (D : LfpDatum V) : LfpDatum V :=
  if D ∈ mp.lfpBlocks then D else reshown env₃ env₂ D

omit [SetTheory V] in
/-- **The job's environment against the stored one.** -/
theorem formerSwap_of_swapped
    (hc : ∀ n, env₂.find? n = env₃.find? n ∨
      ∃ cvR cvS caps, Swapped env env₃ env₂ n cvR cvS caps)
    (hmem : ∀ c ∈ env₂.consts, (∀ cv caps, c ≠ .indInfo cv caps) → c ∈ env₃.consts)
    (htab : env₂.tables = env₃.tables) : FormerSwap env₃ env₂ where
  find := fun n => (hc n).imp id fun ⟨cvR, cvS, caps, h⟩ =>
    ⟨cvR, cvS, caps, h.find₃, h.find₂, h.nameS.trans h.nameR.symm, h.lps.symm, h.guard⟩
  mem := hmem
  tables := htab

/-- **The recursors' law back**: a stored former that does not show its telescope passes no
rescue, and its value is the reduct's. -/
theorem recRules_back {m₃ : EnvModel V env₃} {m₂ : EnvModel V env₂} (hac : m₂.acval = m₃.acval)
    (h : FormerSwap env₃ env₂)
    (hc : ∀ n, env₂.find? n = env₃.find? n ∨
      ∃ cvR cvS caps, Swapped env env₃ env₂ n cvR cvS caps)
    (hrd : ∀ n cvR cvS caps, Swapped env env₃ env₂ n cvR cvS caps → ∀ ψ, ∃ Ts Tr : Term,
      denote m₃.acval env₃ ψ 0 cvS.type = some Ts ∧ denote m₃.acval env₃ ψ 0 cvR.type = some Tr ∧
      ∀ ρ : Nat → V, interp V ρ Ts = interp V ρ Tr)
    (hR : ∀ φ, RecRules m₃ φ) (φ : Name → Nat) : RecRules m₂ φ := by
  intro n cv mI rP isK rules hf rl hrl
  have hl := hR φ n cv mI rP isK rules
    ((h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mp hf) rl hrl
  refine RecRuleLaw.formerSwap h hac (fun φ' cvj us hz => ?_) hl
  refine FamNZ.formerSwap h m₃.acval_params ?_ ?_ hz
  · intro T cv₃ cv₂ caps φ'' us' h₃ h₂ hne hnv
    exfalso
    rcases hc T with he | ⟨cvR, cvS, caps', hS⟩
    · rw [he, h₃] at h₂
      exact hne (by simpa using h₂.symm)
    · rw [hS.find₂] at h₂
      obtain ⟨rfl, -⟩ : cvS = cv₂ ∧ caps' = caps := by simpa using h₂
      have hfalse := ConLeche.Model.holds_false_of_isNever hnv φ''
      have hnone : ConLeche.formerResSort cvS.type = none := by
        have := hS.headed
        simpa [ConLeche.formerDefHeaded] using this
      simp [ConLeche.formerZ, hnone, ConLeche.PropWhen.holds] at hfalse
  · intro T cv₃ cv₂ caps ψ ta _ h₃ h₂ hta ρ
    rcases hc T with he | ⟨cvR, cvS, caps', hS⟩
    · rw [he, h₃] at h₂
      obtain rfl : cv₃ = cv₂ := by simpa using h₂
      exact ⟨ta, hta, rfl⟩
    · rw [hS.find₂] at h₂
      rw [hS.find₃] at h₃
      obtain ⟨rfl, -⟩ : cvS = cv₂ ∧ caps' = caps := by simpa using h₂
      obtain ⟨rfl, -⟩ : cvR = cv₃ ∧ caps' = caps := by simpa using h₃
      obtain ⟨Ts, Tr, h₁', h₂', heq⟩ := hrd T cvR cvS caps' hS ψ
      rw [hta] at h₂'
      obtain rfl := Option.some.inj h₂'
      exact ⟨Ts, h₁', (heq ρ).symm⟩

/-- **The projections' law back.** -/
theorem towerOk_back {m₃ : EnvModel V env₃} {m₂ : EnvModel V env₂} (hac : m₂.acval = m₃.acval)
    (h : FormerSwap env₃ env₂)
    (hc : ∀ n, env₂.find? n = env₃.find? n ∨
      ∃ cvR cvS caps, Swapped env env₃ env₂ n cvR cvS caps)
    (hrd : ∀ n cvR cvS caps, Swapped env env₃ env₂ n cvR cvS caps → ∀ ψ, ∃ Ts Tr : Term,
      denote m₃.acval env₃ ψ 0 cvS.type = some Ts ∧ denote m₃.acval env₃ ψ 0 cvR.type = some Tr ∧
      ∀ ρ : Nat → V, interp V ρ Ts = interp V ρ Tr)
    (hT : ∀ φ, TowerOk m₃ φ) (φ : Name → Nat) : TowerOk m₂ φ := by
  have hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denote m₃.acval env₃ ψ d e = denote m₃.acval env₂ ψ d e :=
    fun ψ d e => denote_formerSwap h ψ d e
  intro T i entry hf
  have hf₀ : env₃.findProj? T i = some entry := by rw [h.projEq]; exact hf
  refine TowerEntryLaw.formerSwap h hac (fun us cvC Ta hus hTa hgd => .inl ?_) (hT φ T i entry hf₀)
  rcases hgd with ⟨cvT, caps, s, hT', hs, hz⟩ | hr | ⟨cvT, caps, u, hT', ht, hu⟩
  · rcases hc entry.structName with he | ⟨cvR, cvS, caps', hS⟩
    · exact .inl ⟨cvT, caps, s, by rw [← he]; exact hT', hs, hz⟩
    · rw [hS.find₂] at hT'
      obtain ⟨rfl, -⟩ : cvS = cvT ∧ caps' = caps := by simpa using hT'
      have := hS.headed
      simp [ConLeche.formerDefHeaded, hs] at this
  · refine .inr (.inl fun ds b hrd' hl' => hr ds b ?_ hl')
    rw [hac, ← hde]; exact hrd'
  · obtain ⟨cv₃, hf₃, hlp⟩ := h.find_ind_back hT'
    refine .inr (.inr ⟨cv₃, caps, u, hf₃, fun ta hta ρ => ?_, hu.imp id fun hr ds b hrd' hl' =>
      hr ds b (by rw [hac, ← hde]; exact hrd') hl'⟩)
    rw [denote_instLevels m₃.acval_params φ] at hta
    rcases hc entry.structName with he | ⟨cvR, cvS, caps', hS⟩
    · rw [he, hf₃] at hT'
      obtain rfl : cv₃ = cvT := by simpa using hT'
      refine ht ta ?_ ρ
      rw [hac, ← hde, denote_instLevels m₃.acval_params φ]
      exact hta
    · rw [hS.find₂] at hT'
      rw [hS.find₃] at hf₃
      obtain ⟨rfl, -⟩ : cvS = cvT ∧ caps' = caps := by simpa using hT'
      obtain ⟨rfl, -⟩ : cvR = cv₃ ∧ caps' = caps := by simpa using hf₃
      obtain ⟨Ts, Tr, h₁, h₂, heq⟩ := hrd _ _ _ _ hS (Level.substFn φ cvR.levelParams us)
      rw [hta] at h₂
      obtain rfl := Option.some.inj h₂
      rw [← heq ρ]
      refine ht Ts ?_ ρ
      rw [hac, ← hde, denote_instLevels m₃.acval_params φ, hlp]
      exact h₁

/-- **The fibres back**: a former that shows its telescope is not swapped. -/
theorem indStrict_back {m₃ : EnvModel V env₃} {m₂ : EnvModel V env₂} (hac : m₂.acval = m₃.acval)
    (h : FormerSwap env₃ env₂)
    (hc : ∀ n, env₂.find? n = env₃.find? n ∨
      ∃ cvR cvS caps, Swapped env env₃ env₂ n cvR cvS caps)
    (hI : IndStrictOk m₃) : IndStrictOk m₂ := by
  intro I cv caps hf hfl ψ ab n hread hn ρ vs hsp
  rw [hac] at hread ⊢
  rw [← denote_formerSwap h] at hread
  rcases hc I with he | ⟨cvR, cvS, caps', hS⟩
  · exact hI I cv caps (by rw [← he]; exact hf) hfl ψ ab n hread hn ρ vs hsp
  · rw [hS.find₂] at hf
    obtain ⟨rfl, -⟩ : cvS = cv ∧ caps' = caps := by simpa using hf
    rw [hS.headed] at hfl
    exact nomatch hfl

omit [SetTheory V] in
theorem recCtors_back (h : FormerSwap env₃ env₂) (hr : ConLeche.RecCtorsStored env₃) :
    ConLeche.RecCtorsStored env₂ := by
  intro n cv mI rP isK rules hf r hrr
  obtain ⟨cvj, cnP, cnF, hc⟩ := hr n cv mI rP isK rules
    ((h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mp hf) r hrr
  exact ⟨cvj, cnP, cnF, (h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mpr hc⟩

omit [SetTheory V] in
theorem projOk_back (h : FormerSwap env₃ env₂) (hp : ProjOkT env₃) : ProjOkT env₂ := by
  intro T tbl hf i hi
  have hf₀ : env₃.findTable? T = some tbl := by rw [h.tableEq]; exact hf
  obtain ⟨h2, h3, h4, h5, ⟨cvT, caps, hT, hlT⟩, ⟨cvC, hC, hlC, hstrip⟩⟩ := hp T tbl hf₀ i hi
  obtain ⟨cvT', hT', hl'⟩ := h.find_ind hT
  exact ⟨h2, h3, h4, h5, ⟨cvT', caps, hT', hl'.trans hlT⟩,
    ⟨cvC, (h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mpr hC, hlC, hstrip⟩⟩

omit [SetTheory V] in
theorem shownAt_same {D : LfpDatum V} {mm : Nat} {cv : ConstantVal} {caps : IndCaps}
    (h₃ : env₃.find? (D.member mm) = some (.indInfo cv caps))
    (h₂ : env₂.find? (D.member mm) = some (.indInfo cv caps)) :
    shownAt env₃ env₂ D mm = none := by
  simp [shownAt, h₃, h₂]

omit [SetTheory V] in
theorem shownAt_swapped {D : LfpDatum V} {mm : Nat} {cvR cvS : ConstantVal} {caps : IndCaps}
    (h₃ : env₃.find? (D.member mm) = some (.indInfo cvR caps))
    (h₂ : env₂.find? (D.member mm) = some (.indInfo cvS caps)) (hne : cvR ≠ cvS) :
    shownAt env₃ env₂ D mm = some cvR := by
  simp [shownAt, h₃, h₂, hne]

/-- **A new block's record at the stored environment**: the same, each member read at the former
the job read. -/
theorem record_back (mp₃ : EnvModelM V env₃) (h : FormerSwap env₃ env₂)
    (hc : ∀ n, env₂.find? n = env₃.find? n ∨
      ∃ cvR cvS caps, Swapped env env₃ env₂ n cvR cvS caps)
    (hrd : ∀ n cvR cvS caps, Swapped env env₃ env₂ n cvR cvS caps → ∀ ψ, ∃ Ts Tr : Term,
      denote mp₃.base2.acval env₃ ψ 0 cvS.type = some Ts ∧
      denote mp₃.base2.acval env₃ ψ 0 cvR.type = some Tr ∧
      ∀ ρ : Nat → V, interp V ρ Ts = interp V ρ Tr)
    {D : LfpDatum V} (hD : D ∈ mp₃.lfpBlocks) (hnone : ∀ mm, D.shown mm = none) :
    LfpClause mp₃.base2.acval (reshown env₃ env₂ D) ∧ LfpStored env₂ (reshown env₃ env₂ D) ∧
      LfpReads mp₃.base2.acval env₂ (reshown env₃ env₂ D) ∧
      LfpCtorReads mp₃.base2.acval env₂ (reshown env₃ env₂ D) ∧
      LfpCaps env₂ (reshown env₃ env₂ D) := by
  obtain ⟨hL, ⟨hst, hstC⟩, hrd₃, ⟨hnk, hrdC⟩, ⟨hcK, hcC⟩⟩ := mp₃.lfp_ok D hD
  have hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denote mp₃.base2.acval env₃ ψ d e = denote mp₃.base2.acval env₂ ψ d e :=
    fun ψ d e => denote_formerSwap h ψ d e
  have hctor : ∀ {n : Name} {cv : ConstantVal} {a b : Nat}, env₃.find? n = some (.ctorInfo cv a b) →
      env₂.find? n = some (.ctorInfo cv a b) := fun hf =>
    (h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mpr hf
  -- a member, on the two sides
  have hmem : ∀ {mm : Nat}, mm < D.k → ∃ cv caps cv₂, env₃.find? (D.member mm) = some (.indInfo cv caps) ∧
      env₂.find? (D.member mm) = some (.indInfo cv₂ caps) ∧ ConLeche.formerDefHeaded cv = false ∧
      (reshown env₃ env₂ D).formerAt mm cv₂ = cv ∧ D.formerAt mm cv = cv ∧
      ((cv₂ = cv ∧ shownAt env₃ env₂ D mm = none) ∨
        (Swapped env env₃ env₂ (D.member mm) cv cv₂ caps ∧ shownAt env₃ env₂ D mm = some cv)) := by
    intro mm hmm
    obtain ⟨cv, caps, hf, ⟨-, hsh⟩, -⟩ := hrd₃ mm hmm
    have hflat : ConLeche.formerDefHeaded cv = false := by
      rcases hsh with ⟨-, h₂⟩ | ⟨f, hs, -⟩
      · exact h₂
      · rw [hnone] at hs; exact nomatch hs
    have hfa : D.formerAt mm cv = cv := by simp [LfpDatum.formerAt, hnone]
    rcases hc (D.member mm) with he | ⟨cvR, cvS, caps', hS⟩
    · have hf₂ : env₂.find? (D.member mm) = some (.indInfo cv caps) := by rw [he]; exact hf
      have hsn := shownAt_same (D := D) hf hf₂
      exact ⟨cv, caps, cv, hf, hf₂, hflat, by simp [LfpDatum.formerAt, reshown, hsn], hfa, .inl ⟨rfl, hsn⟩⟩
    · rw [hS.find₃] at hf
      obtain ⟨rfl, rfl⟩ : cvR = cv ∧ caps' = caps := by simpa using hf
      have hne : cvR ≠ cvS := fun he => by
        rw [he, hS.headed] at hflat; exact nomatch hflat
      have hsn := shownAt_swapped (D := D) hS.find₃ hS.find₂ hne
      exact ⟨cvR, caps', cvS, hS.find₃, hS.find₂, hflat,
        by simp [LfpDatum.formerAt, reshown, hsn], hfa, .inr ⟨hS, hsn⟩⟩
  refine ⟨hL.withShown _, ⟨fun mm hmm => ?_, fun c hc' j hj => ?_⟩, fun mm hmm => ?_,
    ⟨hnk, fun c hc' j hj => ?_⟩, ⟨fun mm hmm => ?_, fun c hc' j hj => ?_⟩⟩
  · obtain ⟨cv, caps, cv₂, -, hf₂, -⟩ := hmem hmm
    exact ⟨cv₂, caps, hf₂⟩
  · obtain ⟨cv, a, b, hf⟩ := hstC c hc' j hj
    exact ⟨cv, a, b, hctor hf⟩
  · obtain ⟨cv, caps, cv₂, hf, hf₂, hflat, hfa₂, hfa, hcase⟩ := hmem hmm
    obtain ⟨cv₀, caps₀, hf₀, -, hab⟩ := hrd₃ mm hmm
    rw [hf] at hf₀
    obtain ⟨rfl, rfl⟩ : cv = cv₀ ∧ caps = caps₀ := by simpa using hf₀
    rw [hfa] at hab
    refine ⟨cv₂, caps, hf₂, ⟨fun _ => ?_, ?_⟩, fun ψ => ?_⟩
    · rcases hcase with ⟨rfl, -⟩ | ⟨hS, -⟩
      · exact hfa₂
      · rename_i hfl
        rw [hS.headed] at hfl; exact nomatch hfl
    · rcases hcase with ⟨rfl, hsn⟩ | ⟨hS, hsn⟩
      · exact .inl ⟨hsn, hflat⟩
      · have hwf := mp₃.base2.wf.consts _ (ConLeche.Env.find?_mem hf)
        refine .inr ⟨cv, hsn, hS.nameR.trans hS.nameS.symm, hS.lps, hwf.1, hwf.2.2.2.1, ?_, ?_, fun ψ => ?_⟩
        · exact ConstsBound.of_isSome (env₀ := env₃) (fun n hn => by rw [← h.isSomeEq]; exact hn)
            (ConLeche.Verify.envWF_constsBound mp₃.base2.wf _ (ConLeche.Env.find?_mem hf)).1
        · exact hwf.2.1
        · obtain ⟨Ts, Tr, h₁, h₂, heq⟩ := hrd _ _ _ _ hS ψ
          refine ⟨Tr, Ts, by rw [← hde]; exact h₂, by rw [← hde]; exact h₁, fun ρ => ⟨heq ρ, ?_⟩⟩
          have := mp₃.mem_type _ (ConLeche.Env.find?_mem hf) ψ Tr h₂ ρ
          rwa [ConLeche.Env.find?_name hf] at this
    · rw [hfa₂]
      obtain ⟨ab, hta, hmap⟩ := hab ψ
      exact ⟨ab, by rw [← hde]; exact hta, hmap⟩
  · obtain ⟨cv, nPc, nF, hf, hcf, hlps, hpars, A, hA, hocc, hrdA⟩ := hrdC c hc' j hj
    refine ⟨cv, nPc, nF, hctor hf, hcf, fun mm hmm => ?_, fun ψ dsC bodyC hrd' hle => ?_, A, hA, hocc,
      fun ψ => ?_⟩
    · obtain ⟨cvm, caps, hfm, hl⟩ := hlps mm hmm
      obtain ⟨cvm', hfm', hl'⟩ := h.find_ind hfm
      exact ⟨cvm', caps, hfm', hl'.trans hl⟩
    · rw [← hde] at hrd'
      exact hpars ψ dsC bodyC hrd' hle
    · obtain ⟨h1, h2, ab, Tys, hta, hlab, hlT, hTys, hab⟩ := hrdA ψ
      refine ⟨h1, h2, ab, Tys, by rw [← hde]; exact hta, hlab, hlT, fun mm hmm => ?_, hab⟩
      obtain ⟨cvm, caps, ty, hfm, hty, hr⟩ := hTys mm hmm
      obtain ⟨cv, caps', cv₂, hf, hf₂, -, hfa₂, hfa, -⟩ := hmem hmm
      rw [hf] at hfm
      obtain ⟨rfl, rfl⟩ : cv = cvm ∧ caps' = caps := by simpa using hfm
      refine ⟨cv₂, caps', ty, hf₂, by rw [hfa₂]; rw [hfa] at hty; exact hty, ?_⟩
      rw [← hde]; exact hr
  · obtain ⟨cv, caps, hf, hz, hlen⟩ := hcK mm hmm
    obtain ⟨cv', caps', cv₂, hf', hf₂, -, hfa₂, hfa, -⟩ := hmem hmm
    rw [hf] at hf'
    obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
    rw [hfa] at hz
    exact ⟨cv₂, caps, hf₂, by rw [hfa₂]; exact hz, hlen⟩
  · obtain ⟨cv, nPc, nF, hf, hshape⟩ := hcC c hc' j hj
    exact ⟨cv, nPc, nF, hctor hf, hshape⟩

omit [SetTheory V] in
theorem LfpOwn.withShown {env : Env} {D : LfpDatum V} (h : LfpOwn env D)
    (s : Nat → Option ConstantVal) : LfpOwn env { D with shown := s } where
  ctors := h.ctors
  noCtors := h.noCtors
  lvlNodup := h.lvlNodup
  ctorConcl := h.ctorConcl

omit [SetTheory V] in
theorem EtaFamiliesClosed_formerSwap {env₀ env₁ : Env} (h : FormerSwap env₀ env₁)
    (hE : ConLeche.EtaFamiliesClosed env₀) : ConLeche.EtaFamiliesClosed env₁ := by
  intro T cvT caps hf he hr
  obtain ⟨cv₀, hf₀, -⟩ := h.find_ind_back hf
  obtain ⟨cvC, hC⟩ := hE T cv₀ caps hf₀ he hr
  exact ⟨cvC, (h.find_of_ne fun _ _ he => ConstantInfo.noConfusion he).mpr hC⟩

theorem reshow_of_mem {mp : EnvModelM V env} {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) :
    reshow mp env₃ env₂ D = D := by
  simp [reshow, hD]

theorem reshow_of_not_mem {mp : EnvModelM V env} {D : LfpDatum V} (hD : D ∉ mp.lfpBlocks) :
    reshow mp env₃ env₂ D = reshown env₃ env₂ D := by
  simp [reshow, hD]

/-- The fields a record's cover reads. -/
theorem reshow_fields (mp : EnvModelM V env) (D : LfpDatum V) :
    (reshow mp env₃ env₂ D).names = D.names ∧ (reshow mp env₃ env₂ D).k = D.k ∧
      (reshow mp env₃ env₂ D).N = D.N := by
  by_cases hD : D ∈ mp.lfpBlocks
  · rw [reshow_of_mem hD]; exact ⟨rfl, rfl, rfl⟩
  · rw [reshow_of_not_mem hD]; exact ⟨rfl, rfl, rfl⟩

end Back

/-! ## The step -/

omit [SetTheory V] in
theorem reduceMembers_lps {F : Nat} {env : Env} {nP : Nat} {p₀ : BlockParts} {ms : List MemberShape}
    (h : reduceMembers (m := CheckM) (fueledOps .verified F) env nP p₀.members = .ok ms) :
    ({ p₀ with members := ms } : BlockParts).lps = p₀.lps := by
  show (ms.head?.map (·.cvT.levelParams)).getD [] = (p₀.members.head?.map (·.cvT.levelParams)).getD []
  cases hm : p₀.members with
  | nil =>
    rw [hm] at h
    simp only [reduceMembers, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | cons m₀ rest =>
    rw [hm] at h
    unfold reduceMembers at h
    obtain ⟨m', hm', h⟩ := exceptBind_ok h
    obtain ⟨r', -, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    exact (reduceMember_inv hm').lps

omit [SetTheory V] in
/-- The classes as swapped formers. -/
theorem restore_swapped {F : Nat} {p₀ : BlockParts} {env env₃ env₂ : Env} (henv : EnvWF env)
    (hclass : ∀ n, env₂.find? n = env₃.find? n ∨
      (∃ (m₀ m : MemberShape) (caps : IndCaps), MemberReduct F env p₀.nP m₀ m ∧
        ConLeche.formerDefHeaded m₀.cvT = true ∧ caps.nparams + caps.nIdx = p₀.nP + m₀.nIdx ∧
        m₀.cvT.name = n ∧ env₃.find? n = some (.indInfo m.cvT caps) ∧
        env₂.find? n = some (.indInfo m₀.cvT caps)) ∨
      (∃ (cv cvR : ConstantVal) (caps : IndCaps), ViewFacts env cv cvR caps ∧ cv.name = n ∧
        env₃.find? n = some (.indInfo cvR caps) ∧ env₂.find? n = some (.indInfo cv caps))) :
    ∀ n, env₂.find? n = env₃.find? n ∨ ∃ cvR cvS caps, Swapped env env₃ env₂ n cvR cvS caps := by
  intro n
  rcases hclass n with he | ⟨m₀, m, caps, hr, hd, hsum, hn, h3, h2⟩ | ⟨cv, cvR, caps, hF, hn, h3, h2⟩
  · exact .inl he
  · rcases hr.how with ⟨hd', -⟩ | ⟨-, hg, h₁, h₂, -, hrf⟩
    · rw [hd] at hd'; exact nomatch hd'
    · exact .inr ⟨m.cvT, m₀.cvT, caps, h3, h2, hn, hr.name.trans hn, hr.lps, hd, by rw [← hn]; exact hg,
        (checkConstantVal_typeWF h₁).2.2.1, (checkConstantVal_typeWF h₂).2.2.1,
        F, by rw [hsum]; exact hrf⟩
  · have hsc := hF.closed
    simp only [ConLeche.viewScoped, Bool.and_eq_true] at hsc
    have hres₀ := (henv.consts _ (ConLeche.Env.find?_mem hF.find)).2.2.1
    exact .inr ⟨cvR, cv, caps, h3, h2, hn, hF.name.trans hn, hF.lps, hF.headed, by rw [← hn]; exact hF.guard,
      hres₀, hsc.1.2, hF.ran⟩

omit [SetTheory V] in
/-- What the stored environment has other than formers, the job's has. -/
theorem restore_mem {F : Nat} {p₀ : BlockParts} {env env₃ env₂ : Env} {vs new : List ConstantInfo}
    {ms : List MemberShape}
    (hreq : env₂ = ⟨new.map (storedFormerOf p₀) ++ env.consts, env₃.tables⟩)
    (hnew : env₃.consts = new ++ (vs ++ env.consts))
    (_hnewI : ∀ c ∈ new, ∀ cv caps, c = .indInfo cv caps → ∃ m ∈ ms, cv = m.cvT ∧
      caps.nparams + caps.nIdx = p₀.nP + m.nIdx)
    (_hmr : ∀ m ∈ ms, ∃ m₀ ∈ p₀.members, MemberReduct F env p₀.nP m₀ m)
    (_hnd : (p₀.members.map (·.cvT.name)).Nodup) :
    ∀ c ∈ env₂.consts, (∀ cv caps, c ≠ .indInfo cv caps) → c ∈ env₃.consts := by
  intro c hc hne
  rw [hreq] at hc
  rw [hnew]
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    by_cases hdi : ∃ cv caps, d = .indInfo cv caps
    · obtain ⟨cv, caps, rfl⟩ := hdi
      have hind : ∃ cv', storedFormerOf p₀ (.indInfo cv caps) = .indInfo cv' caps := by
        simp only [storedFormerOf]
        split
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      obtain ⟨cv', hc'⟩ := hind
      exact absurd hc' (hne _ _)
    · have hsame : storedFormerOf p₀ d = d := by
        cases d <;> first | rfl | exact absurd ⟨_, _, rfl⟩ hdi
      rw [hsame]
      exact List.mem_append_left _ hd
  · exact List.mem_append_right _ (List.mem_append_right _ hc)

/-- **What a run needs of an environment to be read at its extensions.** -/
structure NatFacts (env : Env) : Prop where
  trio : (env.find? ConLeche.natName).isSome = true ∨ (env.find? ConLeche.natSuccName).isSome = true →
    (env.find? ConLeche.natName).isSome = true ∧ (env.find? ConLeche.natZeroName).isSome = true ∧
      (env.find? ConLeche.natSuccName).isSome = true

omit [SetTheory V] in
/-- **The second path's η-families.** -/
theorem blockViewedRun_etaClosed {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    {p₀ : BlockParts} (henv : EnvWF env) (hE : ConLeche.EtaFamiliesClosed env)
    (hrun : ConLeche.Semantics.BlockViewedRun F env block p₀ env₂) :
    ConLeche.EtaFamiliesClosed env₂ := by
  obtain ⟨ms, vs, env₃, hms, hvs, hrun₃, rfl⟩ := hrun
  have hv := blockViews_views hvs
  have hsh := ConLeche.Semantics.reduceMembers_shape hms
  have hmr := reduceMembers_mem hms
  obtain ⟨new, hnew, hnewI, -⟩ := declBlockRun_consts hrun₃
  have hnd : (p₀.members.map (·.cvT.name)).Nodup := by
    obtain ⟨-, hndM, -⟩ := hrun₃
    have : (ms.map (·.cvT.name)).Nodup := hndM
    rwa [hsh.1] at this
  have hclass := restore_find (F := F) (p₀ := p₀) (ms := ms) hnew hnewI hmr hnd hv
  have hreq := restoreBlock_eq (p₀ := p₀) hnew
  have h := formerSwap_of_swapped (restore_swapped (F := F) henv hclass)
    (restore_mem (F := F) hreq hnew hnewI hmr hnd) (by rw [hreq])
  exact EtaFamiliesClosed_formerSwap h (ConLeche.Semantics.declBlockRun_etaClosed
    (EtaFamiliesClosed_formerSwap (formerSwap_views hv) hE) hrun₃)

/-- **The block's second path, in the model.** -/
theorem declBlockViewed {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {p₀ : BlockParts}
    (mp : EnvModelM V env) (hS : ShownFacts mp) (hcov : LfpCover mp [])
    (hE : ConLeche.EtaFamiliesClosed env)
    (hlps₀ : ∀ ms ∈ p₀.members, ms.cvT.levelParams = p₀.lps)
    (hClps₀ : ∀ c ∈ p₀.allCtors, c.1.levelParams = p₀.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false)
    (hrun : ConLeche.Semantics.BlockViewedRun F env block p₀ env₂) (hN : NatFacts env) :
    ∃ (mp₂ : EnvModelM V env₂), LfpCover mp₂ [] ∧ ShownFacts mp₂ := by
  obtain ⟨ms, vs, env₃, hms, hvs, hrun₃, rfl⟩ := hrun
  have hv := blockViews_views hvs
  obtain ⟨mpV, hacV, hlV, hcovV⟩ := mp.toViews hS hcov hv
  have h₀ := formerSwap_views hv
  have hmr := reduceMembers_mem hms
  have hsh := ConLeche.Semantics.reduceMembers_shape hms
  have hlpsR := reduceMembers_lps hms
  obtain ⟨mp₃, r₃, hc₃⟩ := declBlockAt mpV (EtaFamiliesClosed_formerSwap h₀ hE)
    (fun m hm => by
      obtain ⟨m₀, hm₀, hr⟩ := hmr m hm
      rw [hr.lps, hlps₀ m₀ hm₀, hlpsR])
    (fun c hc => by
      rw [hlpsR]
      exact hClps₀ c (by rw [← hsh.2]; exact hc)) hrun₃ hcovV
  obtain ⟨new, hnew, hnewI, -⟩ := declBlockRun_consts hrun₃
  have hnd : (p₀.members.map (·.cvT.name)).Nodup := by
    obtain ⟨-, hndM, -⟩ := hrun₃
    have : (ms.map (·.cvT.name)).Nodup := hndM
    rwa [hsh.1] at this
  have hclass := restore_find (F := F) (p₀ := p₀) (ms := ms) hnew hnewI hmr hnd hv
  generalize henv₂ : restoreBlock p₀ vs.length env env₃ = env₂ at hclass
  have hreq := restoreBlock_eq (p₀ := p₀) hnew
  rw [henv₂] at hreq
  -- the stored environment extends the input
  obtain ⟨hfreshM, newQ, hQ, hQall⟩ := declBlockRun_tables hrun₃
  have htab' : env₂.tables = env₃.tables := by rw [hreq]
  have hfreshE : ∀ m ∈ ms, env.find? m.cvT.name = none := fun m hm => by
    have h₁ := hfreshM m hm
    cases hc : env.find? m.cvT.name with
    | none => rfl
    | some ci =>
      have hs := (h₀.isSomeEq m.cvT.name)
      rw [hc, h₁] at hs
      exact nomatch hs
  have hfd₂ : ∀ n ci, env.find? n = some ci → env₂.find? n = some ci := by
    intro n ci hf
    have hS₂ : env₂.find? n = ((new.find? (·.name == n)).map (storedFormerOf p₀)).or (env.find? n) := by
      rw [hreq]
      show (new.map (storedFormerOf p₀) ++ env.consts).find? (·.name == n) = _
      rw [List.find?_append, List.find?_map]
      have hcomp : ((fun x : ConstantInfo => x.name == n) ∘ storedFormerOf p₀)
          = (fun x => x.name == n) := funext fun c => by
        simp only [Function.comp, ConLeche.Cached.storedFormerOf_name]
      rw [hcomp]; rfl
    rw [hS₂]
    cases hfn : new.find? (·.name == n) with
    | none => simpa using hf
    | some c =>
      have hcm := List.mem_of_find?_eq_some hfn
      have hcn : c.name = n := by simpa using List.find?_some hfn
      obtain ⟨x, hx₁⟩ : ∃ x, (⟨vs ++ env.consts, env.tables⟩ : Env).find? n = some x := by
        cases hc : (⟨vs ++ env.consts, env.tables⟩ : Env).find? n with
        | some x => exact ⟨x, rfl⟩
        | none =>
          have hs := h₀.isSomeEq n
          rw [hf, hc] at hs
          exact nomatch hs
      have h₃ : env₃.find? n = some c := by
        show env₃.consts.find? (·.name == n) = _
        rw [hnew, List.find?_append, hfn]; rfl
      rw [r₃.find n x hx₁] at h₃
      obtain rfl := Option.some.inj h₃
      by_cases hdi : ∃ cv caps, x = .indInfo cv caps
      · obtain ⟨cv, caps, rfl⟩ := hdi
        obtain ⟨m, hm, rfl, -⟩ := hnewI _ hcm cv caps rfl
        have hnm : m.cvT.name = n := hcn
        have := hfreshM m hm
        rw [hnm, hx₁] at this
        exact nomatch this
      · have hsame : storedFormerOf p₀ x = x := by
          cases x <;> first | rfl | exact absurd ⟨_, _, rfl⟩ hdi
        rcases find_views hv n with he | ⟨cvs, cvR, capsv, -, -, h₃'⟩
        · rw [he, hf] at hx₁
          obtain rfl := Option.some.inj hx₁
          simp [hsame]
        · rw [hx₁] at h₃'
          exact absurd ⟨cvR, capsv, Option.some.inj h₃'⟩ hdi
  have hx : EnvExt env env₂ := by
    refine ⟨hfd₂, fun T hT => ?_, hN.trio⟩
    have hne : ∀ t ∈ newQ, (t.structName == T) = false := by
      intro t ht
      obtain ⟨m, hm, hn⟩ := hQall t ht
      have := hfreshE m hm
      rw [beq_eq_false_iff_ne]
      intro he
      rw [← hn, he] at this
      rw [this] at hT
      exact nomatch hT
    have hs₂ : (env₂.find? T).isSome = true := by
      cases hc : env.find? T with
      | none => rw [hc] at hT; exact nomatch hT
      | some ci => rw [hfd₂ T ci hc]; rfl
    unfold Env.findTable?
    rw [hs₂, hT]
    simp only [htab', hQ, List.find?_append]
    rw [List.find?_eq_none.mpr (fun t ht => by simp [hne t ht])]
    rfl
  have hcS := restore_swapped (F := F) mp.base2.wf hclass
  have hmem := restore_mem (F := F) hreq hnew hnewI hmr hnd
  have htab : env₂.tables = env₃.tables := by rw [hreq]
  have h := formerSwap_of_swapped hcS hmem htab
  -- the readings
  have hde₀ : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denote mp.base2.acval env ψ d e
        = denote mp.base2.acval ⟨vs ++ env.consts, env.tables⟩ ψ d e :=
    fun ψ d e => denote_formerSwap h₀ ψ d e
  have hde : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr),
      denote mp₃.base2.acval env₃ ψ d e = denote mp₃.base2.acval env₂ ψ d e :=
    fun ψ d e => denote_formerSwap h ψ d e
  have hbd₀ : ∀ {e}, ConstsBound env e → ConstsBound ⟨vs ++ env.consts, env.tables⟩ e := fun hb =>
    ConstsBound.of_isSome (fun n hn => by rw [← h₀.isSomeEq]; exact hn) hb
  have hup : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr) (ta : Term), ConstsBound env e →
      denote mp.base2.acval env ψ d e = some ta → denote mp₃.base2.acval env₃ ψ d e = some ta := by
    intro ψ d e ta hb hta
    refine r₃.read ψ d e ta (hbd₀ hb) ?_
    rw [hacV, ← hde₀]; exact hta
  have hleaf₃ : ∀ n, (env.find? n).isSome = true → mp₃.base2.acval n = mp.base2.acval n := by
    intro n hn
    rw [r₃.leaf n (by rw [← h₀.isSomeEq]; exact hn), hacV]
  have hrd : ∀ n cvR cvS caps, Swapped env env₃ env₂ n cvR cvS caps → ∀ ψ, ∃ Ts Tr : Term,
      denote mp₃.base2.acval env₃ ψ 0 cvS.type = some Ts ∧
      denote mp₃.base2.acval env₃ ψ 0 cvR.type = some Tr ∧
      ∀ ρ : Nat → V, interp V ρ Ts = interp V ρ Tr := by
    intro n cvR cvS caps hSw ψ
    have hbS := constsBound_of_constsResolve _ hSw.resolve
    have hbR := constsBound_of_constsResolve _ hSw.boundR
    rcases hclass n with he | ⟨m₀, m, caps', hr, hd, -, -, h3, h2⟩ | ⟨cv, cvR', caps', hF, -, h3, h2⟩
    · rw [hSw.find₂, hSw.find₃] at he
      obtain ⟨rfl, -⟩ : cvS = cvR ∧ caps = caps := by simpa using he
      obtain ⟨ta, hta⟩ := mp₃.type_reads _ (ConLeche.Env.find?_mem hSw.find₃) ψ
      exact ⟨ta, ta, hta, hta, fun _ => rfl⟩
    · rw [hSw.find₃] at h3
      rw [hSw.find₂] at h2
      obtain ⟨rfl, rfl⟩ : cvR = m.cvT ∧ caps = caps' := by simpa using h3
      obtain rfl : cvS = m₀.cvT := by
        have := Option.some.inj h2
        simpa using this
      obtain ⟨Ts, Tr, h₁, h₂, heq⟩ := Swapped_read hS hcov (.inl ⟨hr, hd⟩) ψ
      exact ⟨Ts, Tr, hup ψ 0 _ _ hbS h₁, hup ψ 0 _ _ hbR h₂, heq⟩
    · rw [hSw.find₃] at h3
      rw [hSw.find₂] at h2
      obtain ⟨rfl, rfl⟩ : cvR = cvR' ∧ caps = caps' := by simpa using h3
      obtain rfl : cvS = cv := by
        have := Option.some.inj h2
        simpa using this
      obtain ⟨Tr, Ts, h₁, h₂, h₃'⟩ := view_read hS hcov hF ψ
      exact ⟨Ts, Tr, hup ψ 0 _ _ hbS h₂, hup ψ 0 _ _ hbR h₁, fun ρ => (h₃' ρ).1⟩
  -- what the stored environment holds and the job's does not
  have hstored : ∀ c ∈ env₂.consts, c ∉ env₃.consts → ∃ (m₀ m : MemberShape) (caps : IndCaps),
      c = .indInfo m₀.cvT caps ∧ MemberReduct F env p₀.nP m₀ m ∧
      ConLeche.formerDefHeaded m₀.cvT = true ∧ ConstantInfo.indInfo m.cvT caps ∈ env₃.consts := by
    intro c hc hnot
    rw [hreq] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      have hd₃ : d ∈ env₃.consts := by rw [hnew]; exact List.mem_append_left _ hd
      by_cases hdi : ∃ cv caps, d = .indInfo cv caps
      · obtain ⟨cv, caps, rfl⟩ := hdi
        obtain ⟨m, hm, rfl, -⟩ := hnewI _ hd _ caps rfl
        obtain ⟨m₀, hm₀, hr⟩ := hmr m hm
        have hfind : p₀.members.find? (·.cvT.name == m.cvT.name) = some m₀ := by
          rw [hr.name]; exact find_member_of_nodup hnd hm₀
        have hf : storedFormerOf p₀ (.indInfo m.cvT caps) = .indInfo m₀.cvT caps := by
          simp only [storedFormerOf, hfind]
        rw [hf] at hnot ⊢
        rcases hr.how with ⟨-, rfl⟩ | ⟨hd', -⟩
        · exact absurd hd₃ hnot
        · exact ⟨m₀, m, caps, rfl, hr, hd', hd₃⟩
      · have hsame : storedFormerOf p₀ d = d := by
          cases d <;> first | rfl | exact absurd ⟨_, _, rfl⟩ hdi
        rw [hsame] at hnot
        exact absurd hd₃ hnot
    · exact absurd (by rw [hnew]; exact List.mem_append_right _ (List.mem_append_right _ hc)) hnot
  have hisS : ∀ n, (env₂.find? n).isSome = (env₃.find? n).isSome := fun n => (h.isSomeEq n).symm
  have hwf₂ : EnvWF env₂ := by
    refine ⟨fun c hc => ?_, fun t ht => ?_⟩
    · by_cases hc₃ : c ∈ env₃.consts
      · exact (mp₃.base2.wf.consts c hc₃).of_isSome hisS
      · obtain ⟨m₀, m, caps, rfl, hr, hd, hm⟩ := hstored c hc hc₃
        rcases hr.how with ⟨hd', -⟩ | ⟨-, -, h₁, -, -, -⟩
        · rw [hd] at hd'; exact nomatch hd'
        · obtain ⟨g1, g2, g3, g4⟩ := checkConstantVal_typeWF h₁
          obtain ⟨hu, he⟩ := (mp₃.base2.wf.consts _ hm).2.2.2.2.2.2 _ caps rfl
          refine ConLeche.structConstWF g1 g2 (Expr.constsResolve_of_find (fun n hn => ?_) g3) g4
            (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq)
            (ConLeche.IndCapsWF.of_caps hu he)
          cases hfc : env.find? n with
          | none => rw [hfc] at hn; exact nomatch hn
          | some ci => rw [hx.find n ci hfc]; rfl
    · exact (mp₃.base2.wf.tables t (htab ▸ ht)).of_isSome hisS
  have htyS : ∀ c ∈ env₂.consts, c ∉ env₃.consts →
      (∀ ψ : Name → Nat, ∃ ta : Term,
        denote mp₃.base2.acval env₂ ψ 0 c.toConstantVal.type = some ta) ∧
      (∀ (ψ : Name → Nat) (ta : Term),
        denote mp₃.base2.acval env₂ ψ 0 c.toConstantVal.type = some ta →
        ∀ ρ : Nat → V, WellDenotedTy V ρ ta) ∧
      (∀ (ψ : Name → Nat) (ta : Term),
        denote mp₃.base2.acval env₂ ψ 0 c.toConstantVal.type = some ta →
        ∀ ρ : Nat → V, interp V ρ (mp₃.base2.acval c.name ψ) ∈ˢ interp V ρ ta) := by
    intro c hc hc₃
    obtain ⟨m₀, m, caps, rfl, hr, hd, hm⟩ := hstored c hc hc₃
    rcases hr.how with ⟨hd', -⟩ | ⟨-, -, h₁, h₂, hb, -⟩
    · rw [hd] at hd'; exact nomatch hd'
    have hbS := constsBound_of_constsResolve _ (checkConstantVal_typeWF h₁).2.2.1
    have hbR := constsBound_of_constsResolve _ (checkConstantVal_typeWF h₂).2.2.1
    have key : ∀ ψ : Name → Nat, ∃ Ts Tr : Term,
        denote mp₃.base2.acval env₂ ψ 0 m₀.cvT.type = some Ts ∧
        denote mp₃.base2.acval env₃ ψ 0 m.cvT.type = some Tr ∧
        (∀ ρ : Nat → V, WellDenotedTy V ρ Ts) ∧ ∀ ρ : Nat → V, interp V ρ Ts = interp V ρ Tr := by
      intro ψ
      obtain ⟨Ts, Tr, g₁, g₂, g₃, -, g₄⟩ := storedFormer_sem mp h₁ h₂ hb ψ
      exact ⟨Ts, Tr, by rw [← hde]; exact hup ψ 0 _ _ hbS g₁, hup ψ 0 _ _ hbR g₂, g₃, g₄⟩
    refine ⟨fun ψ => ?_, fun ψ ta hta ρ => ?_, fun ψ ta hta ρ => ?_⟩
    · obtain ⟨Ts, -, g₁, -⟩ := key ψ
      exact ⟨Ts, g₁⟩
    · obtain ⟨Ts, Tr, g₁, -, g₃, -⟩ := key ψ
      change denote mp₃.base2.acval env₂ ψ 0 m₀.cvT.type = some ta at hta
      rw [g₁] at hta
      obtain rfl := Option.some.inj hta
      exact g₃ ρ
    · obtain ⟨Ts, Tr, g₁, g₂, -, g₄⟩ := key ψ
      change denote mp₃.base2.acval env₂ ψ 0 m₀.cvT.type = some ta at hta
      rw [g₁] at hta
      obtain rfl := Option.some.inj hta
      have hin := mp₃.mem_type _ hm ψ Tr g₂ ρ
      show interp V ρ (mp₃.base2.acval m₀.cvT.name ψ) ∈ˢ _
      rw [g₄ ρ, ← hr.name]
      exact hin
  -- the records
  have hold := mp.lfp_ok_transport (env' := env₂) (acval' := mp₃.base2.acval)
    (fun n ci hf _ => hx.find n ci hf) (fun n ci hf _ => hleaf₃ n (by rw [hf]; rfl))
    (fun ψ d e ta hb hta => by rw [← hde]; exact hup ψ d e ta hb hta)
    (fun _ => ConstsBound.of_isSome fun n hn => by
      cases hfc : env.find? n with
      | none => rw [hfc] at hn; exact nomatch hn
      | some ci => rw [hx.find n ci hfc]; rfl)
  have hnew' : ∀ {D}, D ∈ mp₃.lfpBlocks → D ∉ mp.lfpBlocks → ∀ mm, D.shown mm = none := by
    intro D hD hDm
    rcases r₃.blocks D hD with hh | hn
    · rw [hlV] at hh; exact absurd hh hDm
    · exact hn
  obtain ⟨mp₂, hac₂, hl₂⟩ := mp₃.swapFormers h hwf₂ (recCtors_back h mp₃.base2.rec_ctors)
    (projOk_back h mp₃.base2.proj_ok)
    (fun _ hac φ => recRules_back hac h hcS hrd mp₃.rec_rules φ)
    (fun _ hac φ => towerOk_back hac h hcS hrd mp₃.tower_ok φ)
    (fun _ hac => indStrict_back hac h hcS mp₃.ind_strict) htyS
    (mp₃.lfpBlocks.map (reshow mp env₃ env₂)) (fun D' hD' => by
      obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hD'
      by_cases hDm : D ∈ mp.lfpBlocks
      · rw [reshow_of_mem hDm]; exact hold D hDm
      · rw [reshow_of_not_mem hDm]
        exact record_back mp₃ h hcS hrd hD (hnew' hD hDm))
  have hmemb : ∀ (D : LfpDatum V) mm, (reshow mp env₃ env₂ D).member mm = D.member mm := by
    intro D mm
    unfold LfpDatum.member
    rw [(reshow_fields mp D).1]
  refine ⟨mp₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- cover
    intro n cv caps hf hn hq
    obtain ⟨cv₃, hf₃, -⟩ := h.find_ind_back hf
    obtain ⟨D, hD, mm, hmm, he⟩ := hc₃.cover n cv₃ caps hf₃ hn hq
    rw [hl₂]
    refine ⟨_, List.mem_map.mpr ⟨D, hD, rfl⟩, mm, ?_, by rw [hmemb]; exact he⟩
    rw [(reshow_fields mp D).2.1]; exact hmm
  · intro D' hD'
    rw [hl₂] at hD'
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hD'
    rw [(reshow_fields mp D).1]; exact hc₃.nodup D hD
  · intro D' hD'
    rw [hl₂] at hD'
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hD'
    rw [(reshow_fields mp D).1, (reshow_fields mp D).2.1]; exact hc₃.len D hD
  · intro D' hD' mm hmm cv caps hf
    rw [hl₂] at hD'
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hD'
    rw [hmemb] at hf
    obtain ⟨cv₃, hf₃, -⟩ := h.find_ind_back hf
    rw [(reshow_fields mp D).2.1] at hmm
    rw [(reshow_fields mp D).1]
    exact hc₃.all D hD mm hmm cv₃ caps hf₃
  · exact fun _ _ _ _ hin => absurd hin List.not_mem_nil
  · intro D' hD'
    rw [hl₂] at hD'
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hD'
    by_cases hDm : D ∈ mp.lfpBlocks
    · rw [reshow_of_mem hDm]; exact LfpOwn.formerSwap h (hc₃.own D hD)
    · rw [reshow_of_not_mem hDm]; exact (LfpOwn.formerSwap h (hc₃.own D hD)).withShown _
  · intro D' hD'
    rw [hl₂] at hD'
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hD'
    rw [(reshow_fields mp D).2.1, (reshow_fields mp D).2.2]; exact hc₃.wid D hD
  · -- the shown formers
    intro D' hD' mm f hmm hs cv caps hf
    rw [hl₂] at hD'
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hD'
    by_cases hDm : D ∈ mp.lfpBlocks
    · rw [reshow_of_mem hDm] at hmm hs hf ⊢
      exact shownFacts_keep hS hx.find hx.table (m' := mp₂.base2)
        (fun n hn => by rw [hac₂]; exact hleaf₃ n hn)
        (fun ψ d e ta hb hta => by rw [hac₂, ← hde]; exact hup ψ d e ta hb hta) hDm hmm hs hf
    · rw [reshow_of_not_mem hDm] at hmm hs hf ⊢
      change env₂.find? (D.member mm) = _ at hf
      change shownAt env₃ env₂ D mm = some f at hs
      change mm < D.k at hmm
      change _ ∧ IndStrictAt (V := V) mp₂.base2.acval env₂ (D.member mm) f ∧
        (∀ φ, TowerViewTyped mp₂.base2 φ (D.member mm) f) ∧ _
      rcases hcS (D.member mm) with he | ⟨cvR, cvS, caps', hSw⟩
      · have hf₃ : env₃.find? (D.member mm) = some (.indInfo cv caps) := by rw [← he]; exact hf
        rw [shownAt_same hf₃ hf] at hs
        exact nomatch hs
      · rw [hSw.find₂] at hf
        obtain ⟨rfl, rfl⟩ : cvS = cv ∧ caps' = caps := by simpa using hf
        by_cases hne : cvR = cvS
        · subst hne
          rw [shownAt_same hSw.find₃ hSw.find₂] at hs
          exact nomatch hs
        rw [shownAt_swapped hSw.find₃ hSw.find₂ hne] at hs
        obtain rfl := Option.some.inj hs
        obtain ⟨-, -, hrd₃, -⟩ := mp₃.lfp_ok D hD
        obtain ⟨cv₁, caps₁, hf₁, ⟨-, hsh⟩, -⟩ := hrd₃ mm hmm
        rw [hSw.find₃] at hf₁
        obtain ⟨rfl, rfl⟩ : cvR = cv₁ ∧ caps' = caps₁ := by simpa using hf₁
        have hflat : ConLeche.formerDefHeaded cvR = false := by
          rcases hsh with ⟨-, h₂⟩ | ⟨f', hs', -⟩
          · exact h₂
          · rw [hnew' hD hDm] at hs'; exact nomatch hs'
        obtain ⟨F', hrf⟩ := hSw.ran
        refine ⟨⟨env, F', mp.base2.wf, hx, hSw.resolve, hrf⟩, ?_, fun φ => ?_, fun ψ ta hta ρ => ?_⟩
        · intro ψ ab n hread hn ρ vs' hsp
          rw [hac₂] at hread ⊢
          rw [← hde] at hread
          exact mp₃.ind_strict _ cvR caps' hSw.find₃ hflat ψ ab n hread hn ρ vs' hsp
        · intro i entry s' hfp hs₁ hz us Ta hus hTa ρ vs' x rest g₁ g₂ g₃ g₄ g₅ g₆
          rw [hac₂] at hTa g₂ g₃ g₅
          rw [← hde] at hTa
          have hfp₃ : env₃.findProj? (D.member mm) i = some entry := by rw [h.projEq]; exact hfp
          obtain ⟨hsn, _, _, _, cvC, _, _, hlaw, _⟩ := mp₃.tower_ok φ _ i entry hfp₃
          obtain ⟨⟨Ta₀, hTa₀, hA⟩, _⟩ := hlaw us hus
          rw [hTa] at hTa₀
          obtain rfl := Option.some.inj hTa₀
          exact hA ρ vs' x rest g₁ g₂ g₃ g₄ g₅ g₆
            (.inl (.inl ⟨cvR, caps', s', by rw [hsn]; exact hSw.find₃, hs₁, hz⟩))
        · rw [hac₂, ← hde] at hta
          exact mp₃.type_wellDenotedTy _ (ConLeche.Env.find?_mem hSw.find₃) ψ ta hta ρ

/-! ## `Nat`'s block across a step -/

omit [SetTheory V] in
/-- An unreserved name is none of `Nat`'s block's three. -/
theorem nat_names_of_unreserved {n : Name} (h : ConLeche.reservedBasisNames.contains n = false) :
    n ≠ ConLeche.natName ∧ n ≠ ConLeche.natZeroName ∧ n ≠ ConLeche.natSuccName := by
  refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; revert h; decide)

omit [SetTheory V] in
/-- New constants named none of `Nat`'s block's names. -/
theorem NatFacts.append {env env₂ : Env} {new : List ConstantInfo} (hN : NatFacts env)
    (hnew : env₂.consts = new ++ env.consts)
    (hres : ∀ c ∈ new, c.name ≠ ConLeche.natName ∧ c.name ≠ ConLeche.natZeroName ∧
      c.name ≠ ConLeche.natSuccName) : NatFacts env₂ := by
  have hf : ∀ n, (∀ c ∈ new, c.name ≠ n) → env₂.find? n = env.find? n := by
    intro n hn
    show env₂.consts.find? (·.name == n) = _
    rw [hnew, List.find?_append]
    rw [List.find?_eq_none.mpr (fun c hc => by
      intro he
      exact hn c hc (by simpa using he))]
    rfl
  have h₁ := hf ConLeche.natName fun c hc => (hres c hc).1
  have h₂ := hf ConLeche.natZeroName fun c hc => (hres c hc).2.1
  have h₃ := hf ConLeche.natSuccName fun c hc => (hres c hc).2.2
  exact ⟨by rw [h₁, h₂, h₃]; exact hN.trio⟩

omit [SetTheory V] in
/-- **`Nat`'s block is stored at once across the block's install.** -/
theorem natFacts_block {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {p₀ : BlockParts}
    (hN : NatFacts env)
    (hClps₀ : ∀ c ∈ p₀.allCtors, ConLeche.reservedBasisNames.contains c.1.name = false)
    (hrun : ConLeche.Semantics.DeclBlockRun F env block p₀ env₂) : NatFacts env₂ := by
  obtain ⟨new, hnew, -, hres⟩ := declBlockRun_consts hrun
  exact hN.append hnew fun c hc => nat_names_of_unreserved (hres hClps₀ c hc)

omit [SetTheory V] in
/-- The same across the block's second path. -/
theorem natFacts_viewed {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {p₀ : BlockParts}
    (hN : NatFacts env)
    (hClps₀ : ∀ c ∈ p₀.allCtors, ConLeche.reservedBasisNames.contains c.1.name = false)
    (hrun : ConLeche.Semantics.BlockViewedRun F env block p₀ env₂) : NatFacts env₂ := by
  obtain ⟨ms, vs, env₃, hms, -, hrun₃, rfl⟩ := hrun
  have hsh := ConLeche.Semantics.reduceMembers_shape hms
  obtain ⟨new, hnew, -, hres⟩ := declBlockRun_consts hrun₃
  have hreq := restoreBlock_eq (p₀ := p₀) hnew
  refine hN.append (new := new.map (storedFormerOf p₀)) (by rw [hreq]) fun c hc => ?_
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
  rw [ConLeche.Cached.storedFormerOf_name]
  exact nat_names_of_unreserved (hres (fun c hc => hClps₀ c (by rw [← hsh.2]; exact hc)) c₀ hc₀)

omit [SetTheory V] in
/-- The ordinary install's tables on the old names. -/
theorem declBlockRun_findTable {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    {p₀ : BlockParts} (hrun : ConLeche.Semantics.DeclBlockRun F env block p₀ env₂) (T : Name)
    (hT : (env.find? T).isSome = true) : env₂.findTable? T = env.findTable? T := by
  obtain ⟨hfresh, newQ, hQ, hQall⟩ := declBlockRun_tables hrun
  obtain ⟨new, hnew, -, -⟩ := declBlockRun_consts hrun
  have hne : ∀ t ∈ newQ, (t.structName == T) = false := by
    intro t ht
    obtain ⟨m, hm, hn⟩ := hQall t ht
    have := hfresh m hm
    rw [beq_eq_false_iff_ne]
    intro he
    rw [← hn, he] at this
    rw [this] at hT
    exact nomatch hT
  have hs₂ : (env₂.find? T).isSome = true := by
    show (env₂.consts.find? (·.name == T)).isSome = true
    rw [hnew, List.find?_append, Option.isSome_or]
    exact Bool.or_eq_true_iff.mpr (Or.inr hT)
  unfold Env.findTable?
  rw [hs₂, hT]
  simp only [hQ, List.find?_append]
  rw [List.find?_eq_none.mpr (fun t ht => by simp [hne t ht])]
  rfl

end ConLeche.Model
