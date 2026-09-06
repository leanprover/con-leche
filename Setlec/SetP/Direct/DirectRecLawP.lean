import Setlec.SetP.Direct.DirectRecLawCoreP

/-!
# The recursor rule's law (task #175 W4c, P3 module 6, part 19)

`recRuleLaw`: the fired-iota contract `RecRuleLawP` of the direct
block's single (plain) rule at the recursor's extension, from the
stage's runs.  The right-hand side's λ-domains fit the full frame
(`recLawFits` over the constructor residual's composite frame), its
body is the minor applied to the fields (the residual's instantiation
sequence), and the frames' `RecBase` feeds `recLawCore`.
-/

namespace Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- A Π-tower's residual past a fitting parameter spine is graded. -/
theorem mkPisAV_drop_okP :
    ∀ {pds fds : List (Nat × Nat × AVExpr)} {b : AVExpr} {ρ : Nat → V} {as : List V},
      AnnotOkP V ρ (mkPisAV (pds ++ fds) b) → SpineFit ρ (pds.map (·.2.2)) as →
      AnnotOkP V (consList as ρ) (mkPisAV fds b)
  | [], _, _, _, [], hok, _ => hok
  | [], _, _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, _, [], _, hsp => hsp.elim
  | d :: pds, fds, b, ρ, a :: as, hok, hsp => by
    simp only [List.map_cons, SpineFit] at hsp
    have hok2 := hok.1
    have hokV := hok.2
    simp only [List.cons_append, mkPisAV, AnnotOk2_pi] at hok2
    simp only [List.cons_append, mkPisAV, AnnotValidV_pi] at hokV
    rw [consList_cons]
    exact mkPisAV_drop_okP ⟨hok2.2 a hsp.1, hokV.2.1 a hsp.1⟩ hsp.2

set_option maxHeartbeats 12800000 in
/-- **The direct block's rule fires at the readings.** -/
theorem recRuleLaw (hμ : μ.verified = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa cvRa : ConstantVal} {caps : IndCaps} {rhsA : Expr}
    (hccv : Setlec.checkConstantVal (Setlec.fueledOps μ F) env p.cvR = .ok cvRa)
    (hRec : Setlec.checkDirectRecTy (Setlec.fueledOps μ F) env p cvTa cvCa cvRa
      = .ok ())
    (hRule : Setlec.checkDirectRule (Setlec.fueledOps μ F) env p cvCa cvRa = .ok rhsA)
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hfC : env.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    {pps ds rds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (hCD : CtorData mp.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds)
    (hRD : RecData mp.base2 cvRa p.nP (elimLevel p) rds)
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2)))
    (hleafC : ∀ ψ, mp.base2.acval p.cvC.name ψ
      = directMkAV (p.resSort.eval ψ) (ds ψ) (((ds ψ).drop p.nP).map (·.2.2)))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        (p.isProp = false → FieldsBound (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2))) ∧
        (p.isProp = true → p.large = true →
          FieldsBound 0 ρ (((ds ψ).drop p.nP).map (·.2.2))))
    (hfresh : env.find? cvRa.name = none)
    {rule : RecRule} (hrule : rule = ⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩)
    (m₂ : EnvS2Core V ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2) [rule] :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval cvRa.name
      (fun ψ => directRecAV ((elimLevel p).eval ψ) (rds ψ) p.nF))
    (hAokP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (directRecAV ((elimLevel p).eval ψ) (rds ψ) p.nF))
    (φ : Name → Nat) :
    RecRuleLawP m₂ φ cvRa.name cvRa (p.nP + 2) (p.nP + 2) rule := by
  subst hrule
  -- the frames
  obtain ⟨hiffR, hbase⟩ := recFrames hμ mp hccv hRec hfT hlpsT hfC hlpsC hFD hCD hRD hleafT
    hleafC hiff hfields
  -- the rule's shape
  obtain ⟨-, -, -, -, hrhsRes, hrhsB, hrhsF, ⟨rbs, hstrip⟩, fvsP', rrest, cdomsP', crest',
    xFvs', xrest, ldoms, lrest, rhsTy, hopR', hci', hopX', hli, hdl, hinf⟩ :=
    Setlec.checkDirectRule_shape hRule
  -- the recursor type's shape
  obtain ⟨-, fvsP, rest, cdomsP, crest, mfv, mbs, mdom, minfv, xFvs, minBody, cdomsF,
    crest2, jbs, jbody, jdom, hopR, hci, hdomsP, hmfv, hmstrip, hmd, hmdeq, hminfv, hopX,
    hcf, hdomsF, hcrest2, hminBody, hjs, hjd, hjdeq, hjbody⟩ :=
    Setlec.checkDirectRecTy_shape hRec
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', -, htr', hst, hens, rfl⟩ :=
    Setlec.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' hst hens hopR hopR' hfresh hac hAokP hRD ⊢
  -- the two openings of the recursor type coincide
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj (hopR.symm.trans hopR'))
  subst h1; subst h2
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj (hci.symm.trans hci'))
  subst h1; subst h2
  -- the special variables
  obtain ⟨nmM, tyM, rfl⟩ := openPisAtFvars_index _ _ _ hopR p.nP mfv hmfv
  obtain ⟨nmm', tym, rfl⟩ := openPisAtFvars_index _ _ _ hopR (p.nP + 1) minfv hminfv
  rw [Nat.zero_add] at hmfv hminfv hminBody hopX
  obtain ⟨nmJ, jdom', mbJ, rfl, hjbs⟩ := stripPis_one_inv hjs
  obtain rfl : jdom = jdom' := by
    rw [hjbs] at hjd
    exact (Option.some.inj hjd).symm
  subst hjbody
  rw [Nat.zero_add] at hopR
  have hlenP : fvsP.length = p.nP + 2 := openPisAtFvars_length _ hopR
  have hlenX' : xFvs'.length = p.nF := openPisAtFvars_length _ hopX'
  -- the full opening
  have hopAll : openPisAtFvars (p.nP + 3) type' 0
      = some (fvsP ++ [.fvar (p.nP + 2) nmJ jdom],
          .app (.fvar p.nP nmM tyM) (.fvar (p.nP + 2) nmJ jdom)) := by
    have := openPisAtFvars_add (p.nP + 2) hopR
      (openPisAtFvars_one nmJ jdom (.app (.fvar p.nP nmM tyM) (.bvar 0)) mbJ (0 + (p.nP + 2)))
    rw [Nat.zero_add] at this
    simpa using this
  have hlenF : (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom]).length = p.nP + 3 := by
    simp [hlenP]
  have hidxR : ∀ (i : Nat) (x : Expr), (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom])[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty := by
    intro i x hx
    obtain ⟨nm, ty, h⟩ := openPisAtFvars_index _ _ _ hopAll i x hx
    exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩
  have htakeR : ∀ k, k ≤ p.nP + 2 →
      (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom]).take k = fvsP.take k :=
    fun k hk => List.take_append_of_le_length (by omega)
  have hpinsP := Setlec.checkDirectDomsAt_inv hdomsP
  have hpinsL := Setlec.checkDefEqList_inv hdl
  -- the constructor's stored type
  obtain ⟨hCf, -, -, hCb, -⟩ := mp.base2.wf _ (Setlec.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  -- the recursor's own name
  have hRC : p.cvC.name ≠ p.cvR.name := by
    intro h
    rw [← h] at hfresh
    rw [hfresh] at hfC
    exact nomatch hfC
  have hRT : p.cvT.name ≠ p.cvR.name := by
    intro h
    rw [← h] at hfresh
    rw [hfresh] at hfT
    exact nomatch hfT
  -- the cons crossing
  have hcross : ∀ e : Expr, ConsCrossAt (.recInfo { p.cvR with type := type' } (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩]) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hfindC : (⟨.recInfo { p.cvR with type := type' } (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩] :: env.consts⟩ : Env).find? p.cvC.name
      = some (.ctorInfo cvCa p.nP p.nF) := by
    rw [Setlec.Env.find?_cons, if_neg (fun h => hRC h.symm)]
    exact hfC
  -- the law
  refine ⟨Nat.le_refl _, fun us hus => ?_⟩
  dsimp only
  -- the readings at the instantiation
  have hinstR : ∀ (d : Nat) (e : Expr),
      denoteP m₂.acval _ φ d (e.instantiateLevelParams p.cvR.levelParams us)
        = denoteP m₂.acval _ (Level.substFn φ p.cvR.levelParams us) d e :=
    fun d e => denoteP_instLevels (acvalParamsAt_of_core m₂) φ d e
  generalize hψR : Level.substFn φ p.cvR.levelParams us = ψR at hinstR ⊢
  -- the right-hand side's reading, at the stage environment
  have hw0 : Expr.WScoped 0 rhsA := Expr.WScoped.of_not_hasFvar hrhsF
  have hL0 : Expr.LeavesBounded rhsA := Expr.LeavesBounded.of_not_hasFvar hrhsF
  have hnil0 : rhsA.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsF
  have hcbR : ConstsBound env rhsA := constsBound_of_constsResolve _ hrhsRes
  obtain ⟨Ra, hRa⟩ := acceptedReadsP_of mp.base2 ψR hinf hw0 hrhsB hL0
  have hcR := claimsAtP_of hμ mp ψR F
  obtain ⟨-, -, hokRa₀, -, -⟩ := hcR.inferRow hinf hw0 hrhsB hL0 (CtxOkP.nil hnil0) hRa
  have hokRa : ∀ ρ : Nat → V, AnnotOkP V ρ Ra := fun ρ => hokRa₀ ρ (Sat2_nil V ρ)
  have hRa₂ : denoteP m₂.acval ⟨.recInfo { p.cvR with type := type' } (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩] :: env.consts⟩ φ 0
      (rhsA.instantiateLevelParams p.cvR.levelParams us) = some Ra := by
    rw [hinstR, hac]
    exact denoteP_cons_mono hfresh (hcross _) ψR 0 hcbR hRa
  refine ⟨Ra, hRa₂, hokRa, fun _ _ h => absurd h (by simp), ?_⟩
  intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl husjl hψ hplain _ _ hTVa
    hTVja hfitR hfitC
  -- the constructor found is the block's
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfindC.symm.trans hfcj))
  -- the level assignments
  have hagree : ∀ q ∈ p.cvT.levelParams,
      Level.substFn φ cvCa.levelParams usj q = ψR q := by
    have h := hψ
    simp only [Setlec.recFireComparands] at h
    rw [hlpsC] at h
    rw [hlpsC, ← hψR]
    exact substFn_agree_of_comparand h
  have hdsEq : ds (Level.substFn φ cvCa.levelParams usj) = ds ψR :=
    hCD.params (Level.substFn φ cvCa.levelParams usj) ψR
      (fun q hq => hagree q (by rw [← hlpsC]; exact hq))
  have hwEq : p.resSort.eval (Level.substFn φ cvCa.levelParams usj) = p.resSort.eval ψR :=
    (hFD.params (Level.substFn φ cvCa.levelParams usj) ψR
      (fun q hq => hagree q (by rw [← hlpsT]; exact hq))).2
  -- the recursor and constructor types' readings, at the extension
  have hcbT : ConstsBound env type' := constsBound_of_constsResolve _ htr'
  have hcbC : ConstsBound env cvCa.type :=
    constsBound_of_constsResolve _ (mp.base2.wf _ (Setlec.Semantics.Env.find?_mem hfC)).2.2.1
  have hRD₂ := hRD.cross (c₀ := .recInfo { p.cvR with type := type' } (p.nP + 2) (p.nP + 2)
    [⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩]) hfresh (hcross _) hcbT m₂ hac
  have hCD₂ := hCD.cross (c₀ := .recInfo { p.cvR with type := type' } (p.nP + 2) (p.nP + 2)
    [⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩]) hfresh hRT (hcross _) hcbC m₂ hac
  have hTVa' : TVa = mkPisAV (rds ψR) (.app (.bvar 2) (.bvar 0)) := by
    have h := hTVa
    rw [hinstR] at h
    exact Option.some.inj (h.symm.trans (hRD₂.read ψR))
  have hTVja' : TVja = mkPisAV (ds ψR) (ctorBodyAV m₂ p.cvT.name p.nP p.nF (Level.substFn φ cvCa.levelParams usj)) := by
    have h := hTVja
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ 0 cvCa.type] at h
    have := Option.some.inj (h.symm.trans (hCD₂.read (Level.substFn φ cvCa.levelParams usj)))
    rw [this, hdsEq]
  -- the constructor's leaf at the extension
  have hleafC₂ : m₂.acval p.cvC.name (Level.substFn φ cvCa.levelParams usj)
      = directMkAV (p.resSort.eval ψR) (ds ψR) (((ds ψR).drop p.nP).map (·.2.2)) := by
    rw [hac]
    show acvalWith mp.base2.acval p.cvR.name _ p.cvC.name (Level.substFn φ cvCa.levelParams usj) = _
    rw [acvalWith_ne hRC, hleafC (Level.substFn φ cvCa.levelParams usj), hdsEq, hwEq]
  have hleafR₂ : m₂.acval p.cvR.name ψR
      = directRecAV ((elimLevel p).eval ψR) (rds ψR) p.nF := by
    rw [hac]
    show acvalWith mp.base2.acval p.cvR.name _ p.cvR.name ψR = _
    rw [acvalWith_self]
  -- the fits, as spines
  have hspR : SpineFit ρ ((rds ψR).map (·.2.2))
      ((xs ++ [AVExpr.mkAppN (directMkAV (p.resSort.eval ψR) (ds ψR)
        (((ds ψR).drop p.nP).map (·.2.2))) ys]).map (interp2 V ρ)) := by
    have hst := stripPisAV_mkPisAV (rds ψR) (AVExpr.app (.bvar 2) (.bvar 0))
    rw [hRD.len ψR] at hst
    have htele := piTeleP_of_stripPisAV hst
    have hfit := hfitR
    rw [hTVa'] at hfit
    try simp only [RecRule.ctor] at hfit
    rw [hleafC₂] at hfit
    have hchain := teleFitPA_to_chain (p.nP + 3) htele (by simp [hxl]) hfit
    refine spineFit_of_chain (by simp [hxl, hRD.len ψR]) ?_
    intro n hn
    have := hchain n (by simpa [hRD.len ψR] using hn)
    simpa [hRD.len ψR] using this
  have hspC : SpineFit ρ ((ds ψR).map (·.2.2)) (ys.map (interp2 V ρ)) := by
    have hst := stripPisAV_mkPisAV (ds ψR) (ctorBodyAV m₂ p.cvT.name p.nP p.nF (Level.substFn φ cvCa.levelParams usj))
    rw [hCD.len ψR] at hst
    have htele := piTeleP_of_stripPisAV hst
    have hfit := hfitC
    rw [hTVja'] at hfit
    have hchain := teleFitPA_to_chain (p.nP + p.nF) htele (by simpa using hyl) hfit
    refine spineFit_of_chain (by simp [hyl, hCD.len ψR]) ?_
    intro n hn
    have := hchain n (by simpa [hCD.len ψR] using hn)
    simpa [hCD.len ψR] using this
  have hplain' : ∀ i, i < p.nP →
      interp2 V ρ (ys.getD i default) = interp2 V ρ (xs.getD i default) :=
    fun i hi => hplain rfl i hi (by omega)
  -- the recursor's opening at ψR, and the constructor's residual
  have hR : OpenedP mp.base2 ψR (p.nP + 3) type' (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom]) _
      (((rds ψR).map (·.2.2)).reverse) (.app (.bvar 2) (.bvar 0)) :=
    openedP_of_peel hopAll htf' hbt' (hRD.read ψR) (hRD.len ψR) (hRD.okTy ψR)
  have hlenΓ : (((rds ψR).map (·.2.2)).reverse).length = p.nP + 3 := hR.len
  obtain ⟨hident, hres, hwres, hbres, hleafres⟩ := recParamIdent hcR hR hidxR hlenF
    (hCD.len ψR) (hCD.read ψR) (hCD.okTy ψR) hCf hCb (by rw [htakeR p.nP (by omega)]; exact hci)
    (fun i hi => by
      obtain ⟨a, b, ha, hb, hdeq⟩ := hpinsP i hi
      exact ⟨a, b, by rw [htakeR p.nP (by omega)]; exact ha, hb, hdeq⟩)
  have hdrop3 := drop_three_rec (rds := rds ψR) (hRD.len ψR)
  have hiffP : ∀ ρ' : Nat → V, Sat2 V ((((rds ψR).map (·.2.2)).reverse).drop 3) ρ' ↔
      Sat2 V ((((ds ψR).take p.nP).map (·.2.2)).reverse) ρ' := by
    intro ρ'
    have := hident p.nP (Nat.le_refl _) ρ'
    rwa [show p.nP + 3 - p.nP = 3 from by omega, Nat.sub_self, List.drop_zero] at this
  have hlenFds : ((ds ψR).drop p.nP).length = p.nF := by simp [hCD.len ψR]
  have hres2 : denoteP mp.base2.acval env ψR (p.nP + 2) crest
      = some ((mkPisAV ((ds ψR).drop p.nP) (ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψR)).liftN 2 0) := by
    have h := denoteP_lift (env := env) (φ := ψR) mp.base2.acval_closed hwres (p.nP + 2)
      (by omega)
    rw [hres, show p.nP + 2 - p.nP = 2 from by omega, Option.map_some] at h
    exact h
  have hokT2 : ∀ (E : AVExpr) (ρ' : Nat → V), Sat2 V (E :: (((rds ψR).map (·.2.2)).reverse).drop 2) ρ' →
      AnnotOkP V ρ' ((mkPisAV ((ds ψR).drop p.nP)
        (ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψR)).liftN 2 0) := by
    intro E ρ' hρ'
    refine (AnnotOkP_liftN V 2 _ 0 ρ').mpr ?_
    rw [shiftE_zero]
    have h3 : Sat2 V ((((rds ψR).map (·.2.2)).reverse).drop 3) (fun k => ρ' (k + 2)) := by
      have h := Sat2_drop (Sat2_tail hρ') 1
      rw [List.drop_drop] at h
      exact h
    have hsatC := (hiffP _).mp h3
    have hsp := spineFit_of_sat2 (Δ₀ := []) (Ds := ((ds ψR).take p.nP).map (·.2.2))
      (by rw [List.append_nil]; exact hsatC)
    have hlenP' : (((ds ψR).take p.nP).map (·.2.2)).length = p.nP := by simp [hCD.len ψR]
    rw [hlenP'] at hsp
    have hokFull := hCD.okTy ψR (fun j => ρ' (j + p.nP + 2))
    rw [← List.take_append_drop p.nP (ds ψR)] at hokFull
    have := mkPisAV_drop_okP hokFull hsp
    rw [consList_range_reverse] at this
    exact this
  obtain ⟨Γx, Rx, compX⟩ := compOpenedP_ofTy hR hidxR (Expr.WScoped.mono (by omega) hwres)
    hbres (fun l hl => mem_take_of_le (hleafres l hl).1 (by omega)) hres2 hokT2 hopX'
  -- the residual's peel
  have hΓx : Γx = (((liftDoms 2 0 ((ds ψR).drop p.nP)).map (·.2.2)).reverse) := by
    have hstL : stripPisAV p.nF (mkPisAV (liftDoms 2 0 ((ds ψR).drop p.nP))
        ((ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψR).liftN 2 (0 + p.nF)))
        = some (liftDoms 2 0 ((ds ψR).drop p.nP),
          (ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψR).liftN 2 (0 + p.nF)) := by
      have := stripPisAV_mkPisAV (liftDoms 2 0 ((ds ψR).drop p.nP))
        ((ctorBodyAV mp.base2 p.cvT.name p.nP p.nF ψR).liftN 2 (0 + p.nF))
      rwa [liftDoms_length, hlenFds] at this
    have htele := compX.tele
    rw [liftN_mkPisAV, hlenFds] at htele
    exact (PiTeleP.det htele (piTeleP_of_stripPisAV hstL)).1
  -- the rule's λ-domains fit the frame
  have htakeF : (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom]).take (p.nP + 2) = fvsP := by
    rw [htakeR (p.nP + 2) (Nat.le_refl _), List.take_of_length_le (by omega)]
  obtain ⟨lds, C, hRaEq, hlenL, hCread, hfits⟩ := recLawFits hcR hR hidxR hlenF compX hrhsF hrhsB
    hRa hokRa (by rw [htakeF]; exact hli) (by rw [htakeF]; exact hpinsL)
  -- the residual's body: the minor applied to the fields
  have hlrest : lrest = Expr.mkAppN (.fvar (p.nP + 1) nmm' tym) xFvs' := by
    have h := instLamsAt_rest_of_stripLams (fvsP ++ xFvs')
      (by rw [List.length_append, hlenP, hlenX']; exact hstrip) hli
    rw [h, List.length_append, hlenP, hlenX',
      show p.nP + 2 + p.nF - 1 = p.nP + 1 + p.nF from by omega,
      instSeq_directRuleBody hlenP hlenX'
        (fun a ha => by
          obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
          obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index _ _ _ hopR q a hq
          rfl)
        (fun a ha => by
          obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
          obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index _ _ _ hopX' q a hq
          rfl),
      List.getD_eq_getElem?_getD, hminfv]
    rfl
  have hCeq : C = AVExpr.mkAppN (.bvar p.nF)
      ((List.range p.nF).map fun k => AVExpr.bvar (p.nF - 1 - k)) := by
    have hidxX' : ∀ (k : Nat) (x : Expr), xFvs'[k]? = some x →
        ∃ nm ty, x = Expr.fvar (p.nP + 2 + k) nm ty :=
      openPisAtFvars_index _ _ _ hopX'
    have hsp := denoteSpineP_fvars (acval := mp.base2.acval) (env := env) (φ := ψR)
      (p.nP + 2 + p.nF) xFvs' (p.nP + 2) hidxX'
    rw [hlenX'] at hsp
    have hread := denoteP_mkAppN hsp (f := .fvar (p.nP + 1) nmm' tym)
      (fa := .bvar (p.nP + 2 + p.nF - 1 - (p.nP + 1))) (by rw [denoteP_fvar])
    rw [← hlrest] at hread
    have := Option.some.inj (hCread.symm.trans hread)
    rw [this, show p.nP + 2 + p.nF - 1 - (p.nP + 1) = p.nF from by omega]
    congr 1
    apply List.map_congr_left
    intro k _
    congr 1; omega
  -- the bound at squash with a large eliminator
  have hbound0 : (elimLevel p).eval ψR ≠ 0 → p.resSort.eval ψR = 0 → ∀ ρ' : Nat → V,
      Sat2 V ((((ds ψR).take p.nP).map (·.2.2)).reverse) ρ' →
      FieldsBound 0 ρ' (((ds ψR).drop p.nP).map (·.2.2)) := by
    intro hl hw ρ' hρ'
    have hlarge : p.large = true := by
      cases hpl : p.large
      · exfalso
        apply hl
        simp [elimLevel, hpl, Level.eval]
      · rfl
    by_cases hnp : p.isProp = true
    · exact (hfields ψR ρ' hρ').2.2.2 hnp hlarge
    · have := (hfields ψR ρ' hρ').2.2.1 (by simpa using hnp)
      rwa [hw] at this
  -- the law's two halves
  have hcore := recLawCore (hRD.len ψR) (hCD.len ψR) (fun ρ' => (hAokP ψR ρ').1) (hbase ψR)
    (fun ρ' h => (hfields ψR ρ' h).1) hbound0 hlenL (by rw [hRaEq, hCeq]) hokRa
    (fun ρ'' h => by
      refine hfits ρ'' ?_
      simp only [compCtx, Nat.sub_self, List.drop_zero, hΓx]
      exact h)
    hxl (by simpa using hyl) hspR hspC hplain'
  try simp only [RecRule.ctor, RecRule.ctorParams] at hcore ⊢
  rw [hleafR₂, hleafC₂]
  exact hcore

end Setlec.Semantics
