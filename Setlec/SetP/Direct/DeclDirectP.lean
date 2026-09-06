import Setlec.SetP.Direct.DirectStageTableP

/-!
# The direct structure's install, assembled (task #175 W4c, P3 module 7, part 9; S1)

`declDirectP`: the P carrier survives the direct install's run
(`DeclDirectRun`).  The stages compose as the checker runs them —
former, constructor, recursor, the projection table (task #175 S1:
one cons, `stageTable`) — with one twist: the
former's leaf mentions the field chain, which is read off the
constructor's stored type, checked *after* the former is stored.  So
the former is installed twice: once with an empty field chain, only
to read the constructor's data at a carrier that stores the former
(`ctorData_of` needs the former's lookup), then with the real chain.
The field readings agree across the two installs because the field
domains resolve in the pre-block environment
(`denoteP_openPis_agree` over `denoteP_acvalWith_unmentioned₂`) — the
constructor stage's `constsResolve env₀` re-check is exactly this
fact.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta ProjEntry projFnName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Readings under two leaves -/

/-- The binder data of one opened telescope's readings under two
valuations agree past index `k` whenever the opened annotations read
alike there. -/
theorem denoteP_openPis_agree {acval₁ acval₂ : Name → (Name → Nat) → AVExpr} {env : Env}
    {φ : Name → Nat} :
    ∀ (n : Nat) {d k : Nat} {e : Expr} {fvs : List Expr} {o : Expr} {ea₁ ea₂ : AVExpr}
      {pps₁ pps₂ : List (Nat × Nat × AVExpr)} {b₁ b₂ : AVExpr},
      openPisAtFvars n e d = some (fvs, o) →
      denoteP acval₁ env φ d e = some ea₁ → denoteP acval₂ env φ d e = some ea₂ →
      stripPisAV n ea₁ = some (pps₁, b₁) → stripPisAV n ea₂ = some (pps₂, b₂) →
      (∀ (i : Nat) (x : Expr), fvs[i]? = some x → k ≤ i →
        denoteP acval₁ env φ (d + i) x.fvarTypeD = denoteP acval₂ env φ (d + i) x.fvarTypeD) →
      pps₁.drop k = pps₂.drop k
  | 0, d, k, e, fvs, o, ea₁, ea₂, pps₁, pps₂, b₁, b₂, _, _, _, hst₁, hst₂, _ => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst₁ hst₂
    rw [← hst₁.1, ← hst₂.1]
  | n + 1, d, k, e, fvs, o, ea₁, ea₂, pps₁, pps₂, b₁, b₂, hop, h₁, h₂, hst₁, hst₂, hag => by
    match e, hop with
    | .forallE nm dom body mb, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨ta₁, ba₁, hta₁, hba₁, rfl⟩ := denoteP_forallE_inv h₁
        obtain ⟨ta₂, ba₂, hta₂, hba₂, rfl⟩ := denoteP_forallE_inv h₂
        simp only [stripPisAV, Option.map_eq_some_iff] at hst₁ hst₂
        obtain ⟨⟨pps₁', b₁'⟩, hst₁', heq₁⟩ := hst₁
        obtain ⟨⟨pps₂', b₂'⟩, hst₂', heq₂⟩ := hst₂
        simp only [Prod.mk.injEq] at heq₁ heq₂
        obtain ⟨rfl, rfl⟩ := heq₁
        obtain ⟨rfl, rfl⟩ := heq₂
        have htail : ∀ k', (∀ (i : Nat) (x : Expr), fvs'[i]? = some x → k' ≤ i →
            denoteP acval₁ env φ (d + 1 + i) x.fvarTypeD
              = denoteP acval₂ env φ (d + 1 + i) x.fvarTypeD) →
            pps₁'.drop k' = pps₂'.drop k' :=
          fun k' hag' => denoteP_openPis_agree n hop' hba₁ hba₂ hst₁' hst₂' hag'
        cases k with
        | zero =>
          have hhead := hag 0 _ rfl (Nat.zero_le _)
          simp only [Expr.fvarTypeD, Nat.add_zero] at hhead
          rw [hta₁, hta₂] at hhead
          obtain rfl := Option.some.inj hhead
          simp only [List.drop_zero]
          congr 1
          have := htail 0 fun i x hx _ => by
            have := hag (i + 1) x (by simpa using hx) (Nat.zero_le _)
            rwa [show d + (i + 1) = d + 1 + i from by omega] at this
          simpa using this
        | succ k =>
          simp only [List.drop_succ_cons]
          exact htail k fun i x hx hi => by
            have := hag (i + 1) x (by simpa using hx) (by omega)
            rwa [show d + (i + 1) = d + 1 + i from by omega] at this
      · exact nomatch hop
    | .bvar _, hop | .fvar _ _ _, hop | .sort _, hop | .const _ _, hop
    | .app _ _, hop | .lam _ _ _ _, hop | .letE _ _ _ _, hop | .lit _, hop
    | .proj _ _ _, hop =>
      simp [openPisAtFvars] at hop

/-- A name fresh at a cons is fresh below it. -/
theorem find?_none_of_cons {c : ConstantInfo} {env : Env} {n : Name}
    (h : Env.find? ⟨c :: env.consts⟩ n = none) : env.find? n = none := by
  rw [Setlec.Env.find?_cons] at h
  split at h
  · exact nomatch h
  · exact h

/-! ## The assembly -/

/-- **The P carrier survives a direct install.** -/
theorem declDirectP (hμ : μ.verified = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p : DirectParts} (mp : EnvS2PM V μ env)
    (hE : Setlec.EtaFamiliesClosed env) (hdp : Setlec.directParts? env block = some p)
    (h : Setlec.Semantics.DeclDirectRun μ F env p env₂) : Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨cvTa, cvCa, cvRa, sorts, rhsA, envI, envC, hInd, hCtor, hccvR, hRec, hRule, hTbl⟩ := h
  dsimp only at hTbl
  -- the table stage's own guards: the projection-function name family
  -- is free (the modeled route's η-family key) and the table is fresh
  obtain ⟨-, -, -, hfam, hfreshTbl, -⟩ := Setlec.checkDirectProjTable_inv hTbl
  obtain ⟨hProp, hRname, hClps, hresT, hresC, hresR, helim⟩ := Setlec.directParts?_inv hdp
  -- the former
  obtain ⟨hccvT, rfl, bsT, hstripT⟩ := Setlec.checkDirectInd_shape hInd
  obtain ⟨hfindT, -, hpshapeT, -, -, -, typeT, -, -, -, -, htrT, -, -, htyT⟩ :=
    Setlec.checkConstantVal_inv hccvT
  have hTname : cvTa.name = p.cvT.name := by rw [htyT]
  have hlpsT : cvTa.levelParams = p.cvT.levelParams := by rw [htyT]
  have hTtype : cvTa.type = typeT := by rw [htyT]
  obtain ⟨pps, hFD⟩ := formerData_of hμ mp hccvT hstripT
  have hTfresh : env.find? cvTa.name = none := by rw [hTname]; exact hfindT
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (by rw [hTtype]; exact htrT)
  -- the constructor's shape
  obtain ⟨hccvC, rfl, ⟨cbs, hstripC⟩, fvsP, crest, tfvs, trest, xFvs, hopC, -, -, hopX, hxres,
    hsorts⟩ := Setlec.checkDirectCtor_shape hCtor
  obtain ⟨hfindC, -, hpshapeC, -, -, hnfC, typeC, -, -, hannC, -, htrC, -, -, htyC⟩ :=
    Setlec.checkConstantVal_inv hccvC
  have hCname : cvCa.name = p.cvC.name := by rw [htyC]
  have hlpsC : cvCa.levelParams = p.cvT.levelParams := by rw [htyC]; exact hClps
  have hlpsCT : cvCa.levelParams = cvTa.levelParams := by rw [hlpsC, hlpsT]
  have hCtype : cvCa.type = typeC := by rw [htyC]
  have hfT_I : (⟨.indInfo cvTa (Setlec.directCaps p) :: env.consts⟩ : Env).find? p.cvT.name
      = some (.indInfo cvTa (Setlec.directCaps p)) := by
    rw [← hTname]; exact Setlec.Env.find?_cons_self _ _
  have hProp' : p.isProp = true → (Level.isEquiv p.resSort .zero == some true) = true :=
    fun h => by rw [← hProp]; exact h
  -- the dummy former: the constructor's field readings need a carrier
  -- storing the former
  obtain ⟨mpI₀, hacI₀⟩ := stageFormer mp hE hInd hfindC hFD (fun _ => []) (fun _ _ _ => rfl)
    (fun _ => trivial) (fun _ _ _ => ⟨trivial, trivial⟩) (fun _ _ => rfl)
  obtain ⟨ds₀, hCD₀⟩ := ctorData_of hμ mpI₀ hCtor hfT_I hlpsT hstripT
  have hFD_I₀ : FormerData mpI₀.base2 cvTa p.nP p.resSort pps :=
    hFD.cross (c₀ := .indInfo cvTa (Setlec.directCaps p)) hTfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT mpI₀.base2 hacI₀
  obtain ⟨hiff₀, hfields₀⟩ := ctorFrames hμ mpI₀ hCtor hfT_I hProp' hFD_I₀ hCD₀
  -- the real former
  obtain ⟨mpI, hacI⟩ := stageFormer mp hE hInd hfindC hFD
    (fun ψ => ((ds₀ ψ).drop p.nP).map (·.2.2))
    (fun ψ₁ ψ₂ hφ => by rw [hCD₀.params ψ₁ ψ₂ (by rw [hlpsCT]; exact hφ)])
    (fun ψ => by
      have := (DomsBelow.drop p.nP (hCD₀.below ψ)).fields
      rwa [Nat.zero_add] at this)
    (fun ψ ρ h => ⟨(hfields₀ ψ ρ ((hiff₀ ψ ρ).mp h)).1, (hfields₀ ψ ρ ((hiff₀ ψ ρ).mp h)).2.1⟩)
    (fun hnF ψ => by
      rw [List.drop_eq_nil_of_le (by rw [hCD₀.len ψ, hnF]; exact Nat.le_refl _)]
      rfl)
  -- the constructor's data at the real former, its fields identified
  obtain ⟨ds, hCD⟩ := ctorData_of hμ mpI hCtor hfT_I hlpsT hstripT
  have hopAll := openPisAtFvars_add p.nP hopC (by rw [Nat.zero_add]; exact hopX)
  have hlenP : fvsP.length = p.nP := openPisAtFvars_length _ hopC
  have hdsEq : ∀ ψ, (ds ψ).drop p.nP = (ds₀ ψ).drop p.nP := by
    intro ψ
    have h1 := hCD.read ψ
    have h2 := hCD₀.read ψ
    rw [hacI] at h1
    rw [hacI₀] at h2
    refine denoteP_openPis_agree (p.nP + p.nF) hopAll h1 h2
      (by rw [← hCD.len ψ]; exact stripPisAV_mkPisAV _ _)
      (by rw [← hCD₀.len ψ]; exact stripPisAV_mkPisAV _ _) ?_
    intro i x hx hi
    have hxin : x ∈ xFvs := by
      rw [List.getElem?_append_right (by omega)] at hx
      exact List.mem_of_getElem? hx
    exact denoteP_acvalWith_unmentioned₂ hTfresh _ _ (hxres x hxin)
  have hleafT_I : ∀ ψ, mpI.base2.acval p.cvT.name ψ
      = directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2)) := by
    intro ψ
    rw [hacI, ← hTname, acvalWith_self, hdsEq]
  have hFD_I : FormerData mpI.base2 cvTa p.nP p.resSort pps :=
    hFD.cross (c₀ := .indInfo cvTa (Setlec.directCaps p)) hTfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT mpI.base2 hacI
  obtain ⟨hiff, hfields⟩ := ctorFrames hμ mpI hCtor hfT_I hProp' hFD_I hCD
  -- the projection-function names are fresh at the recursor's extension
  have hslotsF : ∀ j, j < p.nF →
      (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then .plain else .inert,
          rhsA⟩] :: (⟨.ctorInfo cvCa p.nP p.nF :: (⟨.indInfo cvTa (Setlec.directCaps p) ::
            env.consts⟩ : Env).consts⟩ : Env).consts⟩ : Env).find? (projFnName p.cvT.name j)
        = none := by
    intro j hj
    have := List.all_eq_true.mp hfam j (List.mem_range.mpr hj)
    exact Option.isNone_iff_eq_none.mp this
  -- the constructor's cons
  obtain ⟨mpC, hacC⟩ := stageCtor hE rfl hfindT hTname hlpsCT mpI hCtor
    (fun hnF => find?_none_of_cons (hslotsF 0 hnF)) hFD_I hCD hleafT_I hiff
    (fun ψ ρ h => ⟨(hfields ψ ρ h).1, (hfields ψ ρ h).2.1⟩)
  -- the recursor
  have hCfreshI : (⟨.indInfo cvTa (Setlec.directCaps p) :: env.consts⟩ : Env).find? cvCa.name
      = none := by rw [hCname]; exact hfindC
  have hTC : p.cvT.name ≠ cvCa.name := by
    intro h; rw [h, hCfreshI] at hfT_I; exact nomatch hfT_I
  have hcbT_I : ConstsBound (⟨.indInfo cvTa (Setlec.directCaps p) :: env.consts⟩ : Env) cvTa.type :=
    constsBound_of_constsResolve _ (mpI.base2.wf _ (Setlec.Semantics.Env.find?_mem hfT_I)).2.2.1
  have hcbC : ConstsBound (⟨.indInfo cvTa (Setlec.directCaps p) :: env.consts⟩ : Env) cvCa.type :=
    constsBound_of_constsResolve _ (by rw [hCtype]; exact htrC)
  have hFD_C : FormerData mpC.base2 cvTa p.nP p.resSort pps :=
    hFD_I.cross (c₀ := .ctorInfo cvCa p.nP p.nF) hCfreshI
      (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT_I mpC.base2 hacC
  have hCD_C : CtorData mpC.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds :=
    hCD.cross (c₀ := .ctorInfo cvCa p.nP p.nF) hCfreshI hTC
      (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbC mpC.base2 hacC
  have hfT_C : (⟨.ctorInfo cvCa p.nP p.nF :: (⟨.indInfo cvTa (Setlec.directCaps p) ::
      env.consts⟩ : Env).consts⟩ : Env).find? p.cvT.name
      = some (.indInfo cvTa (Setlec.directCaps p)) := by
    rw [Setlec.Env.find?_cons, if_neg (fun h => hTC h.symm)]
    exact hfT_I
  have hfC_C : (⟨.ctorInfo cvCa p.nP p.nF :: (⟨.indInfo cvTa (Setlec.directCaps p) ::
      env.consts⟩ : Env).consts⟩ : Env).find? p.cvC.name
      = some (.ctorInfo cvCa p.nP p.nF) := by
    rw [← hCname]; exact Setlec.Env.find?_cons_self _ _
  have hleafT_C : ∀ ψ, mpC.base2.acval p.cvT.name ψ
      = directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2)) := by
    intro ψ
    rw [hacC]
    show acvalWith mpI.base2.acval cvCa.name _ p.cvT.name ψ = _
    rw [acvalWith_ne hTC]
    exact hleafT_I ψ
  have hleafC_C : ∀ ψ, mpC.base2.acval p.cvC.name ψ
      = directMkAV (p.resSort.eval ψ) (ds ψ) (((ds ψ).drop p.nP).map (·.2.2)) := by
    intro ψ
    rw [hacC, ← hCname, acvalWith_self]
  -- the η-families stay closed at the constructor's extension
  have hE_C : Setlec.EtaFamiliesClosed ⟨.ctorInfo cvCa p.nP p.nF ::
      (⟨.indInfo cvTa (Setlec.directCaps p) :: env.consts⟩ : Env).consts⟩ := by
    intro T'' cvT'' caps hf he hr
    rw [Setlec.Env.find?_cons] at hf
    split at hf
    · exact nomatch (Option.some.inj hf)
    · rw [Setlec.Env.find?_cons] at hf
      split at hf
      · next heq =>
        obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
        refine ⟨cvCa, ?_⟩
        show Env.find? ⟨.ctorInfo cvCa p.nP p.nF :: _⟩ p.cvC.name
          = some (.ctorInfo cvCa p.nP p.nF)
        rw [← hCname]
        exact Setlec.Env.find?_cons_self _ _
      · obtain ⟨cvC', hfC'⟩ := hE T'' cvT'' caps hf he hr
        exact ⟨cvC', Setlec.Env.find?_cons_of_fresh hCfreshI
          (Setlec.Env.find?_cons_of_fresh hTfresh hfC')⟩
  obtain ⟨rds, hRD⟩ := recData_of hμ mpC hccvR hRec
  obtain ⟨mp₃, hac₃⟩ := stageRec hμ hE_C mpC hccvR hRec hRule hfT_C hlpsT hfC_C hlpsC helim
    (fun hnF => hslotsF 0 hnF) hFD_C hCD_C hRD hleafT_C hleafC_C hiff
    (fun ψ ρ h => ⟨(hfields ψ ρ h).1, (hfields ψ ρ h).2.1, (hfields ψ ρ h).2.2.1,
      (hfields ψ ρ h).2.2.2.1⟩)
  -- the fold's invariant at the first slot
  obtain ⟨hfindR, -, -, -, -, hnfR, typeR, -, -, hannR, -, htrR, -, -, htyR⟩ :=
    Setlec.checkConstantVal_inv hccvR
  have hRname' : cvRa.name = p.cvR.name := by rw [htyR]
  have hRtype : cvRa.type = typeR := by rw [htyR]
  have hRfresh : (⟨.ctorInfo cvCa p.nP p.nF :: (⟨.indInfo cvTa (Setlec.directCaps p) ::
      env.consts⟩ : Env).consts⟩ : Env).find? cvRa.name = none := by
    rw [hRname']; exact hfindR
  have hTR : p.cvT.name ≠ cvRa.name := by
    intro h; rw [h, hRfresh] at hfT_C; exact nomatch hfT_C
  have hCR : p.cvC.name ≠ cvRa.name := by
    intro h; rw [h, hRfresh] at hfC_C; exact nomatch hfC_C
  have hcbT_C := constsBound_of_constsResolve _
    (mpC.base2.wf _ (Setlec.Semantics.Env.find?_mem hfT_C)).2.2.1
  have hcbC_C := constsBound_of_constsResolve _
    (mpC.base2.wf _ (Setlec.Semantics.Env.find?_mem hfC_C)).2.2.1
  obtain ⟨hnfRhs, -, hannRhs, -⟩ := Setlec.checkDirectRule_shape hRule
  -- the structure's slots are mentioned by no stored piece: no table
  -- is stored below the table stage (task #175 S1)
  have hslotI : ∀ j,
      (⟨.indInfo cvTa (Setlec.directCaps p) :: env.consts⟩ : Env).findProj? p.cvT.name j
        = none :=
    fun j => Setlec.Env.findProj?_none_of_fresh
      (find?_none_of_cons (find?_none_of_cons hfreshTbl)) j
  have hslotC : ∀ j,
      (⟨.ctorInfo cvCa p.nP p.nF :: (⟨.indInfo cvTa (Setlec.directCaps p) ::
        env.consts⟩ : Env).consts⟩ : Env).findProj? p.cvT.name j = none :=
    fun j => Setlec.Env.findProj?_none_of_fresh (find?_none_of_cons hfreshTbl) j
  have hnp₃ : ∀ j, NoProjEnv ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP,
        if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then .plain else .inert,
        rhsA⟩] :: (⟨.ctorInfo cvCa p.nP p.nF :: (⟨.indInfo cvTa (Setlec.directCaps p) ::
          env.consts⟩ : Env).consts⟩ : Env).consts⟩ p.cvT.name j := by
    intro j
    have h0 : NoProjEnv env p.cvT.name j := noProjEnv_of_fresh mp.base2.wf hfindT j
    have h1 := h0.cons (c₀ := .indInfo cvTa (Setlec.directCaps p)) (NoProjHead.ofType
      (by
        show Expr.NoProjAt p.cvT.name j cvTa.type
        exact Setlec.Expr.noProjAt_of_constsResolve hfindT _ (by rw [hTtype]; exact htrT))
      (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ h => nomatch h))
    have h2 := h1.cons (c₀ := .ctorInfo cvCa p.nP p.nF) (NoProjHead.ofType
      (by
        show Expr.NoProjAt p.cvT.name j cvCa.type
        rw [hCtype]
        exact Setlec.annotateCore_noProjAt μ hannC hnfC (hslotI j))
      (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ h => nomatch h))
    refine h2.cons ⟨?_, (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h), ?_,
      (fun _ h => nomatch h)⟩
    · show Expr.NoProjAt p.cvT.name j cvRa.type
      rw [hRtype]
      exact Setlec.annotateCore_noProjAt μ hannR hnfR (hslotC j)
    · intro cv mI rP rules heq r hr
      injection heq with _ _ _ hrules
      subst hrules
      rcases List.mem_singleton.mp hr with rfl
      refine ⟨Setlec.annotateCore_noProjAt μ hannRhs hnfRhs (hslotC j), ?_⟩
      intro lvls pins hfire
      split at hfire <;> exact nomatch hfire
  -- the table's cons
  have hfT₃ : (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP,
        if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then .plain else .inert,
        rhsA⟩] :: (⟨.ctorInfo cvCa p.nP p.nF :: (⟨.indInfo cvTa (Setlec.directCaps p) ::
          env.consts⟩ : Env).consts⟩ : Env).consts⟩ : Env).find? p.cvT.name
      = some (.indInfo cvTa (Setlec.directCaps p)) := by
    rw [Setlec.Env.find?_cons, if_neg (fun h => hTR h.symm)]
    exact hfT_C
  have hfC₃ : (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP,
        if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then .plain else .inert,
        rhsA⟩] :: (⟨.ctorInfo cvCa p.nP p.nF :: (⟨.indInfo cvTa (Setlec.directCaps p) ::
          env.consts⟩ : Env).consts⟩ : Env).consts⟩ : Env).find? p.cvC.name
      = some (.ctorInfo cvCa p.nP p.nF) := by
    rw [Setlec.Env.find?_cons, if_neg (fun h => hCR h.symm)]
    exact hfC_C
  have hFD₃ : FormerData mp₃.base2 cvTa p.nP p.resSort pps :=
    hFD_C.cross (c₀ := .recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP,
        if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then .plain else .inert,
        rhsA⟩]) hRfresh (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT_C mp₃.base2 hac₃
  have hCD₃ : CtorData mp₃.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds :=
    hCD_C.cross (c₀ := .recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP,
        if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then .plain else .inert,
        rhsA⟩]) hRfresh hTR (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbC_C mp₃.base2 hac₃
  have hleafT₃ : ∀ ψ, mp₃.base2.acval p.cvT.name ψ
      = directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2)) := by
    intro ψ
    rw [hac₃]
    show acvalWith mpC.base2.acval cvRa.name _ p.cvT.name ψ = _
    rw [acvalWith_ne hTR]
    exact hleafT_C ψ
  have hleafC₃ : ∀ ψ, mp₃.base2.acval p.cvC.name ψ
      = directMkAV (p.resSort.eval ψ) (ds ψ) (((ds ψ).drop p.nP).map (·.2.2)) := by
    intro ψ
    rw [hac₃]
    show acvalWith mpC.base2.acval cvRa.name _ p.cvC.name ψ = _
    rw [acvalWith_ne hCR]
    exact hleafC_C ψ
  exact stageTable mp₃ hsorts hTbl hfT₃ hlpsT hfC₃ hlpsC (by rw [hstripC]; rfl) hProp
    hpshapeT hpshapeC hresT (by rw [← hRname]; exact hresR) hresC hnp₃ hFD₃ hCD₃ hleafT₃
    hleafC₃ hiff hfields

end Setlec.SetP
