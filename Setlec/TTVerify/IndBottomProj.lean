import Setlec.TTVerify.IndBottomStages
import Setlec.TTVerify.IndBottomPlain
import Setlec.TTVerify.OpenRevDenote

/-!
# `IndBottomProjTT`: the projection bottom

The stored projection function is a degenerate recursor
(`checkProjFn`): major at position `nP`, rule prefix the parameters,
`mI = rP = ctorParams`, no indices.  DESIGN §22 records the design:
the statement's telescope domains are syntactically the constructor's
renamed, so the fired-spine fit is the mixed constructor fit
retargeted across `teleAlign_of_stripPis`, and the reduct β-reduces
through the rule's λ-tower (`stripLams_denoteTele` +
`CtxSpine.betaSpine`).
-/

set_option maxHeartbeats 12800000

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

/-- **The projection bottom** (DESIGN §22): a checked `proj_i.iota`
theorem of a stored degenerate projection recursor (`mI = rP`,
`ctorParams = rP`), fired as its `RecRulesTT` law.  The statement's
telescope domains are syntactically the constructor's renamed
(`domsMatchAux`), so the fired-spine fit is the mixed constructor fit
retargeted across `teleAlign_of_stripPis`, and the reduct β-reduces
through the rule's λ-tower (`stripLams_denoteTele` +
`CtxSpine.betaSpine`). -/
theorem IndBottomProjTT
    {env₀ : Env} (m₀ : EnvTT env₀) {F : Nat} (hstep : CheckStepTT mode)
    {f : Name → Name} (hro : RenameOkT m₀.cval env₀ f)
    (heqfE : env₀.find? eqName = some eqA)
    -- the recursor's public data
    {Rn : Name} {lps : List Name} {tyA : Expr} {mI rP : Nat}
    (htyw : tyA.hasFvar = false) (htyb : tyA.looseBVarsBounded 0 = true)
    -- the model recursor carries the statement's constants
    {ciRm : ConstantInfo}
    (hfRnE : env₀.find? (f Rn) = some ciRm)
    (hRmlps : ciRm.toConstantVal.levelParams = lps)
    -- the constructor
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat}
    (hctorE : env₀.find? ctor = some (.ctorInfo cvj cnP cnF))
    {ciCm : ConstantInfo}
    (hfCmE : env₀.find? (f ctor) = some ciCm)
    (hCmlps : ciCm.toConstantVal.levelParams = cvj.levelParams)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hClp : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    -- shape bounds
    (hmIrP : mI = rP) (hcnPrP : cnP = rP) {i : Nat} (hilt : i < cnF)
    -- the rule's annotated right-hand side
    {rhsA : Expr} (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    {rhsTy : Expr} (hinfR : inferTypeCore mode env₀ F 0 rhsA = .ok rhsTy)
    -- the checked theorem's statement and inhabitant
    {stmtTy : Expr}
    (hSw : stmtTy.hasFvar = false) (hSb : stmtTy.looseBVarsBounded 0 = true)
    (hthm : ∀ ψ' : Name → Nat, ∃ pv t,
      denoteClosed m₀.cval env₀ ψ' stmtTy = some t ∧ HasType [] pv t)
    -- the kit (theorem side)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    (hopen : openPisAtFvars (rP + cnF) stmtTy 0 = some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const (f Rn) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP))
    {cbinders : List (Name × Expr × BinderMeta)} {cbody : Expr}
    (hCstrip : cvj.type.stripPis (cnP + cnF) = some (cbinders, cbody))
    (hdomsSC : PiDomsRenEqT f (cnP + cnF) cvj.type stmtTy)
    (hrhsSpin : rhsS = fvs.getD (rP + i) default)
    {rbinders : List (Name × Expr × BinderMeta)}
    (hrhsAstrip : rhsA.stripLams (cnP + cnF) =
      some (rbinders, .bvar (cnF - 1 - i)))
    (hrdomsEq : ∀ (i0 : Nat) (b b' : Name × Expr × BinderMeta),
      i0 < cnP + cnF → rbinders[i0]? = some b →
      cbinders[i0]? = some b' → b.2.1 = b'.2.1)
    -- the kit (public prefix and constructor parameters)
    {fvsP : List Expr} {restP : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type =
      some (cdomsP, crestP))
    (hdePars : DefEqListOk mode F env₀ (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    -- both sides' typings
    (hlhsTyC : ∃ tl, inferTypeCore mode env₀ F (rP + cnF) lhsS = .ok tl ∧
      isDefEqCore mode env₀ F (rP + cnF) tl αS = .ok true)
    (hrhsTyC : ∃ tr, inferTypeCore mode env₀ F (rP + cnF) rhsS = .ok tr ∧
      isDefEqCore mode env₀ F (rP + cnF) tr αS = .ok true)
    -- the premise nothing supplies yet (DESIGN §16.1)
    (hslot : IotaSlotSorted F env₀ (rP + cnF) αS ℓA) :
    ∀ (φ : Name → Nat) (d : Nat) (us : List Level),
      us.length = lps.length →
      ∃ RV, denote m₀.cval env₀ φ d
          (rhsA.instantiateLevelParams lps us) = some RV ∧
        ∀ (Δ : List VExpr) (usj : List Level) (xs ys : List VExpr)
          (TV TVj restR restC : VExpr),
          xs.length = mI →
          ys.length = cnP + cnF →
          usj.length = cvj.levelParams.length →
          Level.substFn φ cvj.levelParams usj =
            Level.substFn φ cvj.levelParams
              (cvj.levelParams.map fun p => Level.subst lps us (.param p)) →
          (∀ i, i < cnP → i < mI →
            Deq Δ (ys.getD i default) (xs.getD i default)) →
          IotaIndexPin Δ restC cnP mI rP xs →
          denote m₀.cval env₀ φ d
            (tyA.instantiateLevelParams lps us) = some TV →
          denote m₀.cval env₀ φ d
            (cvj.type.instantiateLevelParams cvj.levelParams usj)
            = some TVj →
          VTeleTyped Δ TV
            (xs ++ [VExpr.mkAppN
              (m₀.cval ctor (Level.substFn φ cvj.levelParams usj)) ys])
            restR →
          VTeleTyped Δ TVj ys restC →
          Deq Δ
            (VExpr.mkAppN (m₀.cval Rn (Level.substFn φ lps us))
              (xs ++ [VExpr.mkAppN
                (m₀.cval ctor (Level.substFn φ cvj.levelParams usj)) ys]))
            (VExpr.mkAppN RV (xs.take rP ++ ys.drop cnP)) := by
  intro φ d us hlenU
  have hcl := m₀.cval_closed
  have hvp : ValParams env₀ m₀.cval := m₀.val_params
  -- the four claims at the instantiated assignment
  obtain ⟨ihwc, ihw, ihd, ihi⟩ :=
    checkSoundTT hstep m₀ (Level.substFn φ lps us) F
  -- the rule's right-hand side denotes, from its inference run
  obtain ⟨RV, rhsTyV, hRV0, -, -⟩ := ihi (Δ := []) hinfR
    (Expr.WScoped.of_not_hasFvar hrhsw) hrhsb
    (Expr.LeavesBounded.of_not_hasFvar hrhsw)
    (CtxOk.nil (Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsw))
  have hRV : denote m₀.cval env₀ φ d (rhsA.instantiateLevelParams lps us)
      = some RV := by
    rw [denote_instLevels hvp φ d rhsA,
      denote_depth_closed hcl hrhsw hrhsb d]
    exact hRV0
  refine ⟨RV, hRV, ?_⟩
  intro Δ usj xs ys TV TVj restR restC hlenX hlenY hlenJ hlev hpar hidx
    hTV hTVj hfitR hfitC
  have hplainLe : cnP ≤ rP := by omega
  have hrPmI : rP ≤ mI := by omega
  -- ===== Stage A: the statement, opened =====
  obtain ⟨pv, Tstmt, hTstmtC, hpv⟩ := hthm (Level.substFn φ lps us)
  have hTstmt : denote m₀.cval env₀ (Level.substFn φ lps us) 0 stmtTy
      = some Tstmt := hTstmtC
  obtain ⟨Γs, Rbody, htowerS, hRbody, hdomsS0⟩ :=
    openPisAtFvars_denoteTele (rP + cnF) hopen hTstmt
  rw [Nat.zero_add] at hRbody
  have hΓslen : Γs.length = rP + cnF := htowerS.length
  obtain ⟨bsS, bodyS0, hstripS, hfvslen, -, -⟩ :=
    openPisAtFvars_stripPis (rP + cnF) hopen
  have hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty := by
    intro i x hx
    obtain ⟨nm, ty, hx'⟩ := openPisAtFvars_index _ _ _ hopen i x hx
    exact ⟨nm, ty, by simpa using hx'⟩
  have hwsS := openPisAtFvars_WScoped _ _ _ hopen
    (Expr.WScoped.of_not_hasFvar hSw)
  simp only [Nat.zero_add] at hwsS
  obtain ⟨hwsFvs, hwsBody⟩ := hwsS
  obtain ⟨hbBody, hbAnns⟩ := openPisAtFvars_bounded _ hopen hSb
  have hleafS : ∀ l, (l ∈ tbody.fvarLeaves ∨ ∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
    intro l hl
    rcases openPisAtFvars_leaves _ hopen l hl with h1 | h1
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hSw] at h1
      exact nomatch h1
    · exact h1
  have hLB : ∀ (e : Expr),
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs) →
      Expr.LeavesBounded e := by
    intro e hl l hle
    have h1 := hbAnns _ (hl l hle)
    rw [show Expr.fvarTypeD (Expr.fvar l.1 l.2.1 l.2.2) = l.2.2 from rfl]
      at h1
    exact h1
  -- the frame-generic workhorse: an open install fact over a frame's
  -- openers, instantiated along a fitted prefix (padding the rest)
  -- the frame-generic workhorse, sealed (`IndBottomStages`)
  have hopenDeqG := openFrame_deq (Δ := Δ) (K := rP + cnF) m₀ ihd
  -- ===== Stage B: the public and constructor towers =====
  have hTV0 : denote m₀.cval env₀ (Level.substFn φ lps us) 0 tyA
      = some TV := by
    rw [denote_instLevels hvp φ d tyA,
      denote_depth_closed hcl htyw htyb d] at hTV
    exact hTV
  obtain ⟨ΓP, RP, htowerP, hRP, hdomsP0⟩ :=
    openPisAtFvars_denoteTele rP hopenP hTV0
  have hΓPlen : ΓP.length = rP := htowerP.length
  -- the constructor's level assignment agrees with the statement's
  have hagree : ∀ p ∈ cvj.levelParams,
      Level.substFn φ cvj.levelParams usj p = Level.substFn φ lps us p := by
    intro p hp
    rw [hlev,
      show (cvj.levelParams.map fun p => Level.subst lps us (.param p)) =
        (cvj.levelParams.map Level.param).map (Level.subst lps us) from by
          rw [List.map_map]; rfl,
      Level.substFn_map_subst (by simp) hp]
    exact Level.substFn_map_param
  have hTVj0 : denote m₀.cval env₀ (Level.substFn φ lps us) 0 cvj.type
      = some TVj := by
    rw [denote_instLevels hvp φ d cvj.type,
      denote_depth_closed hcl hCw hCb d] at hTVj
    rw [← denote_params_ext hvp hagree 0 cvj.type hClp]
    exact hTVj
  -- open the constructor's telescope (it strips, so it opens)
  obtain ⟨⟨fvsC, restCE⟩, hopenC⟩ := Option.isSome_iff_exists.mp
    (openPisAtFvars_isSome_of_stripPis _
      (show (cvj.type.stripPis (cnP + cnF)).isSome = true from by
        rw [hCstrip]; rfl) 0)
  obtain ⟨Γj, Rj, htowerJ, hRj, hdomsJ0⟩ :=
    openPisAtFvars_denoteTele (cnP + cnF) hopenC hTVj0
  rw [Nat.zero_add] at hRj
  have hΓjlen : Γj.length = cnP + cnF := htowerJ.length
  obtain ⟨bsC, bodyC0, hstripC, hfvsClen, -, -⟩ :=
    openPisAtFvars_stripPis (cnP + cnF) hopenC
  have hshapeC : ∀ (i : Nat) (x : Expr), fvsC[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty := by
    intro i x hx
    obtain ⟨nm, ty, hx'⟩ := openPisAtFvars_index _ _ _ hopenC i x hx
    exact ⟨nm, ty, by simpa using hx'⟩
  -- ===== Stage B': the P-frame bundle =====
  obtain ⟨bsP, bodyP0, hstripP, hfvsPlen, -, -⟩ :=
    openPisAtFvars_stripPis rP hopenP
  have hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty := by
    intro i x hx
    obtain ⟨nm, ty, hx'⟩ := openPisAtFvars_index _ _ _ hopenP i x hx
    exact ⟨nm, ty, by simpa using hx'⟩
  have hwsP0 := openPisAtFvars_WScoped _ _ _ hopenP
    (Expr.WScoped.of_not_hasFvar htyw)
  simp only [Nat.zero_add] at hwsP0
  obtain ⟨hwsFvsP, -⟩ := hwsP0
  have hwsFvsP' : ∀ x ∈ fvsP, Expr.WScoped (rP + cnF) x :=
    fun x hx => (hwsFvsP x hx).mono (by omega)
  obtain ⟨-, hbAnnsP⟩ := openPisAtFvars_bounded _ hopenP htyb
  have hleafP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP := by
    intro l hl
    rcases openPisAtFvars_leaves _ hopenP l (Or.inr hl) with h1 | h1
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htyw] at h1
      exact nomatch h1
    · exact h1
  have hLBP : ∀ (e : Expr),
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP) →
      Expr.LeavesBounded e := by
    intro e hl l hle
    have h1 := hbAnnsP _ (hl l hle)
    rw [show Expr.fvarTypeD (Expr.fvar l.1 l.2.1 l.2.2) = l.2.2 from rfl]
      at h1
    exact h1
  have hdomsP0' : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      denote m₀.cval env₀ (Level.substFn φ lps us) i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default) := by
    intro i x hx
    have h1 := hdomsP0 i x hx
    simpa using h1
  have hdomsS0' : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote m₀.cval env₀ (Level.substFn φ lps us) i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default) := by
    intro i x hx
    have h1 := hdomsS0 i x hx
    simpa using h1
  have hdomsJ0' : ∀ (i : Nat) (x : Expr), fvsC[i]? = some x →
      denote m₀.cval env₀ (Level.substFn φ lps us) i (Expr.fvarTypeD x)
        = some (Γj.getD (cnP + cnF - 1 - i) default) := by
    intro i x hx
    have h1 := hdomsJ0 i x hx
    simpa using h1
  -- ===== Stage C: the fire fittings, read as spines and steps =====
  have htowerJ' : PiTele ys.length TVj Γj Rj := by
    rw [hlenY]
    exact htowerJ
  have hcsC : CtxSpine Δ Γj ys := hfitC.toCtxSpine htowerJ'
  have hrestC : restC = VExpr.instSeq ys (ys.length - 1) Rj :=
    hfitC.rest_of_piTele htowerJ'
  have hstepsC := hfitC.steps htowerJ'
  -- the recursor fitting, truncated at the prefix
  obtain ⟨midR, hfitRpre0, -⟩ := hfitR.take rP
  have htakexs : (xs ++ [VExpr.mkAppN
      (m₀.cval ctor (Level.substFn φ cvj.levelParams usj)) ys]).take rP
      = xs.take rP := List.take_append_of_le_length (by omega)
  rw [htakexs] at hfitRpre0
  have hxstakelen : (xs.take rP).length = rP := by
    rw [List.length_take]
    omega
  have htowerP' : PiTele (xs.take rP).length TV ΓP RP := by
    rw [hxstakelen]
    exact htowerP
  have hstepsR := hfitRpre0.steps htowerP'
  -- truncated constructor-context spines (for the congruences)
  have hcsCpre : ∀ j, j ≤ cnP + cnF →
      CtxSpine Δ (Γj.drop (cnP + cnF - j)) (ys.take j) := by
    intro j hj
    obtain ⟨midC, hfitCpre, -⟩ := hfitC.take j
    obtain ⟨midJ, hpre1, -⟩ := PiTele.prefix htowerJ j hj
    have hylen : (ys.take j).length = j := by
      rw [List.length_take]
      omega
    refine hfitCpre.toCtxSpine (Γ := Γj.drop (cnP + cnF - j)) (R := midJ) ?_
    rw [hylen]
    exact hpre1
  -- truncated recursor-context spines
  have hcsRpre : ∀ j, j ≤ rP →
      CtxSpine Δ (ΓP.drop (rP - j)) (xs.take j) := by
    intro j hj
    obtain ⟨midR2, hfitR2, -⟩ := hfitRpre0.take j
    rw [List.take_take, Nat.min_eq_left hj] at hfitR2
    obtain ⟨midP2, hpre1, -⟩ := PiTele.prefix htowerP j hj
    have hxlen : (xs.take j).length = j := by
      rw [List.length_take]
      omega
    refine hfitR2.toCtxSpine (Γ := ΓP.drop (rP - j)) (R := midP2) ?_
    rw [hxlen]
    exact hpre1
  -- ===== Stage D: the constructor's parameter domains, across openings
  have hCinstAll : Expr.instPisAt fvsC cvj.type =
      some (fvsC.map Expr.fvarTypeD, restCE) :=
    openPisAtFvars_instPisAt _ hopenC
  obtain ⟨midC0, hCtake, hCdrop⟩ := instPisAt_take fvsC cnP hCinstAll
  have hcdomsPlen : cdomsP.length = cnP := by
    have h1 := DefEqListOk.length hdePars
    rw [List.length_map, List.length_take] at h1
    omega
  have hPCdoms : ∀ (j : Nat) (x x' : Expr),
      ((fvsC.map Expr.fvarTypeD).take cnP)[j]? = some x →
      cdomsP[j]? = some x' → Expr.ErasedEq x x' := by
    intro j x x' hx hx'
    have hren : RenEqT (fun n => n) cvj.type cvj.type := by
      show Expr.ErasedEq (cvj.type.renameConsts (fun n => n)) cvj.type
      rw [Expr.renameConsts_id]
      exact Expr.ErasedEq.rfl _
    have hargs : ∀ (i : Nat) (a a' : Expr),
        (fvsC.take cnP)[i]? = some a → (fvsP.take cnP)[i]? = some a' →
        RenEqT (fun n => n) a a' := by
      intro i a a' ha ha'
      have hia : i < cnP + cnF := by
        rcases Nat.lt_or_ge i (cnP + cnF) with h | h
        · exact h
        · rw [List.getElem?_eq_none (by
            rw [List.length_take]; omega)] at ha
          exact nomatch ha
      have hia' : i < cnP := by
        rcases Nat.lt_or_ge i cnP with h | h
        · exact h
        · rw [List.getElem?_eq_none (by
            rw [List.length_take]; omega)] at ha'
          exact nomatch ha'
      rw [List.getElem?_take_of_lt hia'] at ha ha'
      obtain ⟨nm1, ty1, rfl⟩ := hshapeC i a ha
      obtain ⟨nm2, ty2, rfl⟩ := hshapeP i a' ha'
      exact RenEqT.fvar
    obtain ⟨hds, -⟩ := instPisAt_renEq (fvsC.take cnP) (fvsP.take cnP)
      hCtake hcinstP hren hargs
      (by rw [List.length_take, List.length_take]; omega)
    have h1 := hds j x x' hx hx'
    show Expr.ErasedEq x x'
    have h2 : Expr.ErasedEq (x.renameConsts (fun n => n)) x' := h1
    rwa [Expr.renameConsts_id] at h2
  -- the parameter bridge: at each j < cnP, the recursor's j-th
  -- instantiated domain and the constructor's are Deq
  -- the parameter bridge, sealed (`IndBottomStages`)
  have hparBridge := paramBridge m₀ ihd hplainLe (by omega)
    hfvsPlen hfvsClen hΓPlen hΓjlen hcdomsPlen hCw hCb hcinstP
    hdePars hshapeP hshapeC hwsFvsP hwsFvsP' hbAnnsP hleafP hLBP
    hdomsP0' hdomsJ0' hPCdoms hcsRpre
  -- ===== Stage E: the mixed constructor fitting =====
  have hmixlen : (xs.take cnP ++ ys.drop cnP).length = cnP + cnF := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have htowerJ'' : PiTele (xs.take cnP ++ ys.drop cnP).length TVj Γj Rj := by
    rw [hmixlen]
    exact htowerJ
  -- prefix values of the mixed spine
  have hmixget : ∀ p, p < cnP + cnF →
      (xs.take cnP ++ ys.drop cnP).getD p default =
        (if p < cnP then xs.getD p default else ys.getD p default) := by
    intro p hp
    by_cases hpc : p < cnP
    · rw [if_pos hpc]
      have hp1 : p < (xs.take cnP).length := by
        rw [List.length_take]
        omega
      simp only [List.getD]
      rw [List.getElem?_append_left hp1, List.getElem?_take_of_lt hpc]
    · rw [if_neg hpc]
      have hp1 : (xs.take cnP).length ≤ p := by
        rw [List.length_take]
        omega
      simp only [List.getD]
      rw [List.getElem?_append_right hp1, List.length_take,
        show p - min cnP xs.length = p - cnP from by omega,
        List.getElem?_drop,
        show cnP + (p - cnP) = p from by omega]
  have hmixtake : ∀ n, n ≤ cnP →
      (xs.take cnP ++ ys.drop cnP).take n = xs.take n := by
    intro n hn
    rw [List.take_append_of_le_length (by rw [List.length_take]; omega),
      List.take_take, Nat.min_eq_left hn]
  -- the mixed fitting, built sequentially
  have hmixed : VTeleTyped Δ TVj (xs.take cnP ++ ys.drop cnP)
      (VExpr.instSeq (xs.take cnP ++ ys.drop cnP)
        ((xs.take cnP ++ ys.drop cnP).length - 1) Rj) := by
    refine VTeleTyped.ofPiTele htowerJ'' ?_
    intro n hn hpref
    rw [hmixlen] at hn
    by_cases hncnP : n < cnP
    · -- a parameter: the recursor's fitting, converted along the bridge
      have hsrc := hstepsR n (by rw [hxstakelen]; omega)
      rw [hxstakelen, List.take_take, Nat.min_eq_left (by omega : n ≤ rP),
        show (xs.take rP).getD n default = xs.getD n default from by
          simp only [List.getD]
          rw [List.getElem?_take_of_lt (by omega : n < rP)]] at hsrc
      rw [show (xs.take cnP ++ ys.drop cnP).getD n default =
          xs.getD n default from by
        rw [hmixget n (by omega), if_pos hncnP],
        hmixtake n (by omega),
        show (xs.take cnP ++ ys.drop cnP).length - 1 - n =
          cnP + cnF - 1 - n from by rw [hmixlen]]
      exact Deq.conv hsrc (hparBridge n hncnP)
    · -- a field: the constructor's own fitting, prefix-converted
      have hsrc := hstepsC n (by omega)
      rw [show ys.length - 1 - n = cnP + cnF - 1 - n from by omega] at hsrc
      -- the two prefixes are Deq, pointwise
      obtain ⟨mid, hmid⟩ := hpref
      obtain ⟨midJ2, hpre2, -⟩ := PiTele.prefix htowerJ n (by omega)
      have hmixtklen : ((xs.take cnP ++ ys.drop cnP).take n).length = n := by
        rw [List.length_take, hmixlen]
        omega
      have hcsMixPre : CtxSpine Δ (Γj.drop (cnP + cnF - n))
          ((xs.take cnP ++ ys.drop cnP).take n) := by
        refine hmid.toCtxSpine (Γ := Γj.drop (cnP + cnF - n))
          (R := midJ2) ?_
        rw [hmixtklen]
        exact hpre2
      have hylen : (ys.take n).length = n := by
        rw [List.length_take]
        omega
      have hpt : ∀ q : Fin (ys.take n).length, Deq Δ (ys.take n)[q]
          (((xs.take cnP ++ ys.drop cnP).take n).getD q default) := by
        intro q
        have hq : q.1 < n := by
          have h0 := q.2
          omega
        have hyq : (ys.take n)[q.1] = ys.getD q.1 default := by
          rw [List.getElem_take]
          simp only [List.getD]
          rw [List.getElem?_eq_getElem (by omega : q.1 < ys.length)]
          rfl
        have hmq : ((xs.take cnP ++ ys.drop cnP).take n).getD q.1 default =
            (xs.take cnP ++ ys.drop cnP).getD q.1 default := by
          simp only [List.getD]
          rw [List.getElem?_take_of_lt hq]
        rw [Fin.getElem_fin, hyq, hmq, hmixget q.1 (by omega)]
        by_cases hqc : q.1 < cnP
        · rw [if_pos hqc]
          exact hpar q.1 hqc (by omega)
        · rw [if_neg hqc]
      have hcongr := CtxSpine.instSeq_congr (hcsCpre n (by omega))
        hcsMixPre hpt (Γj.getD (cnP + cnF - 1 - n) default)
      rw [hylen, hmixtklen] at hcongr
      rw [show (xs.take cnP ++ ys.drop cnP).getD n default =
          ys.getD n default from by
        rw [hmixget n (by omega), if_neg hncnP],
        show (xs.take cnP ++ ys.drop cnP).length - 1 - n =
          cnP + cnF - 1 - n from by rw [hmixlen]]
      exact Deq.conv hsrc hcongr
  have hstepsMix := hmixed.steps htowerJ''
  have hcsMix : CtxSpine Δ Γj (xs.take cnP ++ ys.drop cnP) :=
    hmixed.toCtxSpine htowerJ''
  -- ===== Stage F: the fired statement spine =====
  have hzslen : (xs.take rP ++ ys.drop cnP).length = rP + cnF := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have hzsget : ∀ p, p < rP + cnF →
      (xs.take rP ++ ys.drop cnP).getD p default =
        (if p < rP then xs.getD p default
         else ys.getD (cnP + (p - rP)) default) := by
    intro p hp
    by_cases hpr : p < rP
    · rw [if_pos hpr]
      have hp1 : p < (xs.take rP).length := by
        rw [List.length_take]
        omega
      simp only [List.getD]
      rw [List.getElem?_append_left hp1, List.getElem?_take_of_lt hpr]
    · rw [if_neg hpr]
      have hp1 : (xs.take rP).length ≤ p := by
        rw [List.length_take]
        omega
      simp only [List.getD]
      rw [List.getElem?_append_right hp1, List.length_take,
        show p - min rP xs.length = p - rP from by omega,
        List.getElem?_drop]
  have hzstake : ∀ n, n ≤ rP →
      (xs.take rP ++ ys.drop cnP).take n = xs.take n := by
    intro n hn
    rw [List.take_append_of_le_length (by rw [List.length_take]; omega),
      List.take_take, Nat.min_eq_left hn]
  -- ===== Stage F': the constructor's scattered run =====
  have hpadhit : ∀ (n p : Nat) (vals : List VExpr), p < n →
      vals.length = n → n ≤ rP + cnF →
      VExpr.instSeq (vals ++ List.replicate (rP + cnF - n) dummyPropT)
        (rP + cnF - 1) (.bvar (rP + cnF - 1 - p)) =
        vals.getD p default := by
    intro n p vals hp hvl hn
    have hlenT : (vals ++ List.replicate (rP + cnF - n) dummyPropT).length
        = rP + cnF := by
      simp only [List.length_append, List.length_replicate, hvl]
      omega
    have hidx : (vals ++ List.replicate (rP + cnF - n)
        dummyPropT)[(vals ++ List.replicate (rP + cnF - n)
          dummyPropT).length - 1 - (rP + cnF - 1 - p)]? =
        some (vals.getD p default) := by
      rw [hlenT, show rP + cnF - 1 - (rP + cnF - 1 - p) = p from by omega,
        List.getElem?_append_left (by omega),
        List.getElem?_eq_getElem (by omega : p < vals.length)]
      simp [List.getD, List.getElem?_eq_getElem
        (by omega : p < vals.length)]
    have h1 := VExpr.instSeq_bvar_hit
      (vals ++ List.replicate (rP + cnF - n) dummyPropT) 0
      (rP + cnF - 1 - p) (vals.getD p default) hidx (by omega)
    simp only [Nat.zero_add] at h1
    rw [hlenT] at h1
    rw [h1, VExpr.liftN_zero]
  -- the scattered spine of the constructor's statement-side run
  have hsplen : (fvs.take cnP ++ fvs.drop rP).length = cnP + cnF := by
    simp only [List.length_append, List.length_take, List.length_drop,
      hfvslen]
    omega
  have hspGet : ∀ (q : Nat), q < cnP + cnF →
      (fvs.take cnP ++ fvs.drop rP)[q]? =
        fvs[if q < cnP then q else rP + (q - cnP)]? := by
    intro q hq
    by_cases hqc : q < cnP
    · rw [if_pos hqc,
        List.getElem?_append_left (by rw [List.length_take, hfvslen]; omega),
        List.getElem?_take_of_lt hqc]
    · rw [if_neg hqc,
        List.getElem?_append_right (by rw [List.length_take, hfvslen]; omega),
        List.length_take, hfvslen,
        show q - min cnP (rP + cnF) = q - cnP from by omega,
        List.getElem?_drop]
  have hspFacts : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      (∃ i nm t, x = Expr.fvar i nm t) ∧ Expr.WScoped (rP + cnF) x ∧
        x.looseBVarsBounded 0 = true := by
    intro q x hx
    have hq : q < cnP + cnF := by
      rcases Nat.lt_or_ge q (cnP + cnF) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hsplen]; omega)] at hx
        exact nomatch hx
    rw [hspGet q hq] at hx
    obtain ⟨nm, t, rfl⟩ := hshapeS _ x hx
    refine ⟨⟨_, nm, t, rfl⟩, hwsFvs _ (List.mem_of_getElem? hx), rfl⟩
  have hspIdx : ∀ (q : Nat), q < cnP + cnF →
      ∃ nm t, (fvs.take cnP ++ fvs.drop rP)[q]? =
        some (Expr.fvar (if q < cnP then q else rP + (q - cnP)) nm t) := by
    intro q hq
    have hlt : (if q < cnP then q else rP + (q - cnP)) < fvs.length := by
      rw [hfvslen]
      by_cases hqc : q < cnP
      · rw [if_pos hqc]
        omega
      · rw [if_neg hqc]
        omega
    obtain ⟨nm, t, hsh⟩ := hshapeS _ fvs[if q < cnP then q else rP + (q - cnP)]
      (List.getElem?_eq_getElem hlt)
    refine ⟨nm, t, ?_⟩
    rw [hspGet q hq, List.getElem?_eq_getElem hlt, hsh]
  -- ===== Stage G: the statement fitting (the zipper) =====
  have htowerS' : PiTele (xs.take rP ++ ys.drop cnP).length Tstmt Γs
      Rbody := by
    rw [hzslen]
    exact htowerS
  -- ===== the statement fit: retarget the mixed fit (§22) =====
  obtain ⟨bsS2, bodyS2, hstripS2⟩ : ∃ bsS2 bodyS2,
      stmtTy.stripPis (cnP + cnF) = some (bsS2, bodyS2) := by
    refine ⟨bsS, bodyS0, ?_⟩
    rw [show cnP + cnF = rP + cnF from by omega]
    exact hstripS
  obtain ⟨Rmix, Rstmt, hRmixden, hRstmtden, halign⟩ :=
    teleAlign_of_stripPis hro (cnP + cnF) hCstrip hstripS2 hdomsSC
      hTVj0 hTstmt
      (xs := xs.take cnP ++ ys.drop cnP)
      (by
        simp only [List.length_append, List.length_take,
          List.length_drop]
        omega)
  obtain ⟨-, hzipMix⟩ := hmixed.retarget' halign
  have hmixzs : (xs.take cnP ++ ys.drop cnP) =
      (xs.take rP ++ ys.drop cnP) := by
    rw [hcnPrP]
  rw [hmixzs] at hzipMix
  have htowerS' : PiTele (xs.take rP ++ ys.drop cnP).length Tstmt Γs
      Rbody := by
    rw [hzslen]
    exact htowerS
  have hzip : VTeleTyped Δ Tstmt (xs.take rP ++ ys.drop cnP)
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
        ((xs.take rP ++ ys.drop cnP).length - 1) Rbody) := by
    have h1 := hzipMix.rest_of_piTele htowerS'
    rw [h1] at hzipMix
    exact hzipMix
  -- ===== Stage H: fire the checked equation =====
  have hcsZfull : CtxSpine Δ Γs (xs.take rP ++ ys.drop cnP) :=
    hzip.toCtxSpine htowerS'
  have htbody : tbody =
      Expr.mkAppN (.const eqName [ℓA]) [αS, lhsS, rhsS] := by
    rw [← hheadEq, ← hargs3, Expr.mkAppN_getApp]
  rw [htbody] at hRbody
  obtain ⟨vEq, vArgs3, hvEq, hsp3, rfl⟩ := denote_mkAppN_inv hRbody
  obtain rfl : vEq = m₀.cval eqName
      (Level.substFn (Level.substFn φ lps us)
        eqA.toConstantVal.levelParams [ℓA]) := by
    rw [denote_const, heqfE] at hvEq
    dsimp only at hvEq
    rw [if_pos (by rfl)] at hvEq
    exact (Option.some.inj hvEq).symm
  -- the three argument denotations
  obtain ⟨vα, vL, vR, hαden, hLden, hRden, rfl⟩ :
      ∃ vα vL vR,
        denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF) αS
          = some vα ∧
        denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF) lhsS
          = some vL ∧
        denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF) rhsS
          = some vR ∧
        vArgs3 = [vα, vL, vR] := by
    cases hsp3 with
    | cons hα h1 =>
      cases h1 with
      | cons hL h2 =>
        cases h2 with
        | cons hR h3 =>
          cases h3
          exact ⟨_, _, _, hα, hL, hR, rfl⟩
  -- the fitting, at the instantiated equation
  have hfitEq : VTeleTyped Δ Tstmt (xs.take rP ++ ys.drop cnP)
      (VExpr.mkAppN (m₀.cval eqName
        (Level.substFn (Level.substFn φ lps us)
          eqA.toConstantVal.levelParams [ℓA]))
        [VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vα,
         VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vL,
         VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vR]) := by
    have h1 : VExpr.instSeq (xs.take rP ++ ys.drop cnP)
        ((xs.take rP ++ ys.drop cnP).length - 1)
        (VExpr.mkAppN (m₀.cval eqName
          (Level.substFn (Level.substFn φ lps us)
            eqA.toConstantVal.levelParams [ℓA])) [vα, vL, vR]) =
        VExpr.mkAppN (m₀.cval eqName
          (Level.substFn (Level.substFn φ lps us)
            eqA.toConstantVal.levelParams [ℓA]))
          [VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vα,
           VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vL,
           VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vR] := by
      rw [VExpr.instSeq_mkAppN,
        VExpr.instSeq_eq_self_of_closed (hcl _ _), hzslen]
      rfl
    rw [← h1]
    exact hzip
  -- frame facts of the three arguments
  have hCtxFull : ∀ (e : Expr),
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs) →
      Expr.WScoped (rP + cnF) e →
      CtxOk m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF) Γs e := by
    intro e hleaf hws
    refine ctxOk_of_openers hcl hΓslen hshapeS hwsFvs hdomsS0'
      hleaf hws ?_
    intro i hi
    simp only [List.getD]
    rw [List.getElem?_eq_getElem
      (show rP + cnF - 1 - i < Γs.length from by omega)]
    rfl
  have hargfacts : ∀ (e : Expr), e ∈ tbody.getAppArgs →
      Expr.WScoped (rP + cnF) e ∧ e.looseBVarsBounded 0 = true ∧
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs) ∧
      Expr.LeavesBounded e ∧
      CtxOk m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF) Γs e := by
    intro e hmem
    have hws := hwsBody.getAppArgs e hmem
    have hlf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs :=
      fun l hl => hleafS l (Or.inl (fvarLeaves_getAppArgs hmem l hl))
    exact ⟨hws, looseBVarsBounded_getAppArgs hbBody e hmem, hlf,
      hLB e hlf, hCtxFull e hlf hws⟩
  obtain ⟨hwsα, hbα, hlfα, hLα, hCα⟩ := hargfacts αS (by
    rw [hargs3]
    simp)
  obtain ⟨hwsL, hbL, hlfL, hLL, hCL⟩ := hargfacts lhsS (by
    rw [hargs3]
    simp)
  obtain ⟨hwsR, hbR, hlfR, hLR, hCR⟩ := hargfacts rhsS (by
    rw [hargs3]
    simp)
  -- the equation slot's sort (the carried premise, §16.1)
  obtain ⟨tα, hinfα, hdeα⟩ := hslot
  obtain ⟨vα₀, vtα, hα₀, htαden, htyα⟩ := ihi hinfα hwsα hbα hLα hCα
  rw [hαden] at hα₀
  rw [← Option.some.inj hα₀] at htyα
  have hwstα := inferTypeCore_WScoped m₀.wf F hinfα hwsα
  have hbtα := inferTypeCore_looseBVars m₀.wf F hinfα hwsα hbα hLα
  have hLtα : Expr.LeavesBounded tα := fun l hl =>
    hLα l (inferTypeCore_fvarLeaves m₀.wf F hinfα hwsα l hl)
  have hCtα := CtxOk.of_subset
    (inferTypeCore_fvarLeaves m₀.wf F hinfα hwsα) hCα
  have hsortden : denote m₀.cval env₀ (Level.substFn φ lps us)
      (rP + cnF) (Expr.sort ℓA) =
      some (.sort (Level.eval (Level.substFn φ lps us) ℓA)) := by
    rw [denote_sort]
  have hCsort : CtxOk m₀.cval env₀ (Level.substFn φ lps us)
      (rP + cnF) Γs (Expr.sort ℓA) := by
    refine ⟨hΓslen, ?_⟩
    intro l hl
    simp [Expr.fvarLeaves] at hl
  have hdeqα := ihd hdeα hwstα hbtα hLtα (by simp [Expr.WScoped]) rfl
    (fun l hl => by simp [Expr.fvarLeaves] at hl) hCtα hCsort
    htαden hsortden
  have htyα2 : HasType Γs vα
      (.sort (Level.eval (Level.substFn φ lps us) ℓA)) :=
    Deq.conv htyα hdeqα
  have hAsort : HasType Δ
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vα)
      (.sort (Level.eval (Level.substFn φ lps us) ℓA)) := by
    have h1 := HasType.instCtx hcsZfull (htyα2.weakenTail Δ)
    rw [VExpr.instSeq_sort, hzslen] at h1
    exact h1
  -- the two sides, typed at the slot
  have hsideTy : ∀ (side : Expr) (vside : VExpr),
      (∃ ts, inferTypeCore mode env₀ F (rP + cnF) side = .ok ts ∧
        isDefEqCore mode env₀ F (rP + cnF) ts αS = .ok true) →
      Expr.WScoped (rP + cnF) side → side.looseBVarsBounded 0 = true →
      Expr.LeavesBounded side →
      CtxOk m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF) Γs side →
      denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF) side
        = some vside →
      HasType Δ
        (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vside)
        (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vα) := by
    intro side vside hty hws hb hL hC hden
    obtain ⟨ts, hinfs, hdes⟩ := hty
    obtain ⟨vs0, vts, hs0, htsden, htys⟩ := ihi hinfs hws hb hL hC
    rw [hden] at hs0
    rw [← Option.some.inj hs0] at htys
    have hwsts := inferTypeCore_WScoped m₀.wf F hinfs hws
    have hbts := inferTypeCore_looseBVars m₀.wf F hinfs hws hb hL
    have hLts : Expr.LeavesBounded ts := fun l hl =>
      hL l (inferTypeCore_fvarLeaves m₀.wf F hinfs hws l hl)
    have hCts := CtxOk.of_subset
      (inferTypeCore_fvarLeaves m₀.wf F hinfs hws) hC
    have hdeqs := ihd hdes hwsts hbts hLts hwsα hbα hLα hCts hCα
      htsden hαden
    have h1 := HasType.instCtx hcsZfull
      ((Deq.conv htys hdeqs).weakenTail Δ)
    rw [hzslen] at h1
    exact h1
  have hLty := hsideTy lhsS vL hlhsTyC hwsL hbL hLL hCL hLden
  have hRty := hsideTy rhsS vR hrhsTyC hwsR hbR hLR hCR hRden
  -- fire
  have hDeqLR : Deq Δ
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vL)
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vR) :=
    Deq.ofEqThmClosed m₀.eq_law heqfE
      (Level.substFn (Level.substFn φ lps us)
        eqA.toConstantVal.levelParams [ℓA])
      (args := xs.take rP ++ ys.drop cnP) hpv hfitEq
      (by
        rw [show Level.substFn (Level.substFn φ lps us)
          eqA.toConstantVal.levelParams [ℓA] uNT =
          Level.eval (Level.substFn φ lps us) ℓA from rfl]
        exact hAsort) hLty hRty
  -- ===== the reduct: β through the rule's λ-tower (§22) =====
  have hRVclosed : VExpr.Closed RV := denote_closed hcl hrhsw hrhsb hRV0
  have hzsel : ∀ q, q < rP + cnF →
      VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)
        (.bvar (rP + cnF - 1 - q)) =
        (xs.take rP ++ ys.drop cnP).getD q default := by
    intro q hq
    have h1 := hpadhit (rP + cnF) q (xs.take rP ++ ys.drop cnP) hq hzslen
      (Nat.le_refl _)
    rw [Nat.sub_self] at h1
    simpa using h1
  obtain ⟨Γβ, Cβ, hRVlam, hΓβlen, hCβden, hβdoms⟩ :=
    stripLams_denoteTele (cnP + cnF) hrhsAstrip hRV0
  -- the opened rule body is the field's opener (sealed)
  have hCβ : Cβ = .bvar (cnP + cnF - 1 - (cnP + i)) :=
    projBodyValue hilt hCβden
  -- the λ-domains are the constructor's: identify the contexts
  obtain ⟨Γc, Cc, hteleC, hΓclen, hCcden, hcdoms⟩ :=
    stripPis_denoteTele (cnP + cnF) hCstrip hTVj0
  obtain ⟨hΓcj, -⟩ := PiTele.det hteleC htowerJ
  have hΓβΓj : Γβ = Γj := by
    rw [← hΓcj]
    exact towerCtxEq (Expr.stripLams_length (cnP + cnF) hrhsAstrip)
      (Expr.stripPis_length (cnP + cnF) hCstrip) hΓβlen hΓclen
      hβdoms hcdoms hrdomsEq
  -- fire the β-spine at the fired arguments
  have hcsMix' : CtxSpine Δ Γj (xs.take rP ++ ys.drop cnP) := by
    rw [← hmixzs]
    exact hcsMix
  have hcsβ : CtxSpine Δ Γβ (xs.take rP ++ ys.drop cnP) := by
    rw [hΓβΓj]
    exact hcsMix'
  have hβspine := Deq.ofBetaSpine (hcsβ.betaSpine Cβ)
  rw [← hRVlam] at hβspine
  -- the field value on both readings (sealed)
  have hfld : VExpr.instSeq (xs.take rP ++ ys.drop cnP)
      ((xs.take rP ++ ys.drop cnP).length - 1) Cβ =
      ys.getD (cnP + i) default := by
    rw [hCβ]
    exact projFieldValue hcnPrP hilt (by omega) hlenY
  rw [hfld] at hβspine
  -- the right side is the field (sealed)
  have hvRfld : vR = .bvar (rP + cnF - 1 - (rP + i)) := by
    have hRden' : denote m₀.cval env₀ (Level.substFn φ lps us)
        (rP + cnF) (fvs.getD (rP + i) default) = some vR := by
      rw [← hrhsSpin]
      exact hRden
    exact projRhsValue hshapeS hfvslen hilt hRden'
  have hDeqRR : Deq Δ
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vR)
      (VExpr.mkAppN RV (xs.take rP ++ ys.drop cnP)) := by
    rw [hvRfld,
      hzsel (rP + i) (by omega), hzsget (rP + i) (by omega),
      if_neg (by omega),
      show cnP + (rP + i - rP) = cnP + i from by omega]
    exact hβspine.symm
  -- ===== Stage J: the left side, position by position =====
  have hlhsE : lhsS = Expr.mkAppN (.const (f Rn) (lps.map .param))
      lhsS.getAppArgs := by
    rw [← hlhead, Expr.mkAppN_getApp]
  rw [hlhsE] at hLden
  obtain ⟨vLf, vLargs, hvLf, hspL, hvLdecomp⟩ := denote_mkAppN_inv hLden
  have hvLflen : (lps.map Level.param).length =
      ciRm.toConstantVal.levelParams.length := by
    rw [List.length_map, hRmlps]
  rw [denote_const, hfRnE] at hvLf
  dsimp only at hvLf
  rw [if_pos hvLflen] at hvLf
  have hcvalRn : m₀.cval (f Rn) (Level.substFn (Level.substFn φ lps us)
      ciRm.toConstantVal.levelParams (lps.map Level.param)) =
      m₀.cval Rn (Level.substFn φ lps us) := by
    rw [hRmlps, show Level.substFn (Level.substFn φ lps us) lps
        (lps.map Level.param) = Level.substFn φ lps us from
      funext fun p => Level.substFn_map_param]
    exact hro.2.2 Rn _
  rw [hcvalRn] at hvLf
  obtain rfl : vLf = m₀.cval Rn (Level.substFn φ lps us) :=
    (Option.some.inj hvLf).symm
  have hvLargslen : vLargs.length = mI + 1 := by
    rw [hspL.length, hlarity]
  -- the pointwise correspondence, sealed
  have hpt := pointStageP m₀ hro hfCmE hCmlps hagree hctorE hplainLe
    hrPmI hmIrP hlenX hlenY hfvslen hvLargslen hlarity hlpre hmaj
    hshapeS hsplen hspIdx hzslen hzsget hzsel hpar hspL
  -- ===== the conclusion =====
  have hlen1 : (xs ++ [VExpr.mkAppN
      (m₀.cval ctor (Level.substFn φ cvj.levelParams usj)) ys]).length =
      (vLargs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
        (rP + cnF - 1))).length := by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map, hvLargslen, hlenX]
  have hstep1 := Deq.mkAppN
    (f := m₀.cval Rn (Level.substFn φ lps us))
    (g := m₀.cval Rn (Level.substFn φ lps us)) Deq.refl hlen1 hpt
  have hvL' : VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vL
      = VExpr.mkAppN (m₀.cval Rn (Level.substFn φ lps us))
        (vLargs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
          (rP + cnF - 1))) := by
    rw [hvLdecomp, VExpr.instSeq_mkAppN,
      VExpr.instSeq_eq_self_of_closed (hcl _ _)]
  rw [hvL'] at hDeqLR
  exact Deq.trans hstep1 (Deq.trans hDeqLR hDeqRR)

end Setlec.TTVerify
