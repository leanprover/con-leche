import Setlec.TTVerify.IndBottom
import Setlec.TTVerify.IotaStep

/-!
# `IndBottomPlainTT`: the plain modeled-iota bottom

The phase's largest obligation (`DESIGN.md` §16.1): a checked
`iota_j` theorem of a *canonical* rule, consumed as the fired
`RecRulesTT` law for that rule.  Transpose of `modeled_bottom_plain` —
in the **fired form**, which is why the public-frame λ-tower conjuncts
of `PlainChecked` (`hopenX`, `hlinst`, `hdeLam`) do not appear: the
law's right side is the rule's denoted rhs applied to the fired spine
directly, so nothing ever walks the λ-tower.

## How the hypotheses divide

* The **kit** conjuncts are `PlainChecked`'s, minus the λ-tower three
  and minus the theorem's `find?` (only its typing is read, §14.7.5) —
  the assembly destructures the kit and passes the pieces.
* `m₀ : EnvTT env₀` is the invariant **at the provisional
  environment** (rule-less recursors installed) — exactly as the model
  takes `EnvModel env₀`, supplied by the transpose of
  `provisionRecs_sound`.  Together with `hstep : CheckStepTT` (proved,
  `checkStepTT`) it turns the kit's install-time checker runs into
  claims.
* `hslot : IotaSlotSorted` is **the carried premise** named in advance
  by §16.1: the equation slot here is a motive application, so no
  syntactic pin serves its sort, and the anticipated supplier is
  form (2) of §14.7.4 (`checkIotaSidesTy` gains the slot's own sort
  check).  One hypothesis, one future swap.

## The proof's shape

Open the statement's telescope once
(`openPisAtFvars_denoteTele`); fit the fired spine
`xs.take rP ++ ys.drop cnP` into it sequentially, converting each
position's typing from the fire site's fittings along the install's
opened definitional equalities (`hopenDeqG` — claims + padding +
`Deq.instCtx`); fire the checked equation (`Deq.ofEqThmClosed`); then
identify the two sides with the law's redex and reduct position by
position — the indices through `IotaIndexPin` via the cross-frame
instantiation (`instPisAt_denote_cross`) and the spine congruence
(`CtxSpine.instSeq_congr`), the major through the parameter pin.
-/

set_option maxHeartbeats 3200000

namespace Setlec.TTVerify

open Setlec.TT

/-- **The plain bottom**: a checked canonical `iota_j` theorem, fired
as the stored rule's `RecRulesTT` law.  All statements are at the
provisional install environment `env₀`; the assembly transports the
law to the final environment (recursors with their rules swapped in),
exactly as the model's `SwapList` step does. -/
theorem IndBottomPlainTT
    {env₀ : Env} (m₀ : EnvTT env₀) {F : Nat} (hstep : CheckStepTT)
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
    (hrPmI : rP ≤ mI) (hplainLe : cnP ≤ rP)
    -- the rule's annotated right-hand side
    {rhsA : Expr} (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    {rhsTy : Expr} (hinfR : inferTypeCore env₀ F 0 rhsA = .ok rhsTy)
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
    (hCstrips : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop rP)
      (cvj.type.renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    (hdeIdx : DefEqListOk F env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP))
    {rdoms : List Expr} {rrest : Expr}
    (hrinst : Expr.instPisAt (fvs.take rP) (tyA.renameConsts f) =
      some (rdoms, rrest))
    (hdePre : DefEqListOk F env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListOk F env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    -- the kit (public prefix and constructor parameters)
    {fvsP : List Expr} {restP : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type =
      some (cdomsP, crestP))
    (hdePars : DefEqListOk F env₀ (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    -- the right side and both sides' typings
    (hdeRhs : isDefEqCore env₀ F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
    (hlhsTyC : ∃ tl, inferTypeCore env₀ F (rP + cnF) lhsS = .ok tl ∧
      isDefEqCore env₀ F (rP + cnF) tl αS = .ok true)
    (hrhsTyC : ∃ tr, inferTypeCore env₀ F (rP + cnF) rhsS = .ok tr ∧
      isDefEqCore env₀ F (rP + cnF) tr αS = .ok true)
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
  have hopenDeqG : ∀ (fvsF : List Expr) (ΓF : List VExpr) (mF : Nat),
      ΓF.length = mF →
      (∀ (i : Nat) (x : Expr), fvsF[i]? = some x →
        ∃ nm ty, x = Expr.fvar i nm ty) →
      (∀ x ∈ fvsF, Expr.WScoped (rP + cnF) x) →
      (∀ (i : Nat) (x : Expr), fvsF[i]? = some x →
        denote m₀.cval env₀ (Level.substFn φ lps us) i (Expr.fvarTypeD x)
          = some (ΓF.getD (mF - 1 - i) default)) →
      ∀ (a b : Expr) (n : Nat), n ≤ mF → mF ≤ rP + cnF →
      isDefEqCore env₀ F (rP + cnF) a b = .ok true →
      (∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsF) →
      (∀ l ∈ b.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsF) →
      Expr.WScoped n a → Expr.WScoped n b →
      a.looseBVarsBounded 0 = true → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a → Expr.LeavesBounded b →
      ∀ {va vb : VExpr},
        denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF) a
          = some va →
        denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF) b
          = some vb →
      ∀ {ws : List VExpr}, CtxSpine Δ (ΓF.drop (mF - n)) ws →
        Deq Δ
          (VExpr.instSeq (ws ++ List.replicate (rP + cnF - n) dummyPropT)
            ((ws ++ List.replicate (rP + cnF - n) dummyPropT).length - 1)
            va)
          (VExpr.instSeq (ws ++ List.replicate (rP + cnF - n) dummyPropT)
            ((ws ++ List.replicate (rP + cnF - n) dummyPropT).length - 1)
            vb) := by
    intro fvsF ΓF mF hΓFl hshapeF hwsF hdomsF a b n hn hmF hde hla hlb
      hwa hwb hba hbb hLa hLb va vb hva hvb ws hcs
    have hΔl : (List.replicate (rP + cnF - n) (VExpr.sort 0) ++
        ΓF.drop (mF - n)).length = rP + cnF := by
      simp only [List.length_append, List.length_replicate,
        List.length_drop, hΓFl]
      omega
    have hent : ∀ i, i < n →
        (List.replicate (rP + cnF - n) (VExpr.sort 0) ++
          ΓF.drop (mF - n))[rP + cnF - 1 - i]? =
        some (ΓF.getD (mF - 1 - i) default) := by
      intro i hi
      rw [List.getElem?_append_right
          (by rw [List.length_replicate]; omega),
        List.length_replicate, List.getElem?_drop,
        show mF - n + (rP + cnF - 1 - i - (rP + cnF - n)) =
          mF - 1 - i from by omega]
      simp only [List.getD]
      rw [List.getElem?_eq_getElem (show mF - 1 - i < ΓF.length from
        by omega)]
      rfl
    have hctx : ∀ (e : Expr),
        (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsF) →
        Expr.WScoped n e →
        CtxOk m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF)
          (List.replicate (rP + cnF - n) (VExpr.sort 0) ++
            ΓF.drop (mF - n)) e := by
      intro e hleaf hws
      exact ctxOk_of_openers hcl hΔl hshapeF hwsF hdomsF hleaf hws hent
    have hdeq := ihd hde (hwa.mono (by omega)) hba hLa
      (hwb.mono (by omega)) hbb hLb
      (hctx a hla hwa) (hctx b hlb hwb) hva hvb
    exact Deq.instCtx (hcs.pad (rP + cnF - n)) (Deq.weakenTail Δ hdeq)
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
    (openPisAtFvars_isSome_of_stripPis _ hCstrips 0)
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
  have hparBridge : ∀ j, j < cnP →
      Deq Δ
        (VExpr.instSeq (xs.take j) (j - 1) (ΓP.getD (rP - 1 - j) default))
        (VExpr.instSeq (xs.take j) (j - 1)
          (Γj.getD (cnP + cnF - 1 - j) default)) := by
    intro j hj
    -- the two sides of hdePars at position j
    have hjP : j < fvsP.length := by omega
    obtain ⟨nmP, tyP, hfvsPj⟩ := hshapeP j fvsP[j]
      (List.getElem?_eq_getElem hjP)
    have hjC : j < fvsC.length := by omega
    obtain ⟨nmC, tyC, hfvsCj⟩ := hshapeC j fvsC[j]
      (List.getElem?_eq_getElem hjC)
    have haP : ((fvsP.take cnP).map Expr.fvarTypeD)[j]? = some tyP := by
      rw [List.getElem?_map, List.getElem?_take_of_lt hj,
        List.getElem?_eq_getElem hjP, hfvsPj]
      rfl
    have hbP : cdomsP[j]? = some (cdomsP.getD j default) := by
      simp [List.getD, List.getElem?_eq_getElem
        (show j < cdomsP.length from by omega)]
    have hde := DefEqListOk.pointwise hdePars j haP hbP
    -- the two sides' denotes at the frame depth
    have hwtyP : Expr.WScoped j tyP := by
      have h1 := hwsFvsP fvsP[j] (List.getElem_mem hjP)
      rw [hfvsPj] at h1
      exact ((by simpa [Expr.WScoped] using h1) :
        j < rP ∧ Expr.WScoped j tyP).2
    have hvaden : denote m₀.cval env₀ (Level.substFn φ lps us)
        (rP + cnF) tyP =
        some ((ΓP.getD (rP - 1 - j) default).liftN (rP + cnF - j)) := by
      have h1 := hdomsP0' j fvsP[j] (List.getElem?_eq_getElem hjP)
      rw [hfvsPj] at h1
      rw [show Expr.fvarTypeD (Expr.fvar j nmP tyP) = tyP from rfl] at h1
      rw [denote_lift hcl hwtyP.fvarsBelow (rP + cnF) (by omega), h1]
      rfl
    -- the constructor side: its parameter domain is the C-opening's
    have hwcdP : Expr.WScoped j (cdomsP.getD j default) := by
      have h1 := instPisAt_index_WScoped (d := 0) (fvsP.take cnP) hcinstP
        (Expr.WScoped.of_not_hasFvar hCw) ?_ j (cdomsP.getD j default) hbP
      · simpa using h1
      · intro i a ha
        have hia : i < cnP := by
          rcases Nat.lt_or_ge i cnP with h | h
          · exact h
          · rw [List.getElem?_eq_none (by
              rw [List.length_take]; omega)] at ha
            exact nomatch ha
        rw [List.getElem?_take_of_lt hia] at ha
        obtain ⟨nm1, ty1, rfl⟩ := hshapeP i a ha
        have h2 := hwsFvsP (Expr.fvar i nm1 ty1) (List.mem_of_getElem? ha)
        have h3 : i < rP ∧ Expr.WScoped i ty1 := by
          simpa [Expr.WScoped] using h2
        show Expr.WScoped (0 + i + 1) (Expr.fvar i nm1 ty1)
        simp only [Expr.WScoped]
        exact ⟨by omega, h3.2⟩
    have hvbden : denote m₀.cval env₀ (Level.substFn φ lps us)
        (rP + cnF) (cdomsP.getD j default) =
        some ((Γj.getD (cnP + cnF - 1 - j) default).liftN
          (rP + cnF - j)) := by
      have hee := hPCdoms j tyC (cdomsP.getD j default)
        (by rw [List.getElem?_take_of_lt hj, List.getElem?_map,
          List.getElem?_eq_getElem hjC, hfvsCj]; rfl) hbP
      have h1 := hdomsJ0' j fvsC[j] (List.getElem?_eq_getElem hjC)
      rw [hfvsCj] at h1
      rw [show Expr.fvarTypeD (Expr.fvar j nmC tyC) = tyC from rfl] at h1
      rw [denote_lift hcl hwcdP.fvarsBelow (rP + cnF) (by omega),
        ← denote_erasedEq hee j, h1]
      rfl
    -- leaves
    have hlaP : ∀ l ∈ tyP.fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP := by
      intro l hl
      refine hleafP l ⟨fvsP[j], List.getElem_mem hjP, ?_⟩
      rw [hfvsPj, Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl
    have hlbP : ∀ l ∈ (cdomsP.getD j default).fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP := by
      intro l hl
      rcases instPisAt_leaves _ hcinstP l
          (Or.inl ⟨cdomsP.getD j default,
            List.mem_of_getElem? hbP, hl⟩) with h1 | ⟨a, ha, hla⟩
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCw] at h1
        exact nomatch h1
      · exact hleafP l ⟨a, List.mem_of_mem_take ha, hla⟩
    -- bounds
    have hbaP : tyP.looseBVarsBounded 0 = true := by
      have h1 := hbAnnsP fvsP[j] (List.getElem_mem hjP)
      rw [hfvsPj] at h1
      exact h1
    have hspBounded : ∀ a ∈ fvsP.take cnP, a.looseBVarsBounded 0 = true := by
      intro a ha
      obtain ⟨q, hq⟩ := List.getElem?_of_mem (List.mem_of_mem_take ha)
      obtain ⟨nm1, ty1, rfl⟩ := hshapeP q a hq
      rfl
    have hbbP : (cdomsP.getD j default).looseBVarsBounded 0 = true := by
      obtain ⟨h1, -⟩ := instPisAt_bounded (fvsP.take cnP) hcinstP hCb
        hspBounded
      exact h1 _ (List.mem_of_getElem? hbP)
    have hgen := hopenDeqG fvsP ΓP rP hΓPlen hshapeP hwsFvsP' hdomsP0'
      tyP (cdomsP.getD j default) j (by omega) (by omega) hde
      hlaP hlbP hwtyP hwcdP hbaP hbbP (hLBP _ hlaP) (hLBP _ hlbP)
      hvaden hvbden (hcsRpre j (by omega))
    have hlen1 : (xs.take j).length = j := by
      rw [List.length_take]
      omega
    have habs1 := instSeq_append_absorb (xs.take j)
      (List.replicate (rP + cnF - j) dummyPropT)
      (ΓP.getD (rP - 1 - j) default)
    have habs2 := instSeq_append_absorb (xs.take j)
      (List.replicate (rP + cnF - j) dummyPropT)
      (Γj.getD (cnP + cnF - 1 - j) default)
    rw [hlen1, List.length_replicate,
      show j + (rP + cnF - j) - 1 = rP + cnF - 1 from by omega]
      at habs1 habs2
    rw [List.length_append, hlen1, List.length_replicate,
      show j + (rP + cnF - j) - 1 = rP + cnF - 1 from by omega,
      habs1, habs2] at hgen
    exact hgen
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
  -- the recursor's opened domains, across the renaming
  have hPinstAll : Expr.instPisAt fvsP tyA =
      some (fvsP.map Expr.fvarTypeD, restP) :=
    openPisAtFvars_instPisAt _ hopenP
  have hrdomslen : rdoms.length = rP := by
    have h1 := DefEqListOk.length hdePre
    rw [List.length_map, List.length_take, hfvslen] at h1
    omega
  have hPRdoms : ∀ (j : Nat) (x x' : Expr),
      (fvsP.map Expr.fvarTypeD)[j]? = some x →
      rdoms[j]? = some x' → RenEqT f x x' := by
    intro j x x' hx hx'
    have hargsPR : ∀ (i : Nat) (a a' : Expr), fvsP[i]? = some a →
        (fvs.take rP)[i]? = some a' → RenEqT f a a' := by
      intro i a a' ha ha'
      have hia : i < rP := by
        rcases Nat.lt_or_ge i rP with h | h
        · exact h
        · rw [List.getElem?_eq_none (by rw [hfvsPlen]; omega)] at ha
          exact nomatch ha
      rw [List.getElem?_take_of_lt hia] at ha'
      obtain ⟨nm1, ty1, rfl⟩ := hshapeP i a ha
      obtain ⟨nm2, ty2, rfl⟩ := hshapeS i a' ha'
      exact RenEqT.fvar
    obtain ⟨hds, -⟩ := instPisAt_renEq fvsP (fvs.take rP)
      hPinstAll hrinst
      (show Expr.ErasedEq (tyA.renameConsts f) (tyA.renameConsts f) from
        Expr.ErasedEq.rfl _) hargsPR
      (by rw [hfvsPlen, List.length_take, hfvslen]; omega)
    exact hds j x x' hx hx'
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
  have hcdomslen : cdoms.length = cnP + cnF := by
    have h1 := instPisAt_length _ hcinst
    rw [hsplen] at h1
    exact h1
  -- ===== Stage G: the statement fitting (the zipper) =====
  have htowerS' : PiTele (xs.take rP ++ ys.drop cnP).length Tstmt Γs
      Rbody := by
    rw [hzslen]
    exact htowerS
  have hzip : VTeleTyped Δ Tstmt (xs.take rP ++ ys.drop cnP)
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
        ((xs.take rP ++ ys.drop cnP).length - 1) Rbody) := by
    refine VTeleTyped.ofPiTele htowerS' ?_
    intro n hn hpref
    rw [hzslen] at hn
    obtain ⟨mid, hmid⟩ := hpref
    obtain ⟨midS2, hpreS, -⟩ := PiTele.prefix htowerS n (by omega)
    have hztklen : ((xs.take rP ++ ys.drop cnP).take n).length = n := by
      rw [List.length_take, hzslen]
      omega
    have hcsZ : CtxSpine Δ (Γs.drop (rP + cnF - n))
        ((xs.take rP ++ ys.drop cnP).take n) := by
      refine hmid.toCtxSpine (Γ := Γs.drop (rP + cnF - n))
        (R := midS2) ?_
      rw [hztklen]
      exact hpreS
    -- the statement's n-th annotation
    have hnfvs : n < fvs.length := by omega
    obtain ⟨nmS, tyS, hfvsn⟩ := hshapeS n fvs[n]
      (List.getElem?_eq_getElem hnfvs)
    have hwtyS : Expr.WScoped n tyS := by
      have h1 := hwsFvs fvs[n] (List.getElem_mem hnfvs)
      rw [hfvsn] at h1
      exact ((by simpa [Expr.WScoped] using h1) :
        n < rP + cnF ∧ Expr.WScoped n tyS).2
    have hvaden : denote m₀.cval env₀ (Level.substFn φ lps us)
        (rP + cnF) tyS =
        some ((Γs.getD (rP + cnF - 1 - n) default).liftN
          (rP + cnF - n)) := by
      have h1 := hdomsS0' n fvs[n] (List.getElem?_eq_getElem hnfvs)
      rw [hfvsn] at h1
      rw [show Expr.fvarTypeD (Expr.fvar n nmS tyS) = tyS from rfl] at h1
      rw [denote_lift hcl hwtyS.fvarsBelow (rP + cnF) (by omega), h1]
      rfl
    have hlaS : ∀ l ∈ tyS.fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
      intro l hl
      refine hleafS l (Or.inr ⟨fvs[n], List.getElem_mem hnfvs, ?_⟩)
      rw [hfvsn, Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl
    have hbaS : tyS.looseBVarsBounded 0 = true := by
      have h1 := hbAnns fvs[n] (List.getElem_mem hnfvs)
      rw [hfvsn] at h1
      exact h1
    by_cases hnrP : n < rP
    · -- a parameter/motive/minor position: the recursor's fitting,
      -- converted along the opened-domain agreement
      have haS : ((fvs.take rP).map Expr.fvarTypeD)[n]? = some tyS := by
        rw [List.getElem?_map, List.getElem?_take_of_lt hnrP,
          List.getElem?_eq_getElem hnfvs, hfvsn]
        rfl
      have hbS : rdoms[n]? = some (rdoms.getD n default) := by
        simp [List.getD, List.getElem?_eq_getElem
          (show n < rdoms.length from by omega)]
      have hde := DefEqListOk.pointwise hdePre n haS hbS
      -- the renamed recursor domain denotes to the P-tower's entry
      have hwrd : Expr.WScoped n (rdoms.getD n default) := by
        have h1 := instPisAt_index_WScoped (d := 0) (fvs.take rP) hrinst
          (Expr.WScoped.of_not_hasFvar (by
            rw [hasFvar_renameConsts]
            exact htyw)) ?_ n (rdoms.getD n default) hbS
        · simpa using h1
        · intro i a ha
          have hia : i < rP := by
            rcases Nat.lt_or_ge i rP with h | h
            · exact h
            · rw [List.getElem?_eq_none (by
                rw [List.length_take, hfvslen]; omega)] at ha
              exact nomatch ha
          rw [List.getElem?_take_of_lt hia] at ha
          obtain ⟨nm1, ty1, rfl⟩ := hshapeS i a ha
          have h2 := hwsFvs (Expr.fvar i nm1 ty1) (List.mem_of_getElem? ha)
          have h3 : i < rP + cnF ∧ Expr.WScoped i ty1 := by
            simpa [Expr.WScoped] using h2
          show Expr.WScoped (0 + i + 1) (Expr.fvar i nm1 ty1)
          simp only [Expr.WScoped]
          exact ⟨by omega, h3.2⟩
      have hvbden : denote m₀.cval env₀ (Level.substFn φ lps us)
          (rP + cnF) (rdoms.getD n default) =
          some ((ΓP.getD (rP - 1 - n) default).liftN
            (rP + cnF - n)) := by
        have hjP : n < fvsP.length := by omega
        obtain ⟨nmP, tyP, hfvsPn⟩ := hshapeP n fvsP[n]
          (List.getElem?_eq_getElem hjP)
        have hre := hPRdoms n tyP (rdoms.getD n default)
          (by rw [List.getElem?_map, List.getElem?_eq_getElem hjP,
            hfvsPn]; rfl) hbS
        have h1 := hdomsP0' n fvsP[n] (List.getElem?_eq_getElem hjP)
        rw [hfvsPn] at h1
        rw [show Expr.fvarTypeD (Expr.fvar n nmP tyP) = tyP from rfl] at h1
        rw [denote_lift hcl hwrd.fvarsBelow (rP + cnF) (by omega),
          RenEqT.denote hro hre n, h1]
        rfl
      have hlbS : ∀ l ∈ (rdoms.getD n default).fvarLeaves,
          Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
        intro l hl
        rcases instPisAt_leaves _ hrinst l
            (Or.inl ⟨rdoms.getD n default,
              List.mem_of_getElem? hbS, hl⟩) with h1 | ⟨a, ha, hla⟩
        · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
            rw [hasFvar_renameConsts]; exact htyw)] at h1
          exact nomatch h1
        · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_take ha, hla⟩)
      have hbbS : (rdoms.getD n default).looseBVarsBounded 0 = true := by
        have hspb : ∀ a ∈ fvs.take rP, a.looseBVarsBounded 0 = true := by
          intro a ha
          obtain ⟨q, hq⟩ := List.getElem?_of_mem (List.mem_of_mem_take ha)
          obtain ⟨nm1, ty1, rfl⟩ := hshapeS q a hq
          rfl
        obtain ⟨h1, -⟩ := instPisAt_bounded (fvs.take rP) hrinst
          (by rw [Expr.looseBVarsBounded_renameConsts]; exact htyb) hspb
        exact h1 _ (List.mem_of_getElem? hbS)
      have hgen := hopenDeqG fvs Γs (rP + cnF) hΓslen hshapeS hwsFvs
        hdomsS0' tyS (rdoms.getD n default) n (by omega) (by omega) hde
        hlaS hlbS hwtyS hwrd hbaS hbbS (hLB _ hlaS) (hLB _ hlbS)
        hvaden hvbden hcsZ
      have habs1 := instSeq_append_absorb
        ((xs.take rP ++ ys.drop cnP).take n)
        (List.replicate (rP + cnF - n) dummyPropT)
        (Γs.getD (rP + cnF - 1 - n) default)
      have habs2 := instSeq_append_absorb
        ((xs.take rP ++ ys.drop cnP).take n)
        (List.replicate (rP + cnF - n) dummyPropT)
        (ΓP.getD (rP - 1 - n) default)
      rw [hztklen, List.length_replicate,
        show n + (rP + cnF - n) - 1 = rP + cnF - 1 from by omega]
        at habs1 habs2
      rw [List.length_append, hztklen, List.length_replicate,
        show n + (rP + cnF - n) - 1 = rP + cnF - 1 from by omega,
        habs1, habs2] at hgen
      -- the source typing, from the recursor's own fitting
      have hsrc := hstepsR n (by rw [hxstakelen]; omega)
      rw [hxstakelen, List.take_take, Nat.min_eq_left (by omega : n ≤ rP),
        show (xs.take rP).getD n default = xs.getD n default from by
          simp only [List.getD]
          rw [List.getElem?_take_of_lt hnrP]] at hsrc
      rw [show (xs.take rP ++ ys.drop cnP).getD n default =
          xs.getD n default from by
        rw [hzsget n (by omega), if_pos hnrP],
        show (xs.take rP ++ ys.drop cnP).length - 1 - n =
          rP + cnF - 1 - n from by rw [hzslen],
        hzstake n (by omega)]
      rw [hzstake n (by omega)] at hgen
      exact Deq.conv hsrc (Deq.symm hgen)
    · -- a field position: the mixed constructor fitting, converted
      -- through the scattered install run
      have hnnrP : rP ≤ n := by omega
      have hXlt : cnP + (n - rP) < cnP + cnF := by omega
      -- the install fact at this field
      have haF : ((fvs.drop rP).map Expr.fvarTypeD)[n - rP]? =
          some tyS := by
        rw [List.getElem?_map, List.getElem?_drop,
          show rP + (n - rP) = n from by omega,
          List.getElem?_eq_getElem hnfvs, hfvsn]
        rfl
      have hbF : (cdoms.drop cnP)[n - rP]? =
          some (cdoms.getD (cnP + (n - rP)) default) := by
        rw [List.getElem?_drop]
        simp [List.getD, List.getElem?_eq_getElem
          (show cnP + (n - rP) < cdoms.length from by omega)]
      have hde := DefEqListOk.pointwise hdeFld (n - rP) haF hbF
      -- the truncated scattered run and the field's domain
      obtain ⟨midE, htakeE, hdropE⟩ :=
        instPisAt_take (fvs.take cnP ++ fvs.drop rP)
          (cnP + (n - rP)) hcinst
      rw [List.drop_eq_getElem_cons (by rw [hsplen]; omega)] at hdropE
      match hmidE : midE, hdropE with
      | .forallE nmE domE bodyE mbE, hdropE => ?_
      simp only [Expr.instPisAt] at hdropE
      cases h1 : Expr.instPisAt
          ((fvs.take cnP ++ fvs.drop rP).drop (cnP + (n - rP) + 1))
          (bodyE.instantiate1
            (fvs.take cnP ++ fvs.drop rP)[cnP + (n - rP)]) with
      | none => rw [h1] at hdropE; exact nomatch hdropE
      | some pE => ?_
      rw [h1] at hdropE
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        at hdropE
      have hdomE' : cdoms.getD (cnP + (n - rP)) default = domE := by
        have h2 : (cdoms.drop (cnP + (n - rP)))[0]? = some domE := by
          rw [← hdropE.1]
          rfl
        rw [List.getElem?_drop, Nat.add_zero] at h2
        simp [List.getD, h2]
      rw [hdomE'] at hde
      -- the spine of the truncated run, scoped at n
      have hspTakeFacts : ∀ (q : Nat) (x : Expr),
          ((fvs.take cnP ++ fvs.drop rP).take (cnP + (n - rP)))[q]? =
            some x →
          (∃ i nm t, x = Expr.fvar i nm t) ∧
            Expr.WScoped (rP + cnF) x ∧
            x.looseBVarsBounded 0 = true := by
        intro q x hx
        have hq : q < cnP + (n - rP) := by
          rcases Nat.lt_or_ge q (cnP + (n - rP)) with h | h
          · exact h
          · rw [List.getElem?_eq_none (by
              rw [List.length_take, hsplen]; omega)] at hx
            exact nomatch hx
        rw [List.getElem?_take_of_lt hq] at hx
        exact hspFacts q x hx
      have hspTakeWSn : ∀ a ∈ (fvs.take cnP ++ fvs.drop rP).take
          (cnP + (n - rP)), Expr.WScoped n a := by
        intro a ha
        obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
        have hqlt : q < cnP + (n - rP) := by
          rcases Nat.lt_or_ge q (cnP + (n - rP)) with h | h
          · exact h
          · rw [List.getElem?_eq_none (by
              rw [List.length_take, hsplen]; omega)] at hq
            exact nomatch hq
        rw [List.getElem?_take_of_lt hqlt] at hq
        obtain ⟨⟨i0, nm0, t0, rfl⟩, hwsK, -⟩ := hspFacts q a hq
        obtain ⟨nm1, t1, hq1⟩ := hspIdx q (by omega)
        have heq := Option.some.inj (hq.symm.trans hq1)
        injection heq with heqi heqn heqt
        have hidx : i0 < n := by
          rw [heqi]
          by_cases hqc : q < cnP
          · rw [if_pos hqc]
            omega
          · rw [if_neg hqc]
            omega
        have hK : i0 < rP + cnF ∧ Expr.WScoped i0 t0 := by
          simpa [Expr.WScoped] using hwsK
        simp only [Expr.WScoped]
        exact ⟨hidx, hK.2⟩
      -- the field domain's own facts
      have hdomEmem : cdoms.getD (cnP + (n - rP)) default ∈ cdoms := by
        refine List.mem_of_getElem? (i := cnP + (n - rP)) ?_
        simp [List.getD, List.getElem?_eq_getElem
          (show cnP + (n - rP) < cdoms.length from by omega)]
      have hwdomE : Expr.WScoped n domE := by
        obtain ⟨-, hmidW⟩ := instPisAt_WScoped (d := n)
          ((fvs.take cnP ++ fvs.drop rP).take (cnP + (n - rP)))
          (cvj.type.renameConsts f) htakeE
          (Expr.WScoped.of_not_hasFvar (by
            rw [hasFvar_renameConsts]
            exact hCw))
          hspTakeWSn
        exact ((by simpa [Expr.WScoped] using hmidW) :
          Expr.WScoped n domE ∧ Expr.WScoped n bodyE).1
      have hlbF : ∀ l ∈ domE.fvarLeaves,
          Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
        intro l hl
        rw [← hdomE'] at hl
        rcases instPisAt_leaves _ hcinst l
            (Or.inl ⟨cdoms.getD (cnP + (n - rP)) default, hdomEmem, hl⟩)
          with h1 | ⟨a, ha, hla⟩
        · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
            rw [hasFvar_renameConsts]; exact hCw)] at h1
          exact nomatch h1
        · rcases List.mem_append.mp ha with ha' | ha'
          · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_take ha', hla⟩)
          · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_drop ha', hla⟩)
      have hbbF : domE.looseBVarsBounded 0 = true := by
        have hspb : ∀ a ∈ fvs.take cnP ++ fvs.drop rP,
            a.looseBVarsBounded 0 = true := by
          intro a ha
          obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
          exact (hspFacts q a hq).2.2
        obtain ⟨h1, -⟩ := instPisAt_bounded _ hcinst
          (by rw [Expr.looseBVarsBounded_renameConsts]; exact hCb) hspb
        rw [← hdomE']
        exact h1 _ hdomEmem
      -- the truncated run's residual denotes at the frame
      have hTVjK : denote m₀.cval env₀ (Level.substFn φ lps us)
          (rP + cnF) (cvj.type.renameConsts f) = some TVj := by
        rw [denote_renameConsts hro,
          denote_depth_closed hcl hCw hCb (rP + cnF)]
        exact hTVj0
      obtain ⟨vMidE, hvMidE⟩ := instPisAt_fvar_denote_defined hcl _
        htakeE (fun q x hx => by
          obtain ⟨⟨i0, nm0, t0, rfl⟩, hw1, hb1⟩ := hspTakeFacts q x hx
          exact ⟨⟨VExpr.bvar (rP + cnF - 1 - i0), by rw [denote_fvar]⟩,
            hw1, hb1⟩)
        ((Expr.WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]; exact hCw)
          (d := rP + cnF)).fvarsBelow)
        (by rw [Expr.looseBVarsBounded_renameConsts]; exact hCb)
        hTVjK
      rw [denote_forallE] at hvMidE
      cases hAE : denote m₀.cval env₀ (Level.substFn φ lps us)
          (rP + cnF) domE with
      | none => rw [hAE] at hvMidE; exact nomatch hvMidE
      | some AE => ?_
      rw [hAE] at hvMidE
      cases hBE : denote m₀.cval env₀ (Level.substFn φ lps us)
          (rP + cnF + 1) (bodyE.instantiate1
            (.fvar (rP + cnF) nmE domE)) with
      | none => rw [hBE] at hvMidE; exact nomatch hvMidE
      | some BE => ?_
      rw [hBE] at hvMidE
      obtain rfl : vMidE = .pi AE BE := (Option.some.inj hvMidE).symm
      -- the workhorse: the statement's field domain against the run's
      have hgen := hopenDeqG fvs Γs (rP + cnF) hΓslen hshapeS hwsFvs
        hdomsS0' tyS domE n (by omega) (by omega) (hdomE' ▸ hde)
        hlaS hlbF hwtyS hwdomE hbaS hbbF (hLB _ hlaS) (hLB _ hlbF)
        hvaden hAE hcsZ
      have habsL := instSeq_append_absorb
        ((xs.take rP ++ ys.drop cnP).take n)
        (List.replicate (rP + cnF - n) dummyPropT)
        (Γs.getD (rP + cnF - 1 - n) default)
      rw [hztklen, List.length_replicate,
        show n + (rP + cnF - n) - 1 = rP + cnF - 1 from by omega]
        at habsL
      rw [List.length_append, hztklen, List.length_replicate,
        show n + (rP + cnF - n) - 1 = rP + cnF - 1 from by omega,
        habsL] at hgen
      -- the cross-frame identification
      have hvalslen : (((xs.take rP ++ ys.drop cnP).take n) ++
          List.replicate (rP + cnF - n) dummyPropT).length = rP + cnF := by
        simp only [List.length_append, List.length_replicate, hztklen]
        omega
      obtain ⟨midJ, hpreJ1, hpreJ2⟩ := PiTele.prefix htowerJ
        (cnP + (n - rP)) (by omega)
      have hTVjClosed : VExpr.Closed TVj :=
        denote_closed hcl hCw hCb hTVj0
      have hsptklen : ((fvs.take cnP ++ fvs.drop rP).take
          (cnP + (n - rP))).length = cnP + (n - rP) := by
        rw [List.length_take, hsplen]
        omega
      have htowerX : PiTele ((fvs.take cnP ++ fvs.drop rP).take
          (cnP + (n - rP))).length
          (VExpr.instSeq ((xs.take rP ++ ys.drop cnP).take n ++
            List.replicate (rP + cnF - n) dummyPropT) (rP + cnF - 1) TVj)
          (Γj.drop (cnP + cnF - (cnP + (n - rP)))) midJ := by
        rw [VExpr.instSeq_eq_self_of_closed hTVjClosed, hsptklen]
        exact hpreJ1
      have hwsXlen : ((xs.take cnP ++ ys.drop cnP).take
          (cnP + (n - rP))).length =
          ((fvs.take cnP ++ fvs.drop rP).take (cnP + (n - rP))).length := by
        rw [hsptklen, List.length_take, hmixlen]
        omega
      have hwsCond : ∀ (q i0 : Nat) (nm0 : Name) (t0 : Expr),
          ((fvs.take cnP ++ fvs.drop rP).take (cnP + (n - rP)))[q]? =
            some (Expr.fvar i0 nm0 t0) →
          ((xs.take cnP ++ ys.drop cnP).take (cnP + (n - rP)))[q]? =
            some (VExpr.instSeq ((xs.take rP ++ ys.drop cnP).take n ++
              List.replicate (rP + cnF - n) dummyPropT) (rP + cnF - 1)
              (.bvar (rP + cnF - 1 - i0))) := by
        intro q i0 nm0 t0 hq
        have hqlt : q < cnP + (n - rP) := by
          rcases Nat.lt_or_ge q (cnP + (n - rP)) with h | h
          · exact h
          · rw [List.getElem?_eq_none (by
              rw [List.length_take, hsplen]; omega)] at hq
            exact nomatch hq
        rw [List.getElem?_take_of_lt hqlt] at hq
        obtain ⟨nm1, t1, hq1⟩ := hspIdx q (by omega)
        have heq := Option.some.inj (hq.symm.trans hq1)
        injection heq with heqi heqn heqt
        have hi0n : i0 < n := by
          rw [heqi]
          by_cases hqc : q < cnP
          · rw [if_pos hqc]
            omega
          · rw [if_neg hqc]
            omega
        rw [List.getElem?_take_of_lt hqlt,
          hpadhit n i0 ((xs.take rP ++ ys.drop cnP).take n) hi0n hztklen
            (by omega)]
        have hqm : q < cnP + cnF := by omega
        rw [List.getElem?_eq_getElem (show q < (xs.take cnP ++
          ys.drop cnP).length from by rw [hmixlen]; omega)]
        have hmixq : (xs.take cnP ++ ys.drop cnP)[q] =
            (xs.take cnP ++ ys.drop cnP).getD q default := by
          simp [List.getD, List.getElem?_eq_getElem
            (show q < (xs.take cnP ++ ys.drop cnP).length from by
              rw [hmixlen]; omega)]
        rw [hmixq, hmixget q hqm]
        -- align the selected value with the frame's
        have hzi0 : ((xs.take rP ++ ys.drop cnP).take n).getD i0 default =
            (xs.take rP ++ ys.drop cnP).getD i0 default := by
          simp only [List.getD]
          rw [List.getElem?_take_of_lt hi0n]
        rw [hzi0, hzsget i0 (by omega)]
        by_cases hqc : q < cnP
        · rw [if_pos hqc,
            show i0 = q from by rw [heqi, if_pos hqc],
            if_pos (show q < rP from by omega)]
        · rw [if_neg hqc,
            show i0 = rP + (q - cnP) from by rw [heqi, if_neg hqc],
            if_neg (show ¬ rP + (q - cnP) < rP from by omega),
            show cnP + (rP + (q - cnP) - rP) = q from by omega]
      have hvMidE2 : denote m₀.cval env₀ (Level.substFn φ lps us)
          (rP + cnF) (Expr.forallE nmE domE bodyE mbE) =
          some (.pi AE BE) := by
        rw [denote_forallE, hAE, hBE]
      have hcross := instPisAt_denote_cross hcl
        ((fvs.take cnP ++ fvs.drop rP).take (cnP + (n - rP))) htakeE
        hvalslen (fun j x hx => (hspTakeFacts j x hx).2)
        ((Expr.WScoped.of_not_hasFvar (d := rP + cnF) (by
          rw [hasFvar_renameConsts]; exact hCw)).fvarsBelow)
        (by rw [Expr.looseBVarsBounded_renameConsts]; exact hCb)
        hTVjK hvMidE2 hwsXlen
        (fun j x hx => by
          obtain ⟨⟨i, nm, t, rfl⟩, -, -⟩ := hspTakeFacts j x hx
          exact ⟨VExpr.bvar (rP + cnF - 1 - i), by rw [denote_fvar],
            hwsCond j i nm t hx⟩)
        htowerX
      -- read the head domain off both sides
      rw [VExpr.instSeq_pi _ _ _ _ (by rw [hvalslen]; omega)] at hcross
      obtain ⟨SJ, hSJ⟩ : ∃ SJ, cnP + cnF - (cnP + (n - rP)) = SJ + 1 :=
        ⟨cnP + cnF - (cnP + (n - rP)) - 1, by omega⟩
      rw [hSJ] at hpreJ2
      obtain ⟨BJ, hmidJpi, -⟩ := hpreJ2.head
      rw [hmidJpi, VExpr.instSeq_pi _ _ _ _ (by
        rw [hwsXlen, hsptklen]; omega)] at hcross
      obtain ⟨hh1, -⟩ := (VExpr.pi.injEq _ _ _ _).mp hcross
      have hentry : (Γj.take (SJ + 1)).getD SJ default =
          Γj.getD SJ default := by
        simp only [List.getD]
        rw [List.getElem?_take_of_lt (by omega)]
      rw [hentry,
        show ((xs.take cnP ++ ys.drop cnP).take (cnP + (n - rP))).length
          = cnP + (n - rP) from by rw [List.length_take, hmixlen]; omega]
        at hh1
      rw [hh1] at hgen
      -- the source typing from the mixed fitting
      have hsrc := hstepsMix (cnP + (n - rP)) (by rw [hmixlen]; omega)
      rw [show (xs.take cnP ++ ys.drop cnP).length - 1 - (cnP + (n - rP))
          = SJ from by rw [hmixlen]; omega,
        show (xs.take cnP ++ ys.drop cnP).getD (cnP + (n - rP)) default
          = ys.getD (cnP + (n - rP)) default from by
          rw [hmixget _ (by omega), if_neg (by omega)]] at hsrc
      -- align the goal and close
      rw [show (xs.take rP ++ ys.drop cnP).getD n default =
          ys.getD (cnP + (n - rP)) default from by
        rw [hzsget n (by omega), if_neg (by omega)],
        show (xs.take rP ++ ys.drop cnP).length - 1 - n =
          rP + cnF - 1 - n from by rw [hzslen]]
      exact Deq.conv hsrc (Deq.symm hgen)
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
      (∃ ts, inferTypeCore env₀ F (rP + cnF) side = .ok ts ∧
        isDefEqCore env₀ F (rP + cnF) ts αS = .ok true) →
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
  -- ===== Stage I: the right side is the rule's own application =====
  have hRVclosed : VExpr.Closed RV := denote_closed hcl hrhsw hrhsb hRV0
  have hRVKren : denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF)
      (rhsA.renameConsts f) = some RV := by
    rw [denote_renameConsts hro,
      denote_depth_closed hcl hrhsw hrhsb (rP + cnF)]
    exact hRV0
  have hfvsden : DenoteSpine m₀.cval env₀ (Level.substFn φ lps us)
      (rP + cnF) fvs ((List.range (rP + cnF)).map
        (fun q => VExpr.bvar (rP + cnF - 1 - q))) := by
    refine DenoteSpine.of_getElem
      (by rw [hfvslen, List.length_map, List.length_range]) ?_
    intro q hq
    rw [hfvslen] at hq
    obtain ⟨nm, t, hsh⟩ := hshapeS q fvs[q]
      (List.getElem?_eq_getElem (by omega))
    rw [show fvs.getD q default = fvs[q] from by
        simp [List.getD, List.getElem?_eq_getElem
          (show q < fvs.length from by omega)],
      hsh, denote_fvar,
      show ((List.range (rP + cnF)).map
        (fun q => VExpr.bvar (rP + cnF - 1 - q))).getD q default =
        VExpr.bvar (rP + cnF - 1 - q) from by
        simp [List.getD, List.getElem?_map, List.getElem?_range hq]]
  have happden : denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF)
      (Expr.mkAppN (rhsA.renameConsts f) fvs) =
      some (VExpr.mkAppN RV ((List.range (rP + cnF)).map
        (fun q => VExpr.bvar (rP + cnF - 1 - q)))) :=
    denote_mkAppN hfvsden hRVKren
  have hwsApp : Expr.WScoped (rP + cnF)
      (Expr.mkAppN (rhsA.renameConsts f) fvs) :=
    Expr.WScoped.mkAppN
      (Expr.WScoped.of_not_hasFvar (by
        rw [hasFvar_renameConsts]; exact hrhsw)) hwsFvs
  have hbApp : (Expr.mkAppN (rhsA.renameConsts f)
      fvs).looseBVarsBounded 0 = true := by
    refine looseBVarsBounded_mkAppN ?_ ?_
    · rw [Expr.looseBVarsBounded_renameConsts]
      exact hrhsb
    · intro x hx
      obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
      obtain ⟨nm, t, rfl⟩ := hshapeS q x hq
      rfl
  have hlfApp : ∀ l ∈ (Expr.mkAppN (rhsA.renameConsts f) fvs).fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
    intro l hl
    rcases fvarLeaves_mkAppN hl with h1 | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
        rw [hasFvar_renameConsts]; exact hrhsw)] at h1
      exact nomatch h1
    · exact hleafS l (Or.inr ⟨a, ha, hla⟩)
  have hdeqR := ihd hdeRhs hwsR hbR hLR hwsApp hbApp (hLB _ hlfApp)
    hCR (hCtxFull _ hlfApp hwsApp) hRden happden
  have hzsel : ∀ q, q < rP + cnF →
      VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)
        (.bvar (rP + cnF - 1 - q)) =
        (xs.take rP ++ ys.drop cnP).getD q default := by
    intro q hq
    have h1 := hpadhit (rP + cnF) q (xs.take rP ++ ys.drop cnP) hq hzslen
      (Nat.le_refl _)
    rw [Nat.sub_self] at h1
    simpa using h1
  have hmapz : ((List.range (rP + cnF)).map
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) ∘
        fun q => VExpr.bvar (rP + cnF - 1 - q))) =
      (xs.take rP ++ ys.drop cnP) := by
    have h2 : ∀ q ∈ List.range (rP + cnF),
        (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) ∘
          fun q => VExpr.bvar (rP + cnF - 1 - q)) q =
        id ((xs.take rP ++ ys.drop cnP).getD q default) := by
      intro q hq
      simp only [Function.comp_apply, id]
      exact hzsel q (List.mem_range.mp hq)
    rw [List.map_congr_left h2, ← hzslen, map_range_getD, List.map_id]
  have hDeqRR : Deq Δ
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) vR)
      (VExpr.mkAppN RV (xs.take rP ++ ys.drop cnP)) := by
    have h1 := Deq.instCtx hcsZfull (Deq.weakenTail Δ hdeqR)
    rw [hzslen] at h1
    have h2 : VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)
        (VExpr.mkAppN RV ((List.range (rP + cnF)).map
          (fun q => VExpr.bvar (rP + cnF - 1 - q)))) =
        VExpr.mkAppN RV (xs.take rP ++ ys.drop cnP) := by
      rw [VExpr.instSeq_mkAppN, VExpr.instSeq_eq_self_of_closed hRVclosed,
        List.map_map, hmapz]
    rw [h2] at h1
    exact h1
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
  -- the full scattered run, crossed to the constructor's walk
  have hTVjClosed : VExpr.Closed TVj := denote_closed hcl hCw hCb hTVj0
  have hTVjK : denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF)
      (cvj.type.renameConsts f) = some TVj := by
    rw [denote_renameConsts hro,
      denote_depth_closed hcl hCw hCb (rP + cnF)]
    exact hTVj0
  obtain ⟨vCres, hcresden⟩ := instPisAt_fvar_denote_defined hcl _ hcinst
    (fun q x hx => by
      obtain ⟨⟨i0, nm0, t0, rfl⟩, hw1, hb1⟩ := hspFacts q x hx
      exact ⟨⟨VExpr.bvar (rP + cnF - 1 - i0), by rw [denote_fvar]⟩,
        hw1, hb1⟩)
    ((Expr.WScoped.of_not_hasFvar (d := rP + cnF) (by
      rw [hasFvar_renameConsts]; exact hCw)).fvarsBelow)
    (by rw [Expr.looseBVarsBounded_renameConsts]; exact hCb) hTVjK
  have hwsCondF : ∀ (q i0 : Nat) (nm0 : Name) (t0 : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some (Expr.fvar i0 nm0 t0) →
      (xs.take cnP ++ ys.drop cnP)[q]? =
        some (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)
          (.bvar (rP + cnF - 1 - i0))) := by
    intro q i0 nm0 t0 hq
    have hqm : q < cnP + cnF := by
      rcases Nat.lt_or_ge q (cnP + cnF) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hsplen]; omega)] at hq
        exact nomatch hq
    obtain ⟨nm1, t1, hq1⟩ := hspIdx q hqm
    have heq := Option.some.inj (hq.symm.trans hq1)
    injection heq with heqi heqn heqt
    have hi0K : i0 < rP + cnF := by
      rw [heqi]
      by_cases hqc : q < cnP
      · rw [if_pos hqc]
        omega
      · rw [if_neg hqc]
        omega
    rw [hzsel i0 hi0K,
      List.getElem?_eq_getElem (show q < (xs.take cnP ++
        ys.drop cnP).length from by rw [hmixlen]; omega)]
    have hmixq : (xs.take cnP ++ ys.drop cnP)[q] =
        (xs.take cnP ++ ys.drop cnP).getD q default := by
      simp [List.getD, List.getElem?_eq_getElem
        (show q < (xs.take cnP ++ ys.drop cnP).length from by
          rw [hmixlen]; omega)]
    rw [hmixq, hmixget q hqm, hzsget i0 hi0K]
    by_cases hqc : q < cnP
    · rw [if_pos hqc,
        show i0 = q from by rw [heqi, if_pos hqc],
        if_pos (show q < rP from by omega)]
    · rw [if_neg hqc,
        show i0 = rP + (q - cnP) from by rw [heqi, if_neg hqc],
        if_neg (show ¬ rP + (q - cnP) < rP from by omega),
        show cnP + (rP + (q - cnP) - rP) = q from by omega]
  have htowerJF : PiTele (fvs.take cnP ++ fvs.drop rP).length
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) TVj)
      Γj Rj := by
    rw [VExpr.instSeq_eq_self_of_closed hTVjClosed, hsplen]
    exact htowerJ
  have hcrossF := instPisAt_denote_cross hcl _ hcinst hzslen
    (fun j x hx => (hspFacts j x hx).2)
    ((Expr.WScoped.of_not_hasFvar (d := rP + cnF) (by
      rw [hasFvar_renameConsts]; exact hCw)).fvarsBelow)
    (by rw [Expr.looseBVarsBounded_renameConsts]; exact hCb)
    hTVjK hcresden (by rw [hmixlen, hsplen])
    (fun j x hx => by
      obtain ⟨⟨i, nm, t, rfl⟩, -, -⟩ := hspFacts j x hx
      exact ⟨VExpr.bvar (rP + cnF - 1 - i), by rw [denote_fvar],
        hwsCondF j i nm t hx⟩)
    htowerJF
  -- the two spines of the crossed residual, aligned by arity
  have hcresE : cres = Expr.mkAppN cres.getAppFn cres.getAppArgs :=
    (Expr.mkAppN_getApp cres).symm
  rw [hcresE] at hcresden
  obtain ⟨vCf, vCargs, hvCf, hspC2, hvCdecomp⟩ :=
    denote_mkAppN_inv hcresden
  have hvCargslen : vCargs.length = cnP + (mI - rP) := by
    rw [hspC2.length]
    exact hclen
  have hrestCEE : restCE = Expr.mkAppN restCE.getAppFn restCE.getAppArgs :=
    (Expr.mkAppN_getApp restCE).symm
  rw [hrestCEE] at hRj
  obtain ⟨vHC, vArgsC, hvHC, hspHC, hRjdecomp⟩ := denote_mkAppN_inv hRj
  have hstripRen := Expr.stripPis_renameConsts (f := f)
    (cnP + cnF) hstripC
  have harity1 : cres.getAppArgs.length = bodyC0.getAppArgs.length := by
    have h1 := instPisAt_fvar_residual_arity _ hcinst
      (fun x hx => by
        obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
        exact (hspFacts q x hq).1)
      (bs := bsC.map (fun b => (b.1, (b.2.1).renameConsts f, b.2.2)))
      (body := bodyC0.renameConsts f)
      (by rw [hsplen]; exact hstripRen)
    rw [Expr.getAppArgs_length_renameConsts] at h1
    exact h1
  have harity2 : restCE.getAppArgs.length =
      bodyC0.getAppArgs.length :=
    instPisAt_fvar_residual_arity _ hCinstAll
      (fun x hx => by
        obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
        obtain ⟨nm, t, hsh⟩ := hshapeC q x hq
        exact ⟨q, nm, t, hsh⟩)
      (by rw [hfvsClen]; exact hstripC)
  have harityC : vArgsC.length = cnP + (mI - rP) := by
    rw [hspHC.length, harity2, ← harity1]
    exact hclen
  -- align the crossed residual's two spines
  have hcrossF2 : VExpr.mkAppN (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
      (rP + cnF - 1) vCf)
      (vCargs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
        (rP + cnF - 1))) =
      VExpr.mkAppN (VExpr.instSeq (xs.take cnP ++ ys.drop cnP)
        (cnP + cnF - 1) vHC)
        (vArgsC.map (VExpr.instSeq (xs.take cnP ++ ys.drop cnP)
          (cnP + cnF - 1))) := by
    have h1 := hcrossF
    rw [hvCdecomp, hRjdecomp, VExpr.instSeq_mkAppN, VExpr.instSeq_mkAppN,
      show (xs.take cnP ++ ys.drop cnP).length - 1 = cnP + cnF - 1 from
        by rw [hmixlen]] at h1
    exact h1
  obtain ⟨-, hargsAligned⟩ := VExpr.mkAppN_inj hcrossF2
    (by rw [List.length_map, List.length_map, hvCargslen, harityC])
  obtain ⟨HH, cargs, hrestCdecomp, hlenDisj, hpinDeq⟩ := hidx
  have hrestCinst : restC = VExpr.mkAppN
      (VExpr.instSeq ys (cnP + cnF - 1) vHC)
      (vArgsC.map (VExpr.instSeq ys (cnP + cnF - 1))) := by
    rw [hrestC, hRjdecomp, VExpr.instSeq_mkAppN, hlenY]
  -- getD through a map
  have hgetD : ∀ (L : List VExpr) (g : VExpr → VExpr) (q : Nat),
      q < L.length → (L.map g).getD q default = g (L.getD q default) := by
    intro L g q hq
    simp [List.getD, List.getElem?_map, List.getElem?_eq_getElem hq]
  have hspLget := DenoteSpine.get hspL
  -- the pointwise correspondence over the redex's spine
  have hpt : ∀ i : Fin (xs ++ [VExpr.mkAppN
      (m₀.cval ctor (Level.substFn φ cvj.levelParams usj)) ys]).length,
      Deq Δ (xs ++ [VExpr.mkAppN
        (m₀.cval ctor (Level.substFn φ cvj.levelParams usj)) ys])[i]
        ((vLargs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
          (rP + cnF - 1))).getD i default) := by
    intro i
    have hilen : i.1 < mI + 1 := by
      have h0 := i.2
      simp only [List.length_append, List.length_cons,
        List.length_nil] at h0
      omega
    rw [Fin.getElem_fin, hgetD vLargs _ i.1 (by omega)]
    by_cases hirP : i.1 < rP
    · -- a prefix position: the frame's own variable, on both sides
      have htk := congrArg (fun l => l[i.1]?) hlpre
      simp only [List.getElem?_take_of_lt hirP] at htk
      obtain ⟨nm, t, hsh⟩ := hshapeS i.1 fvs[i.1]
        (List.getElem?_eq_getElem (show i.1 < fvs.length from by omega))
      have hden := hspLget ⟨i.1, by omega⟩
      simp only [Fin.getElem_fin] at hden
      rw [show lhsS.getAppArgs[i.1] = fvs[i.1] from by
          have h2 := htk
          rw [List.getElem?_eq_getElem
              (show i.1 < lhsS.getAppArgs.length from by omega),
            List.getElem?_eq_getElem
              (show i.1 < fvs.length from by omega)] at h2
          exact Option.some.inj h2,
        hsh, denote_fvar] at hden
      have hvLi : vLargs.getD i.1 default =
          VExpr.bvar (rP + cnF - 1 - i.1) := (Option.some.inj hden).symm
      rw [List.getElem_append_left (by omega : i.1 < xs.length),
        hvLi, hzsel i.1 (by omega), hzsget i.1 (by omega), if_pos hirP,
        show xs.getD i.1 default = xs[i.1] from by
          simp [List.getD, List.getElem?_eq_getElem
            (show i.1 < xs.length from by omega)]]
    · by_cases himI : i.1 < mI
      · -- an index position: through the canonical tuple
        have haI : ((lhsS.getAppArgs.drop rP).take (mI - rP))[i.1 - rP]? =
            some (lhsS.getAppArgs.getD i.1 default) := by
          rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
            show rP + (i.1 - rP) = i.1 from by omega]
          simp [List.getD, List.getElem?_eq_getElem
            (show i.1 < lhsS.getAppArgs.length from by omega)]
        have hbI : (cres.getAppArgs.drop cnP)[i.1 - rP]? =
            some (cres.getAppArgs.getD (cnP + (i.1 - rP)) default) := by
          rw [List.getElem?_drop]
          simp [List.getD, List.getElem?_eq_getElem
            (show cnP + (i.1 - rP) < cres.getAppArgs.length from by
              rw [hclen]; omega)]
        have hdeI := DefEqListOk.pointwise hdeIdx (i.1 - rP) haI hbI
        -- the constructor residual's frame facts
        have hwscres : Expr.WScoped (rP + cnF) cres := by
          obtain ⟨-, h1⟩ := instPisAt_WScoped (d := rP + cnF) _ _ hcinst
            (Expr.WScoped.of_not_hasFvar (by
              rw [hasFvar_renameConsts]
              exact hCw))
            (fun a ha => by
              obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
              exact (hspFacts q a hq).2.1)
          exact h1
        have hbcres : cres.looseBVarsBounded 0 = true := by
          obtain ⟨-, h1⟩ := instPisAt_bounded _ hcinst
            (by rw [Expr.looseBVarsBounded_renameConsts]; exact hCb)
            (fun a ha => by
              obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
              exact (hspFacts q a hq).2.2)
          exact h1
        have hlfcres : ∀ l ∈ cres.fvarLeaves,
            Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
          intro l hl
          rcases instPisAt_leaves _ hcinst l (Or.inr hl)
            with h1 | ⟨a, ha, hla⟩
          · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
              rw [hasFvar_renameConsts]; exact hCw)] at h1
            exact nomatch h1
          · rcases List.mem_append.mp ha with ha' | ha'
            · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_take ha', hla⟩)
            · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_drop ha', hla⟩)
        -- the two compared arguments' facts
        have hmemLA : lhsS.getAppArgs.getD i.1 default ∈
            lhsS.getAppArgs := by
          refine List.mem_of_getElem? (i := i.1) ?_
          simp [List.getD, List.getElem?_eq_getElem
            (show i.1 < lhsS.getAppArgs.length from by omega)]
        have hmemCA : cres.getAppArgs.getD (cnP + (i.1 - rP)) default ∈
            cres.getAppArgs := by
          refine List.mem_of_getElem? (i := cnP + (i.1 - rP)) ?_
          simp [List.getD, List.getElem?_eq_getElem
            (show cnP + (i.1 - rP) < cres.getAppArgs.length from by
              rw [hclen]; omega)]
        have hlfLA : ∀ l ∈ (lhsS.getAppArgs.getD i.1
            default).fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs :=
          fun l hl => hlfL l (fvarLeaves_getAppArgs hmemLA l hl)
        have hlfCA : ∀ l ∈ (cres.getAppArgs.getD (cnP + (i.1 - rP))
            default).fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs :=
          fun l hl => hlfcres l (fvarLeaves_getAppArgs hmemCA l hl)
        have hdenLA : denote m₀.cval env₀ (Level.substFn φ lps us)
            (rP + cnF) (lhsS.getAppArgs.getD i.1 default) =
            some (vLargs.getD i.1 default) := by
          have h1 := hspLget ⟨i.1, by omega⟩
          simp only [Fin.getElem_fin] at h1
          rw [show lhsS.getAppArgs.getD i.1 default =
            lhsS.getAppArgs[i.1] from by
            simp [List.getD, List.getElem?_eq_getElem
              (show i.1 < lhsS.getAppArgs.length from by omega)]]
          exact h1
        have hdenCA : denote m₀.cval env₀ (Level.substFn φ lps us)
            (rP + cnF) (cres.getAppArgs.getD (cnP + (i.1 - rP))
              default) = some (vCargs.getD (cnP + (i.1 - rP))
              default) := by
          have h1 := hspC2.get ⟨cnP + (i.1 - rP), by rw [hclen]; omega⟩
          simp only [Fin.getElem_fin] at h1
          rw [show cres.getAppArgs.getD (cnP + (i.1 - rP)) default =
            cres.getAppArgs[cnP + (i.1 - rP)] from by
            simp [List.getD, List.getElem?_eq_getElem
              (show cnP + (i.1 - rP) < cres.getAppArgs.length from by
                rw [hclen]; omega)]]
          exact h1
        have hcsZ0 : CtxSpine Δ (Γs.drop (rP + cnF - (rP + cnF)))
            (xs.take rP ++ ys.drop cnP) := by
          rw [Nat.sub_self, List.drop_zero]
          exact hcsZfull
        have hgenI := hopenDeqG fvs Γs (rP + cnF) hΓslen hshapeS hwsFvs
          hdomsS0' (lhsS.getAppArgs.getD i.1 default)
          (cres.getAppArgs.getD (cnP + (i.1 - rP)) default)
          (rP + cnF) (Nat.le_refl _) (Nat.le_refl _) hdeI
          hlfLA hlfCA (hwsL.getAppArgs _ hmemLA)
          (hwscres.getAppArgs _ hmemCA)
          (looseBVarsBounded_getAppArgs hbL _ hmemLA)
          (looseBVarsBounded_getAppArgs hbcres _ hmemCA)
          (hLB _ hlfLA) (hLB _ hlfCA) hdenLA hdenCA hcsZ0
        rw [Nat.sub_self] at hgenI
        simp only [List.replicate, List.append_nil] at hgenI
        rw [hzslen] at hgenI
        -- move the compared component onto the constructor's walk
        have hcomp := congrArg
          (fun l => l.getD (cnP + (i.1 - rP)) default) hargsAligned
        rw [hgetD vCargs _ _ (by omega), hgetD vArgsC _ _ (by omega)]
          at hcomp
        rw [hcomp] at hgenI
        -- the walk at the fired constructor spine
        have hptMix : ∀ p : Fin (xs.take cnP ++ ys.drop cnP).length,
            Deq Δ (xs.take cnP ++ ys.drop cnP)[p] (ys.getD p default) := by
          intro p
          have hp2 := p.2
          have hpm : p.1 < cnP + cnF := by omega
          have hmp : (xs.take cnP ++ ys.drop cnP)[p.1] =
              (xs.take cnP ++ ys.drop cnP).getD p.1 default := by
            simp [List.getD, List.getElem?_eq_getElem hp2]
          rw [Fin.getElem_fin, hmp, hmixget p.1 hpm]
          by_cases hpc : p.1 < cnP
          · rw [if_pos hpc]
            exact (hpar p.1 hpc (by omega)).symm
          · rw [if_neg hpc]
        have hcongrI := CtxSpine.instSeq_congr hcsMix hcsC hptMix
          (vArgsC.getD (cnP + (i.1 - rP)) default)
        rw [hmixlen, hlenY] at hcongrI
        -- the pin's fact at this component
        rcases hlenDisj with hmIrP | hcargslen
        · omega
        have h3 := hrestCdecomp.symm.trans hrestCinst
        obtain ⟨-, hcargsEq⟩ := VExpr.mkAppN_inj h3
          (by rw [hcargslen, List.length_map, harityC])
        have hpinI := hpinDeq (i.1 - rP) (by omega)
        rw [hcargsEq, hgetD vArgsC _ _ (by omega),
          show rP + (i.1 - rP) = i.1 from by omega] at hpinI
        -- assemble
        rw [List.getElem_append_left (by omega : i.1 < xs.length),
          show xs[i.1] = xs.getD i.1 default from by
            simp [List.getD, List.getElem?_eq_getElem
              (show i.1 < xs.length from by omega)]]
        exact Deq.symm (Deq.trans hgenI (Deq.trans hcongrI hpinI))
      · -- the major premise: the constructor at parameters and fields
        have hieq : i.1 = mI := by omega
        -- the statement's last argument is the canonical spine
        have hlast : lhsS.getAppArgs.getD mI default =
            Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
              (fvs.take cnP ++ fvs.drop rP) := by
          rw [← hmaj, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
            hlarity, Nat.add_sub_cancel]
          simp [List.getD, List.getElem?_eq_getElem
            (show mI < lhsS.getAppArgs.length from by omega)]
        -- its denotation: the model constructor over the frame's bvars
        have hspden : DenoteSpine m₀.cval env₀ (Level.substFn φ lps us)
            (rP + cnF) (fvs.take cnP ++ fvs.drop rP)
            ((List.range (cnP + cnF)).map (fun q => VExpr.bvar
              (rP + cnF - 1 -
                (if q < cnP then q else rP + (q - cnP))))) := by
          refine DenoteSpine.of_getElem
            (by rw [hsplen, List.length_map, List.length_range]) ?_
          intro q hq
          rw [hsplen] at hq
          obtain ⟨nm, t, hq1⟩ := hspIdx q hq
          rw [show (fvs.take cnP ++ fvs.drop rP).getD q default =
              Expr.fvar (if q < cnP then q else rP + (q - cnP)) nm t
              from by simp [List.getD, hq1],
            denote_fvar,
            show ((List.range (cnP + cnF)).map (fun q => VExpr.bvar
              (rP + cnF - 1 - (if q < cnP then q else rP + (q - cnP))))
              ).getD q default = VExpr.bvar (rP + cnF - 1 -
                (if q < cnP then q else rP + (q - cnP))) from by
              simp [List.getD, List.getElem?_map, List.getElem?_range hq]]
        have hheadden : denote m₀.cval env₀ (Level.substFn φ lps us)
            (rP + cnF) (.const (f ctor) (cvj.levelParams.map .param)) =
            some (m₀.cval ctor (Level.substFn φ cvj.levelParams usj)) := by
          rw [denote_const, hfCmE]
          dsimp only
          rw [if_pos (by rw [List.length_map, hCmlps])]
          congr 1
          rw [hCmlps,
            show Level.substFn (Level.substFn φ lps us) cvj.levelParams
              (cvj.levelParams.map Level.param) =
              Level.substFn φ lps us from
            funext fun p => Level.substFn_map_param, hro.2.2]
          exact (m₀.val_params ctor _ hctorE _ _
            (fun p hp => hagree p hp)).symm
        have hmajden := hspLget ⟨mI, by omega⟩
        simp only [Fin.getElem_fin] at hmajden
        rw [show lhsS.getAppArgs[mI] =
            lhsS.getAppArgs.getD mI default from by
          simp [List.getD, List.getElem?_eq_getElem
            (show mI < lhsS.getAppArgs.length from by omega)],
          hlast, denote_mkAppN hspden hheadden] at hmajden
        have hvLmaj : vLargs.getD i.1 default =
            VExpr.mkAppN (m₀.cval ctor (Level.substFn φ cvj.levelParams
              usj)) ((List.range (cnP + cnF)).map (fun q => VExpr.bvar
              (rP + cnF - 1 -
                (if q < cnP then q else rP + (q - cnP))))) := by
          rw [hieq]
          exact (Option.some.inj hmajden).symm
        have hmapmaj : ((List.range (cnP + cnF)).map
            (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) ∘
              fun q => VExpr.bvar (rP + cnF - 1 -
                (if q < cnP then q else rP + (q - cnP))))) =
            (List.range (cnP + cnF)).map (fun q =>
              if q < cnP then xs.getD q default
              else ys.getD q default) := by
          refine List.map_congr_left ?_
          intro q hq
          have hqm := List.mem_range.mp hq
          simp only [Function.comp_apply]
          by_cases hqc : q < cnP
          · rw [if_pos hqc, if_pos hqc, hzsel q (by omega),
              hzsget q (by omega), if_pos (by omega : q < rP)]
          · rw [if_neg hqc, if_neg hqc,
              hzsel (rP + (q - cnP)) (by omega),
              hzsget (rP + (q - cnP)) (by omega),
              if_neg (by omega : ¬ rP + (q - cnP) < rP),
              show cnP + (rP + (q - cnP) - rP) = q from by omega]
        rw [hvLmaj,
          show (xs ++ [VExpr.mkAppN (m₀.cval ctor
              (Level.substFn φ cvj.levelParams usj)) ys])[i.1]'(i.2) =
            VExpr.mkAppN (m₀.cval ctor
              (Level.substFn φ cvj.levelParams usj)) ys from by
            rw [List.getElem_append_right (by omega : xs.length ≤ i.1)]
            simp [show i.1 - xs.length = 0 from by omega]]
        rw [VExpr.instSeq_mkAppN,
          VExpr.instSeq_eq_self_of_closed (hcl _ _), List.map_map, hmapmaj]
        refine Deq.mkAppN Deq.refl ?_ ?_
        · rw [List.length_map, List.length_range, hlenY]
        · intro q
          have hq2 := q.2
          have hqm : q.1 < cnP + cnF := by omega
          rw [Fin.getElem_fin,
            show ys[q.1]'(hq2) = ys.getD q.1 default from by
              simp [List.getD],
            show ((List.range (cnP + cnF)).map (fun q =>
              if q < cnP then xs.getD q default else ys.getD q default)
              ).getD q.1 default = (if q.1 < cnP then xs.getD q.1 default
                else ys.getD q.1 default) from by
              simp [List.getD, List.getElem?_map, List.getElem?_range hqm]]
          by_cases hqc : q.1 < cnP
          · rw [if_pos hqc]
            exact hpar q.1 hqc (by omega)
          · rw [if_neg hqc]
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
