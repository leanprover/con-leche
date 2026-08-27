import Setlec.TTVerify.IndBottomPlain
import Setlec.Verify.Denote.OpenRevDenote
import Setlec.TTVerify.IndBottomStages

/-!
# `IndBottomNestedTT`: the nested-auxiliary modeled-iota bottom

`IndBottomPlainTT`'s mirror for a nested-auxiliary rule (`DESIGN.md`
§16.2): the constructor is applied at the *stored* level
instantiations `lvls` and parameter instantiations `pins` — in
rP-context at install, `Expr.instSpine` at both frames — instead of at
the leading telescope variables.  Transpose of
`modeled_bottom_nested`, in the same fired form (no λ-tower
conjuncts, no theorem `find?`).

The parameter positions are met by the law's **nested parameter
premise** (`RecRulesTT`, task #119 re-signing): the fired constructor
parameters against the pins' base-`0` reverse openings.  The bridge
from the statement's own pin occurrences to that canonical form is
`denote_openRev` (real-argument instantiation reads through the
reverse opening) plus the chain algebra (`instSeq_instRevChain`).

## How the hypotheses divide

* The **kit** conjuncts are `PlainChecked`'s, minus the λ-tower three
  and minus the theorem's `find?` (only its typing is read, §14.7.5) —
  the assembly destructures the kit and passes the pieces.
* `m₀ : EnvTT env₀` is the invariant **at the provisional
  environment** (rule-less recursors installed) — exactly as the model
  takes `EnvModel env₀`, supplied by the transpose of
  `provisionRecs_sound`.  Together with `hstep : CheckStepTT mode` (proved,
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

set_option maxHeartbeats 12800000

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

/-- **The nested bottom**: a checked nested-auxiliary `iota_j`
theorem, fired as the stored rule's `RecRulesTT` law (its nested
parameter premise consumed, its plain premise unused).  All statements
are at the provisional install environment `env₀`. -/
theorem IndBottomNestedTT
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
    (hrPmI : rP ≤ mI)
    -- the stored fire data and its install-time well-formedness
    {lvls : List Level} {pins : List Expr}
    (hlvlsLen : lvls.length = cvj.levelParams.length)
    (hpinsLen : pins.length = cnP)
    (hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
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
    (hmaj : Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
      (Expr.mkAppN (.const (f ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP)))
    (hCstrips : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    (hCstripsHead : ∃ bsC0 cbody0 Dc usc,
      cvj.type.stripPis (cnP + cnF) = some (bsC0, cbody0) ∧
      cbody0.getAppFn = Expr.const Dc usc)
    {cdoms : List Expr} {cres : Expr}
    (hcinst : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    (hdeIdx : DefEqListOk mode F env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP))
    {rdoms : List Expr} {rrest : Expr}
    (hrinst : Expr.instPisAt (fvs.take rP) (tyA.renameConsts f) =
      some (rdoms, rrest))
    (hdePre : DefEqListOk mode F env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListOk mode F env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    -- the kit (public prefix and constructor parameters)
    {fvsP : List Expr} {restP : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    {cdomsP : List Expr} {crestP : Expr}
    (hcinstP : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p))
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) =
      some (cdomsP, crestP))
    (hTypedP : TypedListOk mode F env₀ (rP + cnF)
      (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p))
      cdomsP)
    -- the right side and both sides' typings
    (hdeRhs : isDefEqCore mode env₀ F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
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
              (lvls.map (Level.subst lps us)) →
          (∀ i, i < cnP →
            ∀ vp : VExpr,
              denote m₀.cval env₀ φ rP (openRev 0 rP
                ((pins.getD i default).instantiateLevelParams lps us))
                = some vp →
              Deq Δ (ys.getD i default)
                (VExpr.instRevChain (xs.take rP) vp)) →
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
  intro Δ usj xs ys TV TVj restR restC hlenX hlenY hlenJ hlev hparN hidx
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
      isDefEqCore mode env₀ F (rP + cnF) a b = .ok true →
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
  -- the constructor's level assignment agrees with the *stored*
  -- instantiations under the statement's (the nested delta: the
  -- constructor fires at `lvls`, not at its own parameters)
  have hagree : ∀ p ∈ cvj.levelParams,
      Level.substFn φ cvj.levelParams usj p =
        Level.substFn (Level.substFn φ lps us) cvj.levelParams lvls p := by
    intro p hp
    rw [hlev, Level.substFn_map_subst (by rw [hlvlsLen]) hp]
  -- the instantiated constructor type: closed, bounded, and stripping
  have hCwL : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls)).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hCw
  have hCbL : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls)).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hCb
  have hCstripsL : (((cvj.type.instantiateLevelParams cvj.levelParams
      lvls)).stripPis (cnP + cnF)).isSome = true :=
    Expr.stripPis_instantiateLevelParams_isSome cvj.levelParams lvls
      (cnP + cnF) hCstrips
  have hTVj0 : denote m₀.cval env₀ (Level.substFn φ lps us) 0
      (cvj.type.instantiateLevelParams cvj.levelParams lvls)
      = some TVj := by
    rw [denote_instLevels hvp φ d cvj.type,
      denote_depth_closed hcl hCw hCb d] at hTVj
    rw [denote_instLevels hvp _ 0 cvj.type,
      ← denote_params_ext hvp hagree 0 cvj.type hClp]
    exact hTVj
  -- open the constructor's telescope (it strips, so it opens)
  obtain ⟨⟨fvsC, restCE⟩, hopenC⟩ := Option.isSome_iff_exists.mp
    (openPisAtFvars_isSome_of_stripPis _ hCstripsL 0)
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
  -- ===== Stages D-E (sealed): pins' values and the mixed fit =====
  have hxstakelen : (xs.take rP).length = rP := by
    rw [List.length_take]
    omega
  obtain ⟨pinVs, hpinVslen, hpinVsget, hmixed⟩ := nestedMixedFit m₀ ihd
    ihi hrPmI hlenX hlenY hxstakelen hpinsLen hpinsWf hfvsPlen hΓPlen
    hΓjlen hCwL hCbL hTVj0 htowerJ hshapeP hwsFvsP hwsFvsP' hbAnnsP
    hleafP hLBP hdomsP0' hcinstP hTypedP hcsRpre hcsCpre
    (hfitC.steps htowerJ') hparN
  have hmixlen : (pinVs ++ ys.drop cnP).length = cnP + cnF := by
    simp only [List.length_append, List.length_drop, hpinVslen]
    omega
  have htowerJ'' : PiTele (pinVs ++ ys.drop cnP).length TVj Γj Rj := by
    rw [hmixlen]
    exact htowerJ
  have hstepsMix := hmixed.steps htowerJ''
  have hcsMix : CtxSpine Δ Γj (pinVs ++ ys.drop cnP) :=
    hmixed.toCtxSpine htowerJ''
  have hmixgetFld : ∀ p, cnP ≤ p → p < cnP + cnF →
      (pinVs ++ ys.drop cnP).getD p default = ys.getD p default := by
    intro p hpc hp
    simp only [List.getD]
    rw [List.getElem?_append_right (by omega), hpinVslen,
      List.getElem?_drop,
      show cnP + (p - cnP) = p from by omega]
  have hptMixN : ∀ p : Fin (pinVs ++ ys.drop cnP).length,
      Deq Δ (pinVs ++ ys.drop cnP)[p] (ys.getD p default) := by
    intro p
    have hp2 := p.2
    have hpm : p.1 < cnP + cnF := by
      have hml := hmixlen
      omega
    have hmp : (pinVs ++ ys.drop cnP)[p.1] =
        (pinVs ++ ys.drop cnP).getD p.1 default := by
      simp [List.getD, List.getElem?_eq_getElem hp2]
    rw [Fin.getElem_fin, hmp]
    by_cases hpc : p.1 < cnP
    · obtain ⟨wp, hwp, -, hcanon⟩ := hpinVsget p.1 hpc
      rw [show (pinVs ++ ys.drop cnP).getD p.1 default =
          pinVs.getD p.1 default from by
        simp only [List.getD]
        rw [List.getElem?_append_left (by omega)], hcanon]
      refine (hparN p.1 hpc wp ?_).symm
      rw [openRev_instantiateLevelParams lps us 0 rP,
        denote_instLevels hvp φ rP]
      exact hwp
    · rw [hmixgetFld p.1 (by omega) hpm]

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
  -- ===== Stage F' (nested): the constructor's scattered run =====
  have hpadhit := padHit (K := rP + cnF)
  have hpinWf' : ∀ q, q < cnP →
      (pins.getD q default).hasFvar = false ∧
      (pins.getD q default).looseBVarsBounded rP = true := by
    intro q hq
    refine hpinsWf _ (List.mem_of_getElem? (i := q) ?_)
    simp [List.getD, List.getElem?_eq_getElem
      (show q < pins.length from by omega)]
  -- the S-frame pin occurrences and the scattered spine
  have hfvstakelen : (fvs.take rP).length = rP := by
    rw [List.length_take, hfvslen]
    omega
  have hsplen : ((pins.map (fun p => Expr.instSpine (fvs.take rP)
      (rP - 1) (p.renameConsts f))) ++ fvs.drop rP).length
      = cnP + cnF := by
    simp only [List.length_append, List.length_map, List.length_drop,
      hfvslen, hpinsLen]
    omega
  have hpinsSget : ∀ q, q < cnP →
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)))[q]?
        = some (Expr.instSpine (fvs.take rP) (rP - 1)
            ((pins.getD q default).renameConsts f)) := by
    intro q hq
    rw [List.getElem?_map, List.getElem?_eq_getElem
      (show q < pins.length from by omega)]
    simp [List.getD, List.getElem?_eq_getElem
      (show q < pins.length from by omega)]
  have hopenersS : ∀ x ∈ fvs.take rP, Expr.WScoped rP x ∧
      x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨q0, hq0⟩ := List.getElem?_of_mem (List.mem_of_mem_take hx)
    have hq0lt : q0 < rP := by
      obtain ⟨q1, hq1⟩ := List.getElem?_of_mem hx
      have : q1 < rP := by
        rcases Nat.lt_or_ge q1 rP with h | h
        · exact h
        · rw [List.getElem?_eq_none (by
            rw [List.length_take, hfvslen]; omega)] at hq1
          exact nomatch hq1
      rw [List.getElem?_take_of_lt this] at hq1
      obtain ⟨nm1, ty1, rfl⟩ := hshapeS q1 x hq1
      obtain ⟨nm2, ty2, h2⟩ := hshapeS q0 _ hq0
      injection h2 with e1 e2 e3
      omega
    obtain ⟨nm1, ty1, rfl⟩ := hshapeS q0 x hq0
    have h1 := hwsFvs _ (List.mem_of_mem_take hx)
    exact ⟨(by simpa [Expr.WScoped] using
      (⟨hq0lt, ((by simpa [Expr.WScoped] using h1) :
        q0 < rP + cnF ∧ Expr.WScoped q0 ty1).2⟩ :
        q0 < rP ∧ Expr.WScoped q0 ty1)), rfl⟩
  -- one S-frame pin occurrence: frames and the canonical value
  have hpinSF : ∀ q, q < cnP →
      Expr.WScoped rP (Expr.instSpine (fvs.take rP) (rP - 1)
        ((pins.getD q default).renameConsts f)) ∧
      (Expr.instSpine (fvs.take rP) (rP - 1)
        ((pins.getD q default).renameConsts f)).looseBVarsBounded 0
        = true ∧
      (∀ l ∈ (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f)).fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs) := by
    intro q hq
    obtain ⟨hpf, hpb⟩ := hpinWf' q hq
    have hpfR : ((pins.getD q default).renameConsts f).hasFvar
        = false := by
      rw [hasFvar_renameConsts]
      exact hpf
    have hpbR : ((pins.getD q default).renameConsts
        f).looseBVarsBounded rP = true := by
      rw [Expr.looseBVarsBounded_renameConsts]
      exact hpb
    refine ⟨instSpine_WScoped _ (Expr.WScoped.of_not_hasFvar hpfR)
        (fun x hx => (hopenersS x hx).1), ?_, ?_⟩
    · rw [show rP - 1 = (fvs.take rP).length - 1 from by
        rw [hfvstakelen]]
      exact instSpine_closed (fun x hx => (hopenersS x hx).2)
        (by rw [hfvstakelen]; exact hpbR)
    · intro l hl
      rcases fvarLeaves_instSpine _ hl with h1 | ⟨a, ha, hla⟩
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hpfR] at h1
        exact nomatch h1
      · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_take ha, hla⟩)
  -- the S-frame openers' values
  have hbvsS : DenoteSpine m₀.cval env₀ (Level.substFn φ lps us)
      (rP + cnF) (fvs.take rP)
      ((List.range rP).map fun j => VExpr.bvar (rP + cnF - 1 - j)) := by
    refine DenoteSpine.of_getElem
      (by rw [hfvstakelen, List.length_map, List.length_range]) ?_
    intro q hq
    rw [hfvstakelen] at hq
    obtain ⟨nm, t, hsh⟩ := hshapeS q fvs[q]
      (List.getElem?_eq_getElem (by omega))
    rw [show (fvs.take rP).getD q default = fvs[q] from by
        simp [List.getD, List.getElem?_take_of_lt hq,
          List.getElem?_eq_getElem
            (show q < fvs.length from by omega)],
      hsh, denote_fvar,
      show ((List.range rP).map
        (fun j => VExpr.bvar (rP + cnF - 1 - j))).getD q default =
        VExpr.bvar (rP + cnF - 1 - q) from by
        simp [List.getD, List.getElem?_map, List.getElem?_range hq]]
  -- the S-frame pin values coincide with the P-frame's
  have hpinSVal : ∀ q, q < cnP → ∃ wp,
      denote m₀.cval env₀ (Level.substFn φ lps us) rP
        (openRev 0 rP (pins.getD q default)) = some wp ∧
      VExpr.bvarsBelow rP wp ∧
      denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF)
        (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f))
        = some (VExpr.instRevChain ((List.range rP).map fun j =>
            VExpr.bvar (rP + cnF - 1 - j)) wp) := by
    intro q hq
    obtain ⟨wp, hwp, hbv, -⟩ := hpinVsget q hq
    obtain ⟨hpf, hpb⟩ := hpinWf' q hq
    have hpfR : ((pins.getD q default).renameConsts f).hasFvar
        = false := by
      rw [hasFvar_renameConsts]
      exact hpf
    have hpbR : ((pins.getD q default).renameConsts
        f).looseBVarsBounded rP = true := by
      rw [Expr.looseBVarsBounded_renameConsts]
      exact hpb
    refine ⟨wp, hwp, hbv, ?_⟩
    have hosp := denote_openRev (env := env₀)
      (φ := Level.substFn φ lps us) hcl (fvs.take rP)
      (fun a ha => ⟨(hopenersS a ha).1.mono (by omega),
        (hopenersS a ha).2, ((hopenersS a ha).1.mono (by
          omega : rP ≤ rP + cnF)).fvarsBelow⟩)
      ((Expr.WScoped.of_not_hasFvar (d := rP + cnF)
        hpfR).fvarsBelow)
      (by rw [hfvstakelen]; exact hpbR) hbvsS
    rw [hfvstakelen] at hosp
    rw [Expr.instSpine_eq_instSeq, hosp,
      denote_openRev_base hcl hpfR hpbR (rP + cnF),
      openRev_renameConsts f 0 rP, denote_renameConsts hro, hwp]
    rfl
  -- the scattered spine's per-entry facts
  have hspFacts : ∀ (q : Nat) (x : Expr),
      ((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f))) ++ fvs.drop rP)[q]? = some x →
      (∃ w, denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF) x
        = some w) ∧ Expr.WScoped (rP + cnF) x ∧
        x.looseBVarsBounded 0 = true := by
    intro q x hx
    have hq : q < cnP + cnF := by
      rcases Nat.lt_or_ge q (cnP + cnF) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hsplen]; omega)] at hx
        exact nomatch hx
    by_cases hqc : q < cnP
    · rw [List.getElem?_append_left (by
        rw [List.length_map, hpinsLen]; omega)] at hx
      have hx2 := (hpinsSget q hqc).symm.trans hx
      rw [← Option.some.inj hx2]
      obtain ⟨wp, -, -, hden⟩ := hpinSVal q hqc
      obtain ⟨hws1, hbd1, -⟩ := hpinSF q hqc
      exact ⟨⟨_, hden⟩, hws1.mono (by omega), hbd1⟩
    · rw [List.getElem?_append_right (by
        rw [List.length_map, hpinsLen]; omega),
        List.length_map, hpinsLen, List.getElem?_drop] at hx
      obtain ⟨nm, t, rfl⟩ := hshapeS _ x hx
      refine ⟨⟨_, by rw [denote_fvar]⟩,
        hwsFvs _ (List.mem_of_getElem? hx), rfl⟩
  -- the field entries' shapes (the drop half is still variables)
  have hspIdx : ∀ (q : Nat), cnP ≤ q → q < cnP + cnF →
      ∃ nm t, ((pins.map (fun p => Expr.instSpine (fvs.take rP)
        (rP - 1) (p.renameConsts f))) ++ fvs.drop rP)[q]? =
        some (Expr.fvar (rP + (q - cnP)) nm t) := by
    intro q hqc hq
    have hlt : rP + (q - cnP) < fvs.length := by
      rw [hfvslen]
      omega
    obtain ⟨nm, t, hsh⟩ := hshapeS _ fvs[rP + (q - cnP)]
      (List.getElem?_eq_getElem hlt)
    refine ⟨nm, t, ?_⟩
    rw [List.getElem?_append_right (by
        rw [List.length_map, hpinsLen]; omega),
      List.length_map, hpinsLen, List.getElem?_drop,
      show rP + (q - cnP) = rP + (q - cnP) from rfl,
      List.getElem?_eq_getElem hlt, hsh]
  have hcdomslen : cdoms.length = cnP + cnF := by
    have h1 := instPisAt_length _ hcinst
    rw [hsplen] at h1
    exact h1
  -- the pins' full-spine facts for the sealed stages
  have hspWSlow : ∀ (q : Nat) (x : Expr),
      ((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f))) ++ fvs.drop rP)[q]? = some x → q < cnP →
      Expr.WScoped rP x := by
    intro q x hx hqc
    rw [List.getElem?_append_left (by
      rw [List.length_map, hpinsLen]; omega)] at hx
    have hx2 := (hpinsSget q hqc).symm.trans hx
    rw [← Option.some.inj hx2]
    exact (hpinSF q hqc).1
  have hspLeaf : ∀ a ∈ (pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f))) ++
        fvs.drop rP, ∀ l ∈ a.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
    intro a ha l hl
    rcases List.mem_append.mp ha with h | h
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem h
      have hqlt : q < cnP := by
        rcases Nat.lt_or_ge q cnP with h1 | h1
        · exact h1
        · rw [List.getElem?_eq_none (by
            rw [List.length_map, hpinsLen]; omega)] at hq
          exact nomatch hq
      have hq2 := (hpinsSget q hqlt).symm.trans hq
      rw [← Option.some.inj hq2] at hl
      exact (hpinSF q hqlt).2.2 l hl
    · exact hleafS l (Or.inr ⟨a, List.mem_of_mem_drop h, hl⟩)
  have hspPin : ∀ q, q < cnP → ∃ Wq,
      denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF)
        (((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f))) ++ fvs.drop rP).getD q default)
        = some Wq ∧
      ∀ n', rP ≤ n' → n' ≤ rP + cnF →
        VExpr.instSeq ((xs.take rP ++ ys.drop cnP).take n' ++
          List.replicate (rP + cnF - n') dummyPropT) (rP + cnF - 1) Wq
          = (pinVs ++ ys.drop cnP).getD q default := by
    intro q hq
    obtain ⟨wp, hwp, hbv, hden⟩ := hpinSVal q hq
    obtain ⟨wp2, hwp2, -, hcanon⟩ := hpinVsget q hq
    have hwpeq : wp2 = wp := by
      rw [hwp] at hwp2
      exact (Option.some.inj hwp2).symm
    rw [hwpeq] at hcanon
    refine ⟨VExpr.instRevChain ((List.range rP).map fun j =>
      VExpr.bvar (rP + cnF - 1 - j)) wp, ?_, ?_⟩
    · rw [show ((pins.map (fun p => Expr.instSpine (fvs.take rP)
          (rP - 1) (p.renameConsts f))) ++ fvs.drop rP).getD q default
          = Expr.instSpine (fvs.take rP) (rP - 1)
            ((pins.getD q default).renameConsts f) from by
        simp only [List.getD]
        rw [List.getElem?_append_left (by
          rw [List.length_map, hpinsLen]; omega), hpinsSget q hq,
          List.getElem?_eq_getElem
            (show q < pins.length from by omega)]
        simp [List.getElem?_eq_getElem
          (show q < pins.length from by omega)]]
      exact hden
    · intro n' hrn' hn'
      have hc := nestedChain hxstakelen
        ((xs.take rP ++ ys.drop cnP).take n') n' wp
        (by rw [List.length_take, hzslen]; omega) hn' hrn'
        (by rw [List.take_take, Nat.min_eq_left hrn', hzstake rP
          (Nat.le_refl _)]) hbv
      rw [hc, ← hcanon]
      simp only [List.getD]
      rw [List.getElem?_append_left (by omega)]
  have hspImgFull : ∀ q, q < cnP → ∃ Wq,
      denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF)
        (((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f))) ++ fvs.drop rP).getD q default)
        = some Wq ∧
      VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) Wq
        = (pinVs ++ ys.drop cnP).getD q default := by
    intro q hq
    obtain ⟨Wq, hden, hIm⟩ := hspPin q hq
    refine ⟨Wq, hden, ?_⟩
    have h1 := hIm (rP + cnF) (by omega) (Nat.le_refl _)
    rw [Nat.sub_self, List.take_of_length_le (Nat.le_of_eq hzslen)] at h1
    simpa [List.replicate] using h1

  -- ===== Stage G (sealed): the statement fitting =====
  have hCwNR : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact hCwL
  have hCbNR : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_renameConsts]
    exact hCbL
  have hTVjClosed : VExpr.Closed TVj := denote_closed hcl hCwL hCbL hTVj0
  have hTVjK : denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) = some TVj := by
    rw [denote_renameConsts hro,
      denote_depth_closed hcl hCwL hCbL (rP + cnF)]
    exact hTVj0
  have htowerS' : PiTele (xs.take rP ++ ys.drop cnP).length Tstmt Γs
      Rbody := by
    rw [hzslen]
    exact htowerS
  have hzip := zipperStageN m₀ ihd hro hrPmI hlenX hlenY hfvslen
    hfvsPlen hΓslen hΓPlen hΓjlen hcdomslen hrdomslen htyw htyb
    hCwNR hCbNR hTVjK hTVjClosed htowerS htowerJ hshapeS hshapeP
    hwsFvs hbAnns
    (fun l hl => hleafS l (Or.inr
      (hl.resolve_left (fun h => nomatch h))))
    hLB hdomsS0' hxstakelen hzslen hzsget hzstake hsplen hspIdx
    hspFacts hspWSlow hspLeaf hspPin hmixlen hmixgetFld hstepsR
    hstepsMix hrinst hcinst hdePre hdeFld hPRdoms hdomsP0'

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
          eqA.toConstantVal.levelParams [ℓA] uN =
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
  -- ===== Stage J (nested): the left side =====
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
  obtain ⟨vCres, hcresden⟩ := instPisAt_fvar_denote_defined hcl _ hcinst
    hspFacts
    ((Expr.WScoped.of_not_hasFvar (d := rP + cnF) hCwNR).fvarsBelow)
    hCbNR hTVjK
  have hwsCondFN : ∀ (q : Nat) (x : Expr),
      ((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f))) ++ fvs.drop rP)[q]? = some x →
      ∃ w0, denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF) x
        = some w0 ∧
      (pinVs ++ ys.drop cnP)[q]? =
        some (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)
          w0) := by
    intro q x hq
    have hqm : q < cnP + cnF := by
      rcases Nat.lt_or_ge q (cnP + cnF) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hsplen]; omega)] at hq
        exact nomatch hq
    by_cases hqc : q < cnP
    · obtain ⟨Wq, hden, hIm⟩ := hspImgFull q hqc
      have hqx : x = ((pins.map (fun p => Expr.instSpine (fvs.take rP)
          (rP - 1) (p.renameConsts f))) ++ fvs.drop rP).getD q
            default := by
        simp [List.getD, hq]
      refine ⟨Wq, by rw [hqx]; exact hden, ?_⟩
      rw [show (pinVs ++ ys.drop cnP)[q]? =
          some ((pinVs ++ ys.drop cnP).getD q default) from by
        simp [List.getD, List.getElem?_eq_getElem
          (show q < (pinVs ++ ys.drop cnP).length from by
            rw [hmixlen]; omega)], hIm]
    · obtain ⟨nm1, t1, hq1⟩ := hspIdx q (by omega) hqm
      have heq := Option.some.inj (hq.symm.trans hq1)
      subst heq
      refine ⟨VExpr.bvar (rP + cnF - 1 - (rP + (q - cnP))),
        by rw [denote_fvar], ?_⟩
      rw [hzsel (rP + (q - cnP)) (by omega),
        hzsget (rP + (q - cnP)) (by omega), if_neg (by omega),
        show cnP + (rP + (q - cnP) - rP) = q from by omega,
        show (pinVs ++ ys.drop cnP)[q]? =
          some ((pinVs ++ ys.drop cnP).getD q default) from by
        simp [List.getD, List.getElem?_eq_getElem
          (show q < (pinVs ++ ys.drop cnP).length from by
            rw [hmixlen]; omega)],
        hmixgetFld q (by omega) hqm]
  have htowerJF : PiTele ((pins.map (fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f))) ++ fvs.drop rP).length
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) TVj)
      Γj Rj := by
    rw [VExpr.instSeq_eq_self_of_closed hTVjClosed, hsplen]
    exact htowerJ
  have hcrossF := instPisAt_denote_cross hcl _ hcinst hzslen
    (fun j x hx => (hspFacts j x hx).2)
    ((Expr.WScoped.of_not_hasFvar (d := rP + cnF) hCwNR).fvarsBelow)
    hCbNR hTVjK hcresden (by rw [hmixlen, hsplen])
    (fun j x hx => hwsCondFN j x hx)
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
  -- the residual arities, through the stored constant head
  obtain ⟨bsC0raw, cbody0, Dc, usc, hstripRaw, hheadRaw⟩ := hCstripsHead
  obtain ⟨hbodyL, -⟩ := Expr.stripPis_instantiateLevelParams_eq
    cvj.levelParams lvls (cnP + cnF) hstripRaw hstripC
  have hheadL : bodyC0.getAppFn =
      .const Dc (usc.map (Level.subst cvj.levelParams lvls)) := by
    rw [hbodyL, Expr.getAppFn_instantiateLevelParams, hheadRaw]
    rfl
  have hbodyLarity : bodyC0.getAppArgs.length =
      cbody0.getAppArgs.length := by
    rw [hbodyL, Expr.getAppArgs_length_instantiateLevelParams]
  have hstripRen := Expr.stripPis_renameConsts (f := f)
    (cnP + cnF) hstripC
  have hheadLR : (bodyC0.renameConsts f).getAppFn =
      .const (f Dc) (usc.map (Level.subst cvj.levelParams lvls)) := by
    rw [Expr.getAppFn_renameConsts, hheadL]
    rfl
  have harity1 : cres.getAppArgs.length = bodyC0.getAppArgs.length := by
    have h1 := instPisAt_residual_arity_const _ hcinst
      (bs := bsC.map (fun b => (b.1, (b.2.1).renameConsts f, b.2.2)))
      (body := bodyC0.renameConsts f)
      (by rw [hsplen]; exact hstripRen) hheadLR
    rw [Expr.getAppArgs_length_renameConsts] at h1
    exact h1
  have hCinstAll : Expr.instPisAt fvsC
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) =
      some (fvsC.map Expr.fvarTypeD, restCE) :=
    openPisAtFvars_instPisAt _ hopenC
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
  have hcrossF2 : VExpr.mkAppN (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
      (rP + cnF - 1) vCf)
      (vCargs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
        (rP + cnF - 1))) =
      VExpr.mkAppN (VExpr.instSeq (pinVs ++ ys.drop cnP)
        (cnP + cnF - 1) vHC)
        (vArgsC.map (VExpr.instSeq (pinVs ++ ys.drop cnP)
          (cnP + cnF - 1))) := by
    have h1 := hcrossF
    rw [hvCdecomp, hRjdecomp, VExpr.instSeq_mkAppN, VExpr.instSeq_mkAppN,
      show (pinVs ++ ys.drop cnP).length - 1 = cnP + cnF - 1 from
        by rw [hmixlen]] at h1
    exact h1
  obtain ⟨-, hargsAligned⟩ := VExpr.mkAppN_inj hcrossF2
    (by rw [List.length_map, List.length_map, hvCargslen, harityC])
  -- the major's denotation pieces
  obtain ⟨WsS, hspdenN⟩ : ∃ WsS, DenoteSpine m₀.cval env₀
      (Level.substFn φ lps us) (rP + cnF)
      ((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f))) ++ fvs.drop rP) WsS := by
    refine DenoteSpine.of_denotes (fun a ha => ?_)
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨-, ⟨w, hw⟩, -⟩ : True ∧ (∃ w, denote m₀.cval env₀
        (Level.substFn φ lps us) (rP + cnF) a = some w) ∧ True :=
      ⟨trivial, (hspFacts q a hq).1, trivial⟩
    exact ⟨w, hw⟩
  have hvSpNlen : WsS.length = cnP + cnF := by
    have h1 := hspdenN.length
    rw [hsplen] at h1
    omega
  have hvSpFld : ∀ q, cnP ≤ q → q < cnP + cnF →
      WsS.getD q default = VExpr.bvar (rP + cnF - 1 -
        (rP + (q - cnP))) := by
    intro q hqc hqm
    obtain ⟨nm1, t1, hq1⟩ := hspIdx q hqc hqm
    have hqlen : q < ((pins.map (fun p => Expr.instSpine (fvs.take rP)
        (rP - 1) (p.renameConsts f))) ++ fvs.drop rP).length := by
      rw [hsplen]
      omega
    have h1 := hspdenN.get ⟨q, hqlen⟩
    have h2 : ((pins.map (fun p => Expr.instSpine (fvs.take rP)
        (rP - 1) (p.renameConsts f))) ++ fvs.drop rP)[q]'hqlen =
        Expr.fvar (rP + (q - cnP)) nm1 t1 :=
      Option.some.inj ((List.getElem?_eq_getElem hqlen).symm.trans hq1)
    have hd2 : denote m₀.cval env₀ (Level.substFn φ lps us) (rP + cnF)
        (((pins.map (fun p => Expr.instSpine (fvs.take rP)
          (rP - 1) (p.renameConsts f))) ++ fvs.drop rP)[q]'hqlen) =
        some (VExpr.bvar (rP + cnF - 1 - (rP + (q - cnP)))) := by
      rw [h2, denote_fvar]
    exact Option.some.inj (h1.symm.trans hd2)
  have hvSpImg : ∀ q, q < cnP →
      Deq Δ (ys.getD q default)
        (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)
          (WsS.getD q default)) := by
    intro q hqc
    obtain ⟨Wq, hden, hIm⟩ := hspImgFull q hqc
    have h1 := hspdenN.get ⟨q, by rw [hsplen]; omega⟩
    rw [show ((pins.map (fun p => Expr.instSpine (fvs.take rP)
        (rP - 1) (p.renameConsts f))) ++ fvs.drop rP)[(⟨q, by
          rw [hsplen]; omega⟩ : Fin _)] =
        ((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f))) ++ fvs.drop rP).getD q default from by
      simp [List.getD, List.getElem?_eq_getElem
        (show q < ((pins.map (fun p => Expr.instSpine (fvs.take rP)
          (rP - 1) (p.renameConsts f))) ++ fvs.drop rP).length from by
          rw [hsplen]; omega)]] at h1
    rw [hden] at h1
    have hWq : WsS.getD q default = Wq := (Option.some.inj h1).symm
    rw [hWq, hIm, show (pinVs ++ ys.drop cnP).getD q default =
        pinVs.getD q default from by
      simp only [List.getD]
      rw [List.getElem?_append_left (by omega)]]
    obtain ⟨wp, hwp, -, hcanon⟩ := hpinVsget q hqc
    rw [hcanon]
    refine hparN q hqc wp ?_
    rw [openRev_instantiateLevelParams lps us 0 rP,
      denote_instLevels hvp φ rP]
    exact hwp
  have hheaddenN : denote m₀.cval env₀ (Level.substFn φ lps us)
      (rP + cnF) (.const (f ctor) lvls) =
      some (m₀.cval ctor (Level.substFn φ cvj.levelParams usj)) := by
    rw [denote_const, hfCmE]
    dsimp only
    rw [if_pos (by rw [hCmlps, hlvlsLen])]
    congr 1
    rw [hro.2.2]
    refine (m₀.val_params ctor _ hctorE _ _ ?_).symm
    intro p hp
    rw [hagree p hp, hCmlps]
  -- the pointwise correspondence, sealed
  have hpt := pointStageN m₀ ihd hro hfCmE hCmlps hrPmI hlenX
    hlenY hlenJ hfvslen hΓslen hclen hCwNR hCbNR hlvlsLen hlarity
    hlpre hmaj hcinst hdeIdx hspdenN hvSpNlen hvSpImg hvSpFld
    hheaddenN hptMixN hshapeS hwsFvs
    (fun l hl => hleafS l (Or.inr
      (hl.resolve_left (fun h => nomatch h))))
    hLB hdomsS0' hctorE hwsL hbL hlfL hvLargslen hzslen hzsget hzsel
    hsplen hspFacts hspLeaf hmixlen hcsC hcsMix hcsZfull hspL
    hargsAligned hvCargslen harityC hspC2 hidx hrestC hRjdecomp

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
