import Setlec.SetR.Install.IndNestedS

/-!
# The nested bottom, assembled (task #148, T5 c3)

`indBottomNestedS` is `indBottomPlainS`'s mirror at a `.nested` fire:
the same six sealed stages of `Setlec/SetR/Install/IndStagesS.lean`,
instantiated at the **pin** parameter spine instead of the frame's own
prefix openers, with `pinCrossS` (`IndNestedS.lean`) supplying the one
fact that differs — the crossing datum of a pin position.

Risk R1's detection point (the campaign design's §8.1): the rule's
parameter premise is quantified over the pin's **value**
(`∀ vp, ⟦openRev 0 rP pin⟧ = some vp → … interp ρ (instRevChain
(xs.take rP) vp)`), never over an expression, so nothing here needs a
"the pin fits in the clause" statement — the task-#13 wall is not
approached.  The pins' canonical values exist because the checked
statement's own pin walk (`TypedListW`) denotes them at the
recursor frame, and `denote_openRev` reads that denotation back to the
opened form.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

set_option maxHeartbeats 12800000 in
theorem indBottomNestedS : IndBottomNestedS V := by
  intro μ envS mS f hro heqfE Rn lps tyA mI rP htyw htyb ciRm hfRnE
    hRmlps ctor cvj cnP cnF hctorE ciCm hfCmE hCmlps hCw hCb hClp hrPmI
    lvls pins hlvlsLen hpinsLen hpinsWf rhsA hrhsw hrhsb hrhsKey stmtTy
    hSw hSb hthm fvs tbody ℓA αS lhsS rhsS hopen hheadEq hargs3 hlhead
    hlarity hlpre hmaj hCstripsHead cdoms cres hcinst hclen rdoms rrest
    hrinst fvsP restP hopenP cdomsP crestP hcinstP xFvsP ldomsE hopenXP
    hstripRhs ldomsL lrest2 hinstLam hTypedP hdeIdx hdePre hdeFld hdeLam
    hdeRhs hsidesTy
  intro φ us huslen
  have hvp : ValParams envS mS.cval := mS.val_params
  have henv := mS.toHyp (Level.substFn φ lps us)
  have hcl' := mS.cval_closed
  -- the rule's right-hand side denotes at the instantiated assignment
  obtain ⟨Rv, tinf, hRvden, hRvFacts⟩ := hrhsKey (Level.substFn φ lps us)
  refine ⟨Rv, ?_, ?_⟩
  · show denoteClosed mS.cval envS φ (rhsA.instantiateLevelParams lps us)
      = some Rv
    unfold denoteClosed
    rw [denote_instLevels hvp]
    exact hRvden
  intro usj ρ xs ys TV TVj restR restC hlenX hlenY husjlen hlev hparP
    hidx hTV hTVj hfitR hfitC
  -- ===== the statement, opened =====
  obtain ⟨Tst, hTstden, hTstFacts⟩ := hthm (Level.substFn φ lps us)
  obtain ⟨Γs, Rbody, htowerS, hRbodyDenA, hdomsS0A⟩ :=
    openPisAtFvars_denoteTele (rP + cnF) hopen hTstden
  have hΓslen : Γs.length = rP + cnF := htowerS.length
  have hfvslen : fvs.length = rP + cnF := openPisAtFvars_length _ hopen
  have hshapeS : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty := by
    intro i x hx
    obtain ⟨nm, ty, hx'⟩ := openPisAtFvars_index _ _ _ hopen i x hx
    exact ⟨nm, ty, by simpa using hx'⟩
  have hwsS := openPisAtFvars_WScoped (rP + cnF) stmtTy 0 hopen
    (Expr.WScoped.of_not_hasFvar hSw)
  have hwsFvs : ∀ x ∈ fvs, Expr.WScoped (rP + cnF) x := by
    intro x hx
    have h := hwsS.1 x hx
    rwa [Nat.zero_add] at h
  have hbFvs : ∀ x ∈ fvs, x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    obtain ⟨nm, ty, rfl⟩ := hshapeS q x hq
    rfl
  have hleafClosed : ∀ l, (∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
    intro l ⟨x, hx, hl⟩
    rcases openPisAtFvars_leaves _ hopen l (Or.inr ⟨x, hx, hl⟩) with
      h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hSw] at h0
      exact nomatch h0
    · exact h0
  have hleafBody : ∀ l ∈ tbody.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
    intro l hl
    rcases openPisAtFvars_leaves _ hopen l (Or.inl hl) with h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hSw] at h0
      exact nomatch h0
    · exact h0
  have hfvsLt : ∀ l : Nat × Name × Expr,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs → l.1 < rP + cnF := by
    intro l hl
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hl
    obtain ⟨nm', ty', heq⟩ := hshapeS q _ hq
    have hql : q < fvs.length := (List.getElem?_eq_some_iff.mp hq).1
    injection heq with h1 _
    rw [h1]
    rw [hfvslen] at hql
    exact hql
  have hdomsS0 : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denote mS.cval envS (Level.substFn φ lps us) i (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i) default) := by
    intro i x hx
    have h := hdomsS0A i x hx
    rwa [Nat.zero_add] at h
  have hRbodyDen : denote mS.cval envS (Level.substFn φ lps us)
      (rP + cnF) tbody = some Rbody := by
    have h := hRbodyDenA
    rwa [Nat.zero_add] at h
  -- ===== the public (recursor) tower =====
  have hTV0 : denote mS.cval envS (Level.substFn φ lps us) 0 tyA
      = some TV := by
    have h := hTV
    unfold denoteClosed at h
    rwa [denote_instLevels hvp] at h
  obtain ⟨ΓP, RP, htowerP, hRPden, hdomsP0A⟩ :=
    openPisAtFvars_denoteTele rP hopenP hTV0
  have hfvsPlen : fvsP.length = rP := openPisAtFvars_length _ hopenP
  have hshapeP : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty := by
    intro i x hx
    obtain ⟨nm, ty, hx'⟩ := openPisAtFvars_index _ _ _ hopenP i x hx
    exact ⟨nm, ty, by simpa using hx'⟩
  have hdomsP0 : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      denote mS.cval envS (Level.substFn φ lps us) i (Expr.fvarTypeD x)
        = some (ΓP.getD (rP - 1 - i) default) := by
    intro i x hx
    have h := hdomsP0A i x hx
    rwa [Nat.zero_add] at h
  have hwsP := openPisAtFvars_WScoped rP tyA 0 hopenP
    (Expr.WScoped.of_not_hasFvar htyw)
  have hwsFvsP : ∀ x ∈ fvsP, Expr.WScoped rP x := by
    intro x hx
    have h := hwsP.1 x hx
    rwa [Nat.zero_add] at h
  have hleafP : ∀ l, (∃ x ∈ fvsP, l ∈ x.fvarLeaves) →
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP := by
    intro l ⟨x, hx, hl⟩
    rcases openPisAtFvars_leaves _ hopenP l (Or.inr ⟨x, hx, hl⟩) with
      h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htyw] at h0
      exact nomatch h0
    · exact h0
  -- ===== the constructor's assignment, at the stored levels =====
  have hagree : ∀ p ∈ cvj.levelParams,
      Level.substFn φ cvj.levelParams usj p
        = Level.substFn (Level.substFn φ lps us) cvj.levelParams lvls p := by
    intro p hp
    rw [hlev]
    exact Level.substFn_map_subst hlvlsLen hp
  have hTVj0 : denote mS.cval envS
      (Level.substFn (Level.substFn φ lps us) cvj.levelParams lvls) 0
      cvj.type = some TVj := by
    have h := hTVj
    unfold denoteClosed at h
    rw [denote_instLevels hvp] at h
    rwa [denote_params_ext hvp hagree 0 cvj.type hClp] at h
  have hTVjcl : VExpr.Closed TVj := denote_closed hcl' hCw hCb hTVj0
  -- the level-instantiated, renamed constructor type
  have hCvLw : (cvj.type.instantiateLevelParams cvj.levelParams lvls).hasFvar
      = false := by
    rw [Expr.hasFvar_instantiateLevelParams]
    exact hCw
  have hCvLb : (cvj.type.instantiateLevelParams cvj.levelParams
      lvls).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]
    exact hCb
  have hCwR : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact hCvLw
  have hCbR : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact hCvLb
  have hTVjK : denote mS.cval envS (Level.substFn φ lps us) (rP + cnF)
      ((cvj.type.instantiateLevelParams cvj.levelParams lvls).renameConsts f)
      = some TVj := by
    rw [denote_depth_closed hcl' hCwR hCbR]
    show denote _ _ _ 0 _ = _
    rw [denote_renameConsts hro, denote_instLevels hvp]
    exact hTVj0
  have htyRw : (tyA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact htyw
  have htyRb : (tyA.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact htyb
  -- ===== `Rj`'s decomposition and its arity =====
  obtain ⟨bsC0, cbody0, Dc, usc, hstripRaw, hheadRaw⟩ := hCstripsHead
  obtain ⟨Γj, Rj, htowerJ, hΓjlen0, hRjdenA, hdomsJ⟩ :=
    stripPis_denoteTele (cnP + cnF) hstripRaw hTVj0
  have hcbApp : Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
      cbody0
      = Expr.mkAppN
          (Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
            cbody0.getAppFn)
          (cbody0.getAppArgs.map
            (Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
              ·)) := by
    have hcb : cbody0 = Expr.mkAppN cbody0.getAppFn cbody0.getAppArgs :=
      (Expr.mkAppN_getApp cbody0).symm
    have h1 : Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
        cbody0
        = Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
          (Expr.mkAppN cbody0.getAppFn cbody0.getAppArgs) := by
      conv => lhs; rw [hcb]
    rw [h1, Expr.instSeq_mkAppN]
  have hRjdenA' := hRjdenA
  rw [Nat.zero_add, hcbApp] at hRjdenA'
  obtain ⟨vHC, vArgsC, hvHCden, hcspJ, hRjdec⟩ :=
    denote_mkAppN_inv hRjdenA'
  -- the fired spine's length, and the pin instantiations
  have hsplen : ((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
      (p.renameConsts f))) ++ fvs.drop rP).length = cnP + cnF := by
    rw [List.length_append, List.length_map, List.length_drop, hpinsLen,
      hfvslen]
    omega
  obtain ⟨⟨bsC, bodyC0⟩, hstripC⟩ := Option.isSome_iff_exists.mp
    (Expr.stripPis_instantiateLevelParams_isSome cvj.levelParams lvls
      (cnP + cnF) (by rw [hstripRaw]; rfl))
  obtain ⟨hbodyL, -⟩ := Expr.stripPis_instantiateLevelParams_eq
    cvj.levelParams lvls (cnP + cnF) hstripRaw hstripC
  have hheadLR : (bodyC0.renameConsts f).getAppFn
      = .const (f Dc) (usc.map (Level.subst cvj.levelParams lvls)) := by
    rw [Expr.getAppFn_renameConsts, hbodyL,
      Expr.getAppFn_instantiateLevelParams, hheadRaw]
    rfl
  have hstripRen : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f).stripPis
      ((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f))) ++ fvs.drop rP).length
      = some (bsC.map (fun b => (b.1, (b.2.1).renameConsts f, b.2.2)),
        bodyC0.renameConsts f) := by
    rw [hsplen]
    exact stripPis_renameConsts (f := f) (cnP + cnF) hstripC
  have harity1 : cres.getAppArgs.length = bodyC0.getAppArgs.length := by
    have h1 := instPisAt_residual_arity_const _ hcinst hstripRen hheadLR
    rw [getAppArgs_length_renameConsts] at h1
    exact h1
  have hcbodyArity : cbody0.getAppArgs.length = cnP + (mI - rP) := by
    have h2 : bodyC0.getAppArgs.length = cbody0.getAppArgs.length := by
      rw [hbodyL, Expr.getAppArgs_length_instantiateLevelParams]
    rw [← h2, ← harity1, hclen]
  have hArgsClen : vArgsC.length = cnP + (mI - rP) := by
    rw [hcspJ.length, List.length_map, hcbodyArity]
  -- ===== the fitting prefix =====
  have htakexs : (xs ++ [VExpr.mkAppN
      (mS.cval ctor (Level.substFn φ cvj.levelParams usj)) ys]).take rP
      = xs.take rP := by
    rw [List.take_append_of_le_length (by rw [hlenX]; omega)]
  obtain ⟨restRpre, hfitRpre⟩ := hfitR.take rP
  rw [htakexs] at hfitRpre
  -- the P-frame annotations, renamed-equal to the recursor's run
  have hPpreRun : Expr.instPisAt fvsP tyA
      = some (fvsP.map Expr.fvarTypeD, restP) :=
    openPisAtFvars_instPisAt _ hopenP
  have hrdomslen : rdoms.length = rP := by
    have h := instPisAt_length _ hrinst
    rw [List.length_take, hfvslen] at h
    omega
  have hrenP : ∀ n, n < rP →
      RenEqT f ((fvsP.map Expr.fvarTypeD).getD n default)
        (rdoms.getD n default) := by
    intro n hn
    have hrenD := instPisAt_renEq fvsP (fvs.take rP) hPpreRun hrinst
      (show Expr.ErasedEq (tyA.renameConsts f) (tyA.renameConsts f) from
        Expr.ErasedEq.rfl _)
      (fun i0 a a' ha ha' => by
        have hi0 : i0 < rP := by
          have := (List.getElem?_eq_some_iff.mp ha).1
          rw [hfvsPlen] at this
          exact this
        obtain ⟨nm, ty, rfl⟩ := hshapeP i0 a ha
        rw [List.getElem?_take_of_lt hi0] at ha'
        obtain ⟨nm', ty', rfl⟩ := hshapeS i0 a' ha'
        exact RenEqT.fvar)
      (by rw [hfvsPlen, List.length_take, hfvslen]; omega)
    rcases hp : fvsP[n]? with _ | px
    · rw [List.getElem?_eq_none_iff, hfvsPlen] at hp
      omega
    rcases hr : rdoms[n]? with _ | rx
    · rw [List.getElem?_eq_none_iff, hrdomslen] at hr
      omega
    rw [List.getD, List.getD, List.getElem?_map, hp, hr]
    exact hrenD.1 n _ _ (by rw [List.getElem?_map, hp]; rfl) hr
  -- ===== the fired spine and the pins =====
  have hzslen : (xs.take rP ++ ys.drop cnP).length = rP + cnF := by
    rw [List.length_append, List.length_take, List.length_drop, hlenX,
      hlenY]
    omega
  have hxtlen : (xs.take rP).length = rP := by
    rw [List.length_take, hlenX]
    omega
  have hzstake : (xs.take rP ++ ys.drop cnP).take rP = xs.take rP := by
    rw [List.take_append_of_le_length (by rw [hxtlen]; omega)]
    exact List.take_of_length_le (by rw [hxtlen]; omega)
  have hzsPre : ∀ n, n < rP →
      (xs.take rP ++ ys.drop cnP).getD n default
        = xs.getD n default := by
    intro n hn
    rw [List.getD, List.getElem?_append_left (by rw [hxtlen]; omega),
      List.getElem?_take_of_lt hn]
    rfl
  have hzsFld : ∀ j, j < cnF →
      (xs.take rP ++ ys.drop cnP).getD (rP + j) default
        = ys.getD (cnP + j) default := by
    intro j hj
    rw [List.getD, List.getElem?_append_right (by rw [hxtlen]; omega),
      hxtlen, List.getElem?_drop, show rP + j - rP = j from by omega]
    rfl
  -- the pins, pointwise
  have hpgetd : ∀ q, q < cnP →
      pins[q]? = some (pins.getD q default) := by
    intro q hq
    rw [List.getD]
    rcases hp : pins[q]? with _ | p
    · rw [List.getElem?_eq_none_iff, hpinsLen] at hp
      omega
    · rfl
  have hpmemd : ∀ q, q < cnP → pins.getD q default ∈ pins :=
    fun q hq => List.mem_of_getElem? (hpgetd q hq)
  have hpwd : ∀ q, q < cnP → (pins.getD q default).hasFvar = false ∧
      (pins.getD q default).looseBVarsBounded rP = true :=
    fun q hq => hpinsWf _ (hpmemd q hq)
  -- the pins' canonical denotations, from the statement's own pin walk
  have hpinPden : ∀ q, q < cnP → ∃ W,
      denote mS.cval envS (Level.substFn φ lps us) rP
        (openRev 0 rP (pins.getD q default)) = some W := by
    intro q hq
    obtain ⟨hwlenT, hwgetT⟩ := Forall2.length_getD (hTypedP
      (Level.substFn φ lps us))
    have hlenM : (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))).length
        = cnP := by
      rw [List.length_map, hpinsLen]
    obtain ⟨Ev, Dv, hEv, -, -⟩ :=
      hwgetT q default default (by rw [hlenM]; exact hq)
    have hmapg : (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))).getD q
        default = Expr.instSpine (fvsP.take rP) (rP - 1)
          (pins.getD q default) := by
      rw [List.getD, List.getElem?_map, hpgetd q hq]
      rfl
    rw [hmapg, Expr.instSpine_eq_instSeq] at hEv
    -- read the instantiation back through the reverse opening
    have htkPlen : (fvsP.take rP).length = rP := by
      rw [List.length_take, hfvsPlen]
      omega
    obtain ⟨vsP, hspP⟩ := DenoteSpine.of_denotes
      (cval := mS.cval) (env := envS) (φ := Level.substFn φ lps us)
      (d := rP + cnF) (as := fvsP.take rP) (fun a ha => by
        obtain ⟨q0, hq0⟩ := List.getElem?_of_mem ha
        have hq0' : fvsP[q0]? = some a := by
          have hq0lt : q0 < rP := by
            have := (List.getElem?_eq_some_iff.mp hq0).1
            rw [htkPlen] at this
            exact this
          rw [← List.getElem?_take_of_lt hq0lt]
          exact hq0
        obtain ⟨nm, ty, rfl⟩ := hshapeP q0 a hq0'
        exact ⟨_, denote_fvar _ _ _ (rP + cnF) q0 nm ty⟩)
    have hkey := denote_openRev (cval := mS.cval) (env := envS)
      (φ := Level.substFn φ lps us) hcl' (fvsP.take rP)
      (e := pins.getD q default) (d := rP + cnF)
      (fun a ha => by
        have hws : Expr.WScoped (rP + cnF) a :=
          (hwsFvsP a (List.mem_of_mem_take ha)).mono (by omega)
        obtain ⟨q0, hq0⟩ := List.getElem?_of_mem ha
        have hq0' : fvsP[q0]? = some a := by
          have hq0lt : q0 < rP := by
            have := (List.getElem?_eq_some_iff.mp hq0).1
            rw [htkPlen] at this
            exact this
          rw [← List.getElem?_take_of_lt hq0lt]
          exact hq0
        obtain ⟨nm, ty, rfl⟩ := hshapeP q0 a hq0'
        exact ⟨hws, rfl, hws.fvarsBelow⟩)
      (Expr.fvarsBelow_of_fvarLeaves (fun l hl => by
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpwd q hq).1] at hl
        exact nomatch hl))
      (by rw [htkPlen]; exact (hpwd q hq).2) hspP
    rw [htkPlen, hEv] at hkey
    rcases hin : denote mS.cval envS (Level.substFn φ lps us)
        (rP + cnF + rP) (openRev (rP + cnF) rP (pins.getD q default))
      with _ | W
    · rw [hin] at hkey
      exact nomatch hkey
    · refine ⟨W, ?_⟩
      rw [← denote_openRev_base (cval := mS.cval) (env := envS)
        (φ := Level.substFn φ lps us) hcl' (hpwd q hq).1 (hpwd q hq).2
        (rP + cnF)]
      exact hin
  -- the pins' values and the crossing datum
  have hpinCross : ∀ q, q < cnP → ∃ vp w0,
      denote mS.cval envS φ rP (openRev 0 rP
        ((pins.getD q default).instantiateLevelParams lps us)) = some vp ∧
      VExpr.bvarsBelow rP vp ∧
      denote mS.cval envS (Level.substFn φ lps us) (rP + cnF)
        (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f)) = some w0 ∧
      VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) w0
        = VExpr.instRevChain (xs.take rP) vp := by
    intro q hq
    obtain ⟨W, hW⟩ := hpinPden q hq
    obtain ⟨w0, hw0, hcross⟩ := pinCrossS hcl' hro hfvslen hshapeS hwsFvs
      hbFvs (hpwd q hq).1 (hpwd q hq).2 hW hxtlen hzslen hzstake
    refine ⟨W, w0, ?_, ?_, hw0, hcross⟩
    · rw [openRev_instantiateLevelParams lps us 0 rP, denote_instLevels hvp]
      exact hW
    · refine denote_bvarsBelow hcl' rP _ ?_ ?_ hW
      · have h := openRev_WScoped (d := 0)
          (Expr.WScoped.of_not_hasFvar (hpwd q hq).1) rP
        rwa [Nat.zero_add] at h
      · exact openRev_bounded rP 0 (by simpa using (hpwd q hq).2)
  -- the fired parameter spine denotes
  have hpinsRden : ∀ a ∈ pins.map (fun p => Expr.instSpine (fvs.take rP)
      (rP - 1) (p.renameConsts f)),
      ∃ w, denote mS.cval envS (Level.substFn φ lps us) (rP + cnF) a
        = some w := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hp
    have hqlt : q < cnP := by
      have := (List.getElem?_eq_some_iff.mp hq).1
      rw [hpinsLen] at this
      exact this
    have hgd : pins.getD q default = p := by
      rw [List.getD, hq]
      rfl
    obtain ⟨vp, w0, -, -, hw0, -⟩ := hpinCross q hqlt
    rw [hgd] at hw0
    exact ⟨w0, hw0⟩
  obtain ⟨pinWs, hspW⟩ := DenoteSpine.of_denotes hpinsRden
  have hpinWslen : pinWs.length = cnP := by
    rw [hspW.length, List.length_map, hpinsLen]
  -- ===== the spine data for the generic stages =====
  have hpinsRlen : (pins.map (fun p => Expr.instSpine (fvs.take rP)
      (rP - 1) (p.renameConsts f))).length = cnP := by
    rw [List.length_map, hpinsLen]
  have hpinsRget : ∀ q, q < cnP →
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)))[q]?
      = some (Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f)) := by
    intro q hq
    rw [List.getElem?_map, hpgetd q hq]
    rfl
  have hopenerLeaf : ∀ (q0 : Nat) (a : Expr), (fvs.take rP)[q0]? = some a →
      ∀ l ∈ a.fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs ∧ l.1 < rP := by
    intro q0 a ha l hl
    have hq0lt : q0 < rP := by
      have := (List.getElem?_eq_some_iff.mp ha).1
      rw [List.length_take, hfvslen] at this
      omega
    rw [List.getElem?_take_of_lt hq0lt] at ha
    obtain ⟨nm, ty, rfl⟩ := hshapeS q0 a ha
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨List.mem_of_getElem? ha, hq0lt⟩
    · have hwsty : Expr.WScoped q0 ty := by
        have h' := hwsFvs _ (List.mem_of_getElem? ha)
        simp only [Expr.WScoped] at h'
        exact h'.2
      have hlt := Expr.fvarLeaves_lt_of_wscoped hwsty l hl'
      refine ⟨hleafClosed l ⟨_, List.mem_of_getElem? ha, ?_⟩, by omega⟩
      rw [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl'
  have hspLeaf : ∀ (q : Nat) (x : Expr),
      ((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f))) ++ fvs.drop rP)[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP) := by
    intro q x hx l hl
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · rw [List.getElem?_append_left (by rw [hpinsRlen]; omega),
        hpinsRget q hqc] at hx
      obtain rfl : x = Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f) :=
        (Option.some.inj hx).symm
      rcases fvarLeaves_instSpine (rP - 1) hl with hl' | ⟨a, ha, hla⟩
      · exfalso
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact (hpwd q hqc).1)] at hl'
        exact nomatch hl'
      · obtain ⟨q0, hq0⟩ := List.getElem?_of_mem ha
        obtain ⟨hmem, hlt⟩ := hopenerLeaf q0 a hq0 l hla
        exact ⟨hmem, by omega⟩
    · rw [List.getElem?_append_right (by rw [hpinsRlen]; omega),
        hpinsRlen, List.getElem?_drop] at hx
      obtain ⟨nm, ty, rfl⟩ := hshapeS (rP + (q - cnP)) x hx
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · exact ⟨List.mem_of_getElem? hx, by omega⟩
      · have hwsty : Expr.WScoped (rP + (q - cnP)) ty := by
          have h' := hwsFvs _ (List.mem_of_getElem? hx)
          simp only [Expr.WScoped] at h'
          exact h'.2
        have hlt := Expr.fvarLeaves_lt_of_wscoped hwsty l hl'
        refine ⟨hleafClosed l ⟨_, List.mem_of_getElem? hx, ?_⟩, by omega⟩
        rw [Expr.fvarLeaves]
        exact List.mem_cons_of_mem _ hl'
  have hspScope : ∀ (q : Nat) (x : Expr),
      ((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f))) ++ fvs.drop rP)[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true := by
    intro q x hx
    have htkSlen : (fvs.take rP).length = rP := by
      rw [List.length_take, hfvslen]
      omega
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · rw [List.getElem?_append_left (by rw [hpinsRlen]; omega),
        hpinsRget q hqc] at hx
      obtain rfl : x = Expr.instSpine (fvs.take rP) (rP - 1)
          ((pins.getD q default).renameConsts f) :=
        (Option.some.inj hx).symm
      constructor
      · exact instSpine_WScoped (rP - 1)
          (Expr.WScoped.of_not_hasFvar (by
            rw [hasFvar_renameConsts]
            exact (hpwd q hqc).1))
          (fun a ha => hwsFvs a (List.mem_of_mem_take ha))
      · have h := instSpine_closed (args := fvs.take rP)
          (e := (pins.getD q default).renameConsts f)
          (fun a ha => hbFvs a (List.mem_of_mem_take ha))
          (by rw [htkSlen, looseBVarsBounded_renameConsts]
              exact (hpwd q hqc).2)
        rwa [htkSlen] at h
    · rw [List.getElem?_append_right (by rw [hpinsRlen]; omega),
        hpinsRlen, List.getElem?_drop] at hx
      obtain ⟨nm, ty, rfl⟩ := hshapeS (rP + (q - cnP)) x hx
      exact ⟨hwsFvs _ (List.mem_of_getElem? hx),
        hbFvs _ (List.mem_of_getElem? hx)⟩
  -- the mixed value spine
  have hmixlen : (pinWs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
      (rP + cnF - 1)) ++ ys.drop cnP).length = cnP + cnF := by
    rw [List.length_append, List.length_map, List.length_drop, hpinWslen,
      hlenY]
    omega
  have hmixsp : ∀ (q : Nat) (x : Expr),
      ((pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f))) ++ fvs.drop rP)[q]? = some x →
      ∃ w0, denote mS.cval envS (Level.substFn φ lps us) (rP + cnF) x
          = some w0 ∧
        (pinWs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
          (rP + cnF - 1)) ++ ys.drop cnP)[q]?
          = some (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
            (rP + cnF - 1) w0) := by
    intro q x hx
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · have hxq : (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)))[q]? = some x := by
        rw [← hx, List.getElem?_append_left (by rw [hpinsRlen]; omega)]
      obtain ⟨w, hw, hdw⟩ := denoteSpine_getElem?' hspW q x hxq
      refine ⟨w, hdw, ?_⟩
      rw [List.getElem?_append_left
        (by rw [List.length_map, hpinWslen]; omega),
        List.getElem?_map, hw]
      rfl
    · rw [List.getElem?_append_right (by rw [hpinsRlen]; omega),
        hpinsRlen, List.getElem?_drop] at hx
      have hqf : q < cnP + cnF := by
        have hlt := (List.getElem?_eq_some_iff.mp hx).1
        rw [hfvslen] at hlt
        omega
      obtain ⟨nm, ty, rfl⟩ := hshapeS (rP + (q - cnP)) x hx
      refine ⟨.bvar (rP + cnF - 1 - (rP + (q - cnP))),
        denote_fvar _ _ _ (rP + cnF) _ nm ty, ?_⟩
      rw [instSeq_bvar_full (by omega) hzslen,
        List.getElem?_append_right
          (by rw [List.length_map, hpinWslen]; omega),
        List.length_map, hpinWslen, List.getElem?_drop,
        show cnP + (q - cnP) = q from by omega]
      rw [hzsFld (q - cnP) (by omega)]
      rw [show cnP + (q - cnP) = q from by omega]
      rw [List.getD]
      rcases hy : ys[q]? with _ | v
      · rw [List.getElem?_eq_none_iff, hlenY] at hy
        omega
      · rfl
  have hmixFldEq : ∀ j, j < cnF →
      (pinWs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
        (rP + cnF - 1)) ++ ys.drop cnP).getD (cnP + j) default
        = ys.getD (cnP + j) default := by
    intro j hj
    rw [List.getD, List.getElem?_append_right
      (by rw [List.length_map, hpinWslen]; omega),
      List.length_map, hpinWslen, List.getElem?_drop,
      show cnP + j - cnP = j from by omega]
    rfl
  have hmixPar : ∀ q, q < cnP →
      interp V ρ ((pinWs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
        (rP + cnF - 1)) ++ ys.drop cnP).getD q default)
        = interp V ρ (ys.getD q default) := by
    intro q hq
    obtain ⟨vp, w0, hvpden, hbv, hw0, hcross⟩ := hpinCross q hq
    obtain ⟨w, hw, hdw⟩ := denoteSpine_getElem?' hspW q _
      (hpinsRget q hq)
    have hww : w = w0 := by
      rw [hw0] at hdw
      exact (Option.some.inj hdw).symm
    have hget : (pinWs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
        (rP + cnF - 1)) ++ ys.drop cnP).getD q default
        = VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) w0 := by
      rw [List.getD, List.getElem?_append_left
        (by rw [List.length_map, hpinWslen]; omega),
        List.getElem?_map, hw]
      exact congrArg
        (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1)) hww
    rw [hget, hcross]
    exact (hparP q hq vp hvpden hbv).symm
  have hmixVal : ∀ q, q < cnP + cnF →
      interp V ρ ((pinWs.map (VExpr.instSeq (xs.take rP ++ ys.drop cnP)
        (rP + cnF - 1)) ++ ys.drop cnP).getD q default)
        = interp V ρ (ys.getD q default) := by
    intro q hq
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · exact hmixPar q hqc
    · rw [show q = cnP + (q - cnP) from by omega]
      exact congrArg _ (hmixFldEq (q - cnP) (by omega))
  -- ===== the zipper: satisfaction and the statement fit =====
  obtain ⟨hsat, hfitS⟩ := zipperS (f := f) henv hrPmI hlenX
    hlenY hfvslen hshapeS hwsFvs hleafClosed htowerS hdomsS0
    hfvsPlen hwsFvsP htowerP hdomsP0 hshapeP htyRw htyRb hrinst hrenP
    hro hCwR hCbR hTVjK hTVjcl htowerJ hsplen hspLeaf hspScope hcinst
    hmixlen hmixsp hmixFldEq hmixPar hfitRpre hfitC
    (hdePre _) (hdeFld _)
  -- ===== fire the checked equation =====
  have htbody : tbody
      = Expr.mkAppN (.const eqName [ℓA]) [αS, lhsS, rhsS] := by
    have h := (Expr.mkAppN_getApp tbody).symm
    rw [hheadEq, hargs3] at h
    exact h
  have heqlaw : EqLawV V envS mS.cval := mS.eq_lawV
  have hargLeaf : ∀ e : Expr, e ∈ tbody.getAppArgs →
      (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs) ∧
      (∀ l ∈ e.fvarLeaves, l.1 < rP + cnF) := by
    intro e hmem
    have h1 : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs :=
      fun l hl => hleafBody l (fvarLeaves_getAppArgs hmem l hl)
    exact ⟨h1, fun l hl => hfvsLt l (h1 l hl)⟩
  have hmemα : αS ∈ tbody.getAppArgs := by
    rw [hargs3]
    exact List.mem_cons_self ..
  have hmemL : lhsS ∈ tbody.getAppArgs := by
    rw [hargs3]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hmemR : rhsS ∈ tbody.getAppArgs := by
    rw [hargs3]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))
  obtain ⟨hleafα, hltα⟩ := hargLeaf αS hmemα
  obtain ⟨hleafL, hltL⟩ := hargLeaf lhsS hmemL
  obtain ⟨hleafR, hltR⟩ := hargLeaf rhsS hmemR
  obtain ⟨vα, vL, vR, hvα, hvL, hvR, heqLR⟩ := fireS (henv.eqFormerKey heqfE) heqlaw heqfE
    htowerS
    (fun ρ0 => (hTstFacts ρ0).2) (fun ρ0 => (hTstFacts ρ0).1)
    hRbodyDen htbody
    (fun vα vL vR h1 h2 h3 _ => sidesMemS henv hshapeS hwsFvs hΓslen
      hdomsS0 (hsidesTy _) hleafα hltα hleafL hltL hleafR hltR hsat
      vα vL vR h1 h2 h3)
    hzslen hsat hfitS
  -- ===== the right side is the rule's own application =====
  have heqR := reductS henv hro hfvslen hshapeS hwsFvs hleafClosed
    hΓslen hdomsS0 hrhsw hrhsb hRvden hvR hleafR hltR (hdeRhs _)
    hzslen hsat
  -- ===== the left side is the fired redex =====
  have hctorHead : denote mS.cval envS (Level.substFn φ lps us)
      (rP + cnF) (.const (f ctor) lvls)
      = some (mS.cval ctor (Level.substFn φ cvj.levelParams usj)) := by
    rw [denote_const, hfCmE]
    dsimp only
    rw [if_pos (by rw [hCmlps]; exact hlvlsLen), hCmlps, hro.2.2.1]
    exact congrArg some
      (mS.val_params ctor _ hctorE _ _ (fun p hp => (hagree p hp).symm))
  have heqL := pointS (V := V) rfl henv hro rfl hrPmI
    hlenX hlenY hfRnE hRmlps
    hfvslen hshapeS hwsFvs hΓslen hdomsS0 hsat hvL
    hlhead hlarity hlpre hmaj hctorHead hleafL hltL
    hCwR hCbR hTVjK hTVjcl htowerJ hsplen hspLeaf hspScope hcinst hclen
    hRjdec hArgsClen (hdeIdx _) hmixlen hmixsp hmixVal hfitC hidx
  refine ⟨heqL.symm.trans (heqLR.trans heqR), ?_⟩
  -- ===== the truthfulness transport =====
  intro hxsA hysA
  have hzsAnnot : ∀ w ∈ xs.take rP ++ ys.drop cnP, AnnotOkV V ρ w := by
    intro w hw
    rcases List.mem_append.mp hw with hw' | hw'
    · exact hxsA w (List.mem_of_mem_take hw')
    · exact hysA w (List.mem_of_mem_drop hw')
  -- the nested fire's parameter spines: the pins at the two frames
  have hpsPlen : (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))).length
      = cnP := by
    rw [List.length_map, hpinsLen]
  have htkPlen : (fvsP.take rP).length = rP := by
    rw [List.length_take, hfvsPlen]
    omega
  have htkSlen : (fvs.take rP).length = rP := by
    rw [List.length_take, hfvslen]
    omega
  have hpsRen : ∀ (i : Nat) (a a' : Expr),
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)))[i]? = some a →
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)))[i]? = some a' → RenEqT f a a' := by
    intro i a a' ha ha'
    have hi : i < cnP := by
      rcases Nat.lt_or_ge i cnP with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by rw [hpsPlen]; omega)] at ha
        exact nomatch ha
    rw [List.getElem?_map, hpgetd i hi] at ha
    rw [hpinsRget i hi] at ha'
    obtain rfl : a = Expr.instSpine (fvsP.take rP) (rP - 1)
        (pins.getD i default) := (Option.some.inj ha).symm
    obtain rfl : a' = Expr.instSpine (fvs.take rP) (rP - 1)
        ((pins.getD i default).renameConsts f) := (Option.some.inj ha').symm
    show Expr.ErasedEq _ _
    rw [Expr.instSpine_eq_instSeq, Expr.instSpine_eq_instSeq]
    refine Expr.ErasedEq.trans
      (Expr.instSeq_renameConsts (f := f) (fvsP.take rP) (rP - 1) ?_) ?_
    · intro x hx
      obtain ⟨q0, hq0⟩ := List.getElem?_of_mem hx
      have hq0lt : q0 < rP := by
        have := (List.getElem?_eq_some_iff.mp hq0).1
        rw [htkPlen] at this
        exact this
      rw [List.getElem?_take_of_lt hq0lt] at hq0
      obtain ⟨nm, ty, rfl⟩ := hshapeP q0 _ hq0
      exact rfl
    · refine Expr.instSeq_erasedEq_args (fvsP.take rP) (fvs.take rP)
        (rP - 1) (Expr.ErasedEq.rfl _) ?_ (by rw [htkPlen, htkSlen])
      intro k b₁ b₂ hb₁ hb₂
      have hklt : k < rP := by
        rcases Nat.lt_or_ge k rP with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none (by rw [htkPlen]; omega)] at hb₁
          exact nomatch hb₁
      rw [List.getElem?_take_of_lt hklt] at hb₁
      rw [List.getElem?_take_of_lt hklt] at hb₂
      obtain ⟨nm, ty, rfl⟩ := hshapeP k _ hb₁
      obtain ⟨nm', ty', rfl⟩ := hshapeS k _ hb₂
      exact rfl
  have hpsPws : ∀ a ∈ pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)),
      Expr.WScoped rP a := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact instSpine_WScoped (rP - 1)
      (Expr.WScoped.of_not_hasFvar (hpinsWf p hp).1)
      (fun x hx => hwsFvsP x (List.mem_of_mem_take hx))
  have hpsPleaf : ∀ a ∈ pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)),
      ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP := by
    intro a ha l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    rcases fvarLeaves_instSpine (rP - 1) hl with hl' | ⟨x, hx, hlx⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpinsWf p hp).1] at hl'
      exact nomatch hl'
    · exact hleafP l ⟨x, List.mem_of_mem_take hx, hlx⟩
  have hpsRleaf : ∀ a ∈ pins.map (fun p => Expr.instSpine (fvs.take rP)
      (rP - 1) (p.renameConsts f)),
      ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs := by
    intro a ha l hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    rcases fvarLeaves_instSpine (rP - 1) hl with hl' | ⟨x, hx, hlx⟩
    · exfalso
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (by
        rw [hasFvar_renameConsts]
        exact (hpinsWf p hp).1)] at hl'
      exact nomatch hl'
    · exact hleafClosed l ⟨x, List.mem_of_mem_take hx, hlx⟩
  exact annotS henv hro hfvslen hshapeS hwsFvs hleafClosed
    hΓslen hdomsS0 hzslen hsat htowerS htyw htyRw
    (show Expr.ErasedEq (tyA.renameConsts f) (tyA.renameConsts f) from
      Expr.ErasedEq.rfl _)
    hopenP hCvLw hCwR
    (show Expr.ErasedEq
        ((cvj.type.instantiateLevelParams cvj.levelParams lvls).renameConsts f)
        ((cvj.type.instantiateLevelParams cvj.levelParams lvls).renameConsts f)
      from Expr.ErasedEq.rfl _)
    hpsPlen hpinsRlen hpsRen hpsPws hpsPleaf hpsRleaf
    hcinstP hopenXP hrinst hcinst hrhsw hinstLam (hdePre _) (hdeFld _)
    (hdeLam _) hRvden (hRvFacts ρ).1 hzsAnnot

end Setlec.SetR
