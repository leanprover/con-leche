import Setlec.SetR.Install.IndStagesS

/-!
# The plain bottom, assembled (task #148, T5 c2)

`indBottomPlainS` glues the sealed stages of
`Setlec/SetR/Install/IndStagesS.lean` into `IndBottomPlainS`: the
checked canonical `iota_j` theorem, fired at an arbitrary fitting
spine, yields the stored `.plain` rule's `RecRulesV` law — the
interp-equality of redex and reduct (`pointS` ∘ `fireS` ∘ `reductS`
at the zipped chain from `zipperS`) together with the truthfulness
transport (`annotS`).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

set_option maxHeartbeats 12800000 in
theorem indBottomPlainS : IndBottomPlainS V := by
  intro μ envS mS f hro heqfE Rn lps tyA mI rP htyw htyb ciRm hfRnE
    hRmlps ctor cvj cnP cnF hctorE ciCm hfCmE hCmlps hCw hCb hClp hrPmI
    hplainLe rhsA hrhsw hrhsb hrhsKey stmtTy hSw hSb hthm fvs tbody ℓA
    αS lhsS rhsS hopen hheadEq hargs3 hlhead hlarity hlpre hmaj hCstrips
    cdoms cres hcinst hclen rdoms rrest hrinst fvsP restP hopenP cdomsP
    crestP hcinstP xFvsP ldomsE hopenXP hstripRhs ldomsL lrest2 hinstLam
    hdeIdx hdePre hdeFld hdePars hdeLam hdeRhs hsidesTy
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
  -- ===== the constructor's assignment and tower =====
  have hagree : ∀ p ∈ cvj.levelParams,
      Level.substFn φ cvj.levelParams usj p
        = Level.substFn φ lps us p := by
    intro p hp
    have hmm : (cvj.levelParams.map fun q => Level.subst lps us (.param q))
        = (cvj.levelParams.map Level.param).map (Level.subst lps us) := by
      rw [List.map_map]
      rfl
    calc Level.substFn φ cvj.levelParams usj p
        = Level.substFn φ cvj.levelParams
            ((cvj.levelParams.map Level.param).map (Level.subst lps us))
            p := by rw [hlev, hmm]
      _ = Level.substFn (Level.substFn φ lps us) cvj.levelParams
            (cvj.levelParams.map Level.param) p :=
          Level.substFn_map_subst (by rw [List.length_map]) hp
      _ = Level.substFn φ lps us p := Level.substFn_map_param
  have hTVj0 : denote mS.cval envS (Level.substFn φ lps us) 0 cvj.type
      = some TVj := by
    have h := hTVj
    unfold denoteClosed at h
    rw [denote_instLevels hvp] at h
    rwa [denote_params_ext hvp hagree 0 cvj.type hClp] at h
  obtain ⟨⟨bsC, cbody⟩, hstripC⟩ := Option.isSome_iff_exists.mp hCstrips
  obtain ⟨Γj, Rj, htowerJ, hΓjlen0, hRjdenA, hdomsJ⟩ :=
    stripPis_denoteTele (cnP + cnF) hstripC hTVj0
  have hTVjcl : VExpr.Closed TVj := denote_closed hcl' hCw hCb hTVj0
  have hCwR : (cvj.type.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact hCw
  have hCbR : (cvj.type.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact hCb
  have hTVjK : denote mS.cval envS (Level.substFn φ lps us) (rP + cnF)
      (cvj.type.renameConsts f) = some TVj := by
    rw [denote_depth_closed hcl' hCwR hCbR]
    show denote _ _ _ 0 _ = _
    rw [denote_renameConsts hro]
    exact hTVj0
  have htyRw : (tyA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact htyw
  have htyRb : (tyA.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact htyb
  -- ===== `Rj`'s decomposition and its arity =====
  have hcbApp : Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
      cbody
      = Expr.mkAppN
          (Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
            cbody.getAppFn)
          (cbody.getAppArgs.map
            (Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
              ·)) := by
    have hcb : cbody = Expr.mkAppN cbody.getAppFn cbody.getAppArgs :=
      (Expr.mkAppN_getApp cbody).symm
    have h1 : Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
        cbody
        = Expr.instSeq (openFvars 0 (cnP + cnF)) (cnP + cnF - 1)
          (Expr.mkAppN cbody.getAppFn cbody.getAppArgs) := by
      conv => lhs; rw [hcb]
    rw [h1, Expr.instSeq_mkAppN]
  have hRjdenA' := hRjdenA
  rw [Nat.zero_add, hcbApp] at hRjdenA'
  obtain ⟨vHC, vArgsC, hvHCden, hcspJ, hRjdec⟩ :=
    denote_mkAppN_inv hRjdenA'
  have hcbodyArity : cbody.getAppArgs.length = cnP + (mI - rP) := by
    have hstripR := stripPis_renameConsts (f := f) (cnP + cnF) hstripC
    have hsplen : (fvs.take cnP ++ fvs.drop rP).length = cnP + cnF := by
      rw [List.length_append, List.length_take, List.length_drop,
        hfvslen]
      omega
    have h1 := instPisAt_fvar_residual_arity
      (fvs.take cnP ++ fvs.drop rP) hcinst
      (fun x hx => by
        rcases List.mem_append.mp hx with hx' | hx'
        · obtain ⟨q, hq⟩ := List.getElem?_of_mem hx'
          have hq' : fvs[q]? = some x := by
            have hql : q < cnP := by
              have := (List.getElem?_eq_some_iff.mp hq).1
              rw [List.length_take] at this
              omega
            rw [← List.getElem?_take_of_lt hql]
            exact hq
          obtain ⟨nm, ty, rfl⟩ := hshapeS q x hq'
          exact ⟨q, nm, ty, rfl⟩
        · obtain ⟨q, hq⟩ := List.getElem?_of_mem hx'
          rw [List.getElem?_drop] at hq
          obtain ⟨nm, ty, rfl⟩ := hshapeS (rP + q) x hq
          exact ⟨rP + q, nm, ty, rfl⟩)
      (bs := bsC.map (fun b => (b.1, b.2.1.renameConsts f, b.2.2)))
      (body := cbody.renameConsts f)
      (by rw [hsplen]; exact hstripR)
    rw [getAppArgs_length_renameConsts] at h1
    rw [← h1, hclen]
  have hArgsClen : vArgsC.length = cnP + (mI - rP) := by
    rw [hcspJ.length, List.length_map, hcbodyArity]
  -- ===== the fitting prefix and parameter equalities =====
  have htakexs : (xs ++ [VExpr.mkAppN
      (mS.cval ctor (Level.substFn φ cvj.levelParams usj)) ys]).take rP
      = xs.take rP := by
    rw [List.take_append_of_le_length (by rw [hlenX]; omega)]
  obtain ⟨restRpre, hfitRpre⟩ := hfitR.take rP
  rw [htakexs] at hfitRpre
  have hpar : ∀ i, i < cnP →
      interp V ρ (ys.getD i default) = interp V ρ (xs.getD i default) :=
    fun i hi => hparP i hi (by omega)
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
  -- ===== the zipper: satisfaction and the statement fit =====
  have hzslen : (xs.take rP ++ ys.drop cnP).length = rP + cnF := by
    rw [List.length_append, List.length_take, List.length_drop, hlenX,
      hlenY]
    omega
  -- the plain fire's spine data: the frame's own openers
  have hsplen : (fvs.take cnP ++ fvs.drop rP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, List.length_drop, hfvslen]
    omega
  have hspIdx : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      ∃ nm ty, x = Expr.fvar
          (if q < cnP then q else rP + (q - cnP)) nm ty ∧
        x ∈ fvs ∧ (if q < cnP then q else rP + (q - cnP))
          < rP + (q + 1 - cnP) := by
    intro q x hx
    have hq : q < cnP + cnF := by
      rcases Nat.lt_or_ge q (cnP + cnF) with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by omega)] at hx
        exact nomatch hx
    by_cases hqc : q < cnP
    · rw [List.getElem?_append_left
        (by rw [List.length_take, hfvslen]; omega),
        List.getElem?_take_of_lt hqc] at hx
      obtain ⟨nm, ty, rfl⟩ := hshapeS q x hx
      exact ⟨nm, ty, by rw [if_pos hqc], List.mem_of_getElem? hx,
        by rw [if_pos hqc]; omega⟩
    · rw [List.getElem?_append_right
        (by rw [List.length_take, hfvslen]; omega),
        List.length_take, hfvslen,
        show min cnP (rP + cnF) = cnP from by omega,
        List.getElem?_drop] at hx
      obtain ⟨nm, ty, rfl⟩ := hshapeS (rP + (q - cnP)) x hx
      exact ⟨nm, ty, by rw [if_neg hqc], List.mem_of_getElem? hx,
        by rw [if_neg hqc]; omega⟩
  have hspLeaf : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP) := by
    intro q x hx l hl
    obtain ⟨nm, ty, rfl, hmem, hidx⟩ := hspIdx q x hx
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨hmem, hidx⟩
    · have hwsty := hwsFvs _ hmem
      have hwsty' : Expr.WScoped
          (if q < cnP then q else rP + (q - cnP)) ty := by
        have h' := hwsty
        simp only [Expr.WScoped] at h'
        exact h'.2
      have hlt := Expr.fvarLeaves_lt_of_wscoped hwsty' l hl'
      refine ⟨hleafClosed l ⟨_, hmem, ?_⟩, by omega⟩
      rw [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl'
  have hspScope : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      Expr.WScoped (rP + cnF) x ∧ x.looseBVarsBounded 0 = true := by
    intro q x hx
    obtain ⟨nm, ty, rfl, hmem, _⟩ := hspIdx q x hx
    exact ⟨hwsFvs _ hmem, hbFvs _ hmem⟩
  have hmixlen : (xs.take cnP ++ ys.drop cnP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, List.length_drop, hlenX,
      hlenY]
    omega
  have hzsPre : ∀ n, n < rP →
      (xs.take rP ++ ys.drop cnP).getD n default
        = xs.getD n default := by
    intro n hn
    rw [List.getD, List.getElem?_append_left
      (by rw [List.length_take, hlenX]; omega),
      List.getElem?_take_of_lt hn]
    rfl
  have hzsFld : ∀ j, j < cnF →
      (xs.take rP ++ ys.drop cnP).getD (rP + j) default
        = ys.getD (cnP + j) default := by
    intro j hj
    rw [List.getD, List.getElem?_append_right
      (by rw [List.length_take, hlenX]; omega),
      List.length_take, hlenX, show min rP mI = rP from by omega,
      List.getElem?_drop, show rP + j - rP = j from by omega]
    rfl
  have hmixsp : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      ∃ w0, denote mS.cval envS (Level.substFn φ lps us) (rP + cnF) x
          = some w0 ∧
        (xs.take cnP ++ ys.drop cnP)[q]? = some (VExpr.instSeq
          (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) w0) := by
    intro q x hx
    have hq : q < cnP + cnF := by
      rcases Nat.lt_or_ge q (cnP + cnF) with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by omega)] at hx
        exact nomatch hx
    obtain ⟨nm, ty, rfl, hmem, _⟩ := hspIdx q x hx
    have hidxK : (if q < cnP then q else rP + (q - cnP)) < rP + cnF := by
      by_cases hqc : q < cnP
      · rw [if_pos hqc]; omega
      · rw [if_neg hqc]; omega
    refine ⟨.bvar (rP + cnF - 1
        - (if q < cnP then q else rP + (q - cnP))),
      denote_fvar mS.cval envS (Level.substFn φ lps us) (rP + cnF)
        _ nm ty, ?_⟩
    rw [instSeq_bvar_full hidxK hzslen]
    by_cases hqc : q < cnP
    · rw [if_pos hqc, List.getElem?_append_left
        (by rw [List.length_take, hlenX]; omega),
        List.getElem?_take_of_lt hqc, hzsPre q (by omega), List.getD]
      rcases hx0 : xs[q]? with _ | v
      · rw [List.getElem?_eq_none_iff, hlenX] at hx0
        omega
      · rfl
    · rw [if_neg hqc, List.getElem?_append_right
        (by rw [List.length_take, hlenX]; omega),
        List.length_take, hlenX, show min cnP mI = cnP from by omega,
        List.getElem?_drop, show cnP + (q - cnP) = q from by omega,
        hzsFld (q - cnP) (by omega),
        show cnP + (q - cnP) = q from by omega, List.getD]
      rcases hy0 : ys[q]? with _ | v
      · rw [List.getElem?_eq_none_iff, hlenY] at hy0
        omega
      · rfl
  have hmixFldEq : ∀ j, j < cnF →
      (xs.take cnP ++ ys.drop cnP).getD (cnP + j) default
        = ys.getD (cnP + j) default := by
    intro j hj
    rw [List.getD, List.getElem?_append_right
      (by rw [List.length_take, hlenX]; omega),
      List.length_take, hlenX, show min cnP mI = cnP from by omega,
      List.getElem?_drop, show cnP + j - cnP = j from by omega]
    rfl
  have hmixPar : ∀ q, q < cnP →
      interp V ρ ((xs.take cnP ++ ys.drop cnP).getD q default)
        = interp V ρ (ys.getD q default) := by
    intro q hq
    have h0 : (xs.take cnP ++ ys.drop cnP).getD q default
        = xs.getD q default := by
      rw [List.getD, List.getD, List.getElem?_append_left
        (by rw [List.length_take, hlenX]; omega),
        List.getElem?_take_of_lt hq]
    rw [h0]
    exact (hpar q hq).symm
  have hmixVal : ∀ q, q < cnP + cnF →
      interp V ρ ((xs.take cnP ++ ys.drop cnP).getD q default)
        = interp V ρ (ys.getD q default) := by
    intro q hq
    rcases Nat.lt_or_ge q cnP with hqc | hqc
    · exact hmixPar q hqc
    · rw [show q = cnP + (q - cnP) from by omega]
      exact congrArg _ (hmixFldEq (q - cnP) (by omega))
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
  -- the plain fire's major head: the parameter-mapped constructor
  have hconstDenC : denote mS.cval envS (Level.substFn φ lps us)
      (rP + cnF) (.const (f ctor) (cvj.levelParams.map .param))
      = some (mS.cval ctor
        (Level.substFn φ cvj.levelParams usj)) := by
    have hctorLev : mS.cval ctor (Level.substFn φ cvj.levelParams usj)
        = mS.cval ctor (Level.substFn φ lps us) := by
      refine mS.val_params ctor _ hctorE _ _ ?_
      intro p hp
      exact hagree p hp
    rw [denote_const, hfCmE]
    dsimp only
    rw [if_pos (by rw [hCmlps, List.length_map]), hCmlps,
      show Level.substFn (Level.substFn φ lps us) cvj.levelParams
          (cvj.levelParams.map .param)
        = Level.substFn φ lps us from
        funext fun _ => Level.substFn_map_param,
      hro.2.2.1, hctorLev]
  have heqL := pointS (V := V) rfl henv hro rfl hrPmI
    hlenX hlenY hfRnE hRmlps
    hfvslen hshapeS hwsFvs hΓslen hdomsS0 hsat hvL
    hlhead hlarity hlpre
    (show Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
        (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
          (fvs.take cnP ++ fvs.drop rP)) from by
      rw [hmaj]
      exact Expr.ErasedEq.rfl _)
    hconstDenC hleafL hltL
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
  -- the plain fire's parameter spines: the two frames' own prefixes
  have hpsPlen : (fvsP.take cnP).length = cnP := by
    rw [List.length_take, hfvsPlen]
    omega
  have hpsRlen : (fvs.take cnP).length = cnP := by
    rw [List.length_take, hfvslen]
    omega
  have hpsRen : ∀ (i : Nat) (a a' : Expr), (fvsP.take cnP)[i]? = some a →
      (fvs.take cnP)[i]? = some a' →
      RenEqT f a a' := by
    intro i a a' ha ha'
    have hi : i < cnP := by
      rcases Nat.lt_or_ge i cnP with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by rw [hpsPlen]; omega)] at ha
        exact nomatch ha
    rw [List.getElem?_take_of_lt hi] at ha
    rw [List.getElem?_take_of_lt hi] at ha'
    obtain ⟨nm, ty, rfl⟩ := hshapeP i a ha
    obtain ⟨nm', ty', rfl⟩ := hshapeS i a' ha'
    exact RenEqT.fvar
  have hpsPws : ∀ a ∈ fvsP.take cnP, Expr.WScoped rP a :=
    fun a ha => hwsFvsP a (List.mem_of_mem_take ha)
  have hpsPleaf : ∀ a ∈ fvsP.take cnP, ∀ l ∈ a.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsP := by
    intro a ha l hl
    rcases openPisAtFvars_leaves _ hopenP l
      (Or.inr ⟨a, List.mem_of_mem_take ha, hl⟩) with h0 | h0
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htyw] at h0
      exact nomatch h0
    · exact h0
  have hpsRleaf : ∀ a ∈ fvs.take cnP, ∀ l ∈ a.fvarLeaves,
      Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs :=
    fun a ha l hl => hleafClosed l ⟨a, List.mem_of_mem_take ha, hl⟩
  exact annotS henv hro hfvslen hshapeS hwsFvs hleafClosed
    hΓslen hdomsS0 hzslen hsat htowerS htyw htyRw
    (show Expr.ErasedEq (tyA.renameConsts f) (tyA.renameConsts f) from
      Expr.ErasedEq.rfl _)
    hopenP hCw hCwR
    (show Expr.ErasedEq (cvj.type.renameConsts f)
        (cvj.type.renameConsts f) from Expr.ErasedEq.rfl _)
    hpsPlen hpsRlen hpsRen hpsPws hpsPleaf hpsRleaf
    hcinstP hopenXP hrinst hcinst hrhsw hinstLam (hdePre _) (hdeFld _)
    (hdeLam _) hRvden (hRvFacts ρ).1 hzsAnnot

end Setlec.SetR
