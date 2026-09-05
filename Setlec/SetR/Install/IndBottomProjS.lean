import Setlec.SetR.Install.IndStagesS

/-!
# The projection bottom, assembled (task #148, T5 c4)

`indBottomProjS` fires the checked `proj_i.iota` theorem of a stored
degenerate projection recursor as its `RecRulesV` law.

The projection install runs *different checks* from the iota install
(`checkProjShape`/`checkProjRule`/`checkProjIota`), so two of the plain
bottom's stages have no inputs here — and neither is needed:

* **the zipper is syntactic.**  `checkProjIota`'s `domsMatchAux` pins
  the statement's telescope domains to the constructor's renamed ones,
  so the two denoted contexts are *equal* (`towerCtxEqD` +
  `PiTele.det`) and the statement's satisfaction is the constructor's
  fit read at the fired spine — no strong induction, no domain walks;
* **the reduct is a β-contraction.**  `checkProjRule` pins the rule to
  the constructor telescope's λ-tower returning the field's bound
  variable, and its λ-domains to the constructor's on the nose, so the
  tower's context is again the statement's (`towerCtxEq`), the
  descent's memberships are the zipper's own, and `lamTowerStepS`
  delivers the equality *and* the truthfulness transport in one step
  (`projBodyValue` names the contractum).

`fireS` and `pointS` are reused verbatim: a projection fire is a
`.plain` fire at `mI = rP = cnP`, so its spine is the frame's openers
and its index walk is empty.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

set_option maxHeartbeats 12800000 in
theorem indBottomProjS : IndBottomProjS V := by
  intro μ envS mS f hro heqfE Rn lps tyA mI rP ciRm hfRnE hRmlps ctor
    cvj cnP cnF hctorE ciCm hfCmE hCmlps hCw hCb hClp i hmIrP hcnPrP
    hilt cbinders cbody hCstrip hcbodyArity Dc usc hcbodyHead rhsA
    hrhsw hrhsb rbinders hrhsAstrip hrdomsEq hrhsKey stmtTy hSw hSb
    hthm fvs tbody ℓA αS lhsS rhsS hopen hheadEq hargs3 hlhead hlarity
    hlpre hmaj hrhsSpin sbinders sbody hSstrip hdomsSC hsidesTy
  intro φ us huslen
  have hvp : ValParams envS mS.cval := mS.val_params
  have henv := mS.toHyp (Level.substFn φ lps us)
  have hcl' := mS.cval_closed
  have hrPmI : rP ≤ mI := by omega
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
  have hshapeS : ∀ (i0 : Nat) (x : Expr), fvs[i0]? = some x →
      ∃ nm ty, x = Expr.fvar i0 nm ty := by
    intro i0 x hx
    obtain ⟨nm, ty, hx'⟩ := openPisAtFvars_index _ _ _ hopen i0 x hx
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
  have hdomsS0 : ∀ (i0 : Nat) (x : Expr), fvs[i0]? = some x →
      denote mS.cval envS (Level.substFn φ lps us) i0 (Expr.fvarTypeD x)
        = some (Γs.getD (rP + cnF - 1 - i0) default) := by
    intro i0 x hx
    have h := hdomsS0A i0 x hx
    rwa [Nat.zero_add] at h
  have hRbodyDen : denote mS.cval envS (Level.substFn φ lps us)
      (rP + cnF) tbody = some Rbody := by
    have h := hRbodyDenA
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
  obtain ⟨Γj, Rj, htowerJ, hΓjlen0, hRjdenA, hdomsJ⟩ :=
    stripPis_denoteTele (cnP + cnF) hCstrip hTVj0
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
  -- ===== the statement's context IS the constructor's =====
  obtain ⟨Γs2, Rbody2, htowerS2, hΓs2len, hRbody2den, hdomsS2⟩ :=
    stripPis_denoteTele (cnP + cnF) hSstrip hTstden
  have hKeq : cnP + cnF = rP + cnF := by omega
  have hΓs2 : Γs2 = Γs := by
    have h := htowerS2
    rw [hKeq] at h
    exact (PiTele.det htowerS h).1.symm
  have hΓsJ : Γs = Γj := by
    refine (hΓs2 ▸ towerCtxEqD (cval := mS.cval) (env := envS)
      (ψ := Level.substFn φ lps us)
      (Expr.stripPis_length _ hSstrip) (Expr.stripPis_length _ hCstrip)
      (by rw [hΓs2len]) hΓjlen0 hdomsS2 hdomsJ ?_)
    intro i0 b b' hi0 hb hb'
    have hdom := hdomsSC i0 b b' hi0 hb hb'
    have hopeners : ∀ a ∈ openFvars 0 i0,
        Expr.ErasedEq (a.renameConsts f) a := by
      intro a ha
      obtain ⟨q0, hq0⟩ := List.getElem?_of_mem ha
      have hq0lt : q0 < i0 := by
        have := (List.getElem?_eq_some_iff.mp hq0).1
        rwa [openFvars_length] at this
      rw [openFvars_getElem? (d := 0) hq0lt] at hq0
      obtain rfl : a = Expr.fvar (0 + q0) Name.anonymous (.sort .zero) :=
        (Option.some.inj hq0).symm
      exact rfl
    have hee := Expr.instSeq_renameConsts (f := f) (openFvars 0 i0)
      (i0 - 1) (X := b'.2.1) hopeners
    rw [hdom]
    rw [← denote_erasedEq hee (0 + i0),
      denote_renameConsts hro]
  -- ===== the fired spine =====
  have hxtlen : (xs.take rP).length = rP := by
    rw [List.length_take, hlenX]
    omega
  have hzslen : (xs.take rP ++ ys.drop cnP).length = rP + cnF := by
    rw [List.length_append, hxtlen, List.length_drop, hlenY]
    omega
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
  have hpar : ∀ i0, i0 < cnP →
      interp V ρ (ys.getD i0 default)
        = interp V ρ (xs.getD i0 default) :=
    fun i0 hi0 => hparP i0 hi0 (by omega)
  have hzsVal : ∀ q, q < rP + cnF →
      interp V ρ ((xs.take rP ++ ys.drop cnP).getD q default)
        = interp V ρ (ys.getD q default) := by
    intro q hq
    rcases Nat.lt_or_ge q rP with hqc | hqc
    · rw [hzsPre q hqc]
      exact (hpar q (by omega)).symm
    · have hz := hzsFld (q - rP) (by omega)
      rw [show rP + (q - rP) = q from by omega,
        show cnP + (q - rP) = q from by omega] at hz
      rw [hz]
  -- ===== the zipper: the constructor fit, read at the fired spine ==
  have hchainC := teleFitV_to_chain (cnP + cnF) htowerJ hlenY hfitC
  have hchainEq : ∀ q, q ≤ rP + cnF →
      chainE V ρ ((xs.take rP ++ ys.drop cnP).take q)
        = chainE V ρ (ys.take q) := by
    intro q hq
    funext i0
    have htq : ((xs.take rP ++ ys.drop cnP).take q).length = q := by
      rw [List.length_take, hzslen]
      omega
    have htq' : (ys.take q).length = q := by
      rw [List.length_take, hlenY]
      omega
    by_cases hiq : i0 < q
    · rw [chainE_lt (by omega), chainE_lt (by omega), htq, htq']
      have hlt : q - 1 - i0 < q := by omega
      rw [show ((xs.take rP ++ ys.drop cnP).take q).getD (q - 1 - i0)
            default
          = (xs.take rP ++ ys.drop cnP).getD (q - 1 - i0) default from by
          rw [List.getD, List.getD, List.getElem?_take_of_lt hlt],
        show (ys.take q).getD (q - 1 - i0) default
          = ys.getD (q - 1 - i0) default from by
          rw [List.getD, List.getD, List.getElem?_take_of_lt hlt]]
      exact hzsVal _ (by omega)
    · rw [chainE_ge (by omega), chainE_ge (by omega), htq, htq']
  have hallK : ∀ m, m < rP + cnF →
      interp V ρ ((xs.take rP ++ ys.drop cnP).getD m default)
        ∈ˢ interp V (chainE V ρ ((xs.take rP ++ ys.drop cnP).take m))
          (Γs.getD (rP + cnF - 1 - m) default) := by
    intro m hm
    have h1 := hchainC m (by omega)
    rw [hchainEq m (by omega), hzsVal m hm, hΓsJ,
      show rP + cnF - 1 - m = cnP + cnF - 1 - m from by omega]
    exact h1
  have hsat : Sat V Γs (chainE V ρ (xs.take rP ++ ys.drop cnP)) :=
    sat_of_tower htowerS hzslen hallK
  have hfitS : TeleFitV V ρ Tst (xs.take rP ++ ys.drop cnP)
      (VExpr.instSeq (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) Rbody) :=
    teleFitV_of_tower (rP + cnF) htowerS hzslen hallK
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
  -- ===== the plain fire's spine data (a projection fire is plain) ==
  have hsplen : (fvs.take cnP ++ fvs.drop rP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, List.length_drop, hfvslen]
    omega
  have hspIdx : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      ∃ nm ty, x = Expr.fvar q nm ty ∧ x ∈ fvs ∧ q < rP + cnF := by
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
      exact ⟨nm, ty, rfl, List.mem_of_getElem? hx, by omega⟩
    · rw [List.getElem?_append_right
        (by rw [List.length_take, hfvslen]; omega),
        List.length_take, hfvslen,
        show min cnP (rP + cnF) = cnP from by omega,
        List.getElem?_drop] at hx
      obtain ⟨nm, ty, hsh⟩ := hshapeS (rP + (q - cnP)) x hx
      rw [show rP + (q - cnP) = q from by omega] at hsh hx
      exact ⟨nm, ty, hsh, List.mem_of_getElem? hx, by omega⟩
  have hspLeaf : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2.1 l.2.2 ∈ fvs ∧ l.1 < rP + (q + 1 - cnP) := by
    intro q x hx l hl
    obtain ⟨nm, ty, rfl, hmem, hidxlt⟩ := hspIdx q x hx
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨hmem, by omega⟩
    · have hwsty := hwsFvs _ hmem
      have hwsty' : Expr.WScoped q ty := by
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
    obtain ⟨nm, ty, rfl, hmem, -⟩ := hspIdx q x hx
    exact ⟨hwsFvs _ hmem, hbFvs _ hmem⟩
  have hmixsp : ∀ (q : Nat) (x : Expr),
      (fvs.take cnP ++ fvs.drop rP)[q]? = some x →
      ∃ w0, denote mS.cval envS (Level.substFn φ lps us) (rP + cnF) x
          = some w0 ∧
        (xs.take rP ++ ys.drop cnP)[q]? = some (VExpr.instSeq
          (xs.take rP ++ ys.drop cnP) (rP + cnF - 1) w0) := by
    intro q x hx
    obtain ⟨nm, ty, rfl, -, hqlt⟩ := hspIdx q x hx
    refine ⟨.bvar (rP + cnF - 1 - q),
      denote_fvar mS.cval envS (Level.substFn φ lps us) (rP + cnF)
        q nm ty, ?_⟩
    rw [instSeq_bvar_full hqlt hzslen, List.getD]
    rcases hz : (xs.take rP ++ ys.drop cnP)[q]? with _ | v
    · rw [List.getElem?_eq_none_iff, hzslen] at hz
      omega
    · rfl
  -- ===== the constructor run at the statement frame =====
  have hCstripR := stripPis_renameConsts (f := f) (cnP + cnF) hCstrip
  obtain ⟨⟨cdoms, cres⟩, hcinst⟩ := Option.isSome_iff_exists.mp
    (instPisAt_isSome_of_stripPis (fvs.take cnP ++ fvs.drop rP)
      (by rw [hsplen, hCstripR]; rfl))
  have hclen : cres.getAppArgs.length = cnP + (mI - rP) := by
    have h1 := instPisAt_fvar_residual_arity
      (fvs.take cnP ++ fvs.drop rP) hcinst
      (fun x hx => by
        obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
        obtain ⟨nm, ty, hsh, -, -⟩ := hspIdx q x hq
        exact ⟨q, nm, ty, hsh⟩)
      (bs := cbinders.map (fun b => (b.1, b.2.1.renameConsts f, b.2.2)))
      (body := cbody.renameConsts f)
      (by rw [hsplen]; exact hCstripR)
    rw [getAppArgs_length_renameConsts] at h1
    rw [h1, hcbodyArity]
    omega
  -- `Rj`'s decomposition and its arity
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
  have hArgsClen : vArgsC.length = cnP + (mI - rP) := by
    rw [hcspJ.length, List.length_map, hcbodyArity]
    omega
  -- ===== the left side is the fired redex =====
  have hconstDenC : denote mS.cval envS (Level.substFn φ lps us)
      (rP + cnF) (.const (f ctor) (cvj.levelParams.map .param))
      = some (mS.cval ctor
        (Level.substFn φ cvj.levelParams usj)) := by
    have hctorLev : mS.cval ctor (Level.substFn φ cvj.levelParams usj)
        = mS.cval ctor (Level.substFn φ lps us) :=
      mS.val_params ctor _ hctorE _ _ (fun p hp => hagree p hp)
    rw [denote_const, hfCmE]
    dsimp only
    rw [if_pos (by rw [hCmlps, List.length_map]), hCmlps,
      show Level.substFn (Level.substFn φ lps us) cvj.levelParams
          (cvj.levelParams.map .param)
        = Level.substFn φ lps us from
        funext fun _ => Level.substFn_map_param,
      hro.2.2, hctorLev]
  have hdeIdxNil : DefEqListW μ envS mS.cval
      (Level.substFn φ lps us) (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP) := by
    rw [show mI - rP = 0 from by omega, List.take_zero,
      List.drop_eq_nil_of_le (by rw [hclen]; omega)]
    trivial
  have heqL := pointS (V := V) rfl henv hro rfl hrPmI hlenX hlenY
    hfRnE hRmlps hfvslen hshapeS hwsFvs hΓslen hdomsS0 hsat hvL
    hlhead hlarity hlpre
    (show Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
        (Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
          (fvs.take cnP ++ fvs.drop rP)) from by
      rw [hmaj]
      exact Expr.ErasedEq.rfl _)
    hconstDenC hleafL hltL hCwR hCbR hTVjK hTVjcl htowerJ hsplen
    hspLeaf hspScope hcinst hclen hRjdec hArgsClen hdeIdxNil
    (show (xs.take rP ++ ys.drop cnP).length = cnP + cnF from by
      rw [hzslen]; omega)
    hmixsp (fun q hq => hzsVal q (by omega)) hfitC hidx
  -- ===== the reduct: the rule λ-tower's β-contractum =====
  obtain ⟨Γlam, C, hRvEq, hΓlamlen, hCden, hdomsLam⟩ :=
    stripLams_denoteTele (cnP + cnF) hrhsAstrip hRvden
  have hΓlamJ : Γlam = Γj :=
    towerCtxEq (Expr.stripLams_length _ hrhsAstrip)
      (Expr.stripPis_length _ hCstrip) hΓlamlen hΓjlen0 hdomsLam hdomsJ
      hrdomsEq
  have hCval : C = .bvar (cnP + cnF - 1 - (cnP + i)) :=
    projBodyValue hilt hCden
  have hmemLam : ∀ k, k < cnP + cnF →
      interp V ρ ((xs.take rP ++ ys.drop cnP).getD k default)
        ∈ˢ interp V (chainE V ρ ((xs.take rP ++ ys.drop cnP).take k))
          (Γlam.getD (cnP + cnF - 1 - k) default) := by
    intro k hk
    rw [hΓlamJ, ← hΓsJ, show cnP + cnF - 1 - k = rP + cnF - 1 - k from
      -- task #77: `rw [hcnPrP]`, not `by omega` (15.2 s in this context)
      by rw [hcnPrP]]
    exact hallK k (by omega)
  have hstep := lamTowerStepS (V := V) (C := C) (cnP + cnF)
    (Nat.le_refl _) hΓlamlen (by rw [hzslen]; omega) hmemLam
  rw [List.take_of_length_le (by rw [hzslen]; omega)] at hstep
  rw [hRvEq]
  refine ⟨heqL.symm.trans (heqLR.trans ?_), ?_⟩
  · -- the statement's right side is the contractum
    have hvRval : vR = .bvar (rP + cnF - 1 - (rP + i)) := by
      refine projRhsValue (cval := mS.cval) (env := envS)
        (ψ := Level.substFn φ lps us) hshapeS hfvslen hilt ?_
      rw [← hrhsSpin]
      exact hvR
    rw [hstep.1, hvRval, hCval,
      show cnP + cnF - 1 - (cnP + i) = rP + cnF - 1 - (rP + i) from
        -- task #77: `rw [hcnPrP]`, not `by omega` (15.2 s in this context)
        by rw [hcnPrP], Nat.sub_self, List.take_zero]
    rfl
  · -- the truthfulness transport, from the same descent
    intro hxsA hysA
    have hzsAnnot : ∀ w ∈ xs.take rP ++ ys.drop cnP, AnnotOkV V ρ w := by
      intro w hw
      rcases List.mem_append.mp hw with hw' | hw'
      · exact hxsA w (List.mem_of_mem_take hw')
      · exact hysA w (List.mem_of_mem_drop hw')
    exact hstep.2 (hRvEq ▸ (hRvFacts ρ).1) hzsAnnot

end Setlec.SetR
