import Setlec.TTVerify.StructEtaCertStep

/-!
# The pair-eta certificate (task #130)

`PairEtaCertStepTT`, the obligation §13 recorded as blocked and task
#130 unblocked.  With `pairEtaCert` now running
`projParamCert entry us' [A, B]`, the certificate records exactly what
`HasType.psigmaEta` asks for and the proof is the shape the other three
certificates in `stuckIrrel` already had:

1. identify the family through the pinned recursor — `PSigma'`, by the
   same four-way refutation `unitLike_eq_punit` uses;
2. turn the new certificate into `⊢ ⟦A⟧ : Sort u` and
   `⊢ ⟦B⟧ : ⟦A⟧ → Sort v` (`certs_typed`, then
   `projEntry_tele_premises` — the #129 lemma, reused unchanged);
3. type the stuck side at the pair type;
4. `psigmaEta`, then congruence for the four certified arguments.

**The levels need no transport.**  The certificate runs at `us'`, the
*type*'s levels, which is where `A` and `B` sit and where `psigmaEta`
names its premises.  That was the implementer's first deviation from
the request's wording and it is the reason step 2 is one `rw` rather
than an `isEquiv` argument.
-/

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode; the seven gated checks
reduce definitionally at `.ttModel`. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

/-- **Only `PSigma'` passes the pair-eta test**: a reserved recursor
with one two-field rule and no indices.  The same refutation as
`unitLike_eq_punit`, at a different rule shape. -/
theorem pairLike_eq_psigma {env : Env} (m : EnvTT env) {c' : Name}
    {cvr : ConstantVal} {mI rP : Nat} {rr : RecRule}
    (hfr : env.find? (c'.str "rec") = some (.recInfo cvr mI rP [rr]))
    (hnf : rr.nfields = 2) (hmi : mI = rP)
    (hres : reservedBasisNames.contains (c'.str "rec") = true) :
    c' = psigmaName ∧ rr.ctor = psigmaMkName := by
  have hpin : pinnedInfoT (c'.str "rec") = .recInfo cvr mI rP [rr] :=
    ((m.basis_pinned _ _ hfr hres).1 rfl).symm
  have hc : c' = psigmaName := by
    rcases pinnedInfoT_recInfo_cases hpin with
      he | he | he | he | he | he | he
    · rw [he] at hpin
      rw [show pinnedInfoT (eqName.str "rec") = eqRecA from rfl] at hpin
      simp only [eqRecA, ConstantInfo.recInfo.injEq] at hpin
      omega
    · rw [he] at hpin
      rw [show pinnedInfoT (natName.str "rec") = natRecA from rfl] at hpin
      simp [natRecA] at hpin
    · exact (Name.str.injEq ..  ▸ he).1
    · rw [he] at hpin
      rw [show pinnedInfoT (punitName.str "rec") = punitRecA from rfl]
        at hpin
      simp only [punitRecA, ConstantInfo.recInfo.injEq,
        List.cons.injEq] at hpin
      have h2 : rr.nfields = 0 := by rw [← hpin.2.2.2.1]
      omega
    · rw [he] at hpin
      rw [show pinnedInfoT (emptyName.str "rec") = emptyRecA from rfl]
        at hpin
      simp [emptyRecA] at hpin
    · exact absurd (Name.str.injEq .. ▸ he).2 (by decide)
    · exact absurd (Name.str.injEq .. ▸ he).2 (by decide)
  refine ⟨hc, ?_⟩
  rw [hc] at hpin
  rw [show pinnedInfoT (psigmaName.str "rec") = psigmaRecA from rfl] at hpin
  simp only [psigmaRecA, ConstantInfo.recInfo.injEq, List.cons.injEq] at hpin
  rw [← hpin.2.2.2.1]
  rfl

/-- **`PairEtaCertStepTT`, discharged.** -/
theorem pairEtaCert_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT mode m φ fuel) (ihd : DefEqClaimsTT mode m φ fuel)
    (ihi : InferClaimsTT mode m φ fuel) : PairEtaCertStepTT m φ fuel := by
  intro d Δ a b h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  obtain ⟨c, us, pα, pβ, s₁, s₂, cvm, tb, c', us', A, B, cvi, capsi, cvr,
    mI, rP, rr, rfl, hfc, htb, hwtb, hfI, hfr, hrc, hrf, hmirp,
    hgres, hlev', hdA, hdB, hd1, hd2, hfec⟩ := pairEtaCert_inv h
  -- task #147: the TT lane runs at `.ttModel`, so the gated conjunct
  -- is delivered
  obtain ⟨entry, hfe, hcert⟩ := hfec rfl
  obtain ⟨rfl, hctor⟩ := pairLike_eq_psigma m hfr hrf hmirp hgres
  obtain rfl : c = psigmaMkName := by rw [← hrc, hctor]
  -- the stuck side's type, reduced
  obtain ⟨vb', Tb, hvb', hTb, hbT⟩ := ihi htb hwb hbb hLb hCb
  obtain rfl : vb = vb' := by
    rw [hvb'] at hvb; exact (Option.some.inj hvb).symm
  have hCtb : CtxOk m.cval env φ d Δ tb :=
    CtxOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htb hwb) hCb
  have hwtb' : Expr.WScoped d tb := inferTypeCore_WScoped m.wf fuel htb hwb
  have hbtb : tb.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel htb hwb hbb hLb
  have hLtb : Expr.LeavesBounded tb := fun l hl =>
    hLb l (inferTypeCore_fvarLeaves m.wf fuel htb hwb l hl)
  obtain ⟨W, hW, hDW⟩ := ihw hwtb hwtb' hbtb hLtb hCtb hTb
  have hwr : Expr.WScoped d (.app (.app (.const psigmaName us') A) B) :=
    whnf_WScoped m.wf fuel hwtb hwtb'
  have hbr : (Expr.app (.app (.const psigmaName us') A) B).looseBVarsBounded 0
      = true := whnf_looseBVars m.wf fuel hwtb hbtb
  have hLr : Expr.LeavesBounded (.app (.app (.const psigmaName us') A) B) :=
    fun l hl => hLtb l (whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hCr : CtxOk m.cval env φ d Δ (.app (.app (.const psigmaName us') A) B) :=
    CtxOk.of_subset (whnf_fvarLeaves m.wf fuel hwtb) hCtb
  -- the pinned pair's stored declarations
  have hpsig : env.find? psigmaName = some psigmaA := by
    have := (m.basis_pinned _ _ hfI (by decide)).1 rfl
    rw [show pinnedInfoT psigmaName = psigmaA from rfl] at this
    exact this ▸ hfI
  have hnat : entry.native = true := m.proj_ok.2 0 entry (by
    rw [Env.findProj?] at hfe
    split at hfe
    · next e heq => exact (Option.some.inj hfe) ▸ heq
    · exact nomatch hfe)
  obtain ⟨hpin, -, hpsigMk⟩ :=
    m.proj_ok.1 _ _ (Env.findProj?_some hfe) hnat
  -- the two type arguments' frames
  obtain ⟨hfAB, hfB⟩ := app_frames hwr hbr hLr hCr
  obtain ⟨hfC, hfA⟩ := app_frames hfAB.1 hfAB.2.1 hfAB.2.2.1 hfAB.2.2.2
  -- the reduced type is the pair type applied to `A` and `B`
  rw [denote_app, denote_app] at hW
  cases hVf : denote m.cval env φ d (Expr.const psigmaName us') with
  | none => rw [hVf] at hW; exact nomatch hW
  | some vf =>
  cases hVA : denote m.cval env φ d A with
  | none => rw [hVf, hVA] at hW; exact nomatch hW
  | some VA =>
  cases hVB : denote m.cval env φ d B with
  | none => rw [hVf, hVA, hVB] at hW; exact nomatch hW
  | some VB =>
  rw [hVf, hVA, hVB] at hW
  dsimp only at hW
  obtain rfl : VExpr.app (.app vf VA) VB = W := Option.some.inj hW
  -- the head is the pinned pair former, at the type's levels
  have hlen2 : us'.length = psigmaA.toConstantVal.levelParams.length := by
    rw [denote_const, hpsig] at hVf
    dsimp only at hVf
    split at hVf
    · assumption
    · exact nomatch hVf
  obtain rfl : m.cval psigmaName
      (Level.substFn φ psigmaA.toConstantVal.levelParams us') = vf := by
    rw [denote_const, hpsig] at hVf
    dsimp only at hVf
    rw [if_pos hlen2] at hVf
    exact Option.some.inj hVf
  have hpp : m.cval psigmaName
      (Level.substFn φ psigmaA.toConstantVal.levelParams us') =
      .const .psigma
        [Level.substFn φ psigmaA.toConstantVal.levelParams us' uNT,
         Level.substFn φ psigmaA.toConstantVal.levelParams us' vNT] :=
    cval_pinned m (n := psigmaName) (by decide) (by rw [hpsig]; rfl) _
      (by simp +decide [pinnedDirectT])
  -- the stuck side is derivably of that pair type
  have hbPi : HasType Δ vb (psigmaT
      (Level.substFn φ psigmaA.toConstantVal.levelParams us' uNT)
      (Level.substFn φ psigmaA.toConstantVal.levelParams us' vNT) VA VB) := by
    have := Deq.conv hbT hDW
    rwa [show psigmaT
        (Level.substFn φ psigmaA.toConstantVal.levelParams us' uNT)
        (Level.substFn φ psigmaA.toConstantVal.levelParams us' vNT) VA VB
        = VExpr.app (.app (m.cval psigmaName
          (Level.substFn φ psigmaA.toConstantVal.levelParams us')) VA) VB
        from by rw [hpp]; rfl]
  -- the new certificate: the type arguments are types
  have hlpE : entry.levelParams = psigmaA.toConstantVal.levelParams := by
    rcases hpin with rfl | rfl <;> rfl
  have husl : us'.length = entry.levelParams.length := by
    rw [hlpE]; exact hlen2
  obtain ⟨TT, hTT⟩ := denote_projEntryTy m φ hpin hpsig husl d
  obtain ⟨xs, rest, hfit⟩ :=
    certs_typed m φ hcl ihd ihi _ _ TT (projParamCert_inv hcert)
      (by rcases hpin with rfl | rfl <;> exact Expr.WScoped.of_not_hasFvar rfl)
      (by rcases hpin with rfl | rfl <;> rfl)
      (by rcases hpin with rfl | rfl <;>
        exact Expr.LeavesBounded.of_not_hasFvar rfl)
      (by
        refine ⟨hCb.1, fun l hl => ?_⟩
        rcases hpin with rfl | rfl <;>
          simp [pairFstEntry, pairSndEntry, pairFstTyA, pairSndTyA,
            Expr.instantiateLevelParams, Expr.fvarLeaves] at hl)
      hTT (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hfA
        · obtain rfl : x = B := by simpa using hx'
          exact hfB)
  obtain ⟨VA', VB', hVA', hVB', hAs, hBs⟩ := projEntry_tele_premises hpin hfit
  obtain rfl : VA = VA' := by rw [hVA] at hVA'; exact Option.some.inj hVA'
  obtain rfl : VB = VB' := by rw [hVB] at hVB'; exact Option.some.inj hVB'
  have hlev : ∀ nm : Name, (Level.subst entry.levelParams us'
      (.param nm)).eval φ =
      Level.substFn φ psigmaA.toConstantVal.levelParams us' nm := by
    intro nm
    rw [Level.eval_subst, hlpE]
    rfl
  rw [hlev uNT] at hAs
  rw [hlev vNT] at hBs
  -- the constructor side, and the four certified arguments
  have hea : Expr.app (.app (.app (.app (.const psigmaMkName us) pα) pβ) s₁) s₂
      = Expr.mkAppN (.const psigmaMkName us) [pα, pβ, s₁, s₂] := rfl
  rw [hea] at hva hwa hba hLa hCa
  obtain ⟨vfm, vms, hvfm, hspm, rfl⟩ := denote_mkAppN_inv hva
  -- the fabricated right-hand side
  have hprojs : DenoteSpine m.cval env φ d
      [pα, pβ, s₁, s₂]
      [VA, VB, .proj 0 vb, .proj 1 vb] → True := fun _ => trivial
  clear hprojs
  have hargs : ∀ x ∈ [pα, pβ, s₁, s₂], Expr.WScoped d x ∧
      x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
      CtxOk m.cval env φ d Δ x := by
    intro x hx
    have hx' : x ∈ (Expr.mkAppN (Expr.const psigmaMkName us)
        [pα, pβ, s₁, s₂]).getAppArgs := by
      rw [Expr.getAppArgs_mkAppN]; exact hx
    exact ⟨hwa.getAppArgs x hx', looseBVarsBounded_getAppArgs hba x hx',
      fun l hl => hLa l (fvarLeaves_getAppArgs hx' l hl),
      CtxOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx' l hl) hCa⟩
  have hprojFrames : ∀ (i : Nat), Expr.WScoped d (.proj psigmaName i b) ∧
      (Expr.proj psigmaName i b).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (.proj psigmaName i b) ∧
      CtxOk m.cval env φ d Δ (.proj psigmaName i b) := by
    intro i
    exact ⟨by simpa [Expr.WScoped] using hwb, hbb,
      fun l hl => hLb l (by simpa [Expr.fvarLeaves] using hl),
      CtxOk.of_subset (fun l hl => by
        simpa [Expr.fvarLeaves] using hl) hCb⟩
  have hdenProj : ∀ i : Nat, i < 2 →
      denote m.cval env φ d (.proj psigmaName i b) = some (.proj i vb) := by
    intro i hi
    rw [denote_proj, hvb]
    dsimp only
    rw [if_pos hi]
  -- the four argument equations
  obtain ⟨w1, w2, w3, w4, hs1, hs2, hs3, hs4, rfl⟩ :
      ∃ w1 w2 w3 w4, denote m.cval env φ d pα = some w1 ∧
        denote m.cval env φ d pβ = some w2 ∧
        denote m.cval env φ d s₁ = some w3 ∧
        denote m.cval env φ d s₂ = some w4 ∧
        vms = [w1, w2, w3, w4] := by
    cases hspm with | cons h1 t1 => ?_
    cases t1 with | cons h2 t2 => ?_
    cases t2 with | cons h3 t3 => ?_
    cases t3 with | cons h4 t4 => ?_
    cases t4
    exact ⟨_, _, _, _, h1, h2, h3, h4, rfl⟩
  have hD1 : Deq Δ w1 VA :=
    ihd hdA (hargs pα (by simp)).1 (hargs pα (by simp)).2.1
      (hargs pα (by simp)).2.2.1 hfA.1 hfA.2.1 hfA.2.2.1
      (hargs pα (by simp)).2.2.2 hfA.2.2.2 hs1 hVA
  have hD2 : Deq Δ w2 VB :=
    ihd hdB (hargs pβ (by simp)).1 (hargs pβ (by simp)).2.1
      (hargs pβ (by simp)).2.2.1 hfB.1 hfB.2.1 hfB.2.2.1
      (hargs pβ (by simp)).2.2.2 hfB.2.2.2 hs2 hVB
  have hD3 : Deq Δ w3 (.proj 0 vb) :=
    ihd hd1 (hargs s₁ (by simp)).1 (hargs s₁ (by simp)).2.1
      (hargs s₁ (by simp)).2.2.1 (hprojFrames 0).1 (hprojFrames 0).2.1
      (hprojFrames 0).2.2.1 (hargs s₁ (by simp)).2.2.2
      (hprojFrames 0).2.2.2 hs3 (hdenProj 0 (by omega))
  have hD4 : Deq Δ w4 (.proj 1 vb) :=
    ihd hd2 (hargs s₂ (by simp)).1 (hargs s₂ (by simp)).2.1
      (hargs s₂ (by simp)).2.2.1 (hprojFrames 1).1 (hprojFrames 1).2.1
      (hprojFrames 1).2.2.1 (hargs s₂ (by simp)).2.2.2
      (hprojFrames 1).2.2.2 hs4 (hdenProj 1 (by omega))
  -- the constructor head, at the type's levels
  have hmk : vfm = .const .psigmaMk
      [Level.substFn φ psigmaA.toConstantVal.levelParams us' uNT,
       Level.substFn φ psigmaA.toConstantVal.levelParams us' vNT] := by
    rw [denote_const, hpsigMk] at hvfm
    dsimp only at hvfm
    · split at hvfm
      · next hlenU =>
        rw [← Option.some.inj hvfm]
        have hsame : Level.substFn φ psigmaMkA.toConstantVal.levelParams us
            = Level.substFn φ psigmaMkA.toConstantVal.levelParams us' := by
          funext q
          exact substFn_of_evalEqList _ (Level.isEquivList_sound hlev' φ) q
        rw [hsame]
        have hpm : m.cval psigmaMkName
            (Level.substFn φ psigmaMkA.toConstantVal.levelParams us')
            = .const .psigmaMk
              [Level.substFn φ psigmaMkA.toConstantVal.levelParams us' uNT,
               Level.substFn φ psigmaMkA.toConstantVal.levelParams us' vNT] :=
          cval_pinned m (n := psigmaMkName) (by decide)
            (by rw [hpsigMk]; rfl) _
            (by simp +decide [pinnedDirectT])
        exact hpm
      · exact nomatch hvfm
  -- structure η, and the four certified arguments under congruence
  rw [hmk]
  refine Deq.trans ?_ (Deq.symm ⟨_, HasType.psigmaEta hAs hBs hbPi⟩)
  exact Deq.app (Deq.app (Deq.app (Deq.app Deq.refl hD1) hD2) hD3) hD4

end Setlec.TTVerify
