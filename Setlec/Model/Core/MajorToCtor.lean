import Setlec.Model.Core.Eta

/-!
# Checker-core soundness: MajorToCtor

Part of the mutual soundness claims layer (split from
`Setlec/Model/TypeChecker.lean`; see that module's docstring).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

section Claims

variable {m : EnvModel V env} {fuel : Nat}
variable (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
  (ihi : InferClaims m φ fuel)

/-- Claims for the stuck-major rescue's result: the substituted major
interprets to the same value as the stuck one (identity trivially; the
K fabrication by proof irrelevance — both are proofs of propositions;
the eta fabrication by the structure-eta law), and it satisfies the
full claims package the iota continuation threads.  The fabricated
constructor application's own claims are assembled from the iota
certificates the reduction then runs on it (`certs_fit` +
`annotOk_spine`); its arguments' claims come from the reduced type's
spine and, for eta, the projection certificates. -/
theorem majorToCtor_claims {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {recName cj : Name} {rules : List RecRule}
    {major₀ major : Expr} {ρ : Nat → V} {usj : List Level}
    {cvj : ConstantVal} {cnP cnF : Nat}
    (hsub : majorToCtorP env fuel d recName rules major₀ = .ok major)
    (hmfn : major.getAppFn = .const cj usj)
    (hfj : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hw : WScoped d major₀) (hb : major₀.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded major₀)
    (hok : FvarsOk V m.val env φ d ρ major₀)
    (hA : AnnotOk V m.val env φ d ρ major₀) :
    interpExpr V m.val env φ d ρ major =
      interpExpr V m.val env φ d ρ major₀ ∧
    AnnotOk V m.val env φ d ρ major ∧ WScoped d major ∧
    major.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded major ∧
    FvarsOk V m.val env φ d ρ major := by
  rcases majorToCtor_inv hsub with rfl | ⟨hwsc, hbM, hall, r, cvj', cnP',
    cnF', tmaj₀, tmaj, T, us₀, ust, cvT, caps, hrs, hfj', hpr', hfT,
    hti, htw, hth, hcase⟩
  · exact ⟨rfl, hA, hw, hb, hLb, hok⟩
  -- fabrication: scoping from the guard
  have hwM : WScoped d major := WScoped.of_wscopedB hwsc
  have hsubL : ∀ l ∈ major.fvarLeaves, l ∈ major₀.fvarLeaves := by
    intro l hl
    have := List.all_eq_true.mp hall l hl
    simpa using this
  have hLbM : Expr.LeavesBounded major := fun l hl => hLb l (hsubL l hl)
  have hokM : FvarsOk V m.val env φ d ρ major := FvarsOk.of_subset hsubL hok
  -- the stuck major's type chain
  obtain ⟨⟨vM, TM, hMi, hTMi, hmemM⟩, hAtm₀⟩ := ihi hti hw hb hLb hok hA
  have htm0w := inferTypeCore_WScoped m.wf fuel hti hw
  have htm0b := inferTypeCore_looseBVars m.wf fuel hti hw hb hLb
  have htm0L : Expr.LeavesBounded tmaj₀ := fun l hl =>
    hLb l (inferTypeCore_fvarLeaves m.wf fuel hti hw l hl)
  have htm0F : FvarsOk V m.val env φ d ρ tmaj₀ :=
    FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hti hw) hok
  obtain ⟨htieq, hAtm⟩ := ihw htw htm0w htm0b htm0L htm0F hAtm₀
  have htmw : WScoped d tmaj := whnf_WScoped m.wf fuel htw htm0w
  have htmb : tmaj.looseBVarsBounded 0 = true :=
    whnf_looseBVars m.wf fuel htw htm0b
  have htmL : Expr.LeavesBounded tmaj := fun l hl =>
    htm0L l (whnf_fvarLeaves m.wf fuel htw l hl)
  have htmF : FvarsOk V m.val env φ d ρ tmaj :=
    FvarsOk.of_subset (whnf_fvarLeaves m.wf fuel htw) htm0F
  have htmaj_eq : Expr.mkAppN (.const T ust) tmaj.getAppArgs = tmaj := by
    rw [← hth]
    exact Expr.mkAppN_getApp tmaj
  -- the type's argument spine
  obtain ⟨psv, hspT, hAtargs⟩ : ∃ psv,
      InterpSpine m.val env φ d ρ tmaj.getAppArgs psv ∧
      ∀ x ∈ tmaj.getAppArgs, AnnotOk V m.val env φ d ρ x := by
    cases hcaseT : tmaj.getAppArgs with
    | nil => exact ⟨[], trivial, fun x hx => absurd hx List.not_mem_nil⟩
    | cons t ts =>
      rw [← hcaseT]
      have hne : tmaj.getAppArgs ≠ [] := by rw [hcaseT]; simp
      have hAtm' : AnnotOk V m.val env φ d ρ
          (Expr.mkAppN (.const T ust) tmaj.getAppArgs) := by
        rw [htmaj_eq]
        exact hAtm
      obtain ⟨-, hAargs, vf, vs, -, hsp, -, -⟩ :=
        annotOk_spine_inv _ _ hne hAtm'
      exact ⟨vs, hsp, hAargs⟩
  have htargswf : ∀ x ∈ tmaj.getAppArgs,
      WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
      AnnotOk V m.val env φ d ρ x := by
    intro x hx
    refine ⟨htmw.getAppArgs x hx, looseBVarsBounded_getAppArgs htmb x hx,
      ?_, ?_, hAtargs x hx⟩
    · intro l hl
      exact htmL l (fvarLeaves_getAppArgs hx l hl)
    · exact FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl)
        htmF
  -- the constructor's telescope facts
  have hcjname : cvj.name = cj := by
    have := find?_name hfj
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
  obtain ⟨hCtf, -, -, hCtb, -, -⟩ := m.wf _ (find?_mem hfj)
  have hChf : (cvj.type.instantiateLevelParams cvj.levelParams
      usj).hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]
    exact hCtf
  have hCw : WScoped d (cvj.type.instantiateLevelParams cvj.levelParams
      usj) := WScoped.of_not_hasFvar hChf
  have hCb : (cvj.type.instantiateLevelParams cvj.levelParams
      usj).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]
    exact hCtb
  have hCA : AnnotOk V m.val env φ d ρ
      (cvj.type.instantiateLevelParams cvj.levelParams usj) := by
    obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfj)
      (Level.substFn φ cvj.levelParams usj)
    exact AnnotOk.closed_invariant hChf d ρ
      (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
  obtain ⟨TC, hCT, hCmem⟩ : ∃ TC, interpExpr V m.val env φ d ρ
      (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TC ∧
      m.val cj (Level.substFn φ cvj.levelParams usj) ∈ˢ TC := by
    obtain ⟨T0, hT0, hTm⟩ := m.mem_type _ (find?_mem hfj)
      (Level.substFn φ cvj.levelParams usj)
    refine ⟨T0, ?_, ?_⟩
    · rw [interp_closed_invariant hChf d ρ]
      unfold interpClosed
      rw [interp_instLevels m.val_params]
      exact hT0
    · rw [← hcjname]
      exact hTm
  have hmspine : Expr.mkAppN (.const cj usj) major.getAppArgs = major := by
    rw [← hmfn]
    exact Expr.mkAppN_getApp major
  have hconstA : AnnotOk V m.val env φ d ρ (.const cj usj) := by
    simp [AnnotOk]
  -- branch on the fabrication kind
  rcases hcase with
    ⟨hKrule, hcnF0, hlvlK, hlenK, hstripK, hfabeq, hcertK, -, hpi⟩ |
    ⟨hEeta, hEctor, hEproj, -, hplenE, hlvlE, hlvlE2, hstripE, hfabeq,
      hcertE, hse | ⟨hZ0, hlvlZ, hpi⟩⟩
  · -- ── K: the fabricated `refl`-like application ──
    have heqc : cj = r.ctor ∧ usj = ust := by
      have hgfn := congrArg Expr.getAppFn hfabeq
      rw [Expr.getAppFn_mkAppN, hmfn] at hgfn
      exact ⟨(Expr.const.inj hgfn).1, (Expr.const.inj hgfn).2⟩
    rw [← heqc.1, ← heqc.2] at hfabeq
    rw [← heqc.1] at hfj'
    obtain ⟨heqv, heqp, heqf⟩ : cvj' = cvj ∧ cnP' = cnP ∧ cnF' = cnF := by
      rw [hfj'] at hfj
      injection hfj with h1
      injection h1 with h1 h2 h3
      exact ⟨h1, h2, h3⟩
    rw [heqp] at hfabeq hlenK hstripK hcertK
    rw [heqv] at hlvlK hstripK hcertK
    have hmargs : major.getAppArgs = tmaj.getAppArgs.take cnP := by
      have hgargs := congrArg Expr.getAppArgs hfabeq
      rw [Expr.getAppArgs_mkAppN] at hgargs
      simpa [Expr.getAppArgs] using hgargs
    -- the relocated synthetic-spine certificate and arity pin
    have hmcerts : iotaCertsP env fuel d
        (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs = .ok true := by
      rw [hmargs, heqc.2]
      exact hcertK
    have hstripLen : (cvj.type.stripPis
        major.getAppArgs.length).isSome = true := by
      rw [hmargs, List.length_take, Nat.min_eq_left hlenK]
      exact hstripK
    have hlenj : usj.length = cvj.levelParams.length := by
      rw [heqc.2]
      exact hlvlK.symm
    have hvalC : interpExpr V m.val env φ d ρ (.const cj usj) =
        some (m.val cj (Level.substFn φ cvj.levelParams usj)) := by
      simp only [interpExpr, hfj]
      rw [if_pos (show usj.length =
        (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
        from hlenj)]
      rfl
    have hmargswf : ∀ x ∈ major.getAppArgs,
        WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x := by
      rw [hmargs]
      intro x hx
      exact htargswf x (List.mem_of_mem_take hx)
    have hspM : InterpSpine m.val env φ d ρ major.getAppArgs
        (psv.take cnP) := by
      rw [hmargs]
      exact InterpSpine.take cnP hspT
    obtain ⟨restC, hfitIC⟩ := certs_fit ihd ihi _ _ _ TC
      hmcerts hCw hCb (Expr.LeavesBounded.of_not_hasFvar hChf)
      (FvarsOk.of_not_hasFvar hChf) hCA hCT hmargswf hspM
    obtain ⟨dC, ρC, restC', hfitC⟩ := TeleFitI.toTeleFit hfitIC hCw
      (stripPis_instantiateLevelParams_isSome _ _ _ hstripLen)
    have hch := TeleFit.chainSlots hfitC hCA hCT hCmem
    obtain ⟨hAfab, hIfab⟩ := annotOk_spine major.getAppArgs
      (.const cj usj) hconstA hvalC
      (fun x hx => (hmargswf x hx).2.2.2.2) hspM hch
    rw [hmspine] at hAfab hIfab
    -- proof irrelevance identifies the values
    obtain ⟨hptM, hptM0⟩ := proofIrrel_pt ihw ihi hpi hwM hw hbM hb
      hLbM hLb hokM hok hAfab hA
    exact ⟨by rw [hptM, hptM0], hAfab, hwM, hbM, hLbM, hokM⟩
  · -- ── eta: the fabricated constructor of the projections ──
    have heqc : cj = caps.etaCtor ∧ usj = ust := by
      have hgfn := congrArg Expr.getAppFn hfabeq
      rw [Expr.getAppFn_mkAppN, hmfn] at hgfn
      exact ⟨(Expr.const.inj hgfn).1, (Expr.const.inj hgfn).2⟩
    simp only [etaFabArgs] at hfabeq hcertE
    rw [← heqc.1, ← heqc.2] at hfabeq
    rw [← heqc.2] at hth hcertE
    -- identify the rule-constructor entry with the continuation's
    rw [hEctor, ← heqc.1] at hfj'
    obtain ⟨heqvE, heqpE, heqfE⟩ : cvj' = cvj ∧ cnP' = cnP ∧ cnF' = cnF := by
      rw [hfj'] at hfj
      injection hfj with h1
      injection h1 with h1 h2 h3
      exact ⟨h1, h2, h3⟩
    rw [heqvE] at hstripE hcertE
    obtain ⟨c2, us2, cvc2, cnP2, cnF2, T2, us'2, cvT2, caps2,
      hfn2, hfc2, hal2, hwfn2, hfT2, hce2, hcc2, hcp2, hcf2, hres2,
      hresC2, htal2, hulen2, hclps2, hTstrip2, hlev2, hic2, hpc2,
      hd1, hd2⟩ := structEtaCertWith_inv hse
    -- identify the certificate's constants with the continuation's
    obtain ⟨rfl, rfl⟩ : cj = c2 ∧ usj = us2 := by
      rw [hmfn] at hfn2
      exact ⟨(Expr.const.inj hfn2).1, (Expr.const.inj hfn2).2⟩
    obtain ⟨rfl, rfl⟩ : T = T2 ∧ usj = us'2 := by
      rw [hth] at hwfn2
      exact ⟨(Expr.const.inj hwfn2).1, (Expr.const.inj hwfn2).2⟩
    obtain ⟨rfl, rfl⟩ : cvT = cvT2 ∧ caps = caps2 := by
      rw [hfT] at hfT2
      injection hfT2 with h1
      injection h1 with h1 h2
      exact ⟨h1, h2⟩
    obtain ⟨rfl, rfl, rfl⟩ : cvj = cvc2 ∧ cnP = cnP2 ∧ cnF = cnF2 := by
      rw [hfj] at hfc2
      injection hfc2 with h1
      injection h1 with h1 h2 h3
      exact ⟨h1, h2, h3⟩
    have hlenj : usj.length = cvj.levelParams.length := by
      rw [hclps2]
      exact hulen2
    have hvalC : interpExpr V m.val env φ d ρ (.const cj usj) =
        some (m.val cj (Level.substFn φ cvj.levelParams usj)) := by
      simp only [interpExpr, hfj]
      rw [if_pos (show usj.length =
        (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
        from hlenj)]
      rfl
    -- the projection certificates
    have hpcFacts : ∀ i, i < cnF → ∃ (cvp : ConstantVal)
        (mIp rPp : Nat) (rulesp : List RecRule),
        env.find? (projFnName T i) =
          some (.recInfo cvp mIp rPp rulesp) ∧
        cvp.levelParams = cvT.levelParams ∧
        (cvp.type.stripPis (tmaj.getAppArgs.length + 1)).isSome = true ∧
        iotaCertsP env fuel d
          (cvp.type.instantiateLevelParams cvp.levelParams usj)
          (tmaj.getAppArgs ++ [major₀]) = .ok true := by
      intro i hi
      exact structEtaProjCerts_inv (List.range cnF) hpc2 i
        (List.mem_range.mpr hi)
    -- each projection application's claims
    have hprojFacts : ∀ j, j < cnF →
        AnnotOk V m.val env φ d ρ
          (Expr.mkAppN (.const (projFnName T j) usj)
            (tmaj.getAppArgs ++ [major₀])) ∧
        interpExpr V m.val env φ d ρ
          (Expr.mkAppN (.const (projFnName T j) usj)
            (tmaj.getAppArgs ++ [major₀])) =
        some (SpineFold V (m.val (projFnName T j)
          (Level.substFn φ cvT.levelParams usj)) (psv ++ [vM])) := by
      intro j hj
      obtain ⟨cvp, mIp, rPp, rulesp, hfpj, hplps,
        hpstrip, hicj⟩ := hpcFacts j hj
      have hpname : cvp.name = projFnName T j := by
        have h1 := find?_name hfpj
        simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using h1
      have hplen : usj.length = cvp.levelParams.length := by
        rw [hplps]
        exact hulen2
      have hψp : Level.substFn φ cvp.levelParams usj =
          Level.substFn φ cvT.levelParams usj := by
        rw [hplps]
      have hvalP : interpExpr V m.val env φ d ρ
          (.const (projFnName T j) usj) =
          some (m.val (projFnName T j)
            (Level.substFn φ cvT.levelParams usj)) := by
        simp only [interpExpr, hfpj]
        rw [if_pos (show usj.length =
          (ConstantInfo.recInfo cvp mIp rPp
            rulesp).toConstantVal.levelParams.length from hplen)]
        rw [show (ConstantInfo.recInfo cvp mIp rPp
          rulesp).toConstantVal.levelParams = cvp.levelParams from rfl, hψp]
      obtain ⟨hPtf, -, -, hPtb, -, -⟩ := m.wf _ (find?_mem hfpj)
      have hPhf : (cvp.type.instantiateLevelParams cvp.levelParams
          usj).hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact hPtf
      have hPw : WScoped d (cvp.type.instantiateLevelParams
          cvp.levelParams usj) := WScoped.of_not_hasFvar hPhf
      have hPb : (cvp.type.instantiateLevelParams cvp.levelParams
          usj).looseBVarsBounded 0 = true := by
        rw [looseBVarsBounded_instantiateLevelParams]
        exact hPtb
      have hPA : AnnotOk V m.val env φ d ρ
          (cvp.type.instantiateLevelParams cvp.levelParams usj) := by
        obtain ⟨hA0, -⟩ := m.annot_ok _ (find?_mem hfpj)
          (Level.substFn φ cvp.levelParams usj)
        exact AnnotOk.closed_invariant hPhf d ρ
          (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hA0)
      obtain ⟨PT, hPT, hPmem⟩ : ∃ PT, interpExpr V m.val env φ d ρ
          (cvp.type.instantiateLevelParams cvp.levelParams usj) =
            some PT ∧
          m.val (projFnName T j) (Level.substFn φ cvp.levelParams usj)
            ∈ˢ PT := by
        obtain ⟨T0, hT0, hTm⟩ := m.mem_type _ (find?_mem hfpj)
          (Level.substFn φ cvp.levelParams usj)
        refine ⟨T0, ?_, ?_⟩
        · rw [interp_closed_invariant hPhf d ρ]
          unfold interpClosed
          rw [interp_instLevels m.val_params]
          exact hT0
        · rw [← hpname]
          exact hTm
      have hargs5 : ∀ x ∈ tmaj.getAppArgs ++ [major₀],
          WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
          AnnotOk V m.val env φ d ρ x := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact htargswf x hx
        · obtain rfl : x = major₀ := by simpa using hx
          exact ⟨hw, hb, hLb, hok, hA⟩
      have hspPB : InterpSpine m.val env φ d ρ
          (tmaj.getAppArgs ++ [major₀]) (psv ++ [vM]) :=
        InterpSpine.append hspT ⟨hMi, trivial⟩
      obtain ⟨restP, hfitIP⟩ := certs_fit ihd ihi _ _ _ PT hicj hPw hPb
        (Expr.LeavesBounded.of_not_hasFvar hPhf)
        (FvarsOk.of_not_hasFvar hPhf) hPA hPT hargs5 hspPB
      obtain ⟨dP, ρP, restP', hfitP⟩ := TeleFitI.toTeleFit hfitIP hPw (by
        rw [show (tmaj.getAppArgs ++ [major₀]).length =
          tmaj.getAppArgs.length + 1 from by simp]
        exact stripPis_instantiateLevelParams_isSome _ _ _ hpstrip)
      have hψpmem : m.val (projFnName T j)
          (Level.substFn φ cvT.levelParams usj) ∈ˢ PT := by
        rw [← hψp]
        exact hPmem
      have hch := TeleFit.chainSlots hfitP hPA hPT hψpmem
      have hconstP : AnnotOk V m.val env φ d ρ
          (.const (projFnName T j) usj) := by
        simp [AnnotOk]
      exact annotOk_spine (tmaj.getAppArgs ++ [major₀])
        (.const (projFnName T j) usj) hconstP hvalP
        (fun x hx => (hargs5 x hx).2.2.2.2) hspPB hch
    -- the fabricated spine and its values
    have hmargs : major.getAppArgs = tmaj.getAppArgs ++
        (List.range cnF).map (fun i => Expr.mkAppN
          (.const (projFnName T i) usj)
          (tmaj.getAppArgs ++ [major₀])) := by
      have hgargs := congrArg Expr.getAppArgs hfabeq
      rw [Expr.getAppArgs_mkAppN] at hgargs
      rw [hcf2] at hgargs
      simpa [Expr.getAppArgs] using hgargs
    -- the relocated synthetic-spine certificate and arity pin
    have hmcerts : iotaCertsP env fuel d
        (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs = .ok true := by
      rw [hmargs, ← hcf2]
      exact hcertE
    have hstripLen : (cvj.type.stripPis
        major.getAppArgs.length).isSome = true := by
      rw [hmargs]
      rw [show (tmaj.getAppArgs ++ (List.range cnF).map (fun i =>
          Expr.mkAppN (.const (projFnName T i) usj)
            (tmaj.getAppArgs ++ [major₀]))).length =
          caps.etaParams + caps.etaFields from by
        rw [List.length_append, List.length_map, List.length_range,
          hplenE, hcf2]]
      exact hstripE
    have hprojSpine : InterpSpine m.val env φ d ρ
        ((List.range cnF).map fun i =>
          Expr.mkAppN (.const (projFnName T i) usj)
            (tmaj.getAppArgs ++ [major₀]))
        ((List.range cnF).map fun i =>
          SpineFold V (m.val (projFnName T i)
            (Level.substFn φ cvT.levelParams usj)) (psv ++ [vM])) := by
      have hgen : ∀ (l : List Nat), (∀ i ∈ l, i < cnF) →
          InterpSpine m.val env φ d ρ
            (l.map fun i => Expr.mkAppN (.const (projFnName T i) usj)
              (tmaj.getAppArgs ++ [major₀]))
            (l.map fun i =>
              SpineFold V (m.val (projFnName T i)
                (Level.substFn φ cvT.levelParams usj)) (psv ++ [vM])) := by
        intro l
        induction l with
        | nil => intro _; exact trivial
        | cons i l ih =>
          intro hl
          exact ⟨(hprojFacts i (hl i List.mem_cons_self)).2,
            ih (fun i' hi' => hl i' (List.mem_cons_of_mem _ hi'))⟩
      exact hgen (List.range cnF) (fun i hi => List.mem_range.mp hi)
    have hprojwf : ∀ x ∈ (List.range cnF).map (fun i => Expr.mkAppN
        (.const (projFnName T i) usj) (tmaj.getAppArgs ++ [major₀])),
        WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hif := hprojFacts i (List.mem_range.mp hi)
      refine ⟨?_, ?_, ?_, ?_, hif.1⟩
      · refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact htmw.getAppArgs x hx
        · obtain rfl : x = major₀ := by simpa using hx
          exact hw
      · refine looseBVarsBounded_mkAppN (by rfl) ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact looseBVarsBounded_getAppArgs htmb x hx
        · obtain rfl : x = major₀ := by simpa using hx
          exact hb
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
        · simp [Expr.fvarLeaves] at hl'
        · rcases List.mem_append.mp hx with hx | hx
          · exact htmL l (fvarLeaves_getAppArgs hx l hlx)
          · obtain rfl : x = major₀ := by simpa using hx
            exact hLb l hlx
      · intro l hl
        rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
        · simp [Expr.fvarLeaves] at hl'
        · rcases List.mem_append.mp hx with hx | hx
          · exact htmF l (fvarLeaves_getAppArgs hx l hlx)
          · obtain rfl : x = major₀ := by simpa using hx
            exact hok l hlx
    have hmargswf : ∀ x ∈ major.getAppArgs,
        WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x := by
      rw [hmargs]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact htargswf x hx
      · exact hprojwf x hx
    have hspM : InterpSpine m.val env φ d ρ major.getAppArgs
        (psv ++ (List.range cnF).map fun i =>
          SpineFold V (m.val (projFnName T i)
            (Level.substFn φ cvT.levelParams usj)) (psv ++ [vM])) := by
      rw [hmargs]
      exact InterpSpine.append hspT hprojSpine
    obtain ⟨restC, hfitIC⟩ := certs_fit ihd ihi _ _ _
      TC hmcerts hCw hCb (Expr.LeavesBounded.of_not_hasFvar hChf)
      (FvarsOk.of_not_hasFvar hChf) hCA hCT hmargswf hspM
    obtain ⟨dC, ρC, restC', hfitC⟩ := TeleFitI.toTeleFit hfitIC hCw
      (stripPis_instantiateLevelParams_isSome _ _ _ hstripLen)
    have hch := TeleFit.chainSlots hfitC hCA hCT hCmem
    obtain ⟨hAfab, hIfab⟩ := annotOk_spine major.getAppArgs
      (.const cj usj) hconstA hvalC
      (fun x hx => (hmargswf x hx).2.2.2.2) hspM hch
    rw [hmspine] at hAfab hIfab
    -- the eta law identifies the values
    have hveq := structEtaWith_sound ihw ihd ihi hse hti htw
      hwM hw hbM hb hLbM hLb hokM hok hAfab hA hIfab hMi
    exact ⟨by rw [hIfab, hMi, hveq], hAfab, hwM, hbM, hLbM, hokM⟩
  · -- ── 0-field eta: the bare-constructor fabrication, certified by
    -- proof irrelevance (the pinned basis `PUnit` rescue) ──
    have heqc : cj = caps.etaCtor ∧ usj = ust := by
      have hgfn := congrArg Expr.getAppFn hfabeq
      rw [Expr.getAppFn_mkAppN, hmfn] at hgfn
      exact ⟨(Expr.const.inj hgfn).1, (Expr.const.inj hgfn).2⟩
    simp only [etaFabArgs] at hfabeq hcertE
    rw [← heqc.1, ← heqc.2] at hfabeq
    -- identify the rule-constructor entry with the continuation's
    rw [hEctor, ← heqc.1] at hfj'
    obtain ⟨heqv, heqp, heqf⟩ : cvj' = cvj ∧ cnP' = cnP ∧ cnF' = cnF := by
      rw [hfj'] at hfj
      injection hfj with h1
      injection h1 with h1 h2 h3
      exact ⟨h1, h2, h3⟩
    rw [heqv] at hlvlZ hstripE hcertE
    rw [← heqc.2] at hcertE
    have hmargs : major.getAppArgs = tmaj.getAppArgs := by
      have hgargs := congrArg Expr.getAppArgs hfabeq
      rw [Expr.getAppArgs_mkAppN] at hgargs
      simpa [Expr.getAppArgs, hZ0] using hgargs
    have hlenj : usj.length = cvj.levelParams.length := by
      rw [heqc.2]
      exact hlvlZ.symm
    have hvalC : interpExpr V m.val env φ d ρ (.const cj usj) =
        some (m.val cj (Level.substFn φ cvj.levelParams usj)) := by
      simp only [interpExpr, hfj]
      rw [if_pos (show usj.length =
        (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
        from hlenj)]
      rfl
    have hmargswf : ∀ x ∈ major.getAppArgs,
        WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x := by
      rw [hmargs]
      exact htargswf
    have hspM : InterpSpine m.val env φ d ρ major.getAppArgs psv := by
      rw [hmargs]
      exact hspT
    -- the relocated synthetic-spine certificate and arity pin
    have hmcerts : iotaCertsP env fuel d
        (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs = .ok true := by
      rw [hmargs]
      have h0 := hcertE
      rw [hZ0] at h0
      simpa using h0
    have hstripLen : (cvj.type.stripPis
        major.getAppArgs.length).isSome = true := by
      rw [hmargs, hplenE]
      have h0 := hstripE
      rw [hZ0] at h0
      simpa using h0
    obtain ⟨restC, hfitIC⟩ := certs_fit ihd ihi _ _ _ TC
      hmcerts hCw hCb (Expr.LeavesBounded.of_not_hasFvar hChf)
      (FvarsOk.of_not_hasFvar hChf) hCA hCT hmargswf hspM
    obtain ⟨dC, ρC, restC', hfitC⟩ := TeleFitI.toTeleFit hfitIC hCw
      (stripPis_instantiateLevelParams_isSome _ _ _ hstripLen)
    have hch := TeleFit.chainSlots hfitC hCA hCT hCmem
    obtain ⟨hAfab, hIfab⟩ := annotOk_spine major.getAppArgs
      (.const cj usj) hconstA hvalC
      (fun x hx => (hmargswf x hx).2.2.2.2) hspM hch
    rw [hmspine] at hAfab hIfab
    -- proof irrelevance identifies the values
    obtain ⟨hptM, hptM0⟩ := proofIrrel_pt ihw ihi hpi hwM hw hbM hb
      hLbM hLb hokM hok hAfab hA
    exact ⟨by rw [hptM, hptM0], hAfab, hwM, hbM, hLbM, hokM⟩

end Claims

end Setlec
