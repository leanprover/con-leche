module

public import ConLeche.Model.Steps.CapsRows
public import ConLeche.Model.Steps.Stuck
public import ConLeche.Model.Steps.InferIO
public import ConLeche.Semantics.WellDenoted
public import ConLeche.Model.Steps.TowerKit
public import ConLeche.Model.Steps.IotaGate
public import ConLeche.Verify.Denote
public import ConLeche.Verify.Denote.OpenVars
public import ConLeche.Verify.Denote.VClosed
public section

/-!
# The semantic projection rows (task #161, PROJ/STR install tier;
task #175 W5/W6, the tower route)

`InferProjStep`/`InferProjStepIO` (`Steps/Infer.lean`,
`Steps/InferIO.lean`) and `ProjStep` (`Steps/Whnf.lean`),
discharged.  Every native projection-table entry is tower-backed
(`ProjOkT`, task #175 W6: the pinned `PSigma'` pair entries are
retired), so every row is the tower law's (`TowerEntryLaw`, keyed on
the entry by `TowerOk`):

* the two infer rows read the returned type as the checker's peel of
  the stored entry type (`denoteMeta_instPisAt_peel`) and take the three
  conclusions from the law's typing clause (A);
* `ProjStep`'s stuck branch is a congruence under the projection
  reading; its firing branch is the law's iota clause (B) at the
  constructor application's graded reading, with the certified spine's
  fit (`projCert`'s `iotaCerts`, through the ι slot's licensed walk
  `certs_teleLic`, bridged to the value-level fit by
  `teleFit_of_teleFitPA`) as the squash-regime premise.

Why the fit is a premise (the W6 finding): `whnfCore`'s projection
clause has **no type for the scrutinee in its premises**; at a graph
instantiation the application's grading pins every slot (graph
rigidity), but at a squash instantiation the application is the point
and a grading pins nothing — an ill-typed spine's value is the point
just as a well-typed one's is.  The memberships have to come from the
run, and `projCert` is that run.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ProjEntry
  inferTypeCore whnf whnfCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## `InferProjStep` -/

/-- **`InferProjStep`, discharged.**  At a pair-backed entry the
subject's type reduces to the pinned pair applied to its two
parameters; `mem_psigmaV2_app` inverts that into the three facts
`WellDenoted_fst`/`WellDenoted_snd` ask for, and the returned type is `projResidualP`'s
computed residual — the first parameter, or the second applied to the
first projection.  At a tower-backed entry (task #175 wiring W5) the
returned type is the checker's peel of the stored entry type along the
parameters and the subject, whose reading is the syntactic peel of the
entry type's reading (`denoteMeta_instPisAt_peel`), and the three
conclusions are the tower law's typing clause at the reduced subject
type's graded reading. -/
theorem inferProjStep_of_claims {m : EnvModel V env}
    (htower : TowerOk m φ)
    (ihw : WhnfClaim μ m φ fuel) (ihi : InferClaim μ m φ fuel)
    (hreads : InferReads m μ φ fuel) (hwreads : WhnfReads m μ φ fuel) :
    InferProjStep m μ φ fuel := by
  intro d i sn pe t Δa ea ta h hws hb hLb hC hea hta
  obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hlenArgs,
    hlenUs, hguard, rfl, hsn⟩ := ConLeche.inferTypeCore_proj_inv h
  subst hsn
  -- the subject's frames
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOk m φ d Δa pe :=
    hC.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hrd⟩ := denoteMeta_proj_inv hea
  -- its inferred type: reading, grading, membership
  obtain ⟨tpea, htpea⟩ :=
    hreads htpe hws hb hLpe (LeafReads.of_ctxOk hCpe) hvp
  obtain ⟨hokPe, hokTpe, hmemPe⟩ := ihi htpe hws hb hLpe hCpe hvp htpea
  have hwtpe : Expr.WScoped d tpe :=
    ConLeche.inferTypeCore_WScoped m.wf fuel htpe hws
  have hbtpe : tpe.looseBVarsBounded 0 = true :=
    ConLeche.inferTypeCore_looseBVars m.wf fuel htpe hws hb hLpe
  have hLtpe : Expr.LeavesBounded tpe := fun l hl =>
    hLpe l (ConLeche.inferTypeCore_fvarLeaves m.wf fuel htpe hws l hl)
  have hCtpe : CtxOk m φ d Δa tpe :=
    hCpe.of_subset
      (ConLeche.inferTypeCore_fvarLeaves m.wf fuel htpe hws)
  -- reduced to the family instance
  obtain ⟨tea, htea⟩ := hwreads hwte hwtpe hbtpe hLtpe
    (LeafReads.of_ctxOk hCtpe) htpea
  obtain ⟨hokTe, heqTe⟩ :=
    ihw hwte hwtpe hbtpe hLtpe hCtpe htpea htea hokTpe
  have hwte' : Expr.WScoped d te := ConLeche.whnf_WScoped m.wf fuel hwte hwtpe
  have hbte : te.looseBVarsBounded 0 = true :=
    ConLeche.whnf_looseBVars m.wf fuel hwte hbtpe
  -- the tower law's typing clause (task #175 wiring W5)
  obtain ⟨-, -, -, ⟨cvT, capsT, hfT, hlpsT, -⟩, hO5, _, -, -, hlaw, -⟩ :=
    htower T i entry hfe
  obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlaw us hlenUs
  obtain ⟨vp', hvp', rfl⟩ := denoteMeta_proj_inv_tower hfe hea
  obtain rfl : vp = vp' := Option.some.inj (hvp.symm.trans hvp')
  -- the reduced type's spine, at the former's leaf
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp te).symm, hfn] at htea
  obtain ⟨vT, vs, hvT, hspt, hteq⟩ := denoteMeta_mkAppN_inv htea
  have hlenT : us.length
      = (ConstantInfo.indInfo cvT capsT).toConstantVal.levelParams.length := by
    show us.length = cvT.levelParams.length
    rw [hlpsT]; exact hlenUs
  rw [denoteMeta_const hfT hlenT] at hvT
  have hvT' : vT = m.acval T (Level.substFn φ entry.levelParams us) := by
    rw [← hlpsT]; exact (Option.some.inj hvT).symm
  subst hvT'
  subst hteq
  -- the residual: the entry type's peel, read
  have hframes : ∀ x ∈ te.getAppArgs ++ [pe],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact ⟨hwte'.getAppArgs x hx',
        ConLeche.looseBVarsBounded_getAppArgs hbte x hx'⟩
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hws, hb⟩
  obtain ⟨restA, hrest, hpeel⟩ :=
    denoteMeta_typeAt_peel hfe hTa hlenArgs hframes (hspt.snoc hvp)
  obtain rfl : ta = restA := Option.some.inj (hta.symm.trans hrest)
  have hlenVs : vs.length = entry.numParams := by
    rw [← hspt.length]; exact hlenArgs
  have hlaw' : ∀ σ : Nat → V, Sat V Δa σ →
      WellDenotedV V σ (projAV (i + entry.off) vp) ∧ WellDenotedV V σ ta ∧
        interp V σ (projAV (i + entry.off) vp) ∈ˢ interp V σ ta := fun σ hσ =>
    hA (towerGuardAt_of hO5 hguard) σ vs vp ta hlenVs (hokTe σ hσ)
      (hokPe σ hσ) ((heqTe σ hσ) ▸ hmemPe σ hσ) hpeel
  exact ⟨fun σ hσ => (hlaw' σ hσ).1, fun σ hσ => (hlaw' σ hσ).2.1,
    fun σ hσ => (hlaw' σ hσ).2.2⟩

/-! ## `InferProjStepIO` (task #172 B4 — the B1b-assigned owed row)

`inferProjStep_of_claims` transposed to the io lane: the scrutinee's
run is the io lane's (the clause infers it at the io grade) and the
subject's `WellDenotedV` moves to the premises, where its `WellDenoted` proj
slot replaces the full lane's establishment of the scrutinee.  The
structure-type walk — whnf, the entry's pins, the spine, the pair-space
inversion — is the full row's, verbatim: those lanes are shared, which
is the io knot's leaf-lane asymmetry seen from the proj clause. -/

theorem inferProjStepIO_of_claims {m : EnvModel V env}
    (htower : TowerOk m φ)
    (ihw : WhnfClaim μ m φ fuel) (ihio : InferClaimIO μ m φ fuel)
    (hreads : InferReadsIO m μ φ fuel) (hwreads : WhnfReads m μ φ fuel) :
    InferProjStepIO m μ φ fuel := by
  intro d i sn pe t Δa ea ta h hws hb hLb hC hea hta hok
  obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hlenArgs,
    hlenUs, hguard, rfl, hsn⟩ := ConLeche.inferTypeCoreIO_proj_inv h
  subst hsn
  -- the subject's frames
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOk m φ d Δa pe :=
    hC.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hrd⟩ := denoteMeta_proj_inv hea
  -- the scrutinee's WellDenotedV, off the subject's own proj slot (premise
  -- form: the full lane established it; the io lane reads it)
  have hokPe : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ vp := by
    intro ρ hρ
    rcases hrd with ⟨_, -, rfl⟩ | ⟨-, hdec⟩
    · exact WellDenotedV_projAV_hoist (hok ρ hρ)
    · rcases AnnotTerm.projPair?_cases hdec with rfl | rfl
      · exact ⟨WellDenoted.hoist_fst (V := V) (fun σ hσ => (hok σ hσ).1) ρ hρ,
          (AnnotValid_fst V ρ vp) ▸ (hok ρ hρ).2⟩
      · exact ⟨WellDenoted.hoist_snd (V := V) (fun σ hσ => (hok σ hσ).1) ρ hρ,
          (AnnotValid_snd V ρ vp) ▸ (hok ρ hρ).2⟩
  -- its io-inferred type: reading, then grading + membership
  obtain ⟨tpea, htpea⟩ :=
    hreads htpe hws hb hLpe (LeafReads.of_ctxOk hCpe) hvp
  obtain ⟨hokTpe, hmemPe⟩ := ihio htpe hws hb hLpe hCpe hvp htpea hokPe
  have hwtpe : Expr.WScoped d tpe :=
    ConLeche.inferTypeCoreIO_WScoped m.wf fuel htpe hws
  have hbtpe : tpe.looseBVarsBounded 0 = true :=
    ConLeche.inferTypeCoreIO_looseBVars m.wf fuel htpe hws hb hLpe
  have hLtpe : Expr.LeavesBounded tpe := fun l hl =>
    hLpe l (ConLeche.inferTypeCoreIO_fvarLeaves m.wf fuel htpe hws l hl)
  have hCtpe : CtxOk m φ d Δa tpe :=
    hCpe.of_subset
      (ConLeche.inferTypeCoreIO_fvarLeaves m.wf fuel htpe hws)
  -- reduced to the family instance
  obtain ⟨tea, htea⟩ := hwreads hwte hwtpe hbtpe hLtpe
    (LeafReads.of_ctxOk hCtpe) htpea
  obtain ⟨hokTe, heqTe⟩ :=
    ihw hwte hwtpe hbtpe hLtpe hCtpe htpea htea hokTpe
  have hwte' : Expr.WScoped d te := ConLeche.whnf_WScoped m.wf fuel hwte hwtpe
  have hbte : te.looseBVarsBounded 0 = true :=
    ConLeche.whnf_looseBVars m.wf fuel hwte hbtpe
  -- the tower law's typing clause (task #175 wiring W5)
  obtain ⟨-, -, -, ⟨cvT, capsT, hfT, hlpsT, -⟩, hO5, _, -, -, hlaw, -⟩ :=
    htower T i entry hfe
  obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlaw us hlenUs
  obtain ⟨vp', hvp', rfl⟩ := denoteMeta_proj_inv_tower hfe hea
  obtain rfl : vp = vp' := Option.some.inj (hvp.symm.trans hvp')
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp te).symm, hfn] at htea
  obtain ⟨vT, vs, hvT, hspt, hteq⟩ := denoteMeta_mkAppN_inv htea
  have hlenT : us.length
      = (ConstantInfo.indInfo cvT capsT).toConstantVal.levelParams.length := by
    show us.length = cvT.levelParams.length
    rw [hlpsT]; exact hlenUs
  rw [denoteMeta_const hfT hlenT] at hvT
  have hvT' : vT = m.acval T (Level.substFn φ entry.levelParams us) := by
    rw [← hlpsT]; exact (Option.some.inj hvT).symm
  subst hvT'
  subst hteq
  have hframes : ∀ x ∈ te.getAppArgs ++ [pe],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact ⟨hwte'.getAppArgs x hx',
        ConLeche.looseBVarsBounded_getAppArgs hbte x hx'⟩
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hws, hb⟩
  obtain ⟨restA, hrest, hpeel⟩ :=
    denoteMeta_typeAt_peel hfe hTa hlenArgs hframes (hspt.snoc hvp)
  obtain rfl : ta = restA := Option.some.inj (hta.symm.trans hrest)
  have hlenVs : vs.length = entry.numParams := by
    rw [← hspt.length]; exact hlenArgs
  have hlaw' : ∀ σ : Nat → V, Sat V Δa σ →
      WellDenotedV V σ (projAV (i + entry.off) vp) ∧ WellDenotedV V σ ta ∧
        interp V σ (projAV (i + entry.off) vp) ∈ˢ interp V σ ta := fun σ hσ =>
    hA (towerGuardAt_of hO5 hguard) σ vs vp ta hlenVs (hokTe σ hσ)
      (hokPe σ hσ) ((heqTe σ hσ) ▸ hmemPe σ hσ) hpeel
  exact ⟨fun σ hσ => (hlaw' σ hσ).2.1, fun σ hσ => (hlaw' σ hσ).2.2⟩


/-! ## `ProjStep` -/

/-- **An annotation-level fit is a value-level fit** (task #175 W6):
`TeleFitPA`'s `inst` residuals un-instantiate step by step
(`teleFit_of_inst0`) under the ∀-chain guard — the bridge from the
licensed walk's output (`certs_teleLic`) to the tower law's premise. -/
theorem teleFit_of_teleFitPA {ρ : Nat → V} :
    ∀ {T : AnnotTerm} {as : List AnnotTerm} {resta : AnnotTerm},
      PiChain as.length T → TeleFitPA V ρ T as resta →
      TeleFit V ρ T (as.map (interp V ρ)) (interp V ρ resta) := by
  intro T as resta hpc h
  revert hpc
  induction h with
  | nil => intro _; exact .nil
  | @cons u v A B rest a as hmem hfit ih =>
    intro hpc
    have hpcB : PiChain as.length B := hpc
    exact .cons hmem (teleFit_of_inst0 (by rw [List.length_map]; exact hpcB)
      (ih (PiChain.inst a 0 hpcB)))

/-- **`ProjStep`, discharged.**  The stuck branch is a congruence
under the projection reading (pair: `.fst`/`.snd`; tower: `projAV i`,
`WellDenotedV_projAV_congr`).  The firing branch at a pair-backed entry
identifies the reduct's value with `sfst`/`ssnd` of the constructor
application through `sfst_mk2`/`ssnd_mk2`, whose four typing
premises are `psigmaMkSpineP`'s walk of `projCert`'s own
`inferTypeCore` run; at a tower-backed entry (task #175 wiring W5) it
is the tower law's iota clause at the constructor application's graded
reading — no run is walked, the grading's slot chain is the whole
premise. -/
theorem projStep_of_claims (hμ : μ.verifiedChecks = true) {m : EnvModel V env}
    (htower : TowerOk m φ) (hct : ConstType m φ)
    (ihwc : WhnfCoreClaim μ m φ fuel) (ihw : WhnfClaim μ m φ fuel)
    (ihd : DefEqClaim μ m φ fuel) (ihis : InferClaimIOS μ m φ fuel)
    (hexi : InferExistsIOS μ m φ fuel)
    (hwreads : WhnfReads m μ φ fuel) :
    ProjStep μ m φ fuel := by
  intro d sn i pe e' Δa h hws hb hLb ea ea' hC hea hea' hokA
  obtain ⟨e₂, e₃, hwpe, hlit, hcase⟩ := ConLeche.whnf_proj_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOk m φ d Δa pe :=
    hC.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hrd⟩ := denoteMeta_proj_inv hea
  have hokVp : ∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ vp := by
    intro σ hσ
    rcases hrd with ⟨_, -, -, rfl⟩ | ⟨-, hdec⟩
    · exact WellDenotedV_projAV_hoist (hokA σ hσ)
    · rcases AnnotTerm.projPair?_cases hdec with rfl | rfl
      · refine ⟨?_, ?_⟩
        · have h1 := (hokA σ hσ).1; rw [WellDenoted_fst] at h1; exact h1.1
        · have h2 := (hokA σ hσ).2; rwa [AnnotValid_fst] at h2
      · refine ⟨?_, ?_⟩
        · have h1 := (hokA σ hσ).1; rw [WellDenoted_snd] at h1; exact h1.1
        · have h2 := (hokA σ hσ).2; rwa [AnnotValid_snd] at h2
  -- the reduced scrutinee
  obtain ⟨v₂, hv₂⟩ := hwreads hwpe hws hb hLpe
    (LeafReads.of_ctxOk hCpe) hvp
  obtain ⟨hok₂, heq₂⟩ := ihw hwpe hws hb hLpe hCpe hvp hv₂ hokVp
  have hw₂ : Expr.WScoped d e₂ := ConLeche.whnf_WScoped m.wf fuel hwpe hws
  have hb₂ : e₂.looseBVarsBounded 0 = true :=
    ConLeche.whnf_looseBVars m.wf fuel hwpe hb
  have hL₂ : Expr.LeavesBounded e₂ := fun l hl =>
    hLpe l (ConLeche.whnf_fvarLeaves m.wf fuel hwpe l hl)
  have hC₂ : CtxOk m φ d Δa e₂ :=
    hCpe.of_subset (ConLeche.whnf_fvarLeaves m.wf fuel hwpe)
  -- the string-literal expansion, if it fired
  obtain ⟨v₃, hv₃, hok₃, heq₃, hw₃, hb₃, hL₃, hC₃⟩ :
      ∃ v₃, denoteMeta m.acval env φ d e₃ = some v₃ ∧
        (∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ v₃) ∧
        (∀ σ : Nat → V, Sat V Δa σ →
          interp V σ vp = interp V σ v₃) ∧
        Expr.WScoped d e₃ ∧ e₃.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e₃ ∧ CtxOk m φ d Δa e₃ := by
    rcases ConLeche.projLitToCtorFueled_inv hlit with rfl | ⟨st, rfl, hg, hred⟩
    · exact ⟨v₂, hv₂, hok₂, heq₂, hw₂, hb₂, hL₂, hC₂⟩
    · obtain ⟨hSC, hwc, hbc, hLc, hfv⟩ := denotePStrLit_of_guard d st hg hv₂
      have hCc : CtxOk m φ d Δa (ConLeche.strLitToConstructor st) :=
        ⟨hCpe.1, fun l hl => by rw [hfv] at hl; exact nomatch hl⟩
      obtain ⟨v₃, hv₃⟩ := hwreads hred hwc hbc hLc
        (fun l hl => by rw [hfv] at hl; exact nomatch hl) hSC
      obtain ⟨hok₃, heq₃⟩ := ihw hred hwc hbc hLc hCc hSC hv₃ hok₂
      exact ⟨v₃, hv₃, hok₃,
        fun σ hσ => (heq₂ σ hσ).trans (heq₃ σ hσ),
        ConLeche.whnf_WScoped m.wf fuel hred hwc,
        ConLeche.whnf_looseBVars m.wf fuel hred hbc,
        fun l hl => hLc l (ConLeche.whnf_fvarLeaves m.wf fuel hred l hl),
        hCc.of_subset (ConLeche.whnf_fvarLeaves m.wf fuel hred)⟩
  rcases hcase with rfl |
    ⟨us, entry, hfn, hfe, hilt, hlenA, hlenU, hfire, hwcf, hcert⟩
  · -- stuck: the projection of the reduced scrutinee, at the node's
    -- own entry kind
    obtain ⟨v₃', hv₃', hrd'⟩ := denoteMeta_proj_inv hea'
    obtain rfl : v₃ = v₃' := Option.some.inj (hv₃.symm.trans hv₃')
    rcases hrd with ⟨entry, hfe, rfl⟩ | ⟨hnt, hdec⟩
    · -- a stored entry: `projAV` congruence
      rcases hrd' with ⟨entry', hfe', rfl⟩ | ⟨hnt', -⟩
      · obtain rfl : entry = entry' := Option.some.inj (hfe.symm.trans hfe')
        exact ⟨fun σ hσ => WellDenotedV_projAV_congr (heq₃ σ hσ) (hok₃ σ hσ)
          (hokA σ hσ), fun σ hσ => interp_projAV_congr (heq₃ σ hσ)⟩
      · rw [hnt'] at hfe; exact nomatch hfe
    · -- table-free: the node's index decodes to the same former on
      -- both sides, so the congruence is one clause equation
      rcases hrd' with ⟨entry', hfe', -⟩ | ⟨-, hdec'⟩
      · rw [hnt] at hfe'; exact nomatch hfe'
      · rcases AnnotTerm.projPair?_cases₂ hdec hdec' with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
          · refine ⟨?_, ?_⟩
            · have h1 := (hokA σ hσ).1
              rw [WellDenoted_fst] at h1 ⊢
              obtain ⟨-, u, v, A, Bf, hsig, hA, hfib⟩ := h1
              exact ⟨(hok₃ σ hσ).1, u, v, A, Bf,
                (heq₃ σ hσ) ▸ hsig, hA, hfib⟩
            · rw [AnnotValid_fst]; exact (hok₃ σ hσ).2
          · rw [interp_fst, interp_fst, heq₃ σ hσ]
        · refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
          · refine ⟨?_, ?_⟩
            · have h1 := (hokA σ hσ).1
              rw [WellDenoted_snd] at h1 ⊢
              obtain ⟨-, u, v, A, Bf, hsig, hA, hfib⟩ := h1
              exact ⟨(hok₃ σ hσ).1, u, v, A, Bf,
                (heq₃ σ hσ) ▸ hsig, hA, hfib⟩
            · rw [AnnotValid_snd]; exact (hok₃ σ hσ).2
          · rw [interp_snd, interp_snd, heq₃ σ hσ]
  · -- the table fires
    -- the tower law's iota clause (task #175 wiring W5)
    obtain ⟨vp', hvp', rfl⟩ := denoteMeta_proj_inv_tower hfe hea
    obtain rfl : vp = vp' := Option.some.inj (hvp.symm.trans hvp')
    obtain ⟨-, -, -, -, hO5, cvC, hfC, hlpsC, hlaw, -⟩ := htower sn i entry hfe
    obtain ⟨-, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hlenU
    -- the constructor spine, read at the constructor's leaf
    have he₃ : e₃ = Expr.mkAppN (.const entry.ctor us) e₃.getAppArgs := by
      rw [← hfn]; exact (ConLeche.Expr.mkAppN_getApp e₃).symm
    have hv₃' := hv₃
    rw [he₃] at hv₃'
    obtain ⟨vf, vs, hvf, hspa, hveq⟩ := denoteMeta_mkAppN_inv hv₃'
    have hlenC : us.length = (ConstantInfo.ctorInfo cvC entry.numParams
        entry.numFields).toConstantVal.levelParams.length := by
      show us.length = cvC.levelParams.length
      rw [hlpsC]; exact hlenU
    rw [denoteMeta_const hfC hlenC] at hvf
    have hvf' : vf = m.acval entry.ctor (Level.substFn φ entry.levelParams us) := by
      rw [← hlpsC]; exact (Option.some.inj hvf).symm
    subst hvf'
    -- the selected argument's frames and reading
    have hidx : entry.numParams + i < e₃.getAppArgs.length := by
      rw [hlenA]; omega
    have hmem : e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0)
        ∈ e₃.getAppArgs := ConLeche.getD_mem hidx
    obtain ⟨hwF, hbF, hLF, hCF⟩ := frame_spine hw₃ hb₃ hL₃ hC₃ _ hmem
    have hlenVs : vs.length = entry.numParams + entry.numFields := by
      rw [← hspa.length]; exact hlenA
    have hfvd : denoteMeta m.acval env φ d
        (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
        = some (vs.getD (entry.numParams + i) default) :=
      hspa.getD_read hidx
    have hok₃' : ∀ σ : Nat → V, Sat V Δa σ →
        WellDenotedV V σ (AnnotTerm.mkAppN
          (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) vs) := by
      intro σ hσ; rw [← hveq]; exact hok₃ σ hσ
    obtain ⟨-, hoA⟩ := hoist_spine vs hok₃'
    have hokArg : ∀ σ : Nat → V, Sat V Δa σ →
        WellDenotedV V σ (vs.getD (entry.numParams + i) default) :=
      hoA _ (ConLeche.getD_mem (by rw [hlenVs]; omega))
    obtain ⟨hokE, heqE⟩ := ihwc hwcf hwF hbF hLF hCF hfvd hea' hokArg
    -- the certificate (task #175 W6): the spine fits the constructor
    -- type's reading — `projCert`'s `iotaCerts` through `certs_tele`
    obtain ⟨cvC', nP', nF', hfC', hcertI⟩ :=
      ConLeche.projCert_inv (ConLeche.projCertAtFueled_verified hμ hcert)
    obtain ⟨rfl, -, -⟩ :=
      ConstantInfo.ctorInfo.inj (Option.some.inj (hfC.symm.trans hfC'))
    have hwfC := m.wf _ (ConLeche.Semantics.Env.find?_mem hfC)
    have hnfC : (cvC.type.instantiateLevelParams cvC.levelParams us).hasFvar
        = false := by
      rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwfC.1
    have hbdC : (cvC.type.instantiateLevelParams cvC.levelParams
        us).looseBVarsBounded 0 = true := by
      rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
      exact hwfC.2.2.2.1
    have hTCd : denoteMeta m.acval env φ d
        (cvC.type.instantiateLevelParams cvC.levelParams us) = some TCa :=
      denoteMeta_depth_of_closed m.acval_closed hnfC
        (fun k => denoteMeta_closed m.acval_erase m.cval_closed hnfC hbdC hTCa 1 k)
        hTCa d
    have hTw : Expr.WScoped d
        (cvC.type.instantiateLevelParams cvC.levelParams us) :=
      ConLeche.Expr.WScoped.of_not_hasFvar hnfC
    have hTL : Expr.LeavesBounded
        (cvC.type.instantiateLevelParams cvC.levelParams us) :=
      ConLeche.Expr.LeavesBounded.of_not_hasFvar hnfC
    have hTC : CtxOk m φ d Δa
        (cvC.type.instantiateLevelParams cvC.levelParams us) :=
      ⟨hC.1, fun l hl => by
        rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfC] at hl
        exact nomatch hl⟩
    -- the reading's grading and the head's membership, off the stored
    -- constant's own
    obtain ⟨TCa', hTCa', hokTCa, hmemC0⟩ := hct 0 entry.ctor _ us hfC rfl
      (by show us.length = cvC.levelParams.length; rw [hlpsC]; exact hlenU)
    obtain rfl : TCa = TCa' := Option.some.inj (hTCa.symm.trans hTCa')
    have hmemC : ∀ σ : Nat → V, Sat V Δa σ →
        interp V σ (m.acval entry.ctor (Level.substFn φ entry.levelParams us))
          ∈ˢ interp V σ TCa := by
      intro σ _
      rw [← hlpsC]
      exact hmemC0 σ
    -- the ∀-chain, off the head data's arity pin
    obtain ⟨cvC'', hfC'', -, hstrip⟩ :=
      (m.proj_ok.towerHead hfe).2.2.2.2.2
    obtain ⟨rfl, -, -⟩ :=
      ConstantInfo.ctorInfo.inj (Option.some.inj (hfC.symm.trans hfC''))
    have hpc : PiChain e₃.getAppArgs.length TCa := by
      rw [hlenA]
      exact piChain_of_stripPis (entry.numParams + entry.numFields)
        (ConLeche.Expr.stripPis_instantiateLevelParams_isSome cvC.levelParams us _
          hstrip) hTCd
    -- the licensed walk (task #175 W6): the spine is a subject subterm,
    -- so the `.never` slots ride the application's own grading
    obtain ⟨resta, hfitA, -, -⟩ :=
      certs_teleLic ihd ihis hexi _ e₃.getAppArgs vs TCa
        (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) hcertI
        hTw hbdC hTL hTC hTCd (fun σ' _ => hokTCa σ')
        (frame_spine hw₃ hb₃ hL₃ hC₃) hspa hoA hok₃' hmemC
    refine ⟨hokE, fun σ hσ => ?_⟩
    have hfit : TeleFit V σ TCa (vs.map (interp V σ)) (interp V σ resta) :=
      teleFit_of_teleFitPA (by rw [← hspa.length]; exact hpc) (hfitA σ hσ)
    rw [interp_projAV_congr (heq₃ σ hσ), hveq,
      hB (towerGuardAt_of_fireOk hO5 hfire) σ vs _ hlenVs (hok₃' σ hσ) hfit]
    exact heqE σ hσ

end ConLeche.Model
