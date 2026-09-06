import Setlec.SetP.Step2.CapsRowsP
import Setlec.SetP.Step2.StuckP
import Setlec.SetP.Step2.InferIOP
import Setlec.Semantics.Spine2
import Setlec.SetP.Step2.TowerKitP
import Setlec.SetP.Step2.IotaGateP
import Setlec.Semantics.SpineV

/-!
# The semantic projection rows (task #161, PROJ/STR install tier;
task #175 W5/W6, the tower route)

`InferProjStepP`/`InferProjStepIOP` (`Step2/InferP.lean`,
`Step2/InferIOP.lean`) and `ProjStepP` (`Step2/WhnfP.lean`),
discharged.  Every native projection-table entry is tower-backed
(`ProjOkT`, task #175 W6: the pinned `PSigma'` pair entries are
retired), so every row is the tower law's (`TowerEntryLawP`, keyed on
the entry by `TowerOkP`):

* the two infer rows read the returned type as the checker's peel of
  the stored entry type (`denoteP_instPisAt_peel`) and take the three
  conclusions from the law's typing clause (A);
* `ProjStepP`'s stuck branch is a congruence under the projection
  reading; its firing branch is the law's iota clause (B) at the
  constructor application's graded reading, with the certified spine's
  fit (`projCert`'s `iotaCerts`, through the ι slot's licensed walk
  `certs_teleLicP`, bridged to the value-level fit by
  `teleFitP_of_teleFitPA`) as the squash-regime premise.

Why the fit is a premise (the W6 finding): `whnfCore`'s projection
clause has **no type for the scrutinee in its premises**; at a graph
instantiation the application's grading pins every slot (graph
rigidity), but at a squash instantiation the application is the point
and a grading pins nothing — an ill-typed spine's value is the point
just as a well-typed one's is.  The memberships have to come from the
run, and `projCert` is that run.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.Semantics (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ProjEntry
  inferTypeCore whnf whnfCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## `InferProjStepP` -/

/-- **`InferProjStepP`, discharged.**  At a pair-backed entry the
subject's type reduces to the pinned pair applied to its two
parameters; `mem_psigmaV2_app` inverts that into the three facts
`AnnotOk2_proj` asks for, and the returned type is `projResidualP`'s
computed residual — the first parameter, or the second applied to the
first projection.  At a tower-backed entry (task #175 wiring W5) the
returned type is the checker's peel of the stored entry type along the
parameters and the subject, whose reading is the syntactic peel of the
entry type's reading (`denoteP_instPisAt_peel`), and the three
conclusions are the tower law's typing clause at the reduced subject
type's graded reading. -/
theorem inferProjStepP_of_claims {m : EnvS2Core V env}
    (htower : TowerOkP m φ)
    (ihw : WhnfClaims2P μ m φ fuel) (ihi : InferClaims2P μ m φ fuel)
    (hreads : InferReadsP m μ φ fuel) (hwreads : WhnfReadsP m μ φ fuel) :
    InferProjStepP m μ φ fuel := by
  intro d i sn pe t Δa ea ta h hws hb hLb hC hea hta
  obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hlenArgs,
    hlenUs, hguard, rfl, hsn⟩ := Setlec.inferTypeCore_proj_inv h
  subst hsn
  -- the subject's frames
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOkP m φ d Δa pe :=
    hC.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hrd⟩ := denoteP_proj_inv hea
  -- its inferred type: reading, grading, membership
  obtain ⟨tpea, htpea⟩ :=
    hreads htpe hws hb hLpe (LeafReadsP.of_ctxOkP hCpe) hvp
  obtain ⟨hokPe, hokTpe, hmemPe⟩ := ihi htpe hws hb hLpe hCpe hvp htpea
  have hwtpe : Expr.WScoped d tpe :=
    Setlec.inferTypeCore_WScoped m.wf fuel htpe hws
  have hbtpe : tpe.looseBVarsBounded 0 = true :=
    Setlec.inferTypeCore_looseBVars m.wf fuel htpe hws hb hLpe
  have hLtpe : Expr.LeavesBounded tpe := fun l hl =>
    hLpe l (Setlec.inferTypeCore_fvarLeaves m.wf fuel htpe hws l hl)
  have hCtpe : CtxOkP m φ d Δa tpe :=
    hCpe.of_subset
      (Setlec.inferTypeCore_fvarLeaves m.wf fuel htpe hws)
  -- reduced to the family instance
  obtain ⟨tea, htea⟩ := hwreads hwte hwtpe hbtpe hLtpe
    (LeafReadsP.of_ctxOkP hCtpe) htpea
  obtain ⟨hokTe, heqTe⟩ :=
    ihw hwte hwtpe hbtpe hLtpe hCtpe htpea htea hokTpe
  have hwte' : Expr.WScoped d te := Setlec.whnf_WScoped m.wf fuel hwte hwtpe
  have hbte : te.looseBVarsBounded 0 = true :=
    Setlec.whnf_looseBVars m.wf fuel hwte hbtpe
  -- the tower law's typing clause (task #175 wiring W5)
  obtain ⟨-, -, -, ⟨cvT, capsT, hfT, hlpsT, -⟩, hO5, _, -, -, hlaw, -⟩ :=
    htower T i entry hfe
  obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlaw us hlenUs
  obtain ⟨vp', hvp', rfl⟩ := denoteP_proj_inv_tower hfe hea
  obtain rfl : vp = vp' := Option.some.inj (hvp.symm.trans hvp')
  -- the reduced type's spine, at the former's leaf
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (Setlec.Expr.mkAppN_getApp te).symm, hfn] at htea
  obtain ⟨vT, vs, hvT, hspt, hteq⟩ := denoteP_mkAppN_inv htea
  have hlenT : us.length
      = (ConstantInfo.indInfo cvT capsT).toConstantVal.levelParams.length := by
    show us.length = cvT.levelParams.length
    rw [hlpsT]; exact hlenUs
  rw [denoteP_const hfT hlenT] at hvT
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
        Setlec.looseBVarsBounded_getAppArgs hbte x hx'⟩
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hws, hb⟩
  obtain ⟨restA, hrest, hpeel⟩ :=
    denoteP_typeAt_peel hfe hTa hlenArgs hframes (hspt.snoc hvp)
  obtain rfl : ta = restA := Option.some.inj (hta.symm.trans hrest)
  have hlenVs : vs.length = entry.numParams := by
    rw [← hspt.length]; exact hlenArgs
  have hlaw' : ∀ σ : Nat → V, Sat2 V Δa σ →
      AnnotOkP V σ (projAV i vp) ∧ AnnotOkP V σ ta ∧
        interp2 V σ (projAV i vp) ∈ˢ interp2 V σ ta := fun σ hσ =>
    hA (towerGuardAt_of hO5 hguard) σ vs vp ta hlenVs (hokTe σ hσ)
      (hokPe σ hσ) ((heqTe σ hσ) ▸ hmemPe σ hσ) hpeel
  exact ⟨fun σ hσ => (hlaw' σ hσ).1, fun σ hσ => (hlaw' σ hσ).2.1,
    fun σ hσ => (hlaw' σ hσ).2.2⟩

/-! ## `InferProjStepIOP` (task #172 B4 — the B1b-assigned owed row)

`inferProjStepP_of_claims` transposed to the io lane: the scrutinee's
run is the io lane's (the clause infers it at the io grade) and the
subject's `AnnotOkP` moves to the premises, where its `AnnotOk2` proj
slot replaces the full lane's establishment of the scrutinee.  The
structure-type walk — whnf, the entry's pins, the spine, the pair-space
inversion — is the full row's, verbatim: those lanes are shared, which
is the io knot's leaf-lane asymmetry seen from the proj clause. -/

theorem inferProjStepIOP_of_claims {m : EnvS2Core V env}
    (htower : TowerOkP m φ)
    (ihw : WhnfClaims2P μ m φ fuel) (ihio : InferClaimsIO2P μ m φ fuel)
    (hreads : InferReadsIOP m μ φ fuel) (hwreads : WhnfReadsP m μ φ fuel) :
    InferProjStepIOP m μ φ fuel := by
  intro d i sn pe t Δa ea ta h hws hb hLb hC hea hta hok
  obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hlenArgs,
    hlenUs, hguard, rfl, hsn⟩ := Setlec.inferTypeCoreIO_proj_inv h
  subst hsn
  -- the subject's frames
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOkP m φ d Δa pe :=
    hC.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hrd⟩ := denoteP_proj_inv hea
  -- the scrutinee's AnnotOkP, off the subject's own proj slot (premise
  -- form: the full lane established it; the io lane reads it)
  have hokPe : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ vp := by
    intro ρ hρ
    rcases hrd with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact AnnotOkP_projAV_hoist (hok ρ hρ)
    · exact ⟨AnnotOk2.hoist_proj (V := V) (fun σ hσ => (hok σ hσ).1) ρ hρ,
        (AnnotValidV_proj V ρ i vp) ▸ (hok ρ hρ).2⟩
  -- its io-inferred type: reading, then grading + membership
  obtain ⟨tpea, htpea⟩ :=
    hreads htpe hws hb hLpe (LeafReadsP.of_ctxOkP hCpe) hvp
  obtain ⟨hokTpe, hmemPe⟩ := ihio htpe hws hb hLpe hCpe hvp htpea hokPe
  have hwtpe : Expr.WScoped d tpe :=
    Setlec.inferTypeCoreIO_WScoped m.wf fuel htpe hws
  have hbtpe : tpe.looseBVarsBounded 0 = true :=
    Setlec.inferTypeCoreIO_looseBVars m.wf fuel htpe hws hb hLpe
  have hLtpe : Expr.LeavesBounded tpe := fun l hl =>
    hLpe l (Setlec.inferTypeCoreIO_fvarLeaves m.wf fuel htpe hws l hl)
  have hCtpe : CtxOkP m φ d Δa tpe :=
    hCpe.of_subset
      (Setlec.inferTypeCoreIO_fvarLeaves m.wf fuel htpe hws)
  -- reduced to the family instance
  obtain ⟨tea, htea⟩ := hwreads hwte hwtpe hbtpe hLtpe
    (LeafReadsP.of_ctxOkP hCtpe) htpea
  obtain ⟨hokTe, heqTe⟩ :=
    ihw hwte hwtpe hbtpe hLtpe hCtpe htpea htea hokTpe
  have hwte' : Expr.WScoped d te := Setlec.whnf_WScoped m.wf fuel hwte hwtpe
  have hbte : te.looseBVarsBounded 0 = true :=
    Setlec.whnf_looseBVars m.wf fuel hwte hbtpe
  -- the tower law's typing clause (task #175 wiring W5)
  obtain ⟨-, -, -, ⟨cvT, capsT, hfT, hlpsT, -⟩, hO5, _, -, -, hlaw, -⟩ :=
    htower T i entry hfe
  obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlaw us hlenUs
  obtain ⟨vp', hvp', rfl⟩ := denoteP_proj_inv_tower hfe hea
  obtain rfl : vp = vp' := Option.some.inj (hvp.symm.trans hvp')
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (Setlec.Expr.mkAppN_getApp te).symm, hfn] at htea
  obtain ⟨vT, vs, hvT, hspt, hteq⟩ := denoteP_mkAppN_inv htea
  have hlenT : us.length
      = (ConstantInfo.indInfo cvT capsT).toConstantVal.levelParams.length := by
    show us.length = cvT.levelParams.length
    rw [hlpsT]; exact hlenUs
  rw [denoteP_const hfT hlenT] at hvT
  have hvT' : vT = m.acval T (Level.substFn φ entry.levelParams us) := by
    rw [← hlpsT]; exact (Option.some.inj hvT).symm
  subst hvT'
  subst hteq
  have hframes : ∀ x ∈ te.getAppArgs ++ [pe],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact ⟨hwte'.getAppArgs x hx',
        Setlec.looseBVarsBounded_getAppArgs hbte x hx'⟩
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hws, hb⟩
  obtain ⟨restA, hrest, hpeel⟩ :=
    denoteP_typeAt_peel hfe hTa hlenArgs hframes (hspt.snoc hvp)
  obtain rfl : ta = restA := Option.some.inj (hta.symm.trans hrest)
  have hlenVs : vs.length = entry.numParams := by
    rw [← hspt.length]; exact hlenArgs
  have hlaw' : ∀ σ : Nat → V, Sat2 V Δa σ →
      AnnotOkP V σ (projAV i vp) ∧ AnnotOkP V σ ta ∧
        interp2 V σ (projAV i vp) ∈ˢ interp2 V σ ta := fun σ hσ =>
    hA (towerGuardAt_of hO5 hguard) σ vs vp ta hlenVs (hokTe σ hσ)
      (hokPe σ hσ) ((heqTe σ hσ) ▸ hmemPe σ hσ) hpeel
  exact ⟨fun σ hσ => (hlaw' σ hσ).2.1, fun σ hσ => (hlaw' σ hσ).2.2⟩


/-! ## `ProjStepP` -/

/-- **An annotation-level fit is a value-level fit** (task #175 W6):
`TeleFitPA`'s `inst` residuals un-instantiate step by step
(`teleFitP_of_inst0`) under the ∀-chain guard — the bridge from the
licensed walk's output (`certs_teleLicP`) to the tower law's premise. -/
theorem teleFitP_of_teleFitPA {ρ : Nat → V} :
    ∀ {T : AVExpr} {as : List AVExpr} {resta : AVExpr},
      PiChainP as.length T → TeleFitPA V ρ T as resta →
      TeleFitP V ρ T (as.map (interp2 V ρ)) (interp2 V ρ resta) := by
  intro T as resta hpc h
  revert hpc
  induction h with
  | nil => intro _; exact .nil
  | @cons u v A B rest a as hmem hfit ih =>
    intro hpc
    have hpcB : PiChainP as.length B := hpc
    exact .cons hmem (teleFitP_of_inst0 (by rw [List.length_map]; exact hpcB)
      (ih (PiChainP.inst a 0 hpcB)))

/-- **`ProjStepP`, discharged.**  The stuck branch is a congruence
under the projection reading (pair: `.proj i`; tower: `projAV i`,
`AnnotOkP_projAV_congr`).  The firing branch at a pair-backed entry
identifies the reduct's value with `sfst`/`ssnd` of the constructor
application through `sfst_mk2`/`ssnd_mk2`, whose four typing
premises are `psigmaMkSpineP`'s walk of `projCert`'s own
`inferTypeCore` run; at a tower-backed entry (task #175 wiring W5) it
is the tower law's iota clause at the constructor application's graded
reading — no run is walked, the grading's slot chain is the whole
premise. -/
theorem projStepP_of_claims (hμ : μ.verifiedChecks = true) {m : EnvS2Core V env}
    (htower : TowerOkP m φ) (hct : ConstTypeP m φ)
    (ihwc : WhnfCoreClaims2P μ m φ fuel) (ihw : WhnfClaims2P μ m φ fuel)
    (ihd : DefEqClaims2P μ m φ fuel) (ihis : InferClaimsIOS2P μ m φ fuel)
    (hexi : InferExistsIOSP μ m φ fuel)
    (hwreads : WhnfReadsP m μ φ fuel) :
    ProjStepP μ m φ fuel := by
  intro d sn i pe e' Δa h hws hb hLb ea ea' hC hea hea' hokA
  obtain ⟨e₂, e₃, hwpe, hlit, hcase⟩ := Setlec.whnf_proj_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOkP m φ d Δa pe :=
    hC.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hrd⟩ := denoteP_proj_inv hea
  have hokVp : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ vp := by
    intro σ hσ
    rcases hrd with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact AnnotOkP_projAV_hoist (hokA σ hσ)
    · refine ⟨?_, ?_⟩
      · have h1 := (hokA σ hσ).1; rw [AnnotOk2_proj] at h1; exact h1.1
      · have h2 := (hokA σ hσ).2; rwa [AnnotValidV_proj] at h2
  -- the reduced scrutinee
  obtain ⟨v₂, hv₂⟩ := hwreads hwpe hws hb hLpe
    (LeafReadsP.of_ctxOkP hCpe) hvp
  obtain ⟨hok₂, heq₂⟩ := ihw hwpe hws hb hLpe hCpe hvp hv₂ hokVp
  have hw₂ : Expr.WScoped d e₂ := Setlec.whnf_WScoped m.wf fuel hwpe hws
  have hb₂ : e₂.looseBVarsBounded 0 = true :=
    Setlec.whnf_looseBVars m.wf fuel hwpe hb
  have hL₂ : Expr.LeavesBounded e₂ := fun l hl =>
    hLpe l (Setlec.whnf_fvarLeaves m.wf fuel hwpe l hl)
  have hC₂ : CtxOkP m φ d Δa e₂ :=
    hCpe.of_subset (Setlec.whnf_fvarLeaves m.wf fuel hwpe)
  -- the string-literal expansion, if it fired
  obtain ⟨v₃, hv₃, hok₃, heq₃, hw₃, hb₃, hL₃, hC₃⟩ :
      ∃ v₃, denoteP m.acval env φ d e₃ = some v₃ ∧
        (∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ v₃) ∧
        (∀ σ : Nat → V, Sat2 V Δa σ →
          interp2 V σ vp = interp2 V σ v₃) ∧
        Expr.WScoped d e₃ ∧ e₃.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e₃ ∧ CtxOkP m φ d Δa e₃ := by
    rcases Setlec.projLitToCtorP_inv hlit with rfl | ⟨st, rfl, hg, hred⟩
    · exact ⟨v₂, hv₂, hok₂, heq₂, hw₂, hb₂, hL₂, hC₂⟩
    · obtain ⟨hSC, hwc, hbc, hLc, hfv⟩ := denotePStrLit_of_guard d st hg hv₂
      have hCc : CtxOkP m φ d Δa (Setlec.strLitToConstructor st) :=
        ⟨hCpe.1, fun l hl => by rw [hfv] at hl; exact nomatch hl⟩
      obtain ⟨v₃, hv₃⟩ := hwreads hred hwc hbc hLc
        (fun l hl => by rw [hfv] at hl; exact nomatch hl) hSC
      obtain ⟨hok₃, heq₃⟩ := ihw hred hwc hbc hLc hCc hSC hv₃ hok₂
      exact ⟨v₃, hv₃, hok₃,
        fun σ hσ => (heq₂ σ hσ).trans (heq₃ σ hσ),
        Setlec.whnf_WScoped m.wf fuel hred hwc,
        Setlec.whnf_looseBVars m.wf fuel hred hbc,
        fun l hl => hLc l (Setlec.whnf_fvarLeaves m.wf fuel hred l hl),
        hCc.of_subset (Setlec.whnf_fvarLeaves m.wf fuel hred)⟩
  rcases hcase with rfl |
    ⟨us, entry, hfn, hfe, hilt, hlenA, hlenU, hfire, hwcf, hcert⟩
  · -- stuck: the projection of the reduced scrutinee, at the node's
    -- own entry kind
    obtain ⟨v₃', hv₃', hrd'⟩ := denoteP_proj_inv hea'
    obtain rfl : v₃ = v₃' := Option.some.inj (hv₃.symm.trans hv₃')
    rcases hrd with ⟨entry, hfe, rfl⟩ | ⟨hnt, hi2, rfl⟩
    · -- a stored entry: `projAV` congruence
      rcases hrd' with ⟨-, -, rfl⟩ | ⟨hnt', -, -⟩
      · exact ⟨fun σ hσ => AnnotOkP_projAV_congr (heq₃ σ hσ) (hok₃ σ hσ)
          (hokA σ hσ), fun σ hσ => interp2_projAV_congr (heq₃ σ hσ)⟩
      · rw [hnt'] at hfe; exact nomatch hfe
    · -- table-free
      rcases hrd' with ⟨entry', hfe', -⟩ | ⟨-, -, rfl⟩
      · rw [hnt] at hfe'; exact nomatch hfe'
      · refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
        · refine ⟨?_, ?_⟩
          · have h1 := (hokA σ hσ).1
            rw [AnnotOk2_proj] at h1 ⊢
            obtain ⟨-, -, u, v, A, Bf, hsig, hA, hfib⟩ := h1
            exact ⟨(hok₃ σ hσ).1, hi2, u, v, A, Bf,
              (heq₃ σ hσ) ▸ hsig, hA, hfib⟩
          · rw [AnnotValidV_proj]; exact (hok₃ σ hσ).2
        · rw [interp2_proj, interp2_proj, heq₃ σ hσ]
  · -- the table fires
    -- the tower law's iota clause (task #175 wiring W5)
    obtain ⟨vp', hvp', rfl⟩ := denoteP_proj_inv_tower hfe hea
    obtain rfl : vp = vp' := Option.some.inj (hvp.symm.trans hvp')
    obtain ⟨-, -, -, -, hO5, cvC, hfC, hlpsC, hlaw, -⟩ := htower sn i entry hfe
    obtain ⟨-, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hlenU
    -- the constructor spine, read at the constructor's leaf
    have he₃ : e₃ = Expr.mkAppN (.const entry.ctor us) e₃.getAppArgs := by
      rw [← hfn]; exact (Setlec.Expr.mkAppN_getApp e₃).symm
    have hv₃' := hv₃
    rw [he₃] at hv₃'
    obtain ⟨vf, vs, hvf, hspa, hveq⟩ := denoteP_mkAppN_inv hv₃'
    have hlenC : us.length = (ConstantInfo.ctorInfo cvC entry.numParams
        entry.numFields).toConstantVal.levelParams.length := by
      show us.length = cvC.levelParams.length
      rw [hlpsC]; exact hlenU
    rw [denoteP_const hfC hlenC] at hvf
    have hvf' : vf = m.acval entry.ctor (Level.substFn φ entry.levelParams us) := by
      rw [← hlpsC]; exact (Option.some.inj hvf).symm
    subst hvf'
    -- the selected argument's frames and reading
    have hidx : entry.numParams + i < e₃.getAppArgs.length := by
      rw [hlenA]; omega
    have hmem : e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0)
        ∈ e₃.getAppArgs := Setlec.getD_mem hidx
    obtain ⟨hwF, hbF, hLF, hCF⟩ := frame_spineP hw₃ hb₃ hL₃ hC₃ _ hmem
    have hlenVs : vs.length = entry.numParams + entry.numFields := by
      rw [← hspa.length]; exact hlenA
    have hfvd : denoteP m.acval env φ d
        (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
        = some (vs.getD (entry.numParams + i) default) :=
      hspa.getD_read hidx
    have hok₃' : ∀ σ : Nat → V, Sat2 V Δa σ →
        AnnotOkP V σ (AVExpr.mkAppN
          (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) vs) := by
      intro σ hσ; rw [← hveq]; exact hok₃ σ hσ
    obtain ⟨-, hoA⟩ := hoistP_spine vs hok₃'
    have hokArg : ∀ σ : Nat → V, Sat2 V Δa σ →
        AnnotOkP V σ (vs.getD (entry.numParams + i) default) :=
      hoA _ (Setlec.getD_mem (by rw [hlenVs]; omega))
    obtain ⟨hokE, heqE⟩ := ihwc hwcf hwF hbF hLF hCF hfvd hea' hokArg
    -- the certificate (task #175 W6): the spine fits the constructor
    -- type's reading — `projCert`'s `iotaCerts` through `certs_teleP`
    obtain ⟨cvC', nP', nF', hfC', hcertI⟩ :=
      Setlec.projCert_inv (Setlec.projCertAtP_verified hμ hcert)
    obtain ⟨rfl, -, -⟩ :=
      ConstantInfo.ctorInfo.inj (Option.some.inj (hfC.symm.trans hfC'))
    have hwfC := m.wf _ (Setlec.Semantics.Env.find?_mem hfC)
    have hnfC : (cvC.type.instantiateLevelParams cvC.levelParams us).hasFvar
        = false := by
      rw [Setlec.Expr.hasFvar_instantiateLevelParams]; exact hwfC.1
    have hbdC : (cvC.type.instantiateLevelParams cvC.levelParams
        us).looseBVarsBounded 0 = true := by
      rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
      exact hwfC.2.2.2.1
    have hTCd : denoteP m.acval env φ d
        (cvC.type.instantiateLevelParams cvC.levelParams us) = some TCa :=
      denoteP_depth_of_closed m.acval_closed hnfC
        (fun k => denoteP_closed m.acval_erase m.cval_closed hnfC hbdC hTCa 1 k)
        hTCa d
    have hTw : Expr.WScoped d
        (cvC.type.instantiateLevelParams cvC.levelParams us) :=
      Setlec.Expr.WScoped.of_not_hasFvar hnfC
    have hTL : Expr.LeavesBounded
        (cvC.type.instantiateLevelParams cvC.levelParams us) :=
      Setlec.Expr.LeavesBounded.of_not_hasFvar hnfC
    have hTC : CtxOkP m φ d Δa
        (cvC.type.instantiateLevelParams cvC.levelParams us) :=
      ⟨hC.1, fun l hl => by
        rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfC] at hl
        exact nomatch hl⟩
    -- the reading's grading and the head's membership, off the stored
    -- constant's own
    obtain ⟨TCa', hTCa', hokTCa, hmemC0⟩ := hct 0 entry.ctor _ us hfC rfl
      (by show us.length = cvC.levelParams.length; rw [hlpsC]; exact hlenU)
    obtain rfl : TCa = TCa' := Option.some.inj (hTCa.symm.trans hTCa')
    have hmemC : ∀ σ : Nat → V, Sat2 V Δa σ →
        interp2 V σ (m.acval entry.ctor (Level.substFn φ entry.levelParams us))
          ∈ˢ interp2 V σ TCa := by
      intro σ _
      rw [← hlpsC]
      exact hmemC0 σ
    -- the ∀-chain, off the head data's arity pin
    obtain ⟨cvC'', hfC'', -, hstrip⟩ :=
      (m.proj_ok.towerHead hfe).2.2.2.2.2
    obtain ⟨rfl, -, -⟩ :=
      ConstantInfo.ctorInfo.inj (Option.some.inj (hfC.symm.trans hfC''))
    have hpc : PiChainP e₃.getAppArgs.length TCa := by
      rw [hlenA]
      exact piChainP_of_stripPis (entry.numParams + entry.numFields)
        (Setlec.Expr.stripPis_instantiateLevelParams_isSome cvC.levelParams us _
          hstrip) hTCd
    -- the licensed walk (task #175 W6): the spine is a subject subterm,
    -- so the `.never` slots ride the application's own grading
    obtain ⟨resta, hfitA, -, -⟩ :=
      certs_teleLicP ihd ihis hexi _ e₃.getAppArgs vs TCa
        (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) hcertI
        hTw hbdC hTL hTC hTCd (fun σ' _ => hokTCa σ')
        (frame_spineP hw₃ hb₃ hL₃ hC₃) hspa hoA hok₃' hmemC
    refine ⟨hokE, fun σ hσ => ?_⟩
    have hfit : TeleFitP V σ TCa (vs.map (interp2 V σ)) (interp2 V σ resta) :=
      teleFitP_of_teleFitPA (by rw [← hspa.length]; exact hpc) (hfitA σ hσ)
    rw [interp2_projAV_congr (heq₃ σ hσ), hveq,
      hB (towerGuardAt_of_fireOk hO5 hfire) σ vs _ hlenVs (hok₃' σ hσ) hfit]
    exact heqE σ hσ

end Setlec.SetP
