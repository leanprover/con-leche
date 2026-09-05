import Setlec.SetP.Step2.CapsRowsP
import Setlec.SetP.Step2.StuckP
import Setlec.SetP.Step2.InferIOP
import Setlec.SetBase.Spine2
import Setlec.SetP.Step2.TowerKitP
import Setlec.SetBase.SpineV

/-!
# The two semantic projection rows (task #161, PROJ/STR install tier)

`InferProjStepP` (`Step2/InferP.lean`) and `ProjStepP`
(`Step2/WhnfP.lean`), discharged.  Both are **pinned-basis** work: the
projection table admits only `pairFstEntry`/`pairSndEntry`
(`projEntry_pins`), so no stored family, no capability record and no
`EnvS2PM` field enters either proof — the recipe is the caps tier's
pinned-pair row (`pairEtaIrrelP_of_claims`) over the `psigmaV2` /
`psigmaMkV2` laws in `Interp2/Value.lean`.

## What each row costs

`InferProjStepP` is the cheap half.  The subject's inferred type
whnfs to `PSigma' A B`, `mem_psigmaV2_app` inverts that one
application into the three facts the pair space is made of, and then
everything is a `Value.lean` law: `sfst_mem2` for the first
component's membership, `ssnd_mem2` for the second's, and
`AnnotOk2_proj`'s own existential is *exactly* the triple
`mem_psigmaV2_app` returns.  The returned type is `projResidualP`'s
computed residual, so there is no `piResidualV` walk at all.

`ProjStepP`'s firing branch is the expensive half, and the reason is
structural rather than accidental: `whnfCore`'s projection clause has
**no type for the scrutinee in its premises**.  What it has is
`projCert`'s `inferTypeCore` run on the constructor application, and
the four typing memberships `sfst_mk2`/`ssnd_mk2` need have to be
walked out of that run — v1 does the same walk generically
(`tele_of_inferSpineR`); here it is done concretely, because the
constructor is pinned at arity four and each partial type is its own
whnf (`whnf_forallE_eq`).

A rigidity shortcut was looked for and does **not** exist: the
constructor's grading alone puts `interp2 vp` in *some* sigma set, but
in the `Prop` regime `psigmaMkV2` collapses the whole tower to `pt`,
so an ill-typed spine's value is a member of a sigma set just as a
well-typed one's is.  The memberships have to come from the run.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
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
  obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hnat, hlenArgs,
    hlenUs, hguard, ⟨ds, hpi⟩, hsn⟩ := Setlec.inferTypeCore_proj_inv h
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
  have htw : entry.tower = true := m.proj_ok.tower_of_native hfe hnat
  -- TOWER-BACKED (task #175 wiring W5): the tower law's typing clause
  obtain ⟨-, -, -, -, ⟨cvT, capsT, hfT, hlpsT, -⟩, hO5, -, -, -, hlaw, -⟩ :=
    htower T i entry hfe htw
  obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlaw us hlenUs
  obtain ⟨hTad, -⟩ := towerEntry_ty_at_depth hfe hTa
  obtain ⟨vp', hvp', rfl⟩ := denoteP_proj_inv_tower hfe htw hea
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
  obtain ⟨restA, hrest, hpeel⟩ := denoteP_instPisAt_peel m.acval_closed
    (acval_inst_self m) (te.getAppArgs ++ [pe]) hpi
    (Expr.WScoped.of_not_hasFvar (towerEntry_tyI_closed m.wf hfe us).1)
    hframes (hTad d) (hspt.snoc hvp)
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
  obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hnat, hlenArgs,
    hlenUs, hguard, ⟨ds, hpi⟩, hsn⟩ := Setlec.inferTypeCoreIO_proj_inv h
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
    rcases hrd with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩
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
  have htw : entry.tower = true := m.proj_ok.tower_of_native hfe hnat
  -- TOWER-BACKED (task #175 wiring W5): the tower law's typing clause
  obtain ⟨-, -, -, -, ⟨cvT, capsT, hfT, hlpsT, -⟩, hO5, -, -, -, hlaw, -⟩ :=
    htower T i entry hfe htw
  obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlaw us hlenUs
  obtain ⟨hTad, -⟩ := towerEntry_ty_at_depth hfe hTa
  obtain ⟨vp', hvp', rfl⟩ := denoteP_proj_inv_tower hfe htw hea
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
  obtain ⟨restA, hrest, hpeel⟩ := denoteP_instPisAt_peel m.acval_closed
    (acval_inst_self m) (te.getAppArgs ++ [pe]) hpi
    (Expr.WScoped.of_not_hasFvar (towerEntry_tyI_closed m.wf hfe us).1)
    hframes (hTad d) (hspt.snoc hvp)
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
theorem projStepP_of_claims {m : EnvS2Core V env}
    (htower : TowerOkP m φ)
    (ihwc : WhnfCoreClaims2P μ m φ fuel) (ihw : WhnfClaims2P μ m φ fuel)
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
    ⟨us, entry, hfn, hfe, hnat, hilt, hlenA, hlenU, hfire, hwcf, hcert⟩
  · -- stuck: the projection of the reduced scrutinee, at the node's
    -- own entry kind
    obtain ⟨v₃', hv₃', hrd'⟩ := denoteP_proj_inv hea'
    obtain rfl : v₃ = v₃' := Option.some.inj (hv₃.symm.trans hv₃')
    rcases hrd with ⟨entry, hfe, htw, rfl⟩ | ⟨hnt, hi2, rfl⟩
    · -- tower-backed: `projAV` congruence
      rcases hrd' with ⟨-, -, -, rfl⟩ | ⟨hnt', -, -⟩
      · exact ⟨fun σ hσ => AnnotOkP_projAV_congr (heq₃ σ hσ) (hok₃ σ hσ)
          (hokA σ hσ), fun σ hσ => interp2_projAV_congr (heq₃ σ hσ)⟩
      · exact absurd htw (by simp [hnt' entry hfe])
    · -- pair-backed
      rcases hrd' with ⟨entry', hfe', htw', -⟩ | ⟨-, -, rfl⟩
      · exact absurd htw' (by simp [hnt entry' hfe'])
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
    have htw : entry.tower = true := m.proj_ok.tower_of_native hfe hnat
    -- TOWER-BACKED (task #175 wiring W5): the tower law's iota clause
    obtain ⟨vp', hvp', rfl⟩ := denoteP_proj_inv_tower hfe htw hea
    obtain rfl : vp = vp' := Option.some.inj (hvp.symm.trans hvp')
    obtain ⟨-, -, -, -, -, hO5, cvC, hfC, hlpsC, hlaw, -⟩ := htower sn i entry hfe htw
    obtain ⟨-, hB⟩ := hlaw us hlenU
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
    refine ⟨hokE, fun σ hσ => ?_⟩
    rw [interp2_projAV_congr (heq₃ σ hσ), hveq,
      hB (towerStructPos_of_fireOk htw hfire) σ vs hlenVs (hok₃' σ hσ)]
    exact heqE σ hσ

end Setlec.SetR.Interp2
