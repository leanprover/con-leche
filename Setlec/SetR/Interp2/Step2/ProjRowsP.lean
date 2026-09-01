import Setlec.SetR.Interp2.Step2.CapsRowsP
import Setlec.SetR.Interp2.Step2.ProjPinsP

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

/-! ## The pinned pair type's leaf -/

/-- The pinned `PSigma'` leaf's value, by erasure injectivity (the
`unitIrrelPQ`/`pairEta` species). -/
theorem acval_psigma_leaf {m : EnvS2Core V env}
    (hpsig : env.find? Setlec.psigmaName = some Setlec.psigmaA)
    (ψ : Name → Nat) :
    m.acval Setlec.psigmaName ψ = .const .psigma [ψ uN, ψ vN] :=
  erase_eq_const (by
    rw [m.acval_erase,
      (m.base.basis_pinned _ _ hpsig (by decide)).2 _ _ rfl])

/-! ## `InferProjStepP` -/

/-- **`InferProjStepP`, discharged.**  The subject's type reduces to
the pinned pair applied to its two parameters; `mem_psigmaV2_app`
inverts that into the three facts `AnnotOk2_proj` asks for, and the
returned type is `projResidualP`'s computed residual — the first
parameter, or the second applied to the first projection. -/
theorem inferProjStepP_of_claims {m : EnvS2Core V env}
    (ihw : WhnfClaims2P μ m φ fuel) (ihi : InferClaims2P μ m φ fuel)
    (hreads : InferReadsP m μ φ fuel) (hwreads : WhnfReadsP m μ φ fuel) :
    InferProjStepP m μ φ fuel := by
  intro d i sn pe t Δa ea ta h hws hb hLb hC hea hta
  obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hnat, hlenArgs,
    hlenUs, -, hres⟩ := Setlec.inferTypeCore_proj_inv h
  -- the subject's frames
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOkP m φ d Δa pe :=
    hC.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hi2, rfl⟩ := denoteP_proj_inv hea
  -- its inferred type: reading, grading, membership
  obtain ⟨tpea, htpea⟩ :=
    hreads htpe hws hb hLpe (LeafReadsP.of_ctxOkP hCpe) hvp
  obtain ⟨hokPe, hokTpe, hmemPe⟩ := ihi htpe hws hb hLpe hCpe hvp htpea
  have hwtpe : Expr.WScoped d tpe :=
    Setlec.inferTypeCore_WScoped m.base.wf fuel htpe hws
  have hbtpe : tpe.looseBVarsBounded 0 = true :=
    Setlec.inferTypeCore_looseBVars m.base.wf fuel htpe hws hb hLpe
  have hLtpe : Expr.LeavesBounded tpe := fun l hl =>
    hLpe l (Setlec.inferTypeCore_fvarLeaves m.base.wf fuel htpe hws l hl)
  have hCtpe : CtxOkP m φ d Δa tpe :=
    hCpe.of_subset
      (Setlec.inferTypeCore_fvarLeaves m.base.wf fuel htpe hws)
  -- reduced to the family instance
  obtain ⟨tea, htea⟩ := hwreads hwte hwtpe hbtpe hLtpe htpea
  obtain ⟨hokTe, heqTe⟩ :=
    ihw hwte hwtpe hbtpe hLtpe hCtpe htpea htea hokTpe
  have hbte : te.looseBVarsBounded 0 = true :=
    Setlec.whnf_looseBVars m.base.wf fuel hwte hbtpe
  -- the entry's pins, and the returned type
  obtain ⟨rfl, -, -, -, -, -, hlU, -, hpsig, -⟩ :=
    projPinsP m.base.proj_ok hfe hnat
  obtain ⟨A, B, hAB, hcase⟩ :=
    projResidualP m.base.proj_ok hfe hnat hlenArgs hlenUs
      (fun x hx => Setlec.looseBVarsBounded_getAppArgs hbte x hx) hres
  -- the reduced type's spine
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (Setlec.Expr.mkAppN_getApp te).symm, hfn] at htea
  obtain ⟨vT, vs, hvT, hspt, hteq⟩ := denoteP_mkAppN_inv htea
  rw [denoteP_const hpsig (by rw [hlenUs, hlU]; rfl)] at hvT
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      Level.substFn φ Setlec.psigmaA.toConstantVal.levelParams us = ψ :=
    ⟨_, rfl⟩
  rw [hψ] at hvT
  obtain rfl : vT = m.acval Setlec.psigmaName ψ := (Option.some.inj hvT).symm
  rw [hAB] at hspt
  cases hspt with | @cons _ Aa _ vs' hAa hsp1 => ?_
  cases hsp1 with | @cons _ Ba _ _ hBa hsp2 => ?_
  cases hsp2
  subst hteq
  -- the pinned leaf, and the pair-space inversion
  have hleafI : m.acval Setlec.psigmaName ψ
      = .const .psigma [ψ uN, ψ vN] := acval_psigma_leaf hpsig ψ
  have hpack : ∀ σ : Nat → V, Sat2 V Δa σ →
      interp2 V σ Aa ∈ˢ (univ (ψ uN) : V) ∧
      interp2 V σ Ba ∈ˢ psigmaFibreSpace V (ψ vN) (interp2 V σ Aa) ∧
      interp2 V σ vp ∈ˢ sigmaSet (Nat.max (ψ uN) (ψ vN))
        (interp2 V σ Aa) fun y => SetTheory.app (interp2 V σ Ba) y := by
    intro σ hσ
    refine mem_psigmaV2_app V ?_
    have hm := (heqTe σ hσ) ▸ hmemPe σ hσ
    rw [show AVExpr.mkAppN (m.acval Setlec.psigmaName ψ) [Aa, Ba]
        = AVExpr.app (.app (m.acval Setlec.psigmaName ψ) Aa) Ba from rfl,
      interp2_app, interp2_app, hleafI, interp2_const] at hm
    exact hm
  -- the two parameters' gradings
  obtain ⟨-, hoT⟩ := hoistP_spine [Aa, Ba] hokTe
  have hokAa : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ Aa :=
    hoT Aa (by simp)
  have hokBa : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ Ba :=
    hoT Ba (by simp)
  -- the subject's own grading (`AnnotOk2_proj` is the pack, verbatim)
  have hokProj : ∀ j : Nat, j < 2 → ∀ σ : Nat → V, Sat2 V Δa σ →
      AnnotOkP V σ ((.proj j vp) : AVExpr) := by
    intro j hj σ hσ
    obtain ⟨hA, hB, hsig⟩ := hpack σ hσ
    refine ⟨?_, ?_⟩
    · rw [AnnotOk2_proj]
      exact ⟨(hokPe σ hσ).1, hj, _, _, _, _, hsig, hA,
        fun x hx => psigmaFibre_apply V hB hx⟩
    · rw [AnnotValidV_proj]; exact (hokPe σ hσ).2
  have hokSubj : ∀ σ : Nat → V, Sat2 V Δa σ →
      AnnotOkP V σ ((.proj i vp) : AVExpr) := hokProj i hi2
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- the first component
    obtain rfl : ta = Aa := Option.some.inj (hta.symm.trans hAa)
    refine ⟨hokSubj, hokAa, fun σ hσ => ?_⟩
    obtain ⟨hA, -, hsig⟩ := hpack σ hσ
    rw [interp2_proj, if_pos rfl]
    exact sfst_mem2 V hA hsig
  · -- the second component: the fibre at the first projection
    have hcompute : denoteP m.acval env φ d
        (Expr.app B (.proj Setlec.psigmaName 0 pe))
        = some ((.app Ba (.proj 0 vp)) : AVExpr) := by
      rw [denoteP_app, hBa, denoteP_proj, hvp]
      rfl
    obtain rfl : ta = .app Ba (.proj 0 vp) :=
      Option.some.inj (hta.symm.trans hcompute)
    refine ⟨hokSubj, fun σ hσ => ?_, fun σ hσ => ?_⟩
    · obtain ⟨hA, hB, hsig⟩ := hpack σ hσ
      refine ⟨?_, ?_⟩
      · rw [AnnotOk2_app]
        refine ⟨(hokBa σ hσ).1, (hokProj 0 (by omega) σ hσ).1, (ψ vN) + 1,
          interp2 V σ Aa, (fun _ => (univ (ψ vN) : V)), hB, ?_,
          fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
        rw [interp2_proj, if_pos rfl]
        exact sfst_mem2 V hA hsig
      · rw [AnnotValidV_app]
        exact ⟨(hokBa σ hσ).2, (hokProj 0 (by omega) σ hσ).2⟩
    · obtain ⟨hA, hB, hsig⟩ := hpack σ hσ
      rw [interp2_proj, if_neg (by omega), interp2_app, interp2_proj,
        if_pos rfl]
      exact ssnd_mem2 V hA hB hsig

end Setlec.SetR.Interp2
