import Setlec.SetBase.Bridge.DefEqClosed

/-!
# The projection inference clause (task #148, T3, batch e)

I9 `Infer.proj`, and the three reusable pieces it needed.

**The pinned entry makes everything a computation.**  `ProjOkT`
(`EnvR.proj_ok`) says a `native` table entry is one of the two pinned
pair entries, so `entry.ty` is a *concrete closed expression*: its
denotation is `denote_pairFstTy_eq` / `denote_pairSndTy_eq`
(`Setlec/SetR/ProjPins.lean`, relocated below both tiers because the
soundness side built them first and needs the same four facts), its
closedness and depth-independence are `denote_closedExprR`, and the
`i < 2` guard that `denote`'s `.proj` clause imposes comes from the
entry's own index.

**`denote_piResidualR` is the clause's real content.**  The checker
states the conclusion type as `piResidual (entry.ty@us) (args ++ [pe])`
and I9 states it as `piResidualV TP (ps ++ [p])`; both peel a `∀` one
argument at a time and instantiate, and the denotation of the
instantiated body is the `VExpr`-level `inst` (`denote_beta`), so the
two walks agree step for step.  That lemma is the `.proj` analogue of
what `certs_teleR` is for `iotaCerts` — and, like it, it needed no
conversion: the rule was already shaped to take what the checker
computes.

Task #129's `projParamCert` used to arrive `mode.ttChecks`-gated and
be discarded; the check was deleted at task #161's de-gating round
(item A, harvest site 20), so the inversion no longer produces it.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify
variable {mode : CheckMode} {env : Env}

/-- **`denote` commutes with `piResidual`.**  Both peel a `∀` one
argument at a time and instantiate; the denotation of the instantiated
body is the `VExpr`-level `inst` (`denote_beta`), so the two walks agree
step for step.  The `.proj` inference clause states its conclusion type
with `piResidual`, and I9 states it with `piResidualV`. -/
theorem denote_piResidualR {cval : TConstVal} {φ : Name → Nat}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ)) {d : Nat} :
    ∀ {T : Expr} {args : List Expr} {rest : Expr} {TV : VExpr}
      {vs : List VExpr},
      piResidual T args = some rest →
      denote cval env φ d T = some TV →
      DenoteSpine cval env φ d args vs →
      Expr.WScoped d T → T.looseBVarsBounded 0 = true →
      (∀ x ∈ args, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true) →
      ∃ RV, denote cval env φ d rest = some RV ∧
        piResidualV TV vs = some RV := by
  intro T args
  induction args generalizing T with
  | nil =>
    intro rest TV vs hres hT hsp _ _ _
    cases hsp
    obtain rfl : rest = T := (Option.some.inj hres).symm
    exact ⟨TV, hT, rfl⟩
  | cons a as ih =>
    intro rest TV vs hres hT hsp hwT hbT hfr
    match T, hres, hT, hwT, hbT with
    | .bvar _, hres, _, _, _ => exact nomatch hres
    | .fvar _ _ _, hres, _, _, _ => exact nomatch hres
    | .sort _, hres, _, _, _ => exact nomatch hres
    | .const _ _, hres, _, _, _ => exact nomatch hres
    | .app _ _, hres, _, _, _ => exact nomatch hres
    | .lam _ _ _ _, hres, _, _, _ => exact nomatch hres
    | .letE _ _ _ _, hres, _, _, _ => exact nomatch hres
    | .lit _, hres, _, _, _ => exact nomatch hres
    | .proj _ _ _, hres, _, _, _ => exact nomatch hres
    | .forallE n ty body mb, hres, hT, hwT, hbT =>
    cases hsp with | cons hav hsp' => ?_
    rename_i va _
    simp only [Expr.WScoped] at hwT
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbT
    rw [denote_forallE] at hT
    split at hT
    · exact nomatch hT
    · next A hA =>
      split at hT
      · exact nomatch hT
      · next B hB =>
        obtain rfl : TV = .pi A B := (Option.some.inj hT).symm
        obtain ⟨hwa, hba⟩ := hfr a (by simp)
        have hbody : denote cval env φ d (body.instantiate1 a)
            = some (VExpr.inst B va) := by
          rw [denote_beta (n := n) (ty := ty) hcl hwT.2.fvarsBelow hwa hba
            hav 0, hB]
          rfl
        have hrec := ih hres hbody hsp'
          (Expr.WScoped.instantiate1_gen hwa 0 hwT.2)
          (Expr.looseBVarsBounded_instantiate1_gen hba hbT.2)
          (fun x hx => hfr x (by simp [hx]))
        simpa only [piResidualV] using hrec

/-- A closed stored expression's denotation is depth-independent and
closed — the packaged form of `denote_closed` + `denote_lift` that every
*pinned* (rather than *stored*) type needs, where `EnvR.wf` does not
apply. -/
theorem denote_closedExprR {cval : TConstVal} {φ : Name → Nat}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ)) {E : Expr} {V : VExpr}
    (hnf : E.hasFvar = false) (hbd : E.looseBVarsBounded 0 = true)
    (h0 : denoteClosed cval env φ E = some V) :
    VExpr.Closed V ∧ ∀ D, denote cval env φ D E = some V := by
  refine ⟨denote_closed hcl hnf hbd h0, fun D => ?_⟩
  rw [denote_lift hcl (Expr.WScoped.of_not_hasFvar hnf).fvarsBelow D
    (Nat.zero_le D)]
  rw [denoteClosed] at h0
  rw [h0]
  simp only [Option.map_some, Nat.sub_zero,
    VExpr.liftN_eq_self_of_closed (denote_closed hcl hnf hbd (by
      rw [denoteClosed]; exact h0))]

/-- A two-element level list, split. -/
theorem List.length_two' {α : Type _} {l : List α} (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

/-- The pinned entry's type, denoted at any depth, with its
closedness — the three side conditions I9 asks for, from
`Setlec/SetR/ProjPins.lean`'s concrete computations. -/
theorem denote_entryTyR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    {entry : ProjEntry} {us : List Level}
    (hpin : entry = pairFstEntry ∨ entry = pairSndEntry)
    (hpsig : env.find? psigmaName = some psigmaA)
    (hlen : us.length = entry.levelParams.length) :
    ∃ TP, denoteClosed m.cval env φ
        (entry.ty.instantiateLevelParams entry.levelParams us) = some TP ∧
      VExpr.Closed TP ∧
      ∀ D, denote m.cval env φ D
        (entry.ty.instantiateLevelParams entry.levelParams us) = some TP := by
  have hlen2 : us.length = 2 := by
    rcases hpin with rfl | rfl <;> simpa [pairFstEntry, pairSndEntry] using hlen
  obtain ⟨l0, l1, rfl⟩ := List.length_two' hlen2
  have hnf : (entry.ty.instantiateLevelParams entry.levelParams [l0, l1]).hasFvar
      = false := by
    rw [Expr.hasFvar_instantiateLevelParams]
    rcases hpin with rfl | rfl <;> rfl
  have hbd : (entry.ty.instantiateLevelParams entry.levelParams
      [l0, l1]).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]
    rcases hpin with rfl | rfl <;> rfl
  rcases hpin with rfl | rfl
  · obtain ⟨hc, hd⟩ := denote_closedExprR hcl hnf hbd
      (denote_pairFstTy_eq (cval := m.cval) (φ := φ) hpsig l0 l1)
    exact ⟨_, denote_pairFstTy_eq hpsig l0 l1, hc, hd⟩
  · obtain ⟨hc, hd⟩ := denote_closedExprR hcl hnf hbd
      (denote_pairSndTy_eq (cval := m.cval) (φ := φ) hpsig
        (fun e he => m.proj_ok.towerFree _ _ _ he) l0 l1)
    exact ⟨_, denote_pairSndTy_eq hpsig
      (fun e he => m.proj_ok.towerFree _ _ _ he) l0 l1, hc, hd⟩

/-- **`InferProjStepR`, proved** (I9).  Head-match only — task #129's
`projParamCert` was TT-lane-only and is deleted (task #161, item A). -/
theorem inferProj_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel) :
    InferProjStepR (mode := mode) m φ fuel := by
  intro d Δ sn i pe t h hws hb hLb hC
  obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hnat, hlenArgs,
    hlenUs, hpair, -⟩ := inferTypeCore_proj_inv h
  obtain ⟨A₀, B₀, hargs₀, hcomp⟩ :=
    hpair (projEntry_not_tower m.proj_ok hfe hnat)
  obtain ⟨hpin, rfl, hidx, hpsig, hpsigMk⟩ := projEntry_pins m.proj_ok hfe hnat
  -- the subject's frames, and its type reduced to the family application
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOkR mode m.cval env φ d Δ pe :=
    CtxOkR.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl) hC
  obtain ⟨vp, W, hvp, hW, TP0, hpI, hpD⟩ :=
    inferShapeR m φ ihw ihi htpe hwte hws hb hLpe hCpe
  obtain ⟨htpew, htpeb, htpeL, htpeC⟩ := frame_inferR m.wf htpe hws hb hLpe hCpe
  have hwr : Expr.WScoped d te := whnf_WScoped m.wf fuel hwte htpew
  have hbr : te.looseBVarsBounded 0 = true := whnf_looseBVars m.wf fuel hwte htpeb
  have hLr : Expr.LeavesBounded te := fun l hl =>
    htpeL l (whnf_fvarLeaves m.wf fuel hwte l hl)
  have hCr : CtxOkR mode m.cval env φ d Δ te :=
    CtxOkR.of_subset (whnf_fvarLeaves m.wf fuel hwte) htpeC
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (Expr.mkAppN_getApp te).symm, hfn] at hW
  obtain ⟨vT, ps, hvT, hspt, rfl⟩ := denote_mkAppN_inv hW
  rw [denote_const, hpsig] at hvT
  dsimp only at hvT
  split at hvT
  · next hlenT =>
    obtain rfl : vT = m.cval psigmaName
        (Level.substFn φ psigmaA.toConstantVal.levelParams us) :=
      (Option.some.inj hvT).symm
    -- the entry's type, denoted
    obtain ⟨TP, hTP0, hTPc, hTPd⟩ := denote_entryTyR m φ hcl hpin hpsig hlenUs
    -- the residual walk
    have hframes : ∀ x ∈ te.getAppArgs ++ [pe],
        Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true := by
      intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact ⟨(frame_spineR hwr hbr hLr hCr x hx').1,
          (frame_spineR hwr hbr hLr hCr x hx').2.1⟩
      · rcases List.mem_singleton.mp hx' with rfl
        exact ⟨hws, hb⟩
    -- task #161 item B2 (harvest site 21 / P10): the clause returns
    -- the *computed* residual; `piResidual_of_computed` turns it back
    -- into the walk this tier's `Infer.proj` states, using the pin and
    -- the two parameters' frames (which `hframes` already supplies).
    have hres : Setlec.piResidual
        (entry.ty.instantiateLevelParams entry.levelParams us)
        (te.getAppArgs ++ [pe]) = some t := by
      rw [hargs₀]
      exact piResidual_of_computed m.proj_ok hfe hnat hlenUs
        (hframes A₀ (by rw [hargs₀]; simp)).2
        (hframes B₀ (by rw [hargs₀]; simp)).2 hcomp
    obtain ⟨RV, hRV, hpres⟩ :=
      denote_piResidualR hcl hres (hTPd d)
        (hspt.append (DenoteSpine.cons hvp DenoteSpine.nil))
        (Expr.WScoped.of_not_hasFvar (by
          rw [Expr.hasFvar_instantiateLevelParams]
          rcases hpin with rfl | rfl <;> rfl))
        (by rw [Expr.looseBVarsBounded_instantiateLevelParams]
            rcases hpin with rfl | rfl <;> rfl)
        hframes
    have hi2 : i < 2 := by
      rcases hpin with rfl | rfl <;> · rw [← hidx]; simp [pairFstEntry, pairSndEntry]
    refine ⟨.proj i vp, RV, ?_, hRV, RV,
      Infer.proj hfe hnat (by rw [hspt.length, hlenArgs]) hlenUs hpsig
        (by rw [← hlenT]) hTP0 hTPc hpres hpI hpD, DefEq.refl⟩
    rw [denote_proj_pair m.cval env φ d sn i pe
      (fun entry' hf' => m.proj_ok.towerFree _ _ _ hf'), hvp]
    dsimp only
    rw [if_pos hi2]
  · exact nomatch hvT

end Setlec.SetR
