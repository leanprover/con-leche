module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Verify.Leaves
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Semantics.Kit

public section

/-!
# A target call's target at the CARRIER

`tgtCall_coreFitG` at the valuation that gives every member hole its
member constant's own value: the holes lie in their formers' types (the
constants inhabit their stored types, `EnvModelM.mem_type`), and the
called field lies in its member-abstracted type's reading because at
that valuation the abstraction IS the concrete term (`targetAbs_read`)
and the frame's fields fit their concrete readings.  The call target's
index readings then fit the callee's member's index telescope and the
applied field lies in the member's former applied to the parameters and
them — a MAJOR of the callee's class, which is what the graph kit's `ih`
rows read.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower

open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockShape TargetMajor)

universe w

variable {V : Type w} [SetTheory V]

section MemberHoles

variable {envC : Env} {mpC : EnvModelM V envC} {d : BlockData V} {pp : BlockShape}
  {cvTas : List ConstantVal}

/-- **The member constants' own values lie in their formers' types**
(`EnvModelM.mem_type`): the holes' values `hv`, when they are the
members' own values. -/
theorem memberHoles_ty (hmr : BlockMembersRun mpC.base2 d pp)
    (ψ : Name → Nat) (ρ : Nat → V) {hv : List V}
    (hvget : ∀ t, t < pp.formers.length →
      hv.getD t pt = interp V ρ (mpC.base2.acval (d.memberName t) ψ)) :
    ∀ t, t < pp.formers.length → ∃ T : Term,
      denote mpC.base2.acval envC ψ 0 (pp.formers.getD t default).type = some T ∧
      hv.getD t pt ∈ˢ interp V ρ T := by
  intro t ht
  obtain ⟨cv, hcv⟩ : ∃ cv, pp.formers[t]? = some cv := ⟨_, List.getElem?_eq_getElem ht⟩
  obtain ⟨hname, -, ⟨caps, hfind⟩, -, -, hFD⟩ := hmr.2.2.2.1 t cv hcv
  have hgc : pp.formers.getD t default = cv := by rw [List.getD_eq_getElem?_getD, hcv]; rfl
  rw [hgc, hvget t ht]
  refine ⟨_, hFD.read ψ, ?_⟩
  rw [hname]
  exact hfind.mem (hFD.read ψ) ρ

/-- **The member constants: found, at the block's levels, valued by
`hvC`** — `targetAbs_read`'s name premise at the members' own values. -/
theorem memberHoles_names (hN : BlockNamesOk (V := V) d pp.formers)
    (hmr : BlockMembersRun mpC.base2 d pp)
    (ψ : Name → Nat) (ρ : Nat → V) {hvC : Nat → V}
    (hvget : ∀ t, t < pp.formers.length → hvC t = interp V ρ (mpC.base2.acval (d.memberName t) ψ)) :
    ∀ (n : Name) (t : Nat),
      pp.memberNames.findIdx? (· == n) = some t →
      t < (pp.formers.map (·.type)).length ∧ ∃ ci : ConstantInfo, envC.find? n = some ci ∧
        (pp.lps.map Level.param).length = ci.toConstantVal.levelParams.length ∧
        ∀ σ : Nat → V, interp V σ (mpC.base2.acval n
          (Level.substFn ψ ci.toConstantVal.levelParams (pp.lps.map Level.param)))
          = hvC t := by
  intro n t hft
  obtain ⟨htl, hbeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hft
  have hmn : pp.memberNames[t] = n := by simpa using hbeq
  have htl' : t < pp.members.length := by
    simpa [ConLeche.BlockShape.memberNames] using htl
  have htc : t < pp.formers.length := by rw [hN.2.2, hmr.2.1]; exact htl'
  obtain ⟨cv, hcv⟩ : ∃ cv, pp.formers[t]? = some cv := ⟨_, List.getElem?_eq_getElem htc⟩
  obtain ⟨hname, hlps, ⟨caps, cvS, hfind, hDS⟩, -, -, -⟩ := hmr.2.2.2.1 t cv hcv
  obtain ⟨hnameMs, -⟩ := hmr.2.2.2.2.1 t _ (List.getElem?_eq_getElem htl')
  have hn : n = cv.name := by
    rw [← hmn, ← hname, hnameMs]
    simp [ConLeche.BlockShape.memberNames]
  subst hn
  refine ⟨by simpa using htc, .indInfo cvS caps, hfind,
    by show _ = cvS.levelParams.length; rw [hDS.lps, hlps]; simp, fun σ => ?_⟩
  show interp V σ (mpC.base2.acval cv.name (Level.substFn ψ cvS.levelParams
    (pp.lps.map Level.param))) = _
  rw [hDS.lps]
  rw [hlps, Level.substFn_param_self, ← hname, hvget t htc]
  exact acval_interp_closed mpC.base2 _ ψ σ ρ

end MemberHoles

end ConLeche.Model
