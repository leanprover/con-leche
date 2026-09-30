module

import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Semantics.Kit
import ConLeche.Verify.BetaGate
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetResidue
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Capstone
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Verify.Rules.InferBridge
import ConLeche.Verify.Subst
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetCallKit

public section

/-!
# A target call's target, at a valuation of the holes

The target check types every recursive call on the member-ABSTRACTED
terms (`targetCallOk`): at the rule frame extended by the block's
member HOLES (`targetHoles`, after the prefix and the fields), the
field's abstract type through whnf (`fnorm`) is defeq to
`∀ a⃗, hole_m x⃗ e⃗` (`hdeq`), whose body was inferred (`hwant`).  So at
EVERY valuation of the holes satisfying their types (each hole at its
member former's type), a field lying in its abstract type's reading has
its call target in the hole's family: the index readings fit the
member's index telescope at the parameters, and the applied field lies
in the hole applied to them.

`tgtCall_coreFitG` states that once, at a hole valuation `hv` with a
member-application law (`hlaw`: the hole of the callee's member, applied
to the parameters and a fitting index spine, is `Y` at the index
tuple), at any caller rule.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section MemberHoles

variable {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V} {pp : BlockParts}
  {cvTas : List ConstantVal}

/-- **The holes' values at their formers' types**: each member former's
type is closed and read, graded at every valuation, and holds the hole's
value `hv` — the formers' facts a call's typing (`targetCall_genW`) asks
for, from the members' run and `hv`'s typing. -/
theorem memberHoles_formers (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (ψ : Name → Nat) (ρ : Nat → V) {hv : List V}
    (hvTy : ∀ t, t < cvTas.length → ∃ T : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 (cvTas.getD t default).type = some T ∧
      hv.getD t pt ∈ˢ interp V ρ T) :
    ∀ t', t' < (cvTas.map (fun cv : ConstantVal => cv.type)).length →
      ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default).hasFvar = false ∧
      ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default).looseBVarsBounded 0 = true ∧
      ConstsBound envC ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default) ∧
      ∃ T : AnnotTerm, denoteMeta mpC.base2.acval envC ψ 0
          ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default)
          = some T ∧ (∀ σ : Nat → V, WellDenotedV V σ T) ∧
        ∀ σ : Nat → V, hv.getD t' pt ∈ˢ interp V σ T := by
  intro t' ht'
  have ht'' : t' < cvTas.length := by simpa using ht'
  obtain ⟨cv, hcv⟩ : ∃ cv, cvTas[t']? = some cv := ⟨_, List.getElem?_eq_getElem ht''⟩
  obtain ⟨-, -, ⟨caps, hfind⟩, hfv, hbv, hFD'⟩ := hmr.2.2.2.1 t' cv hcv
  have hg : (cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default = cv.type := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hcv]; rfl
  have hwf := mpC.base2.wf _ (List.mem_of_find?_eq_some hfind)
  obtain ⟨T', hT', hmemT'⟩ := hvTy t' ht''
  have hgc : (cvTas.getD t' default).type = cv.type := by
    rw [List.getD_eq_getElem?_getD, hcv]; rfl
  rw [hgc, hFD'.read ψ] at hT'
  obtain rfl := Option.some.inj hT'
  have hcl := bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hfv) hbv
    (hFD'.read ψ)
  rw [hg]
  exact ⟨hfv, hbv, constsBound_of_constsResolve _ hwf.2.2.1, _, hFD'.read ψ, hFD'.okTy ψ,
    fun σ => by rw [interp_closed V hcl σ ρ]; exact hmemT'⟩

end MemberHoles

end ConLeche.Model
