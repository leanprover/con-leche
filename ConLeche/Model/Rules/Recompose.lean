module

public import ConLeche.Model.Rules.Inputs
public import ConLeche.Model.Steps.Tiers
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.BetaGate

public section

/-!
# The recomposition: `checkSoundAtP5` through the rules tier (task #305)

The five claims of `Model/Claims*.lean` at every fuel, with EXACTLY the
statement of `Model/Steps/Tiers.lean`'s `checkSoundAtP5` /
`checkSoundAt`, assembled from the bridge (`Verify/Rules/Bridge.lean`:
run ⇒ derivation) and the soundness (`Model/Rules/Sound.lean`:
derivation ⇒ P currency).  Each claim is a few lines: bridge the run,
apply the soundness at the claim's premises, identify the claim's
reading with the existence form's by `Option.some.inj`.

This is the ONE module that imports both the bridge and `Model/Steps/*`
(for `TierInputsAt` and, provisionally, the two literal rows).  At the
end of the campaign `Model/Steps/*` is deleted and `Tiers.lean`
re-exports this file's theorems under the landed names.

**The two literal rows** (`RulesInputs.nat_succ`, `.nat_op`) are the
one place `TierInputsAt` does not hand over a semantic fact: its
`nat_step`/`nat_stepQ` fields are RUN rows (`ReduceNatStep` at every
fuel, each under `WhnfClaim` at that fuel).  The semantic content is
recovered by instantiating the run row at the literal run — `whnf` at
fuel `≥ 2` is the identity on a `rawNatLit?` shape, so `reduceNat` at
fuel `2` fires on `c wa wb` outright — which needs `WhnfClaim μ m φ 2`,
obtainable from the old assembly's `whnf_claims` at fuels `0` and `1`.
That derivation is lane R-nat's; here it is `sorry`, and the DESIGN
record proposes the durable fix (semantic nat fields on
`TierInputsAt`, supplied by `Model/NatStep.lean` from
`EnvModelM.nat_ops`/`div_mod`, which is where the content lives).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}
  {φ : Name → Nat}

/-- **The rules inputs from the tier inputs.**  Seven fields are the
same facts (`ConstTy`/`LeafValid`/`NatLeafHeads`/`DefnReads` are
`ConstType`/`AcvalValid`/`NatHeads`/`AcvalDefnInst` restated, so the
projections typecheck by unfolding); the two literal rows are the
residue named in the module docstring. -/
theorem RulesInputs.ofTier {m : EnvModel V env} (h : TierInputsAt V μ m φ) :
    RulesInputs V m φ where
  const_ty := h.reads.const_ty
  leaf_valid := h.acval_valid
  nat_heads := h.nat_heads
  defn := h.reads.defn
  tower_ok := h.reads.tower_ok
  rec_rules := h.rec_rules
  caps_ok := h.caps_ok
  nat_succ := by sorry
  nat_op := by sorry

/-- **`checkSoundAtP5`, recomposed** — statement identical to
`Model/Steps/Tiers.lean`'s. -/
theorem checkSoundAtP5_rules (hμ : μ.verifiedChecks = true)
    {m : EnvModel V env} (h : TierInputsAt V μ m φ) :
    ∀ fuel : Nat,
      WhnfCoreClaim μ m φ fuel ∧ WhnfClaim μ m φ fuel ∧
        DefEqClaim μ m φ fuel ∧ InferClaim μ m φ fuel ∧
          InferClaimIO μ m φ fuel := by
  have hin : RulesInputs V m φ := RulesInputs.ofTier h
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  intro fuel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d e e' Δa hrun hws hb hLb ea ea' hC hea hea' hok
    obtain ⟨-, -, ea'', hea'', hg, heq⟩ :=
      red_sound hin (whnfCore_bridge hrun) ⟨hws, hb, hLb⟩ hC hea hok
    rw [hea''] at hea'
    cases hea'
    exact ⟨hg, heq⟩
  · intro d e e' Δa hrun hws hb hLb ea ea' hC hea hea' hok
    obtain ⟨-, -, ea'', hea'', hg, heq⟩ :=
      red_sound hin (whnf_bridge hrun) ⟨hws, hb, hLb⟩ hC hea hok
    rw [hea''] at hea'
    cases hea'
    exact ⟨hg, heq⟩
  · intro d a b Δa hrun hwa hba hLa hwb hbb hLb aa ba hCa hCb haa hba' hga hgb
    exact defeq_sound hin (isDefEqCore_bridge hrun) ⟨hwa, hba, hLa⟩
      ⟨hwb, hbb, hLb⟩ hCa hCb haa hba' hga hgb
  · intro d e t Δa hrun hws hb hLb ea ta hC hea hta
    obtain ⟨-, -, ta', hta', hge, hgt, hmem⟩ :=
      infer_sound hin (inferTypeCore_bridge hrun) ⟨hws, hb, hLb⟩ hC hea
    rw [hta'] at hta
    cases hta
    exact ⟨hge, hgt, hmem⟩
  · intro d e t Δa hrun hws hb hLb ea ta hC hea hta hok
    obtain ⟨-, -, ta', hta', hgt, hmem⟩ :=
      infer_sound hin (inferTypeCoreIO_bridge hrun) ⟨hws, hb, hLb⟩ hC hea hok
    rw [hta'] at hta
    cases hta
    exact ⟨hgt, hmem⟩

/-- **`checkSoundAt`, recomposed** — the four sealed claims. -/
theorem checkSoundAt_rules (hμ : μ.verifiedChecks = true)
    {m : EnvModel V env} (h : TierInputsAt V μ m φ) :
    ∀ fuel : Nat,
      WhnfCoreClaim μ m φ fuel ∧ WhnfClaim μ m φ fuel ∧
        DefEqClaim μ m φ fuel ∧ InferClaim μ m φ fuel := fun fuel =>
  ⟨(checkSoundAtP5_rules hμ h fuel).1, (checkSoundAtP5_rules hμ h fuel).2.1,
    (checkSoundAtP5_rules hμ h fuel).2.2.1,
    (checkSoundAtP5_rules hμ h fuel).2.2.2.1⟩

end ConLeche.Model.Rules
