import Setlec.SetR.Sound.Motives
import Setlec.Verify.PinnedShapes

/-!
# Soundness cases — proof irrelevance and λ-eta (task #148, T4, batch c)

The re-hangs of `proofIrrel_pt`/`sortCert_pt`'s content (D8: both
sides' types land in `univ 0`, so both sides are the proof point;
D9: both sides' types are the pinned `PUnit`'s interpretation
`unitSet`, so both sides are the proof point) and of
`etaCert_sound`/`etaBranch_sound`'s content (D13: `lamC_eta` at the
stuck side's reduced `∀`-type, with the pointwise body comparison read
at a `Sat`-extension).

D9's identification consumes the relocated `unitLike_eq_punit`
(`Setlec/Verify/PinnedShapes.lean`) through `EnvSHyp.basis_pinned` —
the [set] instance of the TT lane's four-way pin refutation.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

section Cases

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- D8: proof irrelevance, the `Prop` branch.  Both sides' types'
types are `Prop`; `mem_univ_zero` twice identifies both sides with the
proof point. -/
theorem sndDeqIrrelProp {Δ : List VExpr} {a b ta sta tb stb : VExpr}
    (_ : Infer μ env cval φ Δ a ta)
    (_ : Infer μ env cval φ Δ ta sta)
    (_ : DefEq μ env cval φ Δ sta (.sort 0))
    (_ : Infer μ env cval φ Δ b tb)
    (_ : Infer μ env cval φ Δ tb stb)
    (_ : DefEq μ env cval φ Δ stb (.sort 0))
    (ih1 : InfS V Δ a ta) (ih2 : InfS V Δ ta sta)
    (ih3 : DeqS V Δ sta (.sort 0))
    (ih4 : InfS V Δ b tb) (ih5 : InfS V Δ tb stb)
    (ih6 : DeqS V Δ stb (.sort 0)) :
    DeqS V Δ a b := by
  intro ρ hΔ
  have hta : interp V ρ ta ∈ˢ (univ 0 : V) := by
    have h := ih3 ρ hΔ
    rw [interp_sort] at h
    exact h ▸ (ih2 ρ hΔ).2
  have htb : interp V ρ tb ∈ˢ (univ 0 : V) := by
    have h := ih6 ρ hΔ
    rw [interp_sort] at h
    exact h ▸ (ih5 ρ hΔ).2
  rw [mem_univ_zero hta (ih1 ρ hΔ).2, mem_univ_zero htb (ih4 ρ hΔ).2]

/-- D9: proof irrelevance, the unit branch.  `unitLike_eq_punit` pins
each side's head to `PUnit`; the pinned valuation interprets to
`unitSet`, and `mem_unitSet` identifies both sides with the proof
point — no common-type check, exactly as the checker. -/
theorem sndDeqIrrelUnit (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {a b ta tb : VExpr} {c₁ c₂ : Name}
    {us₁ us₂ : List Level}
    (h1 : isUnitLikeTy env (.const c₁ us₁) = true)
    (_ : us₁.length = (levelParamsAt env c₁).length)
    (h3 : isUnitLikeTy env (.const c₂ us₂) = true)
    (_ : us₂.length = (levelParamsAt env c₂).length)
    (_ : Infer μ env cval φ Δ a ta)
    (_ : DefEq μ env cval φ Δ ta
      (cval c₁ (Level.substFn φ (levelParamsAt env c₁) us₁)))
    (_ : Infer μ env cval φ Δ b tb)
    (_ : DefEq μ env cval φ Δ tb
      (cval c₂ (Level.substFn φ (levelParamsAt env c₂) us₂)))
    (ih1 : InfS V Δ a ta)
    (ih2 : DeqS V Δ ta
      (cval c₁ (Level.substFn φ (levelParamsAt env c₁) us₁)))
    (ih3 : InfS V Δ b tb)
    (ih4 : DeqS V Δ tb
      (cval c₂ (Level.substFn φ (levelParamsAt env c₂) us₂))) :
    DeqS V Δ a b := by
  intro ρ hΔ
  -- one side's identification, applied twice
  have side : ∀ (c : Name) (us : List Level) (x tx : VExpr),
      isUnitLikeTy env (.const c us) = true →
      (∀ ρ' : Nat → V, Sat V Δ ρ' → interp V ρ' tx =
        interp V ρ' (cval c (Level.substFn φ (levelParamsAt env c) us))) →
      interp V ρ x ∈ˢ interp V ρ tx → interp V ρ x = pt := by
    intro c us x tx hu heq hmem
    obtain ⟨us', hce, hfind⟩ := unitLike_eq_punit henv.basis_pinned hu
    obtain ⟨rfl, -⟩ : c = punitName ∧ us = us' := by
      have h1 := (Expr.const.injEq .. ▸ hce)
      exact ⟨h1.1, h1.2⟩
    have hval : cval punitName (Level.substFn φ (levelParamsAt env punitName)
        us) = punitT ((Level.substFn φ (levelParamsAt env punitName) us) uN) :=
      (henv.basis_pinned punitName _ hfind (by decide)).2 _ _ rfl
    have hmem' : interp V ρ x ∈ˢ (unitSet : V) := by
      have h := heq ρ hΔ
      rw [hval] at h
      rw [h, interp_punitT] at hmem
      exact hmem
    exact mem_unitSet hmem'
  rw [side c₁ us₁ a ta h1 (fun ρ' h' => ih2 ρ' h') (ih1 ρ hΔ).2,
    side c₂ us₂ b tb h3 (fun ρ' h' => ih4 ρ' h') (ih3 ρ hΔ).2]

/-- D13: one-sided λ-eta.  The stuck side inhabits its reduced
`∀`-type, so `lamC_eta` rebuilds it as an abstraction; the λ-side's
body agrees pointwise on the (equal) domain by the binder premise at a
`Sat`-extension. -/
theorem sndDeqEta {Δ : List VExpr} {A₁ b₁ b tb A₂ B : VExpr}
    (_ : Infer μ env cval φ Δ b tb)
    (_ : DefEq μ env cval φ Δ tb (.pi A₂ B))
    (_ : DefEq μ env cval φ Δ A₂ A₁)
    (_ : DefEq μ env cval φ (A₁ :: Δ) b₁ (.app b.lift (.bvar 0)))
    (ihb : InfS V Δ b tb) (ihr : DeqS V Δ tb (.pi A₂ B))
    (ihd : DeqS V Δ A₂ A₁)
    (ihe : DeqS V (A₁ :: Δ) b₁ (.app b.lift (.bvar 0))) :
    DeqS V Δ (.lam A₁ b₁) b := by
  intro ρ hΔ
  have hbpi : interp V ρ b ∈ˢ
      piC (interp V ρ A₂) (fun x => interp V (cons V x ρ) B) := by
    have h := ihr ρ hΔ
    rw [interp_pi] at h
    exact h ▸ (ihb ρ hΔ).2
  have hdom : interp V ρ A₂ = interp V ρ A₁ := ihd ρ hΔ
  rw [interp_lam, ← lamC_eta hbpi, hdom]
  refine lamC_congr fun x hx => ?_
  have h := ihe (cons V x ρ) (Sat_cons V hΔ hx)
  rw [interp_app, interp_lift_cons, interp_bvar, cons_zero] at h
  exact h

end Cases

end Setlec.SetR
