import Lech.SetP.Direct.DirectCapsP
import Lech.SetP.Direct.DirectFramesP

/-!
# The direct block's family laws (task #175 W4c, P3 module 5, part 2)

The block's own capability laws, from the leaves' semantic summary:

* `formerFold` — the former applied along a fitting parameter spine is
  the instantiated carrier (`directTyAV_fold` under the hereditary
  premise);
* `directUnitLawP` — a fieldless family is unit-like (its carrier is
  `unitSet`, both regimes);
* `directEtaLawP0` — a fieldless family's η law: the member is the
  point and so is the constructor's application.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Fits and folds -/

/-- A value-level fit of a Π-tower reading, of the tower's own
length, is a fit of its domains. -/
theorem spineFit_of_teleFitP :
    ∀ {pds : List (Nat × Nat × AVExpr)} {b : AVExpr} {ρ : Nat → V}
      {ts : List V} {rest : V},
      ts.length = pds.length →
      TeleFitP V ρ (mkPisAV pds b) ts rest →
      SpineFit ρ (pds.map (·.2.2)) ts
  | [], _, _, [], _, _, _ => trivial
  | [], _, _, _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, _, _, [], _, hlen, _ => by simp at hlen
  | d :: pds, b, ρ, t :: ts, rest, hlen, h => by
    cases h with
    | cons ht hfit =>
      exact ⟨ht, spineFit_of_teleFitP (by simpa using hlen) hfit⟩

theorem foldl_app_pt : ∀ (ts : List V), ts.foldl SetTheory.app (pt : V) = pt
  | [] => rfl
  | t :: ts => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt ts

/-- The hereditary premise's bottom, reached along a fitting spine. -/
theorem paramsOkT_fields {w : Nat} {Fs : List AVExpr} :
    ∀ {pps : List (Nat × Nat × AVExpr)} {ρ : Nat → V} {as : List V},
      ParamsOkT w ρ Fs pps → SpineFit ρ (pps.map (·.2.2)) as →
      FieldsOkB w (consList as ρ) Fs
  | [], _, [], h, _ => h
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | _ :: _, ρ, a :: as, h, hsp => by
    rw [consList_cons]
    exact paramsOkT_fields (h.2.2 a hsp.1) hsp.2

/-- **The former applied along a fit is the instantiated carrier.** -/
theorem formerFold {w : Nat} {Fs : List AVExpr}
    {pps : List (Nat × Nat × AVExpr)} {ρ : Nat → V} {as : List V}
    (hok : ParamsOkT w ρ Fs pps) (hsp : SpineFit ρ (pps.map (·.2.2)) as) :
    as.foldl SetTheory.app (interp2 V ρ (directTyAV w pps Fs))
      = towerSet w (teleOfFields (consList as ρ) Fs) :=
  directTyAV_fold hsp fun hw => (paramsOkT_fields hok hsp).toBound hw

/-! ## The fieldless family's laws -/

/-- **A fieldless family is unit-like**: its carrier is `unitSet` at
every fit, in both regimes. -/
theorem directUnitLawP {m : EnvS2Core V env} {φ' : Name → Nat} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    {w : (Name → Nat) → Nat} {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hleaf : ∀ ψ, m.acval T ψ = directTyAV (w ψ) (pps ψ) [])
    (hread : ∀ ψ, denoteP m.acval env ψ 0 cvT.type
      = some (mkPisAV (pps ψ) (.sort (w ψ))))
    (hokTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (mkPisAV (pps ψ) (.sort (w ψ))))
    (hpok : ∀ (ψ : Name → Nat) (ρ : Nat → V), ParamsOkT (w ψ) ρ [] (pps ψ))
    (hpar : ∀ ψ, caps.unitParams = (pps ψ).length) :
    UnitLawP m φ' T cvT caps := by
  intro us _
  refine ⟨mkPisAV (pps (Level.substFn φ' cvT.levelParams us))
    (.sort (w (Level.substFn φ' cvT.levelParams us))), ?_, hokTy _, ?_⟩
  · rw [denotePInstLevels m φ' cvT.levelParams us 0 cvT.type]
    exact hread _
  · intro ρ ts rest x y hlen hfit hx hy
    have hsp := spineFit_of_teleFitP (by rw [hlen, hpar]) hfit
    rw [hleaf, formerFold (hpok _ _) hsp] at hx hy
    have hx' : x = pt := mem_unitSet_iff.mp hx
    have hy' : y = pt := mem_unitSet_iff.mp hy
    rw [hx', hy']

/-- **A fieldless family's η law**: a member is the point, and the
constructor along the parameters is the point (the tupler of no
fields in the graph regime; the collapsed leaf at squash). -/
theorem directEtaLawP0 {m : EnvS2Core V env} {φ' : Name → Nat} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    {w : (Name → Nat) → Nat} {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    {ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hfields : caps.etaFields = 0)
    (hleaf : ∀ ψ, m.acval T ψ = directTyAV (w ψ) (pps ψ) [])
    (hleafC : ∀ ψ, m.acval caps.etaCtor ψ = directMkAV (w ψ) (ds ψ) [])
    (hread : ∀ ψ, denoteP m.acval env ψ 0 cvT.type
      = some (mkPisAV (pps ψ) (.sort (w ψ))))
    (hokTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (mkPisAV (pps ψ) (.sort (w ψ))))
    (hpok : ∀ (ψ : Name → Nat) (ρ : Nat → V), ParamsOkT (w ψ) ρ [] (pps ψ))
    -- the constructor's binder data are the parameters' (a fieldless
    -- constructor), fitting alike
    (hfit : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as : List V),
      SpineFit ρ ((pps ψ).map (·.2.2)) as → SpineFit ρ ((ds ψ).map (·.2.2)) as)
    (hpar : ∀ ψ, caps.etaParams = (pps ψ).length) :
    EtaLawP m φ' T cvT caps := by
  intro us _
  refine ⟨mkPisAV (pps (Level.substFn φ' cvT.levelParams us))
    (.sort (w (Level.substFn φ' cvT.levelParams us))), ?_, hokTy _, ?_⟩
  · rw [denotePInstLevels m φ' cvT.levelParams us 0 cvT.type]
    exact hread _
  · intro ρ ts rest x hlen hfitT hx
    have hsp := spineFit_of_teleFitP (by rw [hlen, hpar]) hfitT
    rw [hleaf, formerFold (hpok _ _) hsp] at hx
    have hxpt : x = pt := mem_unitSet_iff.mp hx
    rw [hfields]
    simp only [etaFabArgs2, projSpines2, List.range_zero, List.map_nil,
      List.append_nil]
    rw [hleafC, hxpt]
    by_cases hw : w (Level.substFn φ' cvT.levelParams us) = 0
    · rw [hw, directMkAV_zero, foldl_app_pt]
    · have hfd := directMkAV_fold hw (pds := ds _) (fds := []) (bs := [])
        (ρ := ρ) (as := ts) (by simpa using hfit _ ρ ts hsp) trivial trivial
      simp only [List.append_nil, List.map_nil] at hfd
      rw [hfd]
      rfl

end Lech.SetP
