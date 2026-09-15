module

public import ConLeche.Model.IndRepToolkit
import ConLeche.Semantics.Tower.FixFamI
public section

/-!
# Experiment (1): the parameter's map action at a `List`-shaped datum

`IndRep.leaf_mono` (`ConLeche/Model/IndRepToolkit.lean`) turns a
comparison of the representing FUNCTORS at two parameter frames into a
comparison of the represented families.  This module discharges that
premise for the shape of `List` — one parameter, no indices, a
field-less constructor and a constructor with one ORDINARY field whose
domain reads as the parameter variable and one RECURSIVE field — from
the datum's `fibre` clause and the X-chain spelling alone, with no
stored positivity datum: a chain fit at the frame `α := X` is a chain
fit at `α := X'` whenever `X ⊆ˢ X'`, because the only place the
parameter frame is read is the ordinary domain's `.bvar 0`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- At an empty index telescope the tupler is the point constant. -/
theorem tuplerAV_nil (u : Nat) :
    tuplerAV u ([] : List AnnotTerm) = .const .punitUnit [] := by
  show mkTowerGo u ([] : List AnnotTerm) = _
  unfold mkTowerGo
  split <;> rfl

/-- The `List`-shaped constructor's X-chain: the ordinary domain
lifted past `X` and `t`, then the recursive slot at the point tuple. -/
theorem chainXIGo_listShaped (u : Nat) (F₁ : AnnotTerm) :
    chainXIGo u ([] : List AnnotTerm) [false, true] [[], []] [[], []]
        [AnnotTerm.bvar 0, F₁] 0
      = [AnnotTerm.bvar 2, .app (.bvar 2) ((AnnotTerm.const .punitUnit []).liftN 3 0)] := by
  rw [show chainXIGo u ([] : List AnnotTerm) [false, true] [[], []] [[], []]
        [AnnotTerm.bvar 0, F₁] 0
      = [AnnotTerm.bvar 2, .app (.bvar 2) ((tuplerAV u ([] : List AnnotTerm)).liftN 3 0)] from rfl,
    tuplerAV_nil]

/-- **The one place the parameter frame is read**: a field spine
fitting the `List`-shaped X-chain at `α := X` fits it at `α := X'`
whenever `X ⊆ˢ X'`.  The ordinary domain reads as `bvar 2` — the
parameter — and the recursive slot as `X ⟨⟩`, which does not mention
the parameter frame at all. -/
theorem spineFit_chain_listShaped {u : Nat} {F₁ : AnnotTerm} {ρ : Nat → V} {Y t X X' : V}
    (hle : X ⊆ˢ X') {fs : List V}
    (hfit : SpineFit (cons t (cons Y (cons X ρ)))
      (chainXIGo u ([] : List AnnotTerm) [false, true] [[], []] [[], []]
        [AnnotTerm.bvar 0, F₁] 0) fs) :
    SpineFit (cons t (cons Y (cons X' ρ)))
      (chainXIGo u ([] : List AnnotTerm) [false, true] [[], []] [[], []]
        [AnnotTerm.bvar 0, F₁] 0) fs := by
  rw [chainXIGo_listShaped] at hfit ⊢
  match fs, hfit with
  | [], hfit => exact hfit.elim
  | [_], hfit => exact hfit.2.elim
  | [a, b], ⟨ha, hb, _⟩ => exact ⟨hle a ha, hb, trivial⟩
  | _ :: _ :: _ :: _, hfit => exact hfit.2.2.elim

/-- **Experiment (1)**: the map action of a `List`-shaped representation
on its parameter.  The premise of `IndRep.leaf_mono` is discharged from
the datum's `fibre` clause and the X-chain spelling alone — no stored
positivity datum. -/
theorem IndRep.leaf_mono_listShaped {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : IndRepData V}
    (h : IndRep m T cvT cvR mI rP rules d 0)
    (hIds : ∀ ψ, d.IdsC ψ = []) (hIdsM : ∀ ψ, d.IdsM 0 ψ = [])
    (hFss : ∀ ψ, ∃ F₁, d.Fss ψ = [[], [.bvar 0, F₁]])
    (hrss : d.rss = [[], [false, true]])
    (htlss : ∀ ψ, d.tlss ψ = [[], [[], []]])
    (hEiss : ∀ ψ, d.Eiss ψ = [[], [[], []]])
    {ψ : Name → Nat} {ρ : Nat → V} {X X' : V}
    (hsp : SpineFit ρ (d.params ψ) [X]) (hsp' : SpineFit ρ (d.params ψ) [X'])
    (hle : X ⊆ˢ X') :
    app (interp V ρ (m.acval T ψ)) X ⊆ˢ app (interp V ρ (m.acval T ψ)) X' := by
  have hidx : ∀ σ₁ σ₂ : Nat → V, d.idx ψ σ₁ = d.idx ψ σ₂ := by
    intro σ₁ σ₂
    unfold IndRepData.idx idxSet
    rw [hIds]
    rfl
  have hsat : Sat V (d.params ψ).reverse (consList [X] ρ) := d.satOfSpine hsp
  have hsat' : Sat V (d.params ψ).reverse (consList [X'] ρ) := d.satOfSpine hsp'
  have hmono : ∀ Y, Y ∈ˢ famSpace (d.w ψ) (d.idx ψ (consList [X] ρ)) →
      FamLe (d.idx ψ (consList [X] ρ)) (app (d.Φ ψ (consList [X] ρ)) Y)
        (app (d.Φ ψ (consList [X'] ρ)) Y) := by
    intro Y hY t ht x hx
    obtain ⟨j, fs, hj, hcf, rfl⟩ := (h.fibre ψ _ hsat Y hY t ht x).mp hx
    refine (h.fibre ψ _ hsat' Y (by rw [hidx _ (consList [X] ρ)]; exact hY) t
      (by rw [hidx _ (consList [X] ρ)]; exact ht) _).mpr ⟨j, fs, hj, ?_, rfl⟩
    obtain ⟨F₁, hF⟩ := hFss ψ
    unfold IndRepData.ChainFit at hcf ⊢
    obtain ⟨hlen, hfit, -⟩ := hcf
    refine ⟨hlen, ?_, ?_⟩
    · by_cases hj1 : j = 1
      · subst hj1
        have hF1 : (d.Fss ψ).getD 1 [] = [AnnotTerm.bvar 0, F₁] := by rw [hF]; rfl
        have hr1 : d.rss.getD 1 [] = [false, true] := by rw [hrss]; rfl
        have ht1 : (d.tlss ψ).getD 1 [] = [[], []] := by rw [htlss ψ]; rfl
        have he1 : (d.Eiss ψ).getD 1 [] = [[], []] := by rw [hEiss ψ]; rfl
        rw [hF1, hr1, ht1, he1, hIds] at hfit ⊢
        exact spineFit_chain_listShaped hle hfit
      · have hF0 : (d.Fss ψ).getD j [] = [] := by
          rw [hF]
          match j, hj1 with
          | 0, _ => rfl
          | 1, hj1 => exact absurd rfl hj1
          | _ + 2, _ => rfl
        rw [hF0] at hfit ⊢
        match fs, hfit with
        | [], _ => trivial
        | _ :: _, hfit => exact hfit.elim
    · rw [hIds]
      exact EqAll_nil _
  have key := IndRep.leaf_mono h hsp hsp' (hidx _ _) hmono (is := [])
    (by rw [hIdsM]; trivial) (by rw [hIdsM]; trivial)
  simpa using key

end ConLeche.Model
