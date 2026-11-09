module

public import ConLeche.Model.Env.EnvModelM
import ConLeche.Model.Env.CanonCrest
import ConLeche.Model.Env.BlockLfpTup
import ConLeche.Model.NatEqs
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.Denote

public section

/-!
# A recorded block's former, applied to the block's parameters, IS its hole value

A hole stands for a member's WHOLE application to the block's
parameters (`nestCrest`), so its value is a family over the member's
indices (`LfpDatum.holeVal`).  A member's former, applied to the block's
parameters at a satisfying parameter frame, IS the hole value at the
carrier (`former_app_eq`): both inhabit the member's index tower (the
former's type read as the Π-tower over its parameters and indices,
`LfpReads`, M4), and they agree on every fitting index spine (the
clause's `leaf`, and `holeVal_app`).
-/

namespace ConLeche.Model
open ConLeche.Term (Term)
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory

open ConLeche (Env Name Level CheckMode)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Π-towers in the graph regime -/

theorem mkPisAV_append' (B : Term) :
    ∀ (ab₁ ab₂ : List Term),
      mkPisAV (ab₁ ++ ab₂) B = mkPisAV ab₁ (mkPisAV ab₂ B)
  | [], _ => rfl
  | d :: ab₁, ab₂ => by
    show Term.pi _ (mkPisAV (ab₁ ++ ab₂) B) = Term.pi _ _
    rw [mkPisAV_append' B ab₁ ab₂]

/-- An application along a Π-tower lands in its body. -/
theorem foldl_app_mem_mkPisAV_pos {B : Term} {ab : List Term}
    {ρ : Nat → V} {bs : List V} {f : V} (h : SpineFit ρ ab bs)
    (hf : f ∈ˢ interp V ρ (mkPisAV ab B)) : bs.foldl app f ∈ˢ interp V (consList bs ρ) B :=
  foldl_app_mem_mkPisAV h hf

/-- **Extensionality along a graph-regime Π-tower**: two inhabitants
agreeing on every fitting spine are equal. -/
theorem eq_of_mem_mkPisAV_pos {B : Term} :
    ∀ {ab : List Term} {ρ : Nat → V} {f g : V},
      f ∈ˢ interp V ρ (mkPisAV ab B) → g ∈ˢ interp V ρ (mkPisAV ab B) →
      (∀ bs, SpineFit ρ ab bs → bs.foldl app f = bs.foldl app g) → f = g
  | [], _, _, _, _, _, h => h [] trivial
  | d :: ab, ρ, f, g, hf, hg, h => by
    have hf' : f ∈ˢ piV (interp V ρ d) fun x => interp V (cons x ρ) (mkPisAV ab B) := hf
    have hg' : g ∈ˢ piV (interp V ρ d) fun x => interp V (cons x ρ) (mkPisAV ab B) := hg
    unfold piV at hf' hg'
    rw [← lamR_eta hf', ← lamR_eta hg']
    refine lamR_congr fun a ha => ?_
    have hfa : app f a ∈ˢ interp V (cons a ρ) (mkPisAV ab B) :=
      app_mem_piR hf' ha fun h0 => propN_eq_zero.mp h0
    have hga : app g a ∈ˢ interp V (cons a ρ) (mkPisAV ab B) :=
      app_mem_piR hg' ha fun h0 => propN_eq_zero.mp h0
    exact eq_of_mem_mkPisAV_pos hfa hga fun bs hbs => h (a :: bs) ⟨ha, hbs⟩

/-! ## The former at the frame's parameters -/

section Former

variable {env : Env}

/-- **A recorded block's former, applied to the block's parameters at a
satisfying parameter frame, is its hole value at the carrier** (see the
module docstring). -/
theorem former_app_eq (mp : EnvModelM V env) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks)
    {mm : Nat} (hmm : mm < D.k) {ψ : Name → Nat} {ρp : Nat → V}
    (hs : Sat V (D.params ψ).reverse ρp) (ρ : Nat → V) :
    (frameIdx (D.params ψ).length ρp).foldl app (interp V ρ (mp.base2.acval (D.member mm) ψ))
      = D.holeVal ψ ρp (D.carrier ψ ρp) mm := by
  obtain ⟨h, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv, caps, hf, -, hab⟩ := hrd mm hmm
  obtain ⟨ab, hta, hmap⟩ := hab ψ
  have hpl := h.parsLen mm hmm ψ
  have hsP := h.parsSat mm hmm ψ ρp hs
  generalize hρ₀ : shiftE (D.pars mm ψ).length 0 ρp = ρ₀
  -- the former inhabits the member's type, read at `ρ₀`
  have hfm : interp V ρ₀ (mp.base2.acval (D.member mm) ψ) ∈ˢ
      interp V ρ₀ (mkPisAV ab (.sort (D.w ψ))) := mp.formerAt_mem hD hmm hf hta ρ₀
  -- split the tower at the parameters
  have hsplit : ab = ab.take (D.pars mm ψ).length ++ ab.drop (D.pars mm ψ).length :=
    (List.take_append_drop _ _).symm
  have hmap₁ : ab.take (D.pars mm ψ).length = D.pars mm ψ := by
    rw [hmap, List.take_left' rfl]
  have hmap₂ : ab.drop (D.pars mm ψ).length = D.ids mm ψ := by
    rw [hmap, List.drop_left' rfl]
  rw [hsplit, mkPisAV_append'] at hfm
  have hfit : SpineFit ρ₀ (ab.take (D.pars mm ψ).length)
      (frameIdx (D.pars mm ψ).length ρp) := by
    rw [hmap₁, ← hρ₀]; exact spineFit_frameIdx_of_sat hsP
  have hfr : consList (frameIdx (D.pars mm ψ).length ρp) ρ₀ = ρp := by
    rw [← hρ₀]; exact consList_frameIdx _ ρp
  have hf₂ := foldl_app_mem_mkPisAV_pos hfit hfm
  rw [hfr] at hf₂
  -- the hole value inhabits the same index tower
  have hgm : D.holeVal ψ ρp (D.carrier ψ ρp) mm
      ∈ˢ interp V ρp (mkPisAV (ab.drop (D.pars mm ψ).length) (.sort (D.w ψ))) :=
    LfpDatum.holeVal_mem h.kN (lfpTuple_mem _ _ _ _).toU hmm hmap₂
  -- they agree on every fitting index spine: the leaf, `holeVal_app`
  have heq := eq_of_mem_mkPisAV_pos hf₂ hgm fun is' his' => by
    rw [hmap₂] at his'
    rw [← List.foldl_append]
    have hsa : SpineFit ρ₀ (D.params ψ) (frameIdx (D.pars mm ψ).length ρp) := by
      rw [← hρ₀, hpl]
      exact spineFit_frameIdx_of_sat hs
    have hleaf := h.leaf mm hmm ψ ρ₀ _ is' hsa (by rw [hfr]; exact his')
    rw [hfr] at hleaf
    rw [hleaf, LfpDatum.holeVal_app his']
  rw [← hpl, acval_interp_closed mp.base2 _ ψ ρ ρ₀, heq]

end Former

end ConLeche.Model
