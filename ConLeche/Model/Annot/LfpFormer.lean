module

public import ConLeche.Model.Annot.EnvModelM
import ConLeche.Model.Annot.BlockLfpTup
import ConLeche.Model.NatEqs
import ConLeche.Model.Annot.Bit

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
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory

open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Name Level CheckMode)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Π-towers in the graph regime -/

theorem mkPisAV_append' (B : AnnotTerm) :
    ∀ (ab₁ ab₂ : List (Nat × Nat × AnnotTerm)),
      mkPisAV (ab₁ ++ ab₂) B = mkPisAV ab₁ (mkPisAV ab₂ B)
  | [], _ => rfl
  | d :: ab₁, ab₂ => by
    show AnnotTerm.pi _ _ _ (mkPisAV (ab₁ ++ ab₂) B) = AnnotTerm.pi _ _ _ _
    rw [mkPisAV_append' B ab₁ ab₂]

/-- An application along a graph-regime Π-tower lands in its body. -/
theorem foldl_app_mem_mkPisAV_pos {B : AnnotTerm} :
    ∀ {ab : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {bs : List V} {f : V},
      (∀ d ∈ ab, d.2.1 ≠ 0) → SpineFit ρ (ab.map (·.2.2)) bs →
      f ∈ˢ interp V ρ (mkPisAV ab B) → bs.foldl app f ∈ˢ interp V (consList bs ρ) B
  | [], _, [], _, _, _, hf => hf
  | [], _, _ :: _, _, _, h, _ => h.elim
  | _ :: _, _, [], _, _, h, _ => h.elim
  | d :: ab, ρ, b :: bs, f, hv, h, hf => by
    have hf' : f ∈ˢ piR d.2.1 (interp V ρ d.2.2) fun x => interp V (cons x ρ) (mkPisAV ab B) := hf
    rw [piR_pos (hv d List.mem_cons_self)] at hf'
    have happ := app_mem_of_mem_piSet hf' h.1
    rw [List.foldl_cons, consList_cons]
    exact foldl_app_mem_mkPisAV_pos (fun d' hd' => hv d' (List.mem_cons_of_mem _ hd')) h.2 happ

/-- **Extensionality along a graph-regime Π-tower**: two inhabitants
agreeing on every fitting spine are equal. -/
theorem eq_of_mem_mkPisAV_pos {B : AnnotTerm} :
    ∀ {ab : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {f g : V},
      (∀ d ∈ ab, d.2.1 ≠ 0) → f ∈ˢ interp V ρ (mkPisAV ab B) → g ∈ˢ interp V ρ (mkPisAV ab B) →
      (∀ bs, SpineFit ρ (ab.map (·.2.2)) bs → bs.foldl app f = bs.foldl app g) → f = g
  | [], _, _, _, _, _, _, h => h [] trivial
  | d :: ab, ρ, f, g, hv, hf, hg, h => by
    have hf' : f ∈ˢ piR d.2.1 (interp V ρ d.2.2) fun x => interp V (cons x ρ) (mkPisAV ab B) := hf
    have hg' : g ∈ˢ piR d.2.1 (interp V ρ d.2.2) fun x => interp V (cons x ρ) (mkPisAV ab B) := hg
    rw [piR_pos (hv d List.mem_cons_self)] at hf' hg'
    rw [← eq_graph_app_of_mem_piSet hf', ← eq_graph_app_of_mem_piSet hg']
    refine graph_congr fun a ha => ?_
    exact eq_of_mem_mkPisAV_pos (fun d' hd' => hv d' (List.mem_cons_of_mem _ hd'))
      (app_mem_of_mem_piSet hf' ha) (app_mem_of_mem_piSet hg' ha)
      fun bs hbs => h (a :: bs) ⟨ha, hbs⟩

/-! ## The former at the frame's parameters -/

section Former

variable {μ : CheckMode} {env : Env}

/-- **A recorded block's former, applied to the block's parameters at a
satisfying parameter frame, is its hole value at the carrier** (see the
module docstring). -/
theorem former_app_eq (mp : EnvModelM V μ env) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks)
    {mm : Nat} (hmm : mm < D.k) {ψ : Name → Nat} {ρp : Nat → V}
    (hs : Sat V (D.params ψ).reverse ρp) (ρ : Nat → V) :
    (frameIdx (D.params ψ).length ρp).foldl app (interp V ρ (mp.base2.acval (D.member mm) ψ))
      = D.holeVal ψ ρp (D.carrier ψ ρp) mm := by
  obtain ⟨h, -, hrd, -⟩ := mp.lfp_ok D hD
  obtain ⟨cv, caps, hf, hab⟩ := hrd mm hmm
  obtain ⟨ab, hta, hmap, hbits⟩ := hab ψ
  have hpl := h.parsLen mm hmm ψ
  have hsP := h.parsSat mm hmm ψ ρp hs
  generalize hρ₀ : shiftE (D.pars mm ψ).length 0 ρp = ρ₀
  -- the former inhabits the member's type, read at `ρ₀`
  have hmem := ConLeche.Semantics.Env.find?_mem hf
  have hname := ConLeche.Semantics.Env.find?_name hf
  have hfm : interp V ρ₀ (mp.base2.acval (D.member mm) ψ) ∈ˢ
      interp V ρ₀ (mkPisAV ab (.sort (D.w ψ))) := by
    have := mp.mem_type _ hmem ψ _ hta ρ₀
    rwa [hname] at this
  -- split the tower at the parameters
  have hsplit : ab = ab.take (D.pars mm ψ).length ++ ab.drop (D.pars mm ψ).length :=
    (List.take_append_drop _ _).symm
  have hmap₁ : (ab.take (D.pars mm ψ).length).map (·.2.2) = D.pars mm ψ := by
    rw [List.map_take, hmap, List.take_left' rfl]
  have hmap₂ : (ab.drop (D.pars mm ψ).length).map (·.2.2) = D.ids mm ψ := by
    rw [List.map_drop, hmap, List.drop_left' rfl]
  have hbits₁ : ∀ d ∈ ab.take (D.pars mm ψ).length, d.2.1 ≠ 0 :=
    fun d hd => hbits d (List.mem_of_mem_take hd)
  have hbits₂ : ∀ d ∈ ab.drop (D.pars mm ψ).length, d.2.1 ≠ 0 :=
    fun d hd => hbits d (List.mem_of_mem_drop hd)
  rw [hsplit, mkPisAV_append'] at hfm
  have hfit : SpineFit ρ₀ ((ab.take (D.pars mm ψ).length).map (·.2.2))
      (frameIdx (D.pars mm ψ).length ρp) := by
    rw [hmap₁, ← hρ₀]; exact spineFit_frameIdx_of_sat hsP
  have hfr : consList (frameIdx (D.pars mm ψ).length ρp) ρ₀ = ρp := by
    rw [← hρ₀]; exact consList_frameIdx _ ρp
  have hf₂ := foldl_app_mem_mkPisAV_pos hbits₁ hfit hfm
  rw [hfr] at hf₂
  -- the hole value inhabits the same index tower
  have hgm : D.holeVal ψ ρp (D.carrier ψ ρp) mm
      ∈ˢ interp V ρp (mkPisAV (ab.drop (D.pars mm ψ).length) (.sort (D.w ψ))) :=
    LfpDatum.holeVal_mem h.kN (lfpTuple_mem _ _ _ _) hmm hmap₂ hbits₂
  -- they agree on every fitting index spine: the leaf, `holeVal_app`
  have heq := eq_of_mem_mkPisAV_pos hbits₂ hf₂ hgm fun is' his' => by
    rw [hmap₂] at his'
    rw [← List.foldl_append]
    have hsa : SpineFit ρ₀ (D.params ψ) (frameIdx (D.pars mm ψ).length ρp) := by
      rw [← hρ₀, hpl]
      exact spineFit_frameIdx_of_sat hs
    have hleaf := h.leaf mm hmm ψ ρ₀ _ is' hsa (by rw [hfr]; exact his')
    rw [hfr] at hleaf
    rw [hleaf, LfpDatum.holeVal_app his']
  rw [← hpl, acval_interp_closed mp.base2 _ ψ ρ ρ₀, heq]

/-- A hole value reads its tuple only at its own component. -/
theorem holeVal_congr {D : LfpDatum V} {ψ : Name → Nat} {ρp X X' : Nat → V} {m : Nat}
    (h : X m = X' m) : D.holeVal ψ ρp X m = D.holeVal ψ ρp X' m := by
  unfold LfpDatum.holeVal; rw [h]

end Former

end ConLeche.Model
