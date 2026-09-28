module

public import ConLeche.Model.Annot.LfpFormer
public import ConLeche.Model.Annot.LfpHoleOp
import ConLeche.Model.NatEqs
public import ConLeche.Model.Annot.BitLemmas
import ConLeche.Semantics.Tower.FixTower

public section

/-!
# A coherent class's value is its carrier's hole value (P2d, DESIGN CLASSCHECK / P2D4)

A class fact's filler writes a coherent class's CARRIER into the
valuation; the hole frame then holds the carrier's λ-tower over the
class's indices.  The crest's coherence asks for the class's KEY read at
the valuation — its former applied to the key's parameters.  They are
the same set: a recorded former applied to the block's parameters at a
satisfying frame is its hole value at the carrier so applied
(`former_app_eq`), which is the λ-tower of the carrier over the member's
indices (`holeVal_params`) — `key_read_holeFam`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower (projS)
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- **A hole value applied to the block's parameters** is the λ-tower of
the tuple's component over the member's indices. -/
theorem holeVal_params {D : LfpDatum V} {ψ : Name → Nat} {ρp X : Nat → V} {mm : Nat}
    (hpl : (D.pars mm ψ).length = (D.params ψ).length) (hsP : Sat V (D.pars mm ψ).reverse ρp) :
    (frameIdx (D.params ψ).length ρp).foldl app (D.holeVal ψ ρp X mm)
      = holeFam ρp (D.ids mm ψ) fun is => app (X mm) (tupW (D.u mm ψ) is) := by
  have hsp : SpineFit (shiftE (D.pars mm ψ).length 0 ρp) (D.pars mm ψ)
      (frameIdx (D.pars mm ψ).length ρp) := spineFit_frameIdx_of_sat hsP
  have hfr : consList (frameIdx (D.pars mm ψ).length ρp) (shiftE (D.pars mm ψ).length 0 ρp) = ρp :=
    consList_frameIdx _ ρp
  have hlen : (frameIdx (D.pars mm ψ).length ρp).length = (D.pars mm ψ).length := by
    simp [frameIdx]
  unfold LfpDatum.holeVal
  rw [← hpl, holeFam_foldl_prefix _ _ hsp, hfr]
  refine holeFam_congr fun bs _ => ?_
  rw [List.drop_left' hlen]

variable {μ : ConLeche.CheckMode}

/-- **A recorded former applied to the block's parameters** at a
satisfying frame is the λ-tower of its carrier over its indices. -/
theorem former_params_read (mp : EnvModelM V μ env) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks)
    {mm : Nat} (hmm : mm < D.k) {ψ : Name → Nat} {ρp : Nat → V}
    (hs : Sat V (D.params ψ).reverse ρp) (ρ : Nat → V) :
    (frameIdx (D.params ψ).length ρp).foldl app (interp V ρ (mp.base2.acval (D.member mm) ψ))
      = holeFam ρp (D.ids mm ψ) fun is => app (D.carrier ψ ρp mm) (tupW (D.u mm ψ) is) := by
  obtain ⟨h, -⟩ := mp.lfp_ok D hD
  have := former_app_eq mp hD hmm hs ρ []
  simp only [List.append_nil] at this
  rw [this]
  exact holeVal_params (h.parsLen mm hmm ψ) (h.parsSat mm hmm ψ ρp hs)

/-- **A class's key, read, is the λ-tower of its container's carrier**:
the key `I.{us} p⃗` of a recorded member `I`, read at `τ`, is the λ-tower
over the member's indices of its carrier at any satisfying frame whose
parameters are the parameters' readings. -/
theorem key_read_holeFam (mp : EnvModelM V μ env) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks)
    {mm : Nat} (hmm : mm < D.k) {us : List Level} {cvI : ConLeche.ConstantVal}
    {caps : ConLeche.IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cvI caps))
    (hlen : us.length = cvI.levelParams.length) {H : Nat} {ps : List Expr} {a : AnnotTerm}
    (ha : denoteMeta mp.base2.acval env φ H (Expr.mkAppN (.const (D.member mm) us) ps) = some a)
    {τ ρ' : Nat → V}
    (hpar : ∀ vs, DenoteMetaSpine mp.base2.acval env φ H ps vs →
      vs.map (interp V τ) = frameIdx (D.params (Level.substFn φ cvI.levelParams us)).length ρ')
    (hs : Sat V (D.params (Level.substFn φ cvI.levelParams us)).reverse ρ') :
    interp V τ a = holeFam ρ' (D.ids mm (Level.substFn φ cvI.levelParams us)) fun is =>
      app (D.carrier (Level.substFn φ cvI.levelParams us) ρ' mm)
        (tupW (D.u mm (Level.substFn φ cvI.levelParams us)) is) := by
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv ha
  rw [denoteMeta_const hf hlen] at hfa
  cases hfa
  rw [interp_mkAppN_foldl, hpar vs hsp]
  exact former_params_read mp hD hmm hs τ

end ConLeche.Model
