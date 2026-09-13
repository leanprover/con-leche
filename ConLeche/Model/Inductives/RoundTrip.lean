module

public import ConLeche.Model.Inductives.InvCopy
import ConLeche.SetTheory.Derive.LfpFam

public section

/-!
# The round trips ψ⁻¹∘ψ and ψ∘ψ⁻¹ — the STATEMENTS (task #279 M-C′, DESIGN §M.32)

ψ (`PsiRun.lean`, `psiFold_typed_of_read`) is, at every pin `j`, a term
`Ψ_j` over the scratch block's parameter frame — the container's
recursor at the pin's readings with the group's motives (the copies'
carriers) and minors — and ψ⁻¹ (`InvCopy.lean`, `invSetup_of_run`) is,
at every copy `k₀ + j`, the term `Φ_{k₀+j}` — the scratch block's
recursor at `invL`/`invPinsT`/`invHead`/`invUseIh`.  Both are TYPED
(`PsiTypedPi`, `InvSetup.fold_mem`) and FIRE (`PsiSetup.fold_iota`,
`InvSetup.fold_iota`).  This module states the round trips precisely
and proves what needs no induction:

* **`foldApp`** — a fold term applied to index values and an element;
* **`R2At`** (the CONTAINER side, `ψ⁻¹ ∘ ψ = id` on `J DsA ı⃗`) and
  **`R1At`** (the COPY side, `ψ ∘ ψ⁻¹ = id` on `A p⃗ ı⃗`), per pin;
* **`coherence`** — inverse uniqueness: a second candidate inverse
  agreeing with ψ⁻¹ on the container side IS ψ⁻¹ on the copy's carrier
  (what makes `invHead`'s choice of representative immaterial);
* **`IndRep.carrier_induction`** — STRUCTURAL INDUCTION over a member's
  carrier at the set level (`lfpFamSet_induction` through the datum's
  `leaf`/`functor`/`fibre`): a property holding of every injection
  whose chain-fitting fields lie in the carrier restricted to the
  property holds on the whole carrier.  This is the "recursor at a Prop
  motive" of DESIGN §M.3, without a Prop-motive fold kit: R1 is one
  induction over the SCRATCH block's carriers (every copy at once, no
  order), R2 one over the CONTAINER's carrier at the pin, interleaved
  with the kernel order at the transports.

**What the inductions still need, named** (DESIGN §M.32): (i) the two
folds' ι laws at VALUES — `fold_iota` speaks of field TERMS at the base
frame, so an arbitrary spine of values is fed through the frame
`consList vs ρ` and the lifted parameters, which reads the choice's
terms alike only when they are closed above the parameters
(`Term.bvarsBelow d.nP`: the pins' readings from `DenoteMetaSpine` at
`pinsClosed`, the heads and the table's terms along the order) — the
lemma `interp_congr_below` is the tool; (ii) the fields of a
`ChainFit`ting spine, field by field (a recursive field's value under
its telescope lies in the chain family's fibre at its index readings;
an ordinary field's fits its domain) — the datum's `fibre` clause
exposes `ChainFit` whole, and its per-field reading is a Semantics-tier
lemma about `chainXIGo` (`FixFamI.lean`) that the model has not yet
imported.  Neither is a datum or kernel fact.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A fold, applied -/

/-- A fold term at a frame, applied to index values and an element. -/
noncomputable def foldApp (σ : Nat → V) (Ψ : AnnotTerm) (is : List V) (x : V) : V :=
  (is ++ [x]).foldl SetTheory.app (interp V σ Ψ)

/-! ## Structural induction over a carrier -/

namespace IndRep

/-- **Structural induction over member `mm`'s carrier** at fitting
parameters and indices: a property `P` (of the container's index tuple
and the element) that holds of every injection `inj j fs` whose fields
chain-fit at the carrier RESTRICTED to `P` holds of every element of
the carrier (`lfpFamSet_induction` at the datum's functor, read through
`leaf` and `fibre`). -/
theorem carrier_induction {env : Env} {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : IndRepData V} {mm : Nat}
    (hrep : IndRep m T cvT cvR mI rP rules d mm) (ψ : Name → Nat) {ρ : Nat → V} {as is : List V}
    (has : SpineFit ρ (d.params ψ) as) (his : SpineFit (consList as ρ) (d.IdsM mm ψ) is)
    (P : V → V → Prop)
    (hstep : ∀ t, t ∈ˢ d.idx ψ (consList as ρ) → ∀ (j : Nat) (fs : List V), j < d.ctorsA.length →
      d.ChainFit ψ (consList as ρ)
        (graph (fun i => sep (SetTheory.app (lfpFamSet (d.w ψ) (d.idx ψ (consList as ρ))
          (d.Φ ψ (consList as ρ))) i) (P i)) (d.idx ψ (consList as ρ)))
        t j fs →
      P t (d.inj ψ j fs)) :
    ∀ x, x ∈ˢ (as ++ is).foldl SetTheory.app (interp V ρ (m.acval T ψ)) → P (d.tup ψ mm is) x := by
  intro x hx
  rw [hrep.leaf ψ ρ as is has his] at hx
  have hsat : Sat V (d.params ψ).reverse (consList as ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) has
    rwa [List.append_nil] at h
  obtain ⟨-, hmono, -, hclosed⟩ := hrep.functor ψ _ hsat
  have htup : d.tup ψ mm is ∈ˢ d.idx ψ (consList as ρ) := hrep.tupMem ψ _ hsat is his
  refine lfpFamSet_induction hclosed hmono P ?_ _ htup x hx
  intro t ht y hy
  have hS : graph (fun i => sep (SetTheory.app (lfpFamSet (d.w ψ) (d.idx ψ (consList as ρ))
        (d.Φ ψ (consList as ρ))) i) (P i)) (d.idx ψ (consList as ρ))
      ∈ˢ famSpace (d.w ψ) (d.idx ψ (consList as ρ)) :=
    graph_mem_famSpace fun i hi => univ_sep_mem (famSpace_app (lfpFamSet_mem _ _ _) hi)
  obtain ⟨j, fs, hj, hfit, rfl⟩ := (hrep.fibre ψ _ hsat _ hS t ht y).mp hy
  exact hstep t ht j fs hj hfit

end IndRep

/-! ## The round trips, per pin -/

namespace IndRepData

variable (d : IndRepData V)

/-- **R2 at a pin — the CONTAINER side**: on the container member's
carrier at the pin's readings (index values fitting its telescope, an
element of the family there), ψ then ψ⁻¹ is the identity.  `Ψ` is ψ's
fold term at the pin (`psiFold_typed_of_read`'s `orderFold … j`), `Φ`
ψ⁻¹'s at the copy (`invSetup_of_run`'s recursor at the choice), both
over the block's parameter frame `consList (ps-values) ρ`; the copy is
`c`. -/
@[expose] def R2At (m : EnvModel V env) (ρ : Nat → V) (ps : List AnnotTerm) (c : CopyData V)
    (Ψ Φ : AnnotTerm) : Prop :=
  ∀ (is : List V) (x : V),
    SpineFit (consList (c.DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)))
      (consList (ps.map (interp V ρ)) ρ)) (c.dJ.IdsM c.mm c.ψ') is →
    x ∈ˢ (c.DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)) ++ is).foldl SetTheory.app
      (interp V (consList (ps.map (interp V ρ)) ρ) (m.acval (c.dJ.memberName c.mm) c.ψ')) →
    foldApp ρ Φ is (foldApp (consList (ps.map (interp V ρ)) ρ) Ψ is x) = x

/-- **R1 at a pin — the COPY side**: on the copy's carrier at the block's
parameters (index values fitting its telescope, an element of the copy
there), ψ⁻¹ then ψ is the identity.  `t` is the copy's member index
(`k₀ + j`). -/
@[expose] def R1At (m : EnvModel V env) (ψ : Name → Nat) (ρ : Nat → V) (ps : List AnnotTerm)
    (t : Nat) (Ψ Φ : AnnotTerm) : Prop :=
  ∀ (is : List V) (a : V),
    SpineFit (consList (ps.map (interp V ρ)) ρ) (d.IdsM t ψ) is →
    a ∈ˢ (ps.map (interp V ρ) ++ is).foldl SetTheory.app (interp V ρ (m.acval (d.memberName t) ψ)) →
    foldApp (consList (ps.map (interp V ρ)) ρ) Ψ is (foldApp ρ Φ is a) = a

/-- **Coherence — inverse uniqueness**: a term `Φ'` that is a left
inverse of ψ on the container's carrier (`R2At` for `Φ'`) agrees with
ψ⁻¹ on the copy's carrier, given ψ⁻¹'s own round trips and ψ's typing
into the container.  So `invHead`'s representative is immaterial: every
representative's ψ⁻¹ fires the same. -/
theorem coherence (m : EnvModel V env) {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm}
    {c : CopyData V} {t : Nat} {Ψ Φ Φ' : AnnotTerm}
    (h1 : d.R1At m ψ ρ ps t Ψ Φ) (h2' : R2At m ρ ps c Ψ Φ')
    -- ψ⁻¹ lands in the container's carrier (`InvSetup.fold_mem` at the
    -- copy's member, read at the pin's readings)
    (hΦ : ∀ (is : List V) (a : V),
      SpineFit (consList (ps.map (interp V ρ)) ρ) (d.IdsM t ψ) is →
      a ∈ˢ (ps.map (interp V ρ) ++ is).foldl SetTheory.app (interp V ρ (m.acval (d.memberName t) ψ)) →
      foldApp ρ Φ is a ∈ˢ (c.DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)) ++ is).foldl
        SetTheory.app (interp V (consList (ps.map (interp V ρ)) ρ)
          (m.acval (c.dJ.memberName c.mm) c.ψ')))
    -- the copy's index telescope is the container's at the pin
    -- (`CopyIdxRead.idxIff`)
    (hidx : ∀ is : List V, SpineFit (consList (ps.map (interp V ρ)) ρ) (d.IdsM t ψ) is →
      SpineFit (consList (c.DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)))
        (consList (ps.map (interp V ρ)) ρ)) (c.dJ.IdsM c.mm c.ψ') is) :
    ∀ (is : List V) (a : V),
      SpineFit (consList (ps.map (interp V ρ)) ρ) (d.IdsM t ψ) is →
      a ∈ˢ (ps.map (interp V ρ) ++ is).foldl SetTheory.app (interp V ρ (m.acval (d.memberName t) ψ)) →
      foldApp ρ Φ' is a = foldApp ρ Φ is a := by
  intro is a his ha
  have h := h2' is (foldApp ρ Φ is a) (hidx is his) (hΦ is a his ha)
  rw [h1 is a his ha] at h
  exact h

end IndRepData

end ConLeche.Model
