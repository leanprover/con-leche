module

public import ConLeche.SetTheory.Derive.LfpTuple
@[expose] public section

/-!
# The `ℓ = 0` arm of a block's elimination: inhabitation by the tuple lfp's induction

At a `Prop`-valued motive (`ℓ = 0`) the union recursion kit is the
wrong instrument: `mem_type` — "every carrier value's motive fibre is
inhabited" — comes DIRECTLY from `lfpTuple_induction` with
`P := "the motive fibre is inhabited"`, consuming only the step's
typing at the `sepTuple` frame with the ih values `pt`, and the ι rule
is `pt = pt`.  No accessibility, no recursion graph, no bound, at ANY
`w` — including a block with a reflexive field under `Π`.

The arm is stated abstractly, over any tuple functor at any width.  It
was extracted from the indexed/parametric/reflexive falsifier (F3,
`SetModel/UnionRecIndexed.lean`) when the wide-tuple falsifiers were
retired (DESIGN 2026-09-21, decision D-e); it is the seed of the
nested route's `ℓ = 0` regime and the only part of F3 that survives.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}

/-- **The induction kit**: at `ℓ = 0` the recursion data degenerates
to the motive alone.  `step` is the residue's typing at the `sepTuple`
frame — the ih values are `pt` (`lamR 0 = pt`), so the only thing the
frame carries is that the recursive fields' values lie in the carrier
AND have inhabited motive fibres, which is exactly what `sepTuple`
says. -/
structure InductionKit (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) where
  /-- The motive fibre at member `c`, index `i`, value `x`. -/
  B : Nat → V → V → V
  /-- The step, at the separated tuple. -/
  step : ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x,
    x ∈ˢ app (Φ (sepTuple w k Is Φ (fun c i x => ∃ z, z ∈ˢ B c i x)) c) i →
      ∃ z, z ∈ˢ B c i x

namespace InductionKit

variable (K : InductionKit w k Is Φ)

/-- **`mem_type` at `ℓ = 0`**: every carrier value's motive fibre is
inhabited.  The whole proof is `lfpTuple_induction` at the kit's own
step — no `unionRec`, no `PredsFrom`, no `accFam`. -/
theorem mem_type (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ) :
    ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ c) i →
      ∃ z, z ∈ˢ K.B c i x :=
  lfpTuple_induction h hmono (fun c i x => ∃ z, z ∈ˢ K.B c i x) K.step

/-- At a `Prop`-valued motive the fibre is a truth value, so
"inhabited" IS "`pt` is a member" — the recursor's value at every
point. -/
theorem pt_mem_B (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hB : ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ c) i →
      K.B c i x ∈ˢ (univ 0 : V)) :
    ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ c) i →
      (pt : V) ∈ˢ K.B c i x := by
  intro c hc i hi x hx
  obtain ⟨z, hz⟩ := K.mem_type h hmono c hc i hi x hx
  have hsub : K.B c i x ⊆ˢ (unitSet : V) := by
    have := hB c hc i hi x hx
    rw [univ_zero] at this
    exact mem_univZero.mp this
  rwa [← mem_unitSet_iff.mp (hsub z hz)]

end InductionKit

/-- **ι at `ℓ = 0` is `pt = pt`**: a leaf lying in a truth value IS
`pt`, and every application of `pt` is `pt` (`app_pt`), so the ι
equation's left-hand side reads `pt` whatever its arguments are — for
a reflexive field's two-binder telescope as much as for a plain one.
No typing of the rule's body enters. -/
theorem app₂_of_mem_unitSet {f : V} (hf : f ∈ˢ (unitSet : V)) (a b : V) :
    app (app f a) b = (pt : V) := by
  rw [mem_unitSet_iff.mp hf, app_pt, app_pt]

/-- Both sides of an ι equation at `ℓ = 0` read `pt`. -/
theorem eq_of_mem_unitSet {lhs rhs : V} (hl : lhs ∈ˢ (unitSet : V))
    (hr : rhs ∈ˢ (unitSet : V)) : lhs = rhs := by
  rw [mem_unitSet_iff.mp hl, mem_unitSet_iff.mp hr]

end ConLeche.SetTheory
