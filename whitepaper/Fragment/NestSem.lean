module

public import Fragment.IndSem

@[expose] public section

/-!
# The class of a nested block: monotone, bounded

What the installation of a nested block proves about its class from
the container's own model — the **one new idea** of nested blocks:

* the class at a member set `X` is the container's family at the
  instantiation with `X` at the member's position
  (`classSet_eq_Fam`: the container's set in the model is the graph
  over its parameters of its fibre, applied by β);
* **the class grows with the member set** (`contGood_of`): by
  **leastness** of the container's fixed point at the smaller member
  set — every member of the container's family at `X` is a member at
  `Y ⊇ X`, by induction over the family at `X`, because the
  container is **positive** in the member's position: a field of the
  container is the member field (its value is in `X`, hence in `Y`),
  a recursive field (the induction hypothesis), or an ordinary field
  mentioning neither (the same set at `X` and at `Y`); the member at
  `Y` is in the container's bound at `Y` because that bound is closed
  under the container's constructors;
* **the class is inside the class's bound** (`contInBound_of`): the
  closure the block's bound comes from lists the container's
  constructors at the instantiation with the member field at the
  family's bound, so, again by induction over the container's family,
  every member of the class at the family's fibre is in it.

The facts about the container these need (`NestFacts`) are what the
container's own installation left in the model (`BlockModel.lean`)
and what the nested block's checks add (the class's arguments fit,
the sorts agree, N3).

Con-leche: `Model/Inductives/ContLeaf.lean` (`monoOn_of_famLe`: a
container instance grows along a relation as soon as the carrier
does at the two key frames), `ContAcc.lean`.
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V]

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat) (N : NestInfo)

/-- **What is known about the container** when a block nests through
it: its set in the model is its family's graph (its installation's
law), it is plain, positive in the member's position, no field reads
an earlier recursive field, the domains met along a fitting instance
are bounded at every fitting parameter list (its own checks), the
class's arguments fit its parameters at every member set in the result
universe (the nested block's check), and its result universe at the
instantiation is the block's (N3). -/
structure NestFacts : Prop where
  /-- The container's set is its family's graph. -/
  fam : ∀ ls', M N.K.name ls' = N.KS.famSet M ls'
  /-- The container has no container field (depth one). -/
  noCont : N.KS.NoCont
  /-- The container is positive in the member's position. -/
  positive : N.Positive
  /-- No field of the container reads an earlier recursive field. -/
  noRecDep : N.KS.NoRecDep
  /-- The container's domains are bounded at fitting parameters. -/
  domsBounded : ∀ ps', FitsVals M (N.KS.ψ (S.lsK ls N)) base N.KS.params ps' →
    N.KS.DomsBounded M (S.lsK ls N) ps'
  /-- The class's arguments fit the container's parameters at every
  member set in the result universe. -/
  argsFit : ∀ ps, FitsVals M (S.ψ ls) base S.params ps → ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) →
    FitsVals M (N.KS.ψ (S.lsK ls N)) base N.KS.params (S.psK M ls N ps X)
  /-- The container's result universe at the instantiation is the
  block's. -/
  u₀_eq : N.KS.u₀ (S.lsK ls N) = S.u₀ ls

variable {S M ls N}

/-- The container's regime at the instantiation is the block's. -/
theorem NestFacts.z_eq (hf : S.NestFacts M ls N) : N.KS.z (S.lsK ls N) = S.z ls := by
  apply Bool.eq_iff_iff.mpr
  rw [z_iff, z_iff, hf.u₀_eq]

/-- **The class is the container's family** at the instantiation
(the container's set applied by β to fitting parameter values). -/
theorem classSet_eq_Fam (hf : S.NestFacts M ls N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) {X : V} (hX : X ∈ˢ (univ (S.u₀ ls) : V)) :
    S.classSet M ls N ps X = N.KS.Fam M (S.lsK ls N) (S.psK M ls N ps X) [] := by
  sorry

/-- **The class grows with the member set, and stays in the
universe** (`ContGood`), by the leastness of the container's fixed
point and its positivity. -/
theorem contGood_of (hf : S.NestFacts M ls N) (hN : S.nest = some N) : S.ContGood M ls := by
  sorry

/-- **The class is inside the class's bound** (`ContInBound`), by
induction over the container's family at the instantiation: the
closure lists the container's constructors with the member field at
the family's bound. -/
theorem contInBound_of (hf : S.NestFacts M ls N) (hN : S.nest = some N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) : S.ContInBound M ls ps := by
  sorry

end IndSpec

end Fragment
