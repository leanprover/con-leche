module

public import ConLeche.SetTheory.Derive.LfpTuple
@[expose] public section

/-!
# Closing the holes: the least tuple is monotone in its operator (lane POSPROOF)

The set-level half of the CONTAINER case of "positivity ⇒ monotone"
(charter items 2–4, 8).  A container instance `C (t[X])` is read, by
`C`'s lfp clause, as a component of the least pre-fixed tuple of `C`'s
operator at the parameter frame `⟦t[X]⟧`.  Its monotonicity in the
outer holes `X` is NOT a property of `C` (charter item 4): it is

* **positivity at the instantiation** — the operator at the frame of
  `X` lies below the operator at the frame of `X'`, at every tuple of
  the space, the in-progress instantiations (`C`'s own holes) HELD
  FIXED (`lfpTuple_le_of_opLe`'s `hle`; the term-level supplier is
  `Semantics/Inductives/HoleMono.lean`, the per-case lemmas of
  `nestPos`'s run); plus
* **the lfp's monotonicity in its operator**, by leastness
  (`lfpTuple_le_of_opLe`): the larger operator's least tuple is closed
  for the smaller one.  Only the larger operator's closure and
  monotonicity in its own holes are used — both are the container's own
  clause (`LfpClause.functor`), established when the container was
  installed, at every parameter frame.

Monotonicity in the in-progress holes is therefore never needed jointly
with `X`: at a fixed tuple the in-progress holes are constants, and the
container's own monotonicity in them is its clause's.

**D2 (charter item 8: unreached members of a container's group).**
`lfpTuple_eq_lfpFam_of_indep`: when component `m` of the operator reads
the tuple only at `m` (the member's constructors never reach the other
members), `m`'s component of the group's least tuple is the least family
of `m`'s own operator, the others held at ANY tuple of the space —
Bekić's section law (`lfpTuple_eq_section`) plus the independence.  So an
unreached member (positive or not) does not change the reached
component, and positivity of the reached member alone suffices.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

section Close

variable {w k : Nat} {Is : Nat → V} {Φ Φ' : (Nat → V) → Nat → V}

/-- **The least tuple is monotone in its operator, by leastness.**  If
the smaller operator lies below the larger one at the larger one's
least tuple, the larger least tuple is closed for the smaller operator.
Only the LARGER operator's closure and monotonicity are used. -/
theorem lfpTuple_le_of_opLe (hcl' : ∃ L, IsClosedTuple w k Is Φ' L)
    (hmono' : MonoTuple w k Is Φ')
    (hle : TupleLe k Is (Φ (lfpTuple w k Is Φ')) (Φ' (lfpTuple w k Is Φ'))) :
    TupleLe k Is (lfpTuple w k Is Φ) (lfpTuple w k Is Φ') :=
  lfpTuple_le ⟨lfpTuple_mem w k Is Φ', TupleLe.trans hle (lfpTuple_closed hcl' hmono')⟩

/-- **The same, for a parametrised operator** (a container's operator
as a function of its parameter frame): pointwise comparison on the
space at the two parameters gives the comparison of the least
tuples. -/
theorem lfpTuple_mono_param {P : Type u} (Ψ : P → (Nat → V) → Nat → V) {a b : P}
    (hcl : ∃ L, IsClosedTuple w k Is (Ψ b) L) (hmono : MonoTuple w k Is (Ψ b))
    (hab : ∀ Y, InTupleSpace w k Is Y → TupleLe k Is (Ψ a Y) (Ψ b Y)) :
    TupleLe k Is (lfpTuple w k Is (Ψ a)) (lfpTuple w k Is (Ψ b)) :=
  lfpTuple_le_of_opLe hcl hmono (hab _ (lfpTuple_mem w k Is (Ψ b)))

end Close

section Unreached

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}

/-- Component `m` of the operator reads the tuple only at `m`: the
member's constructors never reach the other members. -/
def ReadsOnly (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) (m : Nat) : Prop :=
  ∀ X Y, InTupleSpace w k Is X → InTupleSpace w k Is Y → X m = Y m → Φ X m = Φ Y m

/-- The sections at two tuples of the space coincide when component `m`
reads only `m`. -/
theorem secF_eq_of_readsOnly {m : Nat} (hro : ReadsOnly w k Is Φ m) {L L₀ : Nat → V}
    (hL : InTupleSpace w k Is L) (hL₀ : InTupleSpace w k Is L₀) :
    secF w Is Φ L m = secF w Is Φ L₀ m := by
  unfold secF
  refine graph_congr fun X hX => ?_
  exact hro _ _ (inTupleSpace_updTuple hL hX) (inTupleSpace_updTuple hL₀ hX)
    (by rw [updTuple_same, updTuple_same])

/-- **D2: an unreached member does not change the reached component.**
Member `m`'s component of the group's least tuple is the least family
of `m`'s own operator (the section at ANY tuple `L₀` of the space), when
`m`'s component of the operator reads the tuple only at `m`. -/
theorem lfpTuple_eq_lfpFam_of_indep (h : ∃ L, IsClosedTuple w k Is Φ L)
    (hmono : MonoTuple w k Is Φ) {m : Nat} (hm : m < k) (hro : ReadsOnly w k Is Φ m)
    {L₀ : Nat → V} (hL₀ : InTupleSpace w k Is L₀) :
    lfpTuple w k Is Φ m = lfpFamSet w (Is m) (secF w Is Φ L₀ m) := by
  rw [lfpTuple_eq_section h hmono hm,
    secF_eq_of_readsOnly hro (lfpTuple_mem w k Is Φ) hL₀]

end Unreached

section Fibre

variable {k : Nat} {Is : Nat → V}

/-- **Operators compared through their fibre laws.**  Two tuples whose
components' fibres are the injections of the spines satisfying `fits₁`,
resp. `fits₂`, compare as soon as the fit relations do.  This is how a
positivity fact about the constructors' field readings (a fit relation
growing) becomes a comparison of operator values — at two tuples (the
operator's own monotonicity) or at two parameter frames (a container's
instance, `lfpTuple_le_of_opLe`). -/
theorem tupleLe_of_fibre {A B : Nat → V} {fits₁ fits₂ : V → Nat → Nat → List V → Prop}
    {inj : Nat → Nat → List V → V}
    (h₁ : ∀ c, c < k → ∀ t, t ∈ˢ Is c → ∀ x,
      x ∈ˢ app (A c) t ↔ ∃ j fs, fits₁ t c j fs ∧ x = inj c j fs)
    (h₂ : ∀ c, c < k → ∀ t, t ∈ˢ Is c → ∀ x,
      x ∈ˢ app (B c) t ↔ ∃ j fs, fits₂ t c j fs ∧ x = inj c j fs)
    (hfits : ∀ c, c < k → ∀ t, t ∈ˢ Is c → ∀ j fs, fits₁ t c j fs → fits₂ t c j fs) :
    TupleLe k Is A B := by
  intro c hc t ht x hx
  obtain ⟨j, fs, hf, rfl⟩ := (h₁ c hc t ht x).mp hx
  exact (h₂ c hc t ht _).mpr ⟨j, fs, hfits c hc t ht j fs hf, rfl⟩

end Fibre

section OnGroup

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}

open Classical in
/-- **The least tuple lies below `B` on a group `G` of components**
(lane CONTSEM: a container frame abstracts only the reached part `G` of
its group; the other components are read concretely, i.e. held at the
least tuple itself): if the operator, at the least tuple with its
`G`-components replaced by `B`'s, lies below `B` on `G`, then so does
the least tuple.  By induction (`lfpTuple_induction`) at the separation
"on `G`, inside `B`": no Bekić needed. -/
theorem lfpTuple_le_on (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (G : Nat → Prop) {B : Nat → V} (hB : InTupleSpace w k Is B)
    (hZ : ∀ g, g < k → G g →
      FamLe (Is g) (Φ (fun x => if G x then B x else lfpTuple w k Is Φ x) g) (B g)) :
    ∀ g, g < k → G g → FamLe (Is g) (lfpTuple w k Is Φ g) (B g) := by
  let P : Nat → V → V → Prop := fun m i x => G m → x ∈ˢ app (B m) i
  have hZmem : InTupleSpace w k Is (fun x => if G x then B x else lfpTuple w k Is Φ x) := by
    intro m hm
    by_cases hg : G m
    · simp only [if_pos hg]; exact hB m hm
    · simp only [if_neg hg]; exact lfpTuple_mem w k Is Φ m hm
  have hSZ : TupleLe k Is (sepTuple w k Is Φ P)
      (fun x => if G x then B x else lfpTuple w k Is Φ x) := by
    intro m hm i hi y hy
    have hy' := hy
    unfold sepTuple at hy'
    rw [app_graph hi, mem_sep] at hy'
    by_cases hg : G m
    · simp only [if_pos hg]; exact hy'.2 hg
    · simp only [if_neg hg]; exact hy'.1
  have hind := lfpTuple_induction h hmono P fun m hm i hi x hx hg => by
    have hx' := hmono _ _ (sepTuple_mem w k Is Φ P) hZmem hSZ m hm i hi x hx
    exact hZ m hm hg i hi x hx'
  intro g hg hG i hi x hx
  exact hind g hg i hi x hx hG

end OnGroup

end ConLeche.SetTheory
