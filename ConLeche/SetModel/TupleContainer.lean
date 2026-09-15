module

import ConLeche.SetModel.Container
import ConLeche.SetTheory.Derive.Universe
public import ConLeche.SetTheory.Derive.LfpTuple
public import ConLeche.SetModel.TaggedSum
@[expose] public section

/-!
# The closed tuple of a block presented as a member container (task #315, (W) at tuples)

The least pre-fixed TUPLE of a block's operator (`lfpTuple`,
`ConLeche/SetTheory/Derive/LfpTuple.lean`) is a fixed point only under a
closed tuple, and the uniform datum's `functor` clause records one
(`∃ L, IsClosedTuple …`).  This module supplies it for every block
whose operator is presented as a **member container per component**:
an element of component `m`'s fibre at `i` is `mk m a g` for a shape
`a ∈ A m i` and a function `g` from the shape's positions `B a` into
the fibres of the ARGUMENT TUPLE at the targets `(tgtM a p, tgtI a p)`
— a target is a member together with an index of that member, so a
recursive field of a mutual block reads the component of the member it
targets.  Shapes and position sets are members of `univ w`, the
builder keeps members.

**The proof is the single-family witness at the disjoint union of the
index sets** (`container_closed_exists`, `SetModel/Container.lean`):
a tuple of families over `Is` is one family over `unionIdx k Is =
{ ⟨m, i⟩ | m < k, i ∈ Is m }` (`splitFam`/`joinFun`), the block's
operator is one container over that union (the shapes tagged by their
member), and the closed family the container theorem yields splits
back into a closed tuple.  The union is a device of THIS proof: it is
neither a carrier nor an index set of the datum, exactly as
`UnionRec.lean`'s union of values is the recursor's index set only.

Two further forms complete (W):

* `closedTuple_zero`: at a `Prop`-valued block (`w = 0`) the top tuple
  is closed under `MapsTuple` alone;
* `closedTuple_composeAt`: a NESTED slot.  When component `c` of an
  auxiliary operator `Ψ` is a container pin (a family read through a
  stored container at the members), the block's operator is `Ψ` with
  that component replaced by the least pre-fixed family of `Ψ`'s
  section there (`composeAt`), and a closed tuple for `Ψ` is a closed
  tuple for the composed operator — by leastness of the section's lfp
  and monotonicity of `Ψ` at the member components, under no container
  law and no level fact (the experiment's
  `closed_composed_of_closed_aux`, `SetModel/NestedTreeList.lean`, is
  the instance at `Tree ::= node (List Tree)`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

open Tower (natFibre natFibre_vnat)

universe u

variable {V : Type u} [SetTheory V]

/-! ## The disjoint union of the index sets, and the split/join of a tuple -/

/-- The disjoint union of the first `k` index sets: `⟨m, i⟩` for
`m < k`, `i ∈ Is m`. -/
noncomputable def unionIdx (k : Nat) (Is : Nat → V) : V :=
  sigmaPairs (sep omega fun c => ∃ n, n < k ∧ c = vnat n) (natFibre Is)

theorem mem_unionIdx {k : Nat} {Is : Nat → V} {u : V} :
    u ∈ˢ unionIdx k Is ↔ ∃ m, m < k ∧ ∃ i, i ∈ˢ Is m ∧ u = kpair (vnat m) i := by
  unfold unionIdx
  rw [mem_sigmaPairs]
  constructor
  · rintro ⟨t, ht, i, hi, rfl⟩
    obtain ⟨-, n, hn, rfl⟩ := mem_sep.mp ht
    rw [natFibre_vnat] at hi
    exact ⟨n, hn, i, hi, rfl⟩
  · rintro ⟨m, hm, i, hi, rfl⟩
    refine ⟨vnat m, mem_sep.mpr ⟨vnat_mem_omega m, m, hm, rfl⟩, i, ?_, rfl⟩
    rw [natFibre_vnat]
    exact hi

theorem kpair_vnat_mem_unionIdx {k : Nat} {Is : Nat → V} {m : Nat} (hm : m < k) {i : V}
    (hi : i ∈ˢ Is m) : kpair (vnat m) i ∈ˢ unionIdx k Is :=
  mem_unionIdx.mpr ⟨m, hm, i, hi, rfl⟩

/-- A family over the union, read as a tuple of families. -/
noncomputable def splitFam (Is : Nat → V) (Y : V) : Nat → V :=
  fun m => graph (fun i => app Y (kpair (vnat m) i)) (Is m)

theorem app_splitFam {Is : Nat → V} {Y : V} {m : Nat} {i : V} (hi : i ∈ˢ Is m) :
    app (splitFam Is Y m) i = app Y (kpair (vnat m) i) :=
  app_graph hi

theorem splitFam_mem {w k : Nat} {Is : Nat → V} {Y : V} (hY : Y ∈ˢ famSpace w (unionIdx k Is)) :
    InTupleSpace w k Is (splitFam Is Y) := fun _ hm =>
  graph_mem_famSpace fun _ hi => famSpace_app hY (kpair_vnat_mem_unionIdx hm hi)

/-- The tuple functor `Φ`, read as a family functor over the union:
at `⟨m, i⟩` the fibre of `Φ`'s component `m` at `i`, the argument
split into a tuple. -/
noncomputable def joinFun (k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) (Y : V) : V :=
  graph (fun u => natFibre (fun m => app (Φ (splitFam Is Y) m) (ssnd u)) (sfst u)) (unionIdx k Is)

theorem app_joinFun {k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} {Y : V} {m : Nat}
    (hm : m < k) {i : V} (hi : i ∈ˢ Is m) :
    app (joinFun k Is Φ Y) (kpair (vnat m) i) = app (Φ (splitFam Is Y) m) i := by
  unfold joinFun
  rw [app_graph (kpair_vnat_mem_unionIdx hm hi), sfst_kpair, ssnd_kpair, natFibre_vnat]

/-! ## The closed tuple of a member container -/

/-- A natural number is a member of every positive universe. -/
theorem vnat_mem_univ_pos {w : Nat} (hw : w ≠ 0) (n : Nat) : (vnat n : V) ∈ˢ (univ w : V) := by
  match w, hw with
  | w + 1, _ =>
    exact (univ_isTGUniverse (Nat.succ_ne_zero w)).transitive (omega_mem_univ_succ w)
      (vnat_mem_omega n)

/-- **A block presented as a member container has a closed tuple** (W
at tuples).  Component `m`'s fibre at `i` consists of `mk m a g` for
shapes `a ∈ A m i` and functions `g` from the positions `B a` into the
argument tuple's fibres at the targets `(tgtM a p, tgtI a p)`
(`helim`); shapes and positions are members of `univ w`, the targets
are indices of their members, the builder keeps members.  The proof
is `container_closed_exists` at the union of the index sets, with the
shapes tagged by their member. -/
theorem tupleContainer_closed_exists {w : Nat} (hw : w ≠ 0) {k : Nat} {Is : Nat → V}
    (Φ : (Nat → V) → Nat → V) (A : Nat → V → V) (B : V → V) (tgtM : V → V → Nat)
    (tgtI : V → V → V) (mk : Nat → V → V → V)
    (hA : ∀ m, m < k → ∀ i, i ∈ˢ Is m → A m i ∈ˢ (univ w : V))
    (hB : ∀ m, m < k → ∀ i a, i ∈ˢ Is m → a ∈ˢ A m i → B a ∈ˢ (univ w : V))
    (htgt : ∀ m, m < k → ∀ i a p, i ∈ˢ Is m → a ∈ˢ A m i → p ∈ˢ B a →
      tgtM a p < k ∧ tgtI a p ∈ˢ Is (tgtM a p))
    (hmkU : ∀ m, m < k → ∀ i a g, i ∈ˢ Is m → a ∈ˢ A m i → g ∈ˢ (univ w : V) →
      mk m a g ∈ˢ (univ w : V))
    (helim : ∀ X, InTupleSpace w k Is X → ∀ m, m < k → ∀ i, i ∈ˢ Is m → ∀ x,
      x ∈ˢ app (Φ X m) i →
      ∃ a, a ∈ˢ A m i ∧ ∃ g, g ∈ˢ piSet (B a) (fun p => app (X (tgtM a p)) (tgtI a p)) ∧
        x = mk m a g) :
    ∃ L, IsClosedTuple w k Is Φ L := by
  have hU := univ_isTGUniverse (V := V) hw
  -- the container over the union: shapes tagged by their member
  let A' : V → V := fun u => natFibre (fun m => image (fun a => kpair (vnat m) a) (A m (ssnd u))) (sfst u)
  let B' : V → V := fun a' => B (ssnd a')
  let tgt' : V → V → V := fun a' p => kpair (vnat (tgtM (ssnd a') p)) (tgtI (ssnd a') p)
  let mk' : V → V → V := fun a' g => natFibre (fun m => mk m (ssnd a') g) (sfst a')
  have hA'_at : ∀ m i, A' (kpair (vnat m) i) = image (fun a => kpair (vnat m) a) (A m i) := by
    intro m i
    show natFibre _ (sfst (kpair (vnat m) i)) = _
    rw [sfst_kpair, natFibre_vnat, ssnd_kpair]
  have hmk'_at : ∀ m a g, mk' (kpair (vnat m) a) g = mk m a g := by
    intro m a g
    show natFibre _ (sfst (kpair (vnat m) a)) = _
    rw [sfst_kpair, natFibre_vnat, ssnd_kpair]
  have hmemA' : ∀ {u a'}, u ∈ˢ unionIdx k Is → a' ∈ˢ A' u →
      ∃ m, m < k ∧ ∃ i, i ∈ˢ Is m ∧ u = kpair (vnat m) i ∧ ∃ a, a ∈ˢ A m i ∧ a' = kpair (vnat m) a := by
    intro u a' hu ha'
    obtain ⟨m, hm, i, hi, rfl⟩ := mem_unionIdx.mp hu
    rw [hA'_at] at ha'
    obtain ⟨a, ha, rfl⟩ := mem_image.mp ha'
    exact ⟨m, hm, i, hi, rfl, a, ha, rfl⟩
  obtain ⟨L', hL'mem, hL'cl⟩ := container_closed_exists hw (I := unionIdx k Is) (joinFun k Is Φ)
    A' B' tgt' mk'
    (fun u hu => by
      obtain ⟨m, hm, i, hi, rfl⟩ := mem_unionIdx.mp hu
      rw [hA'_at]
      exact hU.image_mem (hA m hm i hi) fun a ha =>
        hU.kpair_mem (hA m hm i hi) (vnat_mem_univ_pos hw m) (hU.transitive (hA m hm i hi) ha))
    (fun u a' hu ha' => by
      obtain ⟨m, hm, i, hi, rfl, a, ha, rfl⟩ := hmemA' hu ha'
      show B (ssnd (kpair (vnat m) a)) ∈ˢ _
      rw [ssnd_kpair]
      exact hB m hm i a hi ha)
    (fun u a' p hu ha' hp => by
      obtain ⟨m, hm, i, hi, rfl, a, ha, rfl⟩ := hmemA' hu ha'
      show kpair (vnat (tgtM (ssnd (kpair (vnat m) a)) p)) (tgtI (ssnd (kpair (vnat m) a)) p)
        ∈ˢ unionIdx k Is
      rw [ssnd_kpair]
      have hp' : p ∈ˢ B a := by
        have h : p ∈ˢ B (ssnd (kpair (vnat m) a)) := hp
        rwa [ssnd_kpair] at h
      obtain ⟨h1, h2⟩ := htgt m hm i a p hi ha hp'
      exact kpair_vnat_mem_unionIdx h1 h2)
    (fun u a' g hu ha' hg => by
      obtain ⟨m, hm, i, hi, rfl, a, ha, rfl⟩ := hmemA' hu ha'
      rw [hmk'_at]
      exact hmkU m hm i a g hi ha hg)
    (fun Y hY u hu x hx => by
      obtain ⟨m, hm, i, hi, rfl⟩ := mem_unionIdx.mp hu
      rw [app_joinFun hm hi] at hx
      obtain ⟨a, ha, g, hg, rfl⟩ := helim _ (splitFam_mem hY) m hm i hi x hx
      refine ⟨kpair (vnat m) a, by rw [hA'_at]; exact mem_image.mpr ⟨a, ha, rfl⟩, g, ?_, ?_⟩
      · show g ∈ˢ piSet (B (ssnd (kpair (vnat m) a))) fun p =>
          app Y (kpair (vnat (tgtM (ssnd (kpair (vnat m) a)) p)) (tgtI (ssnd (kpair (vnat m) a)) p))
        rw [ssnd_kpair]
        rw [piSet_congr (B' := fun p => app (splitFam Is Y (tgtM a p)) (tgtI a p))
          (fun p hp => (app_splitFam (htgt m hm i a p hi ha hp).2).symm)]
        exact hg
      · rw [hmk'_at])
  -- the closed family splits into a closed tuple
  refine ⟨splitFam Is L', splitFam_mem hL'mem, fun m hm i hi x hx => ?_⟩
  rw [app_splitFam hi]
  refine hL'cl (kpair (vnat m) i) (kpair_vnat_mem_unionIdx hm hi) x ?_
  rw [app_joinFun hm hi]
  exact hx

/-- **At a `Prop`-valued block the top tuple is closed**: every fibre
at `w = 0` is a subset of `{pt}`, so `MapsTuple` alone suffices. -/
theorem closedTuple_zero {k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    (hmaps : MapsTuple 0 k Is Φ) : ∃ L, IsClosedTuple 0 k Is Φ L := by
  have htop : InTupleSpace 0 k Is (fun m => graph (fun _ => unitSet) (Is m)) := fun m _ =>
    graph_mem_famSpace fun _ _ => unitSet_mem_univ 0
  refine ⟨_, htop, fun m hm i hi x hx => ?_⟩
  show x ∈ˢ app (graph (fun _ => unitSet) (Is m)) i
  rw [app_graph hi]
  have := famSpace_app (hmaps _ htop m hm) hi
  rw [univ_zero] at this
  exact mem_univZero.mp this x hx

/-! ## A nested slot: the composed operator's closed tuple from the auxiliary one -/

/-- **The composed operator**: the auxiliary operator `Ψ` with its
component `c` — a container pin — replaced by the least pre-fixed
family of `Ψ`'s section at `c`, the other components held at the
argument.  At `Tree ::= node (List Tree)`, with `Ψ` the two-member
auxiliary operator (trees, lists of trees), `composeAt … Ψ 1` at
component `0` is the node arm at `⟦List⟧(X 0)`. -/
noncomputable def composeAt (w : Nat) (Is : Nat → V) (Ψ : (Nat → V) → Nat → V) (c : Nat)
    (X : Nat → V) : Nat → V :=
  Ψ (updTuple X c (lfpFamSet w (Is c) (secF w Is Ψ X c)))

/-- A closed tuple's component `c` is a closed family of `Ψ`'s section
at `c`. -/
theorem isClosedFam_secF_of_closedTuple {w k : Nat} {Is : Nat → V} {Ψ : (Nat → V) → Nat → V}
    {L : Nat → V} (hL : IsClosedTuple w k Is Ψ L) {c : Nat} (hc : c < k) :
    IsClosedFam w (Is c) (secF w Is Ψ L c) (L c) := by
  refine ⟨hL.1 c hc, ?_⟩
  rw [app_secF (hL.1 c hc), updTuple_self]
  exact hL.2 c hc

/-- **(W) at a nested slot**: a closed tuple of the auxiliary operator
`Ψ` on `k + 1` components is a closed tuple of the operator composed
at the pin `k`, on the `k` member components — by leastness of the
section's lfp below `L k`, and monotonicity of `Ψ` at the MEMBER
components (`hmono`, the member half of `MonoTuple w (k + 1) Is Ψ`;
nothing is asked of the pin's component, so no container law and no
level fact enters). -/
theorem closedTuple_composeAt {w k : Nat} {Is : Nat → V} {Ψ : (Nat → V) → Nat → V}
    (hmono : ∀ X Y, InTupleSpace w (k + 1) Is X → InTupleSpace w (k + 1) Is Y →
      TupleLe (k + 1) Is X Y → TupleLe k Is (Ψ X) (Ψ Y))
    {L : Nat → V} (hL : IsClosedTuple w (k + 1) Is Ψ L) :
    IsClosedTuple w k Is (composeAt w Is Ψ k) L := by
  have hP : lfpFamSet w (Is k) (secF w Is Ψ L k) ∈ˢ famSpace w (Is k) := lfpFamSet_mem _ _ _
  have hPle : FamLe (Is k) (lfpFamSet w (Is k) (secF w Is Ψ L k)) (L k) :=
    lfpFamSet_le (isClosedFam_secF_of_closedTuple hL (Nat.lt_succ_self k))
  refine ⟨fun m hm => hL.1 m (Nat.lt_succ_of_lt hm), fun m hm => ?_⟩
  refine FamLe.trans ?_ (hL.2 m (Nat.lt_succ_of_lt hm))
  refine hmono _ _ (inTupleSpace_updTuple hL.1 hP) hL.1 ?_ m hm
  intro j hj
  by_cases hjk : j = k
  · subst hjk
    rw [updTuple_same]
    exact hPle
  · rw [updTuple_other _ _ hjk]
    exact FamLe.refl _ _

end ConLeche.SetTheory
