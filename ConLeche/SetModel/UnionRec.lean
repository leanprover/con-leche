module

public import ConLeche.SetModel.RecGraph
public import ConLeche.SetTheory.Derive.LfpTuple
public import ConLeche.SetModel.TaggedSum
@[expose] public section

/-!
# The simultaneous recursor of a block, over the disjoint union of its values (task #315)

A block of `k` families has ONE recursion: its recursors (one per
member — and, at a nested block, one per container pin) are the
components of a single function on the **disjoint union of the
block's values**, `unionSet k Is L = { ⟨c, i, x⟩ | c < k, i ∈ Is c,
x ∈ app (L c) i }`, obtained from the recursion theorem
(`recGraph_exists_unique`, `ConLeche/SetModel/RecGraph.lean`) at that
index set.  The union appears here and only here: never in a carrier,
never in an index set — it is the index set of the recursor's GRAPH.

Abstractly, over an arbitrary tuple of recursion CLASSES `C`, a
predecessor map `pred` on tagged values, a bound `B` and a step `st`:
the recursor's graph has exactly one value at every union element
(`UnionRecKitC.exists_unique`), the recursor is the selector
`unionRecC`, and it satisfies the recursion equation
(`UnionRecKitC.rec_eq`) — the ι rules of every class at once.  The two
obligations are that the predecessor map stays inside the union and
that every union element is ACCESSIBLE along it; `SetModel/WfRec.lean`
discharges both once and for all, for ANY classes, from regularity.

**Retired (DESIGN 2026-09-21).**  This module also carried the kit at
a tuple LFP's own components: `PredsFrom` — "an element `Φ` builds
from `X` has all its predecessors in `X`'s union" — with accessibility
by simultaneous lfp induction (`unionAcc_all`), the recursor
`unionRec` and `UnionRecKit`.  That kit belonged to the WIDE route,
where a nested block's container pin was a component of the block's
tuple and the recursion had to reach it by the tuple's own induction.
Under the narrow clause the classes are ordinary carriers and the
recursion is ∈-recursion on the global subterm relation (`WfRec.lean`,
`SetTheory/Derive/TransClosure.lean`), which needs NOTHING of where
the classes come from — so `PredsFrom` and everything above it had no
consumer left and went with the wide-tuple falsifiers.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

open Tower (natFibre natFibre_vnat)

universe u

variable {V : Type u} [SetTheory V]

/-! ## The disjoint union of a tuple's values -/

/-- A value of the union: class `c`, index tuple `i`, value `x`. -/
noncomputable def tagged (c : Nat) (i x : V) : V := kpair (vnat c) (kpair i x)

theorem tagged_inj {c c' : Nat} {i x i' x' : V} (h : tagged c i x = tagged c' i' x') :
    c = c' ∧ i = i' ∧ x = x' := by
  unfold tagged at h
  obtain ⟨h1, h2⟩ := kpair_inj h
  obtain ⟨h3, h4⟩ := kpair_inj h2
  exact ⟨vnat_inj h1, h3, h4⟩

/-- **The disjoint union** of the values of the first `k` components of
a tuple of families. -/
noncomputable def unionSet (k : Nat) (Is : Nat → V) (X : Nat → V) : V :=
  sigmaPairs (sep omega fun c => ∃ n, n < k ∧ c = vnat n)
    (natFibre fun c => sigmaPairs (Is c) fun i => app (X c) i)

theorem mem_unionSet {k : Nat} {Is X : Nat → V} {u : V} :
    u ∈ˢ unionSet k Is X ↔
      ∃ c, c < k ∧ ∃ i, i ∈ˢ Is c ∧ ∃ x, x ∈ˢ app (X c) i ∧ u = tagged c i x := by
  unfold unionSet
  rw [mem_sigmaPairs]
  constructor
  · rintro ⟨t, ht, p, hp, rfl⟩
    obtain ⟨-, n, hn, rfl⟩ := mem_sep.mp ht
    rw [natFibre_vnat] at hp
    obtain ⟨i, hi, x, hx, rfl⟩ := mem_sigmaPairs.mp hp
    exact ⟨n, hn, i, hi, x, hx, rfl⟩
  · rintro ⟨c, hc, i, hi, x, hx, rfl⟩
    refine ⟨vnat c, mem_sep.mpr ⟨vnat_mem_omega c, c, hc, rfl⟩, kpair i x, ?_, rfl⟩
    rw [natFibre_vnat]
    exact mem_sigmaPairs.mpr ⟨i, hi, x, hx, rfl⟩

theorem tagged_mem_unionSet {k : Nat} {Is X : Nat → V} {c : Nat} (hc : c < k) {i x : V}
    (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (X c) i) : tagged c i x ∈ˢ unionSet k Is X :=
  mem_unionSet.mpr ⟨c, hc, i, hi, x, hx, rfl⟩

theorem tagged_mem_unionSet_iff {k : Nat} {Is X : Nat → V} {c : Nat} {i x : V} :
    tagged c i x ∈ˢ unionSet k Is X ↔ c < k ∧ i ∈ˢ Is c ∧ x ∈ˢ app (X c) i := by
  rw [mem_unionSet]
  constructor
  · rintro ⟨c', hc', i', hi', x', hx', h⟩
    obtain ⟨rfl, rfl, rfl⟩ := tagged_inj h
    exact ⟨hc', hi', hx'⟩
  · rintro ⟨hc, hi, hx⟩
    exact ⟨c, hc, i, hi, x, hx, rfl⟩

theorem unionSet_mono {k : Nat} {Is X Y : Nat → V} (h : TupleLe k Is X Y) :
    unionSet k Is X ⊆ˢ unionSet k Is Y := by
  intro u hu
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  exact tagged_mem_unionSet hc hi (h c hc i hi x hx)

/-! ## Relation-defined predecessors -/

/-- The predecessor SET of a predecessor RELATION `R`, separated off
the union `U`: what every instance spells (`PairRel`, `TreeRel`). -/
noncomputable def relPred (U : V) (R : V → V → Prop) (u : V) : V := sep U (R u)

theorem mem_relPred {U : V} {R : V → V → Prop} {u v : V} :
    v ∈ˢ relPred U R u ↔ v ∈ˢ U ∧ R u v := mem_sep

theorem relPred_subset (U : V) (R : V → V → Prop) (u : V) : relPred U R u ⊆ˢ U := sep_subset

/-! ## The recursor over classes with their OWN accessibility (task #315 M7)

A NESTED block's recursion classes are the members' carriers followed
by the containers' carriers at the hole — and a container's class is
not a component of anything the block builds, so a simultaneous
induction over the block's own carrier does not reach it.  What the
recursion theorem needs of the classes is only that every element of
their union is ACCESSIBLE along the predecessor map and that the map
stays inside the union: this section states the recursor over an
ARBITRARY tuple of classes `C` under exactly those two obligations
(`unionRecC`, `UnionRecKitC`).  Both are discharged for every class at
once in `SetModel/WfRec.lean`, off regularity. -/

section Classes

variable {ℓ k : Nat} {Is C : Nat → V} {pred : V → V} {B : V → V} {st : V → V → V}

/-- **The recursor over the classes `C`**: the selector of the
recursion graph over their union, at class `c`, index `i`, value `x`. -/
noncomputable def unionRecC (ℓ k : Nat) (Is C : Nat → V) (pred : V → V) (B : V → V)
    (st : V → V → V) (c : Nat) (i x : V) : V :=
  recSel (recGraph ℓ (unionSet k Is C) pred B st) (tagged c i x)

/-- **An accessibility introduction**: an element of the index set
whose predecessors are all accessible is accessible (the `Acc`
family's fixed-point equation, read backwards). -/
theorem accFam_intro {I : V} {Cond : V → Prop} (hpred : ∀ i, i ∈ˢ I → pred i ⊆ˢ I) {u : V}
    (hu : u ∈ˢ I) (hC : Cond u) (h : ∀ v, v ∈ˢ pred u → ∃ y, y ∈ˢ app (accFam I pred Cond) v) :
    (pt : V) ∈ˢ app (accFam I pred Cond) u := by
  unfold accFam
  rw [← app_lfpFamSet_eq ⟨_, accStep_closed⟩ (accStep_mono hpred) accStep_maps hu,
    app_app_accStep (lfpFamSet_mem _ _ _) hu]
  exact pt_mem_truthVal ⟨hC, h⟩

/-- **The recursion data over classes, bundled**: the predecessor map
stays inside the union, the bound is a set at the level, the step
lands in the bound — and the recursion theorem HOLDS at that data
(`exu`).

`exu` is a field, not a consequence of an accessibility field,
because accessibility is a WAY to the recursion theorem and not the
only one.  `ofAcc` is that way (every element of the union accessible
along `pred`, which `SetModel/WfRec.lean` discharges for any classes
off regularity) and regimes WF and IND take it; regime SQ proves the
singleton property by the block's OWN lfp induction instead
(`sqGraph_singleton`, `Semantics/Tower/FixSquashI.lean`) and has no
accessibility argument to give.  Making the theorem the field is what
lets both in. -/
structure UnionRecKitC (ℓ k : Nat) (Is C : Nat → V) where
  pred : V → V
  B : V → V
  st : V → V → V
  predSub : ∀ u, u ∈ˢ unionSet k Is C → pred u ⊆ˢ unionSet k Is C
  hB : ∀ u, u ∈ˢ unionSet k Is C → B u ∈ˢ (univ ℓ : V)
  hst : ∀ u, u ∈ˢ unionSet k Is C → ∀ g,
    g ∈ˢ piSet (pred u) (fun j => app (recGraph ℓ (unionSet k Is C) pred B st) j) →
    st u g ∈ˢ B u
  /-- **The recursion theorem at this data**: the graph has exactly
  one value at every union element. -/
  exu : ∀ u, u ∈ˢ unionSet k Is C →
    (∃ v, v ∈ˢ app (recGraph ℓ (unionSet k Is C) pred B st) u) ∧
    ∀ v v', v ∈ˢ app (recGraph ℓ (unionSet k Is C) pred B st) u →
      v' ∈ˢ app (recGraph ℓ (unionSet k Is C) pred B st) u → v = v'

/-- **The kit from ACCESSIBILITY** — the way regimes WF and IND build
it: `recGraph_exists_unique` at an accessibility witness. -/
noncomputable def UnionRecKitC.ofAcc (pred B : V → V) (st : V → V → V)
    (predSub : ∀ u, u ∈ˢ unionSet k Is C → pred u ⊆ˢ unionSet k Is C)
    (hB : ∀ u, u ∈ˢ unionSet k Is C → B u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ unionSet k Is C → ∀ g,
      g ∈ˢ piSet (pred u) (fun j => app (recGraph ℓ (unionSet k Is C) pred B st) j) →
      st u g ∈ˢ B u)
    (acc : ∀ u, u ∈ˢ unionSet k Is C →
      ∃ y, y ∈ˢ app (accFam (unionSet k Is C) pred (fun _ => True)) u) :
    UnionRecKitC ℓ k Is C where
  pred := pred
  B := B
  st := st
  predSub := predSub
  hB := hB
  hst := hst
  exu := fun u hu => (acc u hu).elim fun y hy =>
    recGraph_exists_unique hB predSub hst u hu y hy

@[simp] theorem UnionRecKitC.ofAcc_pred (pred B st predSub hB hst acc) :
    (UnionRecKitC.ofAcc (ℓ := ℓ) (k := k) (Is := Is) (C := C)
      pred B st predSub hB hst acc).pred = pred := rfl

@[simp] theorem UnionRecKitC.ofAcc_B (pred B st predSub hB hst acc) :
    (UnionRecKitC.ofAcc (ℓ := ℓ) (k := k) (Is := Is) (C := C)
      pred B st predSub hB hst acc).B = B := rfl

@[simp] theorem UnionRecKitC.ofAcc_st (pred B st predSub hB hst acc) :
    (UnionRecKitC.ofAcc (ℓ := ℓ) (k := k) (Is := Is) (C := C)
      pred B st predSub hB hst acc).st = st := rfl

namespace UnionRecKitC

variable (K : UnionRecKitC ℓ k Is C)

/-- The kit's recursor at class `c`. -/
noncomputable def recAt (c : Nat) (i x : V) : V := unionRecC ℓ k Is C K.pred K.B K.st c i x

/-- **The recursion theorem over classes**: the graph has exactly one
value at every union element — the kit's own field. -/
theorem exists_unique {u : V} (hu : u ∈ˢ unionSet k Is C) :
    (∃ v, v ∈ˢ app (recGraph ℓ (unionSet k Is C) K.pred K.B K.st) u) ∧
    ∀ v v', v ∈ˢ app (recGraph ℓ (unionSet k Is C) K.pred K.B K.st) u →
      v' ∈ˢ app (recGraph ℓ (unionSet k Is C) K.pred K.B K.st) u → v = v' :=
  K.exu u hu

/-- The graph's values are bounded. -/
theorem graph_mem_B {u v : V} (hu : u ∈ˢ unionSet k Is C)
    (hv : v ∈ˢ app (recGraph ℓ (unionSet k Is C) K.pred K.B K.st) u) : v ∈ˢ K.B u := by
  rw [app_recGraph_eq K.hB K.predSub hu] at hv
  exact (mem_recGraphFibre.mp hv).1

/-- The recursor's value is in the graph's fibre. -/
theorem rec_mem {c : Nat} (hc : c < k) {i x : V} (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (C c) i) :
    K.recAt c i x ∈ˢ app (recGraph ℓ (unionSet k Is C) K.pred K.B K.st) (tagged c i x) :=
  recSel_mem (K.exists_unique (tagged_mem_unionSet hc hi hx)).1

/-- **Typing**: the recursor's value at a class element lies in the
bound. -/
theorem rec_mem_B {c : Nat} (hc : c < k) {i x : V} (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (C c) i) :
    K.recAt c i x ∈ˢ K.B (tagged c i x) :=
  K.graph_mem_B (tagged_mem_unionSet hc hi hx) (K.rec_mem hc hi hx)

/-- **The recursion equation**: the recursor at a class element is the
step at the recursor's graph over its predecessors. -/
theorem rec_eq {c : Nat} (hc : c < k) {i x : V} (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (C c) i) :
    K.recAt c i x
      = K.st (tagged c i x)
          (graph (fun j => recSel (recGraph ℓ (unionSet k Is C) K.pred K.B K.st) j)
            (K.pred (tagged c i x))) :=
  recSel_eq K.hB K.predSub (tagged_mem_unionSet hc hi hx)
    (K.exists_unique (tagged_mem_unionSet hc hi hx)).1
    fun j hj => K.exists_unique (K.predSub _ (tagged_mem_unionSet hc hi hx) j hj)

end UnionRecKitC

end Classes

end ConLeche.SetTheory
