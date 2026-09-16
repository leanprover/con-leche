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

Abstractly, over a tuple functor `Φ` with carrier `L = lfpTuple w k Is
Φ` (`ConLeche/SetTheory/Derive/LfpTuple.lean`), a predecessor map
`pred` on tagged values, a bound `B` and a step `st`:

* `PredsFrom`: an element built by `Φ` from a tuple `X` has all its
  predecessors in `X`'s union — the one fact the constructor
  decomposition (the block model's `fibre`) must supply;
* every value of the carrier is accessible (`unionAcc_all`), by
  SIMULTANEOUS lfp induction (`lfpTuple_induction`);
* hence the recursor's graph has exactly one value at every union
  element (`unionRec_exists_unique`), the recursor is the selector
  `unionRec`, and it satisfies the recursion equation
  (`unionRec_eq`) — the ι rules of every member at once.

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

/-! ## Accessibility by simultaneous induction -/

section Acc

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} (pred : V → V)

/-- **Predecessors come from the argument tuple**: an element that `Φ`
builds from `X` (at any tuple `X` below the carrier) has every
predecessor in `X`'s union.  This is what the constructor decomposition
supplies: the predecessors of `inj j f⃗` are its recursive fields, and
those are read at `X`. -/
def PredsFrom (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) (pred : V → V) : Prop :=
  ∀ X, InTupleSpace w k Is X → TupleLe k Is X (lfpTuple w k Is Φ) →
    ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x, x ∈ˢ app (Φ X c) i →
      pred (tagged c i x) ⊆ˢ unionSet k Is X

variable {pred}

/-- The predecessor map stays inside the carrier's union. -/
theorem pred_sub_union (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) (hpf : PredsFrom w k Is Φ pred) :
    ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → pred u ⊆ˢ unionSet k Is (lfpTuple w k Is Φ) := by
  intro u hu
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  rw [← app_lfpTuple_eq h hmono hmaps hc hi] at hx
  exact hpf _ (lfpTuple_mem w k Is Φ) (TupleLe.refl k Is _) c hc i hi x hx

/-- The accessibility property, per class/index/value. -/
def AccAt (k : Nat) (Is : Nat → V) (L : Nat → V) (pred : V → V) (Cond : V → Prop)
    (c : Nat) (i x : V) : Prop :=
  ∃ y, y ∈ˢ app (accFam (unionSet k Is L) pred Cond) (tagged c i x)

/-- **Accessibility over the union is a class-wise obligation**: every
union element is accessible once every class is, at any tuple of
classes `C` — nothing forces a class to be a component of a tuple lfp.
`unionAcc_all` below discharges it for a tuple's own components by
simultaneous induction; a nested block discharges it for a container
pin's class by the container's own induction at a parameter
(`SetModel/NestedTreeList.lean`, `treeAccL_of_param`). -/
theorem unionAcc_of_classAcc {k : Nat} {Is C : Nat → V} {pred : V → V} {Cond : V → Prop}
    (h : ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x, x ∈ˢ app (C c) i →
      ∃ y, y ∈ˢ app (accFam (unionSet k Is C) pred Cond) (tagged c i x)) :
    ∀ u, u ∈ˢ unionSet k Is C → ∃ y, y ∈ˢ app (accFam (unionSet k Is C) pred Cond) u := by
  intro u hu
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  exact h c hc i hi x hx

/-- **Every value of the carrier is accessible** along `pred`, by
simultaneous structural induction on the tuple. -/
theorem unionAcc_all (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) (hpf : PredsFrom w k Is Φ pred) (Cond : V → Prop)
    (hCond : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → Cond u) :
    ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ c) i →
      AccAt k Is (lfpTuple w k Is Φ) pred Cond c i x := by
  have hpredU := pred_sub_union h hmono hmaps hpf
  refine lfpTuple_induction h hmono (AccAt k Is (lfpTuple w k Is Φ) pred Cond) ?_
  intro c hc i hi x hx
  have hSmem := sepTuple_mem w k Is Φ (AccAt k Is (lfpTuple w k Is Φ) pred Cond)
  have hSle := sepTuple_le w k Is Φ (AccAt k Is (lfpTuple w k Is Φ) pred Cond)
  have hpre := hpf _ hSmem hSle c hc i hi x hx
  -- the element is in the carrier, hence its tag is in the union
  have hxL : x ∈ˢ app (lfpTuple w k Is Φ c) i := by
    have := hmono _ _ hSmem (lfpTuple_mem w k Is Φ) hSle c hc i hi x hx
    exact lfpTuple_closed h hmono c hc i hi x this
  have huU : tagged c i x ∈ˢ unionSet k Is (lfpTuple w k Is Φ) := tagged_mem_unionSet hc hi hxL
  -- the accessibility fibre is inhabited: the condition holds and every predecessor's is
  refine ⟨pt, ?_⟩
  unfold accFam
  rw [← app_lfpFamSet_eq ⟨_, accStep_closed⟩ (accStep_mono hpredU) accStep_maps huU,
    app_app_accStep (lfpFamSet_mem _ _ _) huU]
  refine mem_truthVal.mpr ⟨⟨hCond _ huU, fun j hj => ?_⟩, rfl⟩
  have hjS := hpre j hj
  obtain ⟨c', hc', i', hi', x', hx', rfl⟩ := mem_unionSet.mp hjS
  unfold sepTuple at hx'
  rw [app_graph hi'] at hx'
  exact (mem_sep.mp hx').2

/-- Every element of the carrier's union is accessible: the class-wise
obligation discharged by `unionAcc_all`. -/
theorem unionAcc_all_union (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) (hpf : PredsFrom w k Is Φ pred) (Cond : V → Prop)
    (hCond : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → Cond u) :
    ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) →
      ∃ y, y ∈ˢ app (accFam (unionSet k Is (lfpTuple w k Is Φ)) pred Cond) u :=
  unionAcc_of_classAcc (unionAcc_all h hmono hmaps hpf Cond hCond)

end Acc

/-! ## Relation-defined predecessors -/

/-- The predecessor SET of a predecessor RELATION `R`, separated off
the union `U`: what every instance spells (`PairRel`, `TreeRel`). -/
noncomputable def relPred (U : V) (R : V → V → Prop) (u : V) : V := sep U (R u)

theorem mem_relPred {U : V} {R : V → V → Prop} {u v : V} :
    v ∈ˢ relPred U R u ↔ v ∈ˢ U ∧ R u v := mem_sep

theorem relPred_subset (U : V) (R : V → V → Prop) (u : V) : relPred U R u ⊆ˢ U := sep_subset

/-! ## The recursor -/

section Rec

variable {ℓ w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
  {pred : V → V} {B : V → V} {st : V → V → V}

/-- **The block's recursor**: the selector of the recursion graph over
the union of the carrier's values, at class `c`, index `i`, value `x`.
Member `c`'s recursor is `unionRec … c`. -/
noncomputable def unionRec (ℓ w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (pred : V → V) (B : V → V) (st : V → V → V) (c : Nat) (i x : V) : V :=
  recSel (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) (tagged c i x)

/-- The recursor IS the graph's selector at the tagged value (by
definition). -/
theorem recSel_tagged (c : Nat) (i x : V) :
    unionRec ℓ w k Is Φ pred B st c i x
      = recSel (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) (tagged c i x) := rfl

/-- **The graph's values are typed**: a value of the recursion graph at
a union element lies in the bound there. -/
theorem unionGraph_mem_B (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) (hpf : PredsFrom w k Is Φ pred)
    (hB : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → B u ∈ˢ (univ ℓ : V))
    {u v : V} (hu : u ∈ˢ unionSet k Is (lfpTuple w k Is Φ))
    (hv : v ∈ˢ app (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) u) : v ∈ˢ B u := by
  rw [app_recGraph_eq hB (pred_sub_union h hmono hmaps hpf) hu] at hv
  exact (mem_recGraphFibre.mp hv).1

/-- **The recursion theorem for a block**: at every value of every
member, the recursion graph over the union has exactly one value. -/
theorem unionRec_exists_unique (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) (hpf : PredsFrom w k Is Φ pred)
    (hB : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → B u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → ∀ g,
      g ∈ˢ piSet (pred u) (fun j => app (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) j) →
      st u g ∈ˢ B u) :
    ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ c) i →
      (∃ v, v ∈ˢ app (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) (tagged c i x)) ∧
      ∀ v v', v ∈ˢ app (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) (tagged c i x) →
        v' ∈ˢ app (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) (tagged c i x) →
        v = v' := by
  intro c hc i hi x hx
  obtain ⟨y, hy⟩ : AccAt k Is (lfpTuple w k Is Φ) pred (fun _ => True) c i x :=
    unionAcc_all h hmono hmaps hpf (fun _ => True) (fun _ _ => trivial) c hc i hi x hx
  exact recGraph_exists_unique hB (pred_sub_union h hmono hmaps hpf) hst _
    (tagged_mem_unionSet hc hi hx) y hy

/-- The recursor's value is in the graph's fibre (hence in the bound
`B`: the recursor is typed). -/
theorem unionRec_mem (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) (hpf : PredsFrom w k Is Φ pred)
    (hB : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → B u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → ∀ g,
      g ∈ˢ piSet (pred u) (fun j => app (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) j) →
      st u g ∈ˢ B u)
    {c : Nat} (hc : c < k) {i x : V} (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (lfpTuple w k Is Φ c) i) :
    unionRec ℓ w k Is Φ pred B st c i x
      ∈ˢ app (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) (tagged c i x) :=
  recSel_mem (unionRec_exists_unique h hmono hmaps hpf hB hst c hc i hi x hx).1

theorem unionRec_mem_B (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) (hpf : PredsFrom w k Is Φ pred)
    (hB : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → B u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → ∀ g,
      g ∈ˢ piSet (pred u) (fun j => app (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) j) →
      st u g ∈ˢ B u)
    {c : Nat} (hc : c < k) {i x : V} (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (lfpTuple w k Is Φ c) i) :
    unionRec ℓ w k Is Φ pred B st c i x ∈ˢ B (tagged c i x) := by
  have hm := unionRec_mem h hmono hmaps hpf hB hst hc hi hx
  rw [app_recGraph_eq hB (pred_sub_union h hmono hmaps hpf) (tagged_mem_unionSet hc hi hx)] at hm
  exact (mem_recGraphFibre.mp hm).1

/-- **The recursion equation**: the recursor at a value is the step at
the recursor's graph over the value's predecessors — every member's ι
rule at once. -/
theorem unionRec_eq (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) (hpf : PredsFrom w k Is Φ pred)
    (hB : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → B u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → ∀ g,
      g ∈ˢ piSet (pred u) (fun j => app (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) j) →
      st u g ∈ˢ B u)
    {c : Nat} (hc : c < k) {i x : V} (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (lfpTuple w k Is Φ c) i) :
    unionRec ℓ w k Is Φ pred B st c i x
      = st (tagged c i x)
          (graph (fun j => recSel (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) j)
            (pred (tagged c i x))) := by
  have hpredU := pred_sub_union h hmono hmaps hpf
  refine recSel_eq hB hpredU (tagged_mem_unionSet hc hi hx)
    (unionRec_exists_unique h hmono hmaps hpf hB hst c hc i hi x hx).1 fun j hj => ?_
  obtain ⟨c', hc', i', hi', x', hx', rfl⟩ :=
    mem_unionSet.mp (hpredU _ (tagged_mem_unionSet hc hi hx) j hj)
  exact unionRec_exists_unique h hmono hmaps hpf hB hst c' hc' i' hi' x' hx'

/-! ### The bundled kit -/

/-- **The recursion data of a block, bundled**: the predecessor map,
the bound and the step with their three obligations — what
`unionRec_mem_B`/`unionRec_eq` read (the instances spell `hB`/`hst`
four times each without it). -/
structure UnionRecKit (ℓ w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) where
  pred : V → V
  B : V → V
  st : V → V → V
  predsFrom : PredsFrom w k Is Φ pred
  hB : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → B u ∈ˢ (univ ℓ : V)
  hst : ∀ u, u ∈ˢ unionSet k Is (lfpTuple w k Is Φ) → ∀ g,
    g ∈ˢ piSet (pred u) (fun j => app (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) pred B st) j) →
    st u g ∈ˢ B u

namespace UnionRecKit

variable (K : UnionRecKit ℓ w k Is Φ)

/-- The kit's recursor at class `c`. -/
noncomputable def recAt (c : Nat) (i x : V) : V := unionRec ℓ w k Is Φ K.pred K.B K.st c i x

theorem rec_mem_B (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) {c : Nat} (hc : c < k) {i x : V} (hi : i ∈ˢ Is c)
    (hx : x ∈ˢ app (lfpTuple w k Is Φ c) i) : K.recAt c i x ∈ˢ K.B (tagged c i x) :=
  unionRec_mem_B h hmono hmaps K.predsFrom K.hB K.hst hc hi hx

theorem rec_eq (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) {c : Nat} (hc : c < k) {i x : V} (hi : i ∈ˢ Is c)
    (hx : x ∈ˢ app (lfpTuple w k Is Φ c) i) :
    K.recAt c i x
      = K.st (tagged c i x)
          (graph (fun j => recSel (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) K.pred K.B K.st) j)
            (K.pred (tagged c i x))) :=
  unionRec_eq h hmono hmaps K.predsFrom K.hB K.hst hc hi hx

theorem graph_mem_B (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) {u v : V} (hu : u ∈ˢ unionSet k Is (lfpTuple w k Is Φ))
    (hv : v ∈ˢ app (recGraph ℓ (unionSet k Is (lfpTuple w k Is Φ)) K.pred K.B K.st) u) :
    v ∈ˢ K.B u :=
  unionGraph_mem_B h hmono hmaps K.predsFrom K.hB hu hv

end UnionRecKit

end Rec

/-! ## The recursor over classes with their OWN accessibility (task #315 M7)

A NESTED block's recursion classes are the members' carriers followed
by the PINS' carriers at the least tuple — and a pin's class is not a
component of the tuple lfp, so `unionAcc_all`'s simultaneous induction
does not reach it (`SetModel/NestedTreeList.lean`'s finding).  What the
recursion theorem needs of the classes is only that every element of
their union is ACCESSIBLE along the predecessor map and that the map
stays inside the union: this section states the recursor over an
ARBITRARY tuple of classes `C` under exactly those two obligations
(`unionRecC`, `UnionRecKitC`), and the lfp version above is its instance
(`unionRec_eq_unionRecC`, `UnionRecKit.toC`).  A nested block's class-wise
accessibility is the block model's job (`Model/Inductives/NestedRecCand.lean`). -/

section Classes

variable {ℓ k : Nat} {Is C : Nat → V} {pred : V → V} {B : V → V} {st : V → V → V}

/-- **The recursor over the classes `C`**: the selector of the
recursion graph over their union, at class `c`, index `i`, value `x`. -/
noncomputable def unionRecC (ℓ k : Nat) (Is C : Nat → V) (pred : V → V) (B : V → V)
    (st : V → V → V) (c : Nat) (i x : V) : V :=
  recSel (recGraph ℓ (unionSet k Is C) pred B st) (tagged c i x)

/-- The lfp recursor is the class recursor at the carrier's classes. -/
theorem unionRec_eq_unionRecC {w : Nat} {Φ : (Nat → V) → Nat → V} (c : Nat) (i x : V) :
    unionRec ℓ w k Is Φ pred B st c i x = unionRecC ℓ k Is (lfpTuple w k Is Φ) pred B st c i x :=
  rfl

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
stays inside the union, every element of the union is accessible, the
bound is a set at the level and the step lands in the bound. -/
structure UnionRecKitC (ℓ k : Nat) (Is C : Nat → V) where
  pred : V → V
  B : V → V
  st : V → V → V
  predSub : ∀ u, u ∈ˢ unionSet k Is C → pred u ⊆ˢ unionSet k Is C
  acc : ∀ u, u ∈ˢ unionSet k Is C →
    ∃ y, y ∈ˢ app (accFam (unionSet k Is C) pred (fun _ => True)) u
  hB : ∀ u, u ∈ˢ unionSet k Is C → B u ∈ˢ (univ ℓ : V)
  hst : ∀ u, u ∈ˢ unionSet k Is C → ∀ g,
    g ∈ˢ piSet (pred u) (fun j => app (recGraph ℓ (unionSet k Is C) pred B st) j) →
    st u g ∈ˢ B u

namespace UnionRecKitC

variable (K : UnionRecKitC ℓ k Is C)

/-- The kit's recursor at class `c`. -/
noncomputable def recAt (c : Nat) (i x : V) : V := unionRecC ℓ k Is C K.pred K.B K.st c i x

/-- **The recursion theorem over classes**: the graph has exactly one
value at every union element. -/
theorem exists_unique {u : V} (hu : u ∈ˢ unionSet k Is C) :
    (∃ v, v ∈ˢ app (recGraph ℓ (unionSet k Is C) K.pred K.B K.st) u) ∧
    ∀ v v', v ∈ˢ app (recGraph ℓ (unionSet k Is C) K.pred K.B K.st) u →
      v' ∈ˢ app (recGraph ℓ (unionSet k Is C) K.pred K.B K.st) u → v = v' := by
  obtain ⟨y, hy⟩ := K.acc u hu
  exact recGraph_exists_unique K.hB K.predSub K.hst u hu y hy

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

/-- The lfp kit is a class kit at the carrier's classes: the two
obligations `predSub`/`acc` are `pred_sub_union`/`unionAcc_all_union`. -/
noncomputable def UnionRecKit.toC {w : Nat} {Φ : (Nat → V) → Nat → V}
    (K : UnionRecKit ℓ w k Is Φ) (h : ∃ L, IsClosedTuple w k Is Φ L)
    (hmono : MonoTuple w k Is Φ) (hmaps : MapsTuple w k Is Φ) :
    UnionRecKitC ℓ k Is (lfpTuple w k Is Φ) :=
  ⟨K.pred, K.B, K.st, pred_sub_union h hmono hmaps K.predsFrom,
    unionAcc_all_union h hmono hmaps K.predsFrom (fun _ => True) (fun _ _ => trivial), K.hB, K.hst⟩

theorem UnionRecKit.toC_recAt {w : Nat} {Φ : (Nat → V) → Nat → V}
    (K : UnionRecKit ℓ w k Is Φ) (h : ∃ L, IsClosedTuple w k Is Φ L)
    (hmono : MonoTuple w k Is Φ) (hmaps : MapsTuple w k Is Φ) (c : Nat) (i x : V) :
    (K.toC h hmono hmaps).recAt c i x = K.recAt c i x := rfl

end Classes

end ConLeche.SetTheory
