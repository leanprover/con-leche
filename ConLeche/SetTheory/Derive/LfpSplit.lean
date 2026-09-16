module

public import ConLeche.SetTheory.Derive.LfpTuple
@[expose] public section

/-!
# The split/join theorem: a tuple lfp is the split of a union lfp (task #315, M4)

The uniform block model records a block as the least pre-fixed TUPLE of an
operator on tuples of families (`lfpTuple`).  The checker's term
language has ONE fixpoint primitive, a least pre-fixed FAMILY over a
single index set (`lfpFam`), so a block's members are spelled at the
term level as fibres of one family over the disjoint union of the
members' index tuples (`Semantics/Tower/MutualLeafI.lean`: the tagged
sum).  This module is the bridge, over the bare `SetTheory` interface:

* an **encoding** `IdxEnc k Is U e` of the members' index sets into
  one index set `U` (`e m i ∈ U`, every element of `U` is some
  `e m i`, `e` injective) — the tagged tuple is the instance, the
  union of `TupleContainer.lean` another;
* the **split** of a family over `U` into a tuple (`splitE`), the
  **join** of a tuple into a family over `U` (`joinE`), and the tuple
  operator a family functor `F` over `U` induces (`splitFun` =
  split ∘ F ∘ join);
* **the theorem** (`lfpTuple_splitFun`): the least pre-fixed tuple of
  `splitFun F` is the split of the least pre-fixed family of `F`, and
  `splitFun F` is a monotone, space-preserving tuple functor with a
  closed tuple whenever `F` is a monotone, space-preserving family
  functor with a closed family.

The union is a device of the TERM-LEVEL spelling and of this proof: it
is neither a carrier nor an index set of the block model (DESIGN §U.6 (e)).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The encoding -/

/-- **An encoding of `k` index sets into one**: `e m i` is `U`'s
element for member `m`'s index `i`; every element of `U` is one, and
distinct `(m, i)` encode distinctly. -/
structure IdxEnc (k : Nat) (Is : Nat → V) (U : V) (e : Nat → V → V) : Prop where
  mem : ∀ m, m < k → ∀ i, i ∈ˢ Is m → e m i ∈ˢ U
  surj : ∀ u, u ∈ˢ U → ∃ m, m < k ∧ ∃ i, i ∈ˢ Is m ∧ u = e m i
  inj : ∀ m m', m < k → m' < k → ∀ i i', i ∈ˢ Is m → i' ∈ˢ Is m' →
    e m i = e m' i' → m = m' ∧ i = i'

/-! ## Split and join -/

/-- A family over `U`, read as a tuple of families over the members'
index sets. -/
noncomputable def splitE (Is : Nat → V) (e : Nat → V → V) (Y : V) : Nat → V :=
  fun m => graph (fun i => app Y (e m i)) (Is m)

/-- The decoding an element of the range of `e` admits (a pair, so
that rewriting one component leaves the other's type alone). -/
noncomputable def decodeE {k : Nat} {Is : Nat → V} {e : Nat → V → V} {u : V}
    (h : ∃ m, m < k ∧ ∃ i, i ∈ˢ Is m ∧ u = e m i) : Nat × V :=
  (Classical.choose h, Classical.choose (Classical.choose_spec h).2)

theorem decodeE_spec {k : Nat} {Is : Nat → V} {e : Nat → V → V} {u : V}
    (h : ∃ m, m < k ∧ ∃ i, i ∈ˢ Is m ∧ u = e m i) :
    (decodeE h).1 < k ∧ (decodeE h).2 ∈ˢ Is (decodeE h).1 ∧ u = e (decodeE h).1 (decodeE h).2 :=
  ⟨(Classical.choose_spec h).1, Classical.choose_spec (Classical.choose_spec h).2⟩

open Classical in
/-- A tuple of families, read as one family over `U`: at `u = e m i`
the tuple's component `m` at `i` (the member and index recovered by
`decodeE`; `empty` off the encoding's range, which `U` never is). -/
noncomputable def joinE (k : Nat) (Is : Nat → V) (U : V) (e : Nat → V → V) (X : Nat → V) : V :=
  graph (fun u =>
    if h : ∃ m, m < k ∧ ∃ i, i ∈ˢ Is m ∧ u = e m i then app (X (decodeE h).1) (decodeE h).2
    else empty) U

/-- **The tuple operator a family functor over the union induces**:
split ∘ `F` ∘ join. -/
noncomputable def splitFun (k : Nat) (Is : Nat → V) (U : V) (e : Nat → V → V) (F : V) :
    (Nat → V) → Nat → V :=
  fun X => splitE Is e (app F (joinE k Is U e X))

section Laws

variable {k : Nat} {Is : Nat → V} {U : V} {e : Nat → V → V}

theorem app_splitE {Y : V} {m : Nat} {i : V} (hi : i ∈ˢ Is m) :
    app (splitE Is e Y m) i = app Y (e m i) :=
  app_graph hi

theorem splitE_mem {w : Nat} (henc : IdxEnc k Is U e) {Y : V} (hY : Y ∈ˢ famSpace w U) :
    InTupleSpace w k Is (splitE Is e Y) := fun m hm =>
  graph_mem_famSpace fun i hi => famSpace_app hY (henc.mem m hm i hi)

/-- The join, read at an encoded index. -/
theorem app_joinE (henc : IdxEnc k Is U e) {X : Nat → V} {m : Nat} (hm : m < k) {i : V}
    (hi : i ∈ˢ Is m) : app (joinE k Is U e X) (e m i) = app (X m) i := by
  unfold joinE
  rw [app_graph (henc.mem m hm i hi)]
  have h : ∃ m', m' < k ∧ ∃ i', i' ∈ˢ Is m' ∧ e m i = e m' i' := ⟨m, hm, i, hi, rfl⟩
  rw [dif_pos h]
  obtain ⟨hm', hi', heq⟩ := decodeE_spec h
  obtain ⟨h1, h2⟩ := henc.inj m _ hm hm' i _ hi hi' heq
  rw [← h1, ← h2]

theorem joinE_mem {w : Nat} (henc : IdxEnc k Is U e) {X : Nat → V} (hX : InTupleSpace w k Is X) :
    joinE k Is U e X ∈ˢ famSpace w U := by
  refine graph_mem_famSpace fun u hu => ?_
  obtain ⟨m, hm, i, hi, rfl⟩ := henc.surj u hu
  have h : ∃ m', m' < k ∧ ∃ i', i' ∈ˢ Is m' ∧ e m i = e m' i' := ⟨m, hm, i, hi, rfl⟩
  rw [dif_pos h]
  obtain ⟨hm', hi', heq⟩ := decodeE_spec h
  obtain ⟨h1, h2⟩ := henc.inj m _ hm hm' i _ hi hi' heq
  rw [← h1, ← h2]
  exact famSpace_app (hX m hm) hi

/-- The induced operator, read fibrewise. -/
theorem app_splitFun {F : V} {X : Nat → V} {m : Nat} {i : V} (hi : i ∈ˢ Is m) :
    app (splitFun k Is U e F X m) i = app (app F (joinE k Is U e X)) (e m i) :=
  app_graph hi

end Laws

/-! ## Split and join are mutually inverse, and monotone -/

section Theorem

variable {k : Nat} {Is : Nat → V} {U : V} {e : Nat → V → V} {w : Nat} {F : V}

/-- **Join after split is the identity** on the family space: a family
over the union is its tuple of fibres, rejoined. -/
theorem joinE_splitE (henc : IdxEnc k Is U e) {Y : V} (hY : Y ∈ˢ famSpace w U) :
    joinE k Is U e (splitE Is e Y) = Y := by
  refine famSpace_ext (joinE_mem henc (splitE_mem henc hY)) hY fun u hu => ?_
  obtain ⟨m, hm, i, hi, rfl⟩ := henc.surj u hu
  rw [app_joinE henc hm hi, app_splitE hi]

/-- **Split after join is the identity** on the tuple space (on the
block's positions; positions `≥ k` are junk on both sides). -/
theorem splitE_joinE (henc : IdxEnc k Is U e) {X : Nat → V} (hX : InTupleSpace w k Is X) :
    ∀ m, m < k → splitE Is e (joinE k Is U e X) m = X m := by
  intro m hm
  refine famSpace_ext (splitE_mem henc (joinE_mem henc hX) m hm) (hX m hm) fun i hi => ?_
  rw [app_splitE hi, app_joinE henc hm hi]

/-- **The split is monotone**: fibrewise it is a reindexing. -/
theorem splitE_le (henc : IdxEnc k Is U e) {Y Y' : V} (h : FamLe U Y Y') :
    TupleLe k Is (splitE Is e Y) (splitE Is e Y') := by
  intro m hm i hi
  rw [app_splitE hi, app_splitE hi]
  exact h _ (henc.mem m hm i hi)

/-- **The join is monotone**: at an encoded index it is the component. -/
theorem joinE_le (henc : IdxEnc k Is U e) {X X' : Nat → V} (h : TupleLe k Is X X') :
    FamLe U (joinE k Is U e X) (joinE k Is U e X') := by
  intro u hu
  obtain ⟨m, hm, i, hi, rfl⟩ := henc.surj u hu
  rw [app_joinE henc hm hi, app_joinE henc hm hi]
  exact h m hm i hi

/-! ## The induced tuple functor -/

/-- **The induced operator is monotone** when the family functor is. -/
theorem splitFun_mono (henc : IdxEnc k Is U e) (hmono : MonoFam w U F) :
    MonoTuple w k Is (splitFun k Is U e F) := by
  intro X Y hX hY hle
  exact splitE_le henc (hmono _ _ (joinE_mem henc hX) (joinE_mem henc hY) (joinE_le henc hle))

/-- **The induced operator preserves the tuple space** when the family
functor preserves the family space. -/
theorem splitFun_maps (henc : IdxEnc k Is U e) (hmaps : MapsFam w U F) :
    MapsTuple w k Is (splitFun k Is U e F) := fun _X hX =>
  splitE_mem henc (hmaps _ (joinE_mem henc hX))

/-- The split of an `F`-closed family is a closed tuple for the
induced operator. -/
theorem splitE_closedTuple (henc : IdxEnc k Is U e) {L : V} (hL : IsClosedFam w U F L) :
    IsClosedTuple w k Is (splitFun k Is U e F) (splitE Is e L) := by
  refine ⟨splitE_mem henc hL.1, ?_⟩
  show TupleLe k Is (splitE Is e (app F (joinE k Is U e (splitE Is e L)))) (splitE Is e L)
  rw [joinE_splitE henc hL.1]
  exact splitE_le henc hL.2

/-- **The induced operator has a closed tuple** when the family functor
has a closed family. -/
theorem splitFun_closed_exists (henc : IdxEnc k Is U e) (hcl : ∃ L, IsClosedFam w U F L) :
    ∃ L, IsClosedTuple w k Is (splitFun k Is U e F) L :=
  ⟨_, splitE_closedTuple henc (Classical.choose_spec hcl)⟩

/-- The join of a closed tuple for the induced operator is an
`F`-closed family. -/
theorem joinE_closedFam (henc : IdxEnc k Is U e) (hmaps : MapsFam w U F) {X : Nat → V}
    (hX : IsClosedTuple w k Is (splitFun k Is U e F) X) :
    IsClosedFam w U F (joinE k Is U e X) := by
  have h1 : joinE k Is U e (splitFun k Is U e F X) = app F (joinE k Is U e X) :=
    joinE_splitE henc (hmaps _ (joinE_mem henc hX.1))
  refine ⟨joinE_mem henc hX.1, ?_⟩
  rw [← h1]
  exact joinE_le henc hX.2

/-! ## The theorem -/

/-- **The split/join theorem**: the least pre-fixed TUPLE of the
operator a family functor over the union induces is the split of that
functor's least pre-fixed FAMILY.  The tagged union is thus only a
spelling device: a block's members are the fibres of one fixpoint. -/
theorem lfpTuple_splitFun (henc : IdxEnc k Is U e) (hmono : MonoFam w U F)
    (hmaps : MapsFam w U F) (hcl : ∃ L, IsClosedFam w U F L) :
    ∀ m, m < k → lfpTuple w k Is (splitFun k Is U e F) m = splitE Is e (lfpFamSet w U F) m := by
  have hTcl : IsClosedTuple w k Is (splitFun k Is U e F) (splitE Is e (lfpFamSet w U F)) :=
    splitE_closedTuple henc ⟨lfpFamSet_mem w U F, lfpFamSet_closed hcl hmono⟩
  have hXcl : IsClosedTuple w k Is (splitFun k Is U e F) (lfpTuple w k Is (splitFun k Is U e F)) :=
    lfpTuple_isClosed ⟨_, hTcl⟩ (splitFun_mono henc hmono)
  have hle1 := lfpTuple_le hTcl
  have hle2 : TupleLe k Is (splitE Is e (lfpFamSet w U F))
      (splitE Is e (joinE k Is U e (lfpTuple w k Is (splitFun k Is U e F)))) :=
    splitE_le henc (lfpFamSet_le (joinE_closedFam henc hmaps hXcl))
  intro m hm
  have hle2m := hle2 m hm
  rw [splitE_joinE henc (lfpTuple_mem w k Is (splitFun k Is U e F)) m hm] at hle2m
  exact famSpace_ext (lfpTuple_mem w k Is (splitFun k Is U e F) m hm)
    (splitE_mem henc (lfpFamSet_mem w U F) m hm)
    fun i hi => Subset.antisymm (hle1 m hm i hi) (hle2m i hi)

/-- **The theorem, fibrewise**: member `m`'s carrier at index `i` is
the union fixpoint's fibre at the encoded index `e m i`. -/
theorem app_lfpTuple_splitFun (henc : IdxEnc k Is U e) (hmono : MonoFam w U F)
    (hmaps : MapsFam w U F) (hcl : ∃ L, IsClosedFam w U F L) {m : Nat} (hm : m < k) {i : V}
    (hi : i ∈ˢ Is m) :
    app (lfpTuple w k Is (splitFun k Is U e F) m) i = app (lfpFamSet w U F) (e m i) := by
  rw [lfpTuple_splitFun henc hmono hmaps hcl m hm, app_splitE hi]

end Theorem

end ConLeche.SetTheory
