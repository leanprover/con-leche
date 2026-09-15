module

public import ConLeche.SetTheory.Derive.BekicUnit
@[expose] public section

/-!
# `Tree := node (List Tree)` — the two-component instance of Bekić (task #279)

The smallest genuinely NESTED block, at the set level and with an
ABSTRACT container: `Tree` has one constructor `node : List Tree →
Tree`, and `List` is a datum-shaped container (`nil`, `cons`) over a
parameter.  The aux block the nested route installs has two
components — the Tree component (index `0`) and a COPY of the
container specialised to `Tree` (index `1`) — and its simultaneous
least fixed point `μ` is `lfpFamSet` of

    Φ : X ↦ (0 ↦ TOp (X 1), 1 ↦ LOp (X 0) (X 1)).

The theorem of this file (`treeList_copy_eq_container`) is the copy's
identification: `μ 1` is the CONTAINER's own least fixed point
`lfp (G (μ 0))` — `List` at the parameter value `μ 0` — with no order
among the components and no hypothesis relating the two carriers.  It
is `bekic_component` at `S = {1}`, `C = {0}`, `J = {0}` along the
constant bijection `1 ↦ 0`, whose agreement hypothesis computes to
`LOp (μ 0) (Y 1)` on both sides.

The corollary `treeListMu_tree_eq` then reads the Tree component off
the fixed-point equation: `μ 0 = TOp (⟦List⟧ (μ 0))`, i.e. Tree's
carrier is a fixed point of the COMPOSED operator `X ↦ TOp (lfp (G
X))`.  **Leastness of that composed fixed point is NOT claimed here**
— it is a separate (harder) statement, needing the container's own
induction principle.

Everything is over the bare `SetTheory` interface; no syntax.  The
constructors are abstract injections `mkT`, `mkNil`, `mkCons` into a
bounding set `U ∈ univ w`; their closure hypotheses (`mkT_mem_TOp`,
`mkNil_mem_LOp`, `mkCons_mem_LOp`) are what puts the constructors'
values INTO the operators, and are not needed for the fixed-point
identities, which are bounded by `U` through `sep` alone.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The two datum-shaped operators, the index sets, the functors -/

section Defs

variable (w : Nat) (U : V) (mkT : V → V) (mkNil : V) (mkCons : V → V → V)

/-- **Tree's operator**: one constructor `node`, its one field read at
the (copy of the) container component. -/
noncomputable def TOp (XL : V) : V := sep U fun x => ∃ l, l ∈ˢ XL ∧ x = mkT l

/-- **List's operator**, datum-shaped: `nil`, or `cons` of a parameter
element (`α`) and a recursive element (`Y`). -/
noncomputable def LOp (α Y : V) : V :=
  sep U fun x => x = mkNil ∨ ∃ h t, h ∈ˢ α ∧ t ∈ˢ Y ∧ x = mkCons h t

/-- The copy component's index set: the singleton `{1}` (the `S` of
Bekić). -/
noncomputable def copyIdx : V := upair (vnat 1) (vnat 1)

/-- The Tree component's index set: the singleton `{0}` (the `C` of
Bekić). -/
noncomputable def treeIdx : V := upair (vnat 0) (vnat 0)

/-- The container's own index set: `List` has no indices, so one
tuple. -/
noncomputable def listIdx : V := upair (vnat 0) (vnat 0)

open Classical in
/-- The aux block's simultaneous functor on families over `{1} ∪ {0}`. -/
noncomputable def treeListPhi : V :=
  graph (fun X => graph (fun i =>
        if i = vnat 0 then TOp U mkT (app X (vnat 1))
        else LOp U mkNil mkCons (app X (vnat 0)) (app X (vnat 1)))
      (binUnion copyIdx treeIdx))
    (famSpace w (binUnion (copyIdx : V) treeIdx))

/-- The container's own functor, at a parameter value `α`. -/
noncomputable def listG (α : V) : V :=
  graph (fun Y => graph (fun _ => LOp U mkNil mkCons α (app Y (vnat 0))) listIdx)
    (famSpace w (listIdx : V))

/-- The aux block's simultaneous least fixed point. -/
noncomputable def treeListMu : V :=
  lfpFamSet w (binUnion (copyIdx : V) treeIdx) (treeListPhi w U mkT mkNil mkCons)

/-- The container's own least fixed point, at the Tree carrier. -/
noncomputable def listMu : V :=
  lfpFamSet w (listIdx : V)
    (listG w U mkNil mkCons (app (treeListMu w U mkT mkNil mkCons) (vnat 0)))

end Defs

section Facts

variable {w : Nat} {U : V} {mkT : V → V} {mkNil : V} {mkCons : V → V → V}

/-! ## The operators -/

theorem mem_TOp {XL x : V} :
    x ∈ˢ TOp U mkT XL ↔ x ∈ˢ U ∧ ∃ l, l ∈ˢ XL ∧ x = mkT l := mem_sep

theorem mem_LOp {α Y x : V} :
    x ∈ˢ LOp U mkNil mkCons α Y ↔
      x ∈ˢ U ∧ (x = mkNil ∨ ∃ h t, h ∈ˢ α ∧ t ∈ˢ Y ∧ x = mkCons h t) := mem_sep

theorem TOp_subset_U {XL : V} : TOp U mkT XL ⊆ˢ U := sep_subset

theorem LOp_subset_U {α Y : V} : LOp U mkNil mkCons α Y ⊆ˢ U := sep_subset

theorem TOp_mem_univ (hU : U ∈ˢ (univ w : V)) (XL : V) :
    TOp U mkT XL ∈ˢ (univ w : V) := univ_sep_mem hU

theorem LOp_mem_univ (hU : U ∈ˢ (univ w : V)) (α Y : V) :
    LOp U mkNil mkCons α Y ∈ˢ (univ w : V) := univ_sep_mem hU

theorem TOp_mono {XL XL' : V} (h : XL ⊆ˢ XL') : TOp U mkT XL ⊆ˢ TOp U mkT XL' := by
  intro x hx
  obtain ⟨hxU, l, hl, hx⟩ := mem_TOp.mp hx
  exact mem_TOp.mpr ⟨hxU, l, h l hl, hx⟩

theorem LOp_mono {α α' Y Y' : V} (hα : α ⊆ˢ α') (hY : Y ⊆ˢ Y') :
    LOp U mkNil mkCons α Y ⊆ˢ LOp U mkNil mkCons α' Y' := by
  intro x hx
  obtain ⟨hxU, hx⟩ := mem_LOp.mp hx
  refine mem_LOp.mpr ⟨hxU, ?_⟩
  rcases hx with hx | ⟨h, t, hh, ht, hx⟩
  · exact Or.inl hx
  · exact Or.inr ⟨h, t, hα h hh, hY t ht, hx⟩

/-- The constructors land in the operators — this is where the
closure hypotheses on `U` are used. -/
theorem mkT_mem_TOp (hT : ∀ l, l ∈ˢ U → mkT l ∈ˢ U) {XL l : V} (hXL : XL ⊆ˢ U)
    (hl : l ∈ˢ XL) : mkT l ∈ˢ TOp U mkT XL :=
  mem_TOp.mpr ⟨hT l (hXL l hl), l, hl, rfl⟩

theorem mkNil_mem_LOp (hNil : mkNil ∈ˢ U) (α Y : V) :
    mkNil ∈ˢ LOp U mkNil mkCons α Y :=
  mem_LOp.mpr ⟨hNil, Or.inl rfl⟩

theorem mkCons_mem_LOp (hCons : ∀ h t, h ∈ˢ U → t ∈ˢ U → mkCons h t ∈ˢ U)
    {α Y h t : V} (hα : α ⊆ˢ U) (hY : Y ⊆ˢ U) (hh : h ∈ˢ α) (ht : t ∈ˢ Y) :
    mkCons h t ∈ˢ LOp U mkNil mkCons α Y :=
  mem_LOp.mpr ⟨hCons h t (hα h hh) (hY t ht), Or.inr ⟨h, t, hh, ht, rfl⟩⟩

/-! ## The index sets -/

theorem vnat1_ne_vnat0 : (vnat 1 : V) ≠ vnat 0 := by
  intro h
  exact Nat.one_ne_zero (vnat_inj h)

theorem mem_copyIdx {x : V} : x ∈ˢ (copyIdx : V) ↔ x = vnat 1 := by
  unfold copyIdx
  rw [mem_upair]
  exact ⟨fun h => h.elim id id, Or.inl⟩

theorem mem_treeIdx {x : V} : x ∈ˢ (treeIdx : V) ↔ x = vnat 0 := by
  unfold treeIdx
  rw [mem_upair]
  exact ⟨fun h => h.elim id id, Or.inl⟩

theorem mem_listIdx {x : V} : x ∈ˢ (listIdx : V) ↔ x = vnat 0 := by
  unfold listIdx
  rw [mem_upair]
  exact ⟨fun h => h.elim id id, Or.inl⟩

theorem mem_auxIdx {x : V} :
    x ∈ˢ binUnion (copyIdx : V) treeIdx ↔ x = vnat 1 ∨ x = vnat 0 := by
  rw [mem_binUnion, mem_copyIdx, mem_treeIdx]

theorem vnat1_mem_copyIdx : (vnat 1 : V) ∈ˢ copyIdx := mem_copyIdx.mpr rfl

theorem vnat0_mem_treeIdx : (vnat 0 : V) ∈ˢ treeIdx := mem_treeIdx.mpr rfl

theorem vnat0_mem_listIdx : (vnat 0 : V) ∈ˢ listIdx := mem_listIdx.mpr rfl

theorem vnat0_not_mem_copyIdx : ¬ (vnat 0 : V) ∈ˢ copyIdx :=
  fun h => vnat1_ne_vnat0 (mem_copyIdx.mp h).symm

theorem vnat1_mem_auxIdx : (vnat 1 : V) ∈ˢ binUnion (copyIdx : V) treeIdx :=
  mem_auxIdx.mpr (Or.inl rfl)

theorem vnat0_mem_auxIdx : (vnat 0 : V) ∈ˢ binUnion (copyIdx : V) treeIdx :=
  mem_auxIdx.mpr (Or.inr rfl)

/-! ## The aux functor computes -/

theorem app_treeListPhi_tree {X : V}
    (hX : X ∈ˢ famSpace w (binUnion (copyIdx : V) treeIdx)) :
    app (app (treeListPhi w U mkT mkNil mkCons) X) (vnat 0)
      = TOp U mkT (app X (vnat 1)) := by
  unfold treeListPhi
  rw [app_graph hX, app_graph vnat0_mem_auxIdx]
  exact if_pos rfl

theorem app_treeListPhi_copy {X : V}
    (hX : X ∈ˢ famSpace w (binUnion (copyIdx : V) treeIdx)) :
    app (app (treeListPhi w U mkT mkNil mkCons) X) (vnat 1)
      = LOp U mkNil mkCons (app X (vnat 0)) (app X (vnat 1)) := by
  unfold treeListPhi
  rw [app_graph hX, app_graph vnat1_mem_auxIdx]
  exact if_neg vnat1_ne_vnat0

theorem app_listG {α Y : V} (hY : Y ∈ˢ famSpace w (listIdx : V)) :
    app (app (listG w U mkNil mkCons α) Y) (vnat 0)
      = LOp U mkNil mkCons α (app Y (vnat 0)) := by
  unfold listG
  rw [app_graph hY, app_graph vnat0_mem_listIdx]

/-! ## The two functors are monotone, map the family space, and are closed -/

theorem treeListPhi_mono :
    MonoFam w (binUnion (copyIdx : V) treeIdx) (treeListPhi w U mkT mkNil mkCons) := by
  intro X Y hX hY hle i hi
  rcases mem_auxIdx.mp hi with rfl | rfl
  · rw [app_treeListPhi_copy hX, app_treeListPhi_copy hY]
    exact LOp_mono (hle (vnat 0) vnat0_mem_auxIdx) (hle (vnat 1) vnat1_mem_auxIdx)
  · rw [app_treeListPhi_tree hX, app_treeListPhi_tree hY]
    exact TOp_mono (hle (vnat 1) vnat1_mem_auxIdx)

theorem treeListPhi_maps (hU : U ∈ˢ (univ w : V)) :
    MapsFam w (binUnion (copyIdx : V) treeIdx) (treeListPhi w U mkT mkNil mkCons) := by
  intro X hX
  unfold treeListPhi
  rw [app_graph hX]
  refine graph_mem_famSpace fun i _ => ?_
  split
  · exact TOp_mem_univ hU _
  · exact LOp_mem_univ hU _ _

theorem treeListPhi_closed (hU : U ∈ˢ (univ w : V)) :
    ∃ L, IsClosedFam w (binUnion (copyIdx : V) treeIdx)
      (treeListPhi w U mkT mkNil mkCons) L := by
  have hmem : graph (fun _ => U) (binUnion (copyIdx : V) treeIdx)
      ∈ˢ famSpace w (binUnion (copyIdx : V) treeIdx) :=
    graph_mem_famSpace fun _ _ => hU
  refine ⟨graph (fun _ => U) (binUnion (copyIdx : V) treeIdx), hmem, fun i hi => ?_⟩
  rcases mem_auxIdx.mp hi with rfl | rfl
  · rw [app_treeListPhi_copy hmem, app_graph hi]
    exact LOp_subset_U
  · rw [app_treeListPhi_tree hmem, app_graph hi]
    exact TOp_subset_U

theorem listG_mono (α : V) : MonoFam w (listIdx : V) (listG w U mkNil mkCons α) := by
  intro X Y hX hY hle i hi
  rcases mem_listIdx.mp hi with rfl
  rw [app_listG hX, app_listG hY]
  exact LOp_mono (Subset.refl _) (hle (vnat 0) vnat0_mem_listIdx)

theorem listG_maps (hU : U ∈ˢ (univ w : V)) (α : V) :
    MapsFam w (listIdx : V) (listG w U mkNil mkCons α) := by
  intro X hX
  unfold listG
  rw [app_graph hX]
  exact graph_mem_famSpace fun _ _ => LOp_mem_univ hU _ _

theorem listG_closed (hU : U ∈ˢ (univ w : V)) (α : V) :
    ∃ L, IsClosedFam w (listIdx : V) (listG w U mkNil mkCons α) L := by
  have hmem : graph (fun _ => U) (listIdx : V) ∈ˢ famSpace w (listIdx : V) :=
    graph_mem_famSpace fun _ _ => hU
  refine ⟨graph (fun _ => U) (listIdx : V), hmem, fun i hi => ?_⟩
  rcases mem_listIdx.mp hi with rfl
  rw [app_listG hmem, app_graph hi]
  exact LOp_subset_U

/-! ## The copy is the container -/

/-- **The copy component of the aux block's simultaneous least fixed
point IS the container's own least fixed point**, at the parameter
value the Tree component takes.  `bekic_component` at `S = {1}`,
`C = {0}`, `J = {0}`, along `f = fun _ => 1`, `g = fun _ => 0`. -/
theorem treeList_copy_eq_container (hU : U ∈ˢ (univ w : V)) :
    app (treeListMu w U mkT mkNil mkCons) (vnat 1)
      = app (listMu w U mkT mkNil mkCons) (vnat 0) := by
  unfold listMu treeListMu
  have hμmem : lfpFamSet w (binUnion (copyIdx : V) treeIdx) (treeListPhi w U mkT mkNil mkCons)
      ∈ˢ famSpace w (binUnion (copyIdx : V) treeIdx) := lfpFamSet_mem _ _ _
  have hCsub : (treeIdx : V) ⊆ˢ binUnion (copyIdx : V) treeIdx :=
    fun i hi => mem_binUnion.mpr (Or.inr hi)
  have hf : ∀ i, i ∈ˢ (listIdx : V) → (vnat 1 : V) ∈ˢ copyIdx :=
    fun _ _ => vnat1_mem_copyIdx
  refine bekic_component (treeListPhi_mono) (treeListPhi_maps hU) (treeListPhi_closed hU)
    (listG_mono _) (listG_maps hU _) (listG_closed hU _)
    (fun _ => vnat 1) (fun _ => vnat 0) hf (fun _ _ => vnat0_mem_listIdx)
    (fun i hi => (mem_listIdx.mp hi).symm) (fun s hs => (mem_copyIdx.mp hs).symm)
    ?_ (vnat 0) vnat0_mem_listIdx
  intro Y hY i hi
  rcases mem_listIdx.mp hi with rfl
  have hjoin : famJoin (copyIdx : V) treeIdx Y
      (famRestr (lfpFamSet w (binUnion (copyIdx : V) treeIdx)
        (treeListPhi w U mkT mkNil mkCons)) treeIdx)
      ∈ˢ famSpace w (binUnion (copyIdx : V) treeIdx) :=
    famJoin_mem hY (famRestr_mem hμmem hCsub)
  rw [app_treeListPhi_copy hjoin, app_listG (famPull_mem hY hf), app_famPull hi,
    app_famJoin_left vnat1_mem_copyIdx,
    app_famJoin_right vnat0_mem_treeIdx vnat0_not_mem_copyIdx,
    app_famRestr vnat0_mem_treeIdx]

/-- The Tree component's own equation: `μ 0 = TOp (μ 1)`. -/
theorem treeListMu_tree_eq (hU : U ∈ˢ (univ w : V)) :
    app (treeListMu w U mkT mkNil mkCons) (vnat 0)
      = TOp U mkT (app (treeListMu w U mkT mkNil mkCons) (vnat 1)) := by
  have hfix : app (treeListPhi w U mkT mkNil mkCons)
      (lfpFamSet w (binUnion (copyIdx : V) treeIdx) (treeListPhi w U mkT mkNil mkCons))
      = lfpFamSet w (binUnion (copyIdx : V) treeIdx) (treeListPhi w U mkT mkNil mkCons) :=
    lfpFamSet_eq (treeListPhi_closed hU) treeListPhi_mono (treeListPhi_maps hU)
  have h := app_treeListPhi_tree (w := w) (U := U) (mkT := mkT) (mkNil := mkNil)
    (mkCons := mkCons) (lfpFamSet_mem w (binUnion (copyIdx : V) treeIdx)
      (treeListPhi w U mkT mkNil mkCons))
  rw [hfix] at h
  unfold treeListMu
  exact h

/-- **Tree's carrier is a fixed point of the COMPOSED operator**
`X ↦ TOp (⟦List⟧ X)`: the Tree component of the aux block's
simultaneous fixed point is `TOp` of the container's own least fixed
point at that very carrier.  Leastness of this composed fixed point is
NOT claimed (see the module docstring). -/
theorem treeListMu_tree_eq_container (hU : U ∈ˢ (univ w : V)) :
    app (treeListMu w U mkT mkNil mkCons) (vnat 0)
      = TOp U mkT (app (listMu w U mkT mkNil mkCons) (vnat 0)) := by
  rw [treeListMu_tree_eq hU, treeList_copy_eq_container hU]

end Facts

end ConLeche.SetTheory
