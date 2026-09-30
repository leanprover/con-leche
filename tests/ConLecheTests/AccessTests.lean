module

public import ConLeche.SetModel.Access

public section

/-!
# (W) from accessibility on examples

`closed_of_acc` (`ConLeche/SetModel/Access.lean`) at `List α`, binary
trees, the reflexive `zero | sup : (Nat → T) → T`, and the nested
`Rose ::= node : List Rose → Rose` WITHOUT a key: Rose's operator reads
its field as List's least tuple at the parameter (`lfpP`), and its (W) is
`closed_of_acc ∘ accRead_comp ∘ lfpP_acc`.
-/

namespace ConLeche.SetTheory.AccessEx


universe u

variable {V : Type u} [SetTheory V]

section Instances

variable {w : Nat}

/-- One-component operators whose single fibre (over `{pt}`) is `F X`. -/
noncomputable def op1 (F : (Nat → V) → V) : (Nat → V) → Nat → V :=
  fun X _ => graph (fun _ => F X) unitSet

/-- The single index set. -/
noncomputable def is1 : Nat → V := fun _ => unitSet

theorem acc_op1 {kI : Nat} {IsI : Nat → V} {F : (Nat → V) → V} {A : V} (h : AccRead w kI IsI F A) :
    AccTuple w kI IsI 1 is1 (op1 F) A := by
  intro X hX m _ i hi x hx
  have hi' : i ∈ˢ (unitSet : V) := hi
  simp only [op1] at hx ⊢
  rw [app_graph hi'] at hx
  obtain ⟨B, g, hB, hg, hs⟩ := h X hX x hx
  exact ⟨B, g, hB, hg, fun X' hX' h' => by rw [app_graph hi']; exact hs X' hX' h'⟩

theorem maps_op1 {kI : Nat} {IsI : Nat → V} {F : (Nat → V) → V}
    (h : ∀ X, InTupleSpace w kI IsI X → F X ∈ˢ (univ w : V)) :
    ∀ X, InTupleSpace w kI IsI X → InTupleSpace w 1 is1 (op1 F X) :=
  fun X hX _ _ => graph_mem_famSpace fun _ _ => h X hX

theorem hole_mem {k : Nat} {Is X : Nat → V} (hX : InTupleSpace w k Is X) {m : Nat} (hm : m < k)
    {i : V} (hi : i ∈ˢ Is m) : app (X m) i ∈ˢ (univ w : V) :=
  famSpace_app (hX m hm) hi

theorem hole1_mem {X : Nat → V} {k : Nat} (hX : InTupleSpace w k is1 X) {m : Nat} (hm : m < k) :
    app (X m) pt ∈ˢ (univ w : V) :=
  hole_mem hX hm pt_mem_unitSet

variable (hw : w ≠ 0)
include hw

theorem pt_mem_univ : (pt : V) ∈ˢ (univ w : V) :=
  (univ_isTGUniverse hw).transitive (unitSet_mem_univ w) pt_mem_unitSet

theorem nilV_mem : (kpair empty empty : V) ∈ˢ (univ w : V) :=
  (univ_isTGUniverse hw).kpair_mem (empty_mem_univ w) (empty_mem_univ w) (empty_mem_univ w)

theorem tag_image_mem {S : V} (hS : S ∈ˢ (univ w : V)) : image (kpair pt) S ∈ˢ (univ w : V) :=
  (univ_isTGUniverse hw).image_mem hS fun _ hx =>
    (univ_isTGUniverse hw).kpair_mem (empty_mem_univ w) (pt_mem_univ hw)
      ((univ_isTGUniverse hw).transitive hS hx)

theorem nil_or_mem {S : V} (hS : S ∈ˢ (univ w : V)) :
    binUnion (sing (kpair empty empty)) (image (kpair pt) S) ∈ˢ (univ w : V) :=
  (univ_isTGUniverse hw).binUnion_mem (empty_mem_univ w)
    ((univ_isTGUniverse hw).sing_mem (empty_mem_univ w) (nilV_mem hw)) (tag_image_mem hw hS)

omit hw in
open Classical in
/-- The two-tag product bound is a set of the level. -/
theorem prodA_mem (hw : w ≠ 0) {A1 A2 : V} (h1 : A1 ∈ˢ (univ w : V)) (h2 : A2 ∈ˢ (univ w : V)) :
    (sigmaPairs (upair empty pt) fun t => if t = empty then A1 else A2) ∈ˢ (univ w : V) := by
  classical
  have hU := univ_isTGUniverse (V := V) hw
  refine hU.sigmaPairs_mem (hU.upair_mem (empty_mem_univ w) (empty_mem_univ w) (pt_mem_univ hw))
    fun t _ => ?_
  by_cases h : t = empty
  · simp only [h, if_true]; exact h1
  · simp only [h, if_false]; exact h2

/-! ### `List α` (flat): `nil | cons : α → List α → List α` -/

/-- `List α`'s fibre. -/
noncomputable def listF (α : V) (X : Nat → V) : V :=
  binUnion (sing (kpair empty empty)) (image (kpair pt) (sigmaPairs α fun _ => app (X 0) pt))

theorem list_closed {α : V} (hα : α ∈ˢ (univ w : V)) :
    ∃ L, IsClosedTuple w 1 is1 (op1 (listF α)) L := by
  refine closed_of_acc hw (A := unitSet) (unitSet_mem_univ w)
    (maps_op1 fun X hX => nil_or_mem hw ((univ_isTGUniverse hw).sigmaPairs_mem hα
      fun _ _ => hole1_mem hX Nat.zero_lt_one)) (acc_op1 ?_)
  exact accRead_binUnion (accRead_const _ _) (accRead_image _ (accRead_sigma fun _ _ =>
    accRead_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet))

/-! ### Binary trees (flat, two recursive fields): `leaf | node : T → T → T` -/

noncomputable def treeF (X : Nat → V) : V :=
  binUnion (sing (kpair empty empty)) (image (kpair pt) (sigmaPairs (app (X 0) pt) fun _ => app (X 0) pt))

theorem tree_closed : ∃ L : Nat → V, IsClosedTuple w 1 is1 (op1 treeF) L := by
  refine closed_of_acc hw (prodA_mem hw (unitSet_mem_univ w) (unitSet_mem_univ w))
    (maps_op1 fun X hX => nil_or_mem hw ((univ_isTGUniverse hw).sigmaPairs_mem
      (hole1_mem hX Nat.zero_lt_one) fun _ _ => hole1_mem hX Nat.zero_lt_one)) (acc_op1 ?_)
  refine accRead_binUnion (accRead_const _ _) (accRead_image _ (accRead_prod ?_ ?_)) <;>
    exact accRead_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet

/-! ### Reflexive (infinitary): `zero | sup : (Nat → T) → T` -/

noncomputable def supF (X : Nat → V) : V :=
  binUnion (sing (kpair empty empty)) (image (kpair pt) (piSet omega fun _ => app (X 0) pt))

theorem sup_closed : ∃ L : Nat → V, IsClosedTuple w 1 is1 (op1 supF) L := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  have hU := univ_isTGUniverse (V := V) hw
  have hω : (omega : V) ∈ˢ (univ (w' + 1) : V) := omega_mem_univ_succ w'
  refine closed_of_acc hw (hU.sigmaPairs_mem hω fun _ _ => unitSet_mem_univ _)
    (maps_op1 fun X hX => nil_or_mem hw (hU.piSet_mem hω fun _ _ => hole1_mem hX Nat.zero_lt_one))
    (acc_op1 ?_)
  exact accRead_binUnion (accRead_const _ _) (accRead_image _ (accRead_pi fun _ _ =>
    accRead_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet))

/-! ### Nested, no keys: `Rose ::= node : List Rose → Rose` -/

/-- `List`'s JOINT operator at the instantiation: component `0` the
parameter (Rose's hole), component `1` List's own hole. -/
noncomputable def listJ : (Nat → V) → Nat → V :=
  op1 fun Z => binUnion (sing (kpair empty empty))
    (image (kpair pt) (sigmaPairs (app (Z 0) pt) fun _ => app (Z 1) pt))

open Classical in
/-- Its support bound. -/
noncomputable def listA : V := sigmaPairs (upair empty pt) fun t => if t = empty then unitSet else unitSet

omit hw in
theorem catT_is1 : catT 1 (is1 : Nat → V) is1 = is1 := by
  funext i; unfold catT is1; split <;> rfl

omit hw in
theorem listJ_acc : AccTuple w (1 + 1) (catT 1 is1 is1) 1 is1 (listJ : (Nat → V) → Nat → V) listA := by
  rw [catT_is1]
  refine acc_op1 (accRead_binUnion (accRead_const _ _) (accRead_image _ (accRead_prod ?_ ?_)))
  · exact accRead_hole (by omega) pt_mem_unitSet pt_mem_unitSet
  · exact accRead_hole (by omega) pt_mem_unitSet pt_mem_unitSet

theorem listJ_maps : ∀ X Y : Nat → V, InTupleSpace w 1 is1 X → InTupleSpace w 1 is1 Y →
    InTupleSpace w 1 is1 (listJ (catT 1 X Y)) := by
  intro X Y hX hY
  have hZ := catT_mem hX hY
  rw [catT_is1] at hZ
  exact maps_op1 (fun Z hZ => nil_or_mem hw ((univ_isTGUniverse hw).sigmaPairs_mem
    (hole1_mem hZ (by omega)) fun _ _ => hole1_mem hZ (by omega))) _ hZ

/-- `Rose`'s operator: the field reads `⟦List⟧(X)` = List's least tuple
at the parameter `X` — the model's own nested reading, no key. -/
noncomputable def roseΦ (w : Nat) : (Nat → V) → Nat → V :=
  op1 fun X => image (kpair pt) (app (lfpP w 1 1 is1 listJ X 0) pt)

theorem rose_closed : ∃ L : Nat → V, IsClosedTuple w 1 is1 (roseΦ w) L := by
  have hU := univ_isTGUniverse (V := V) hw
  have hLA : (listA : V) ∈ˢ (univ w : V) := prodA_mem hw (unitSet_mem_univ w) (unitSet_mem_univ w)
  -- List is accessible in its parameter (the nested case)
  have hP : AccTuple w 1 is1 1 is1 (lfpP w 1 1 is1 (listJ : (Nat → V) → Nat → V)) (accPaths listA) :=
    lfpP_acc hw hLA (listJ_maps hw) listJ_acc
  have hPm : ∀ X : Nat → V, InTupleSpace w 1 is1 X →
      InTupleSpace w 1 is1 (lfpP w 1 1 is1 (listJ : (Nat → V) → Nat → V) X) :=
    fun X _ => lfpTuple_mem _ _ _ _
  refine closed_of_acc hw (A := sigmaPairs unitSet fun _ => accPaths listA)
    (hU.sigmaPairs_mem (unitSet_mem_univ w) fun _ _ => accPaths_mem hw hLA)
    (maps_op1 fun X hX => tag_image_mem hw (hole1_mem (hPm X hX) Nat.zero_lt_one)) (acc_op1 ?_)
  exact accRead_image _ (accRead_comp hP hPm (accRead_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet))

end Instances

end ConLeche.SetTheory.AccessEx
