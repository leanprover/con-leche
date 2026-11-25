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

theorem hasImage_kpair_pt (S : V) : HasImage (kpair pt) S :=
  hasImage_of_defFun1 (DefFun.kpair_apply DefFun.pt (DefFun.proj 0)) S

open Classical in
theorem hasSigmaPairs_ite (A1 A2 : V) :
    HasSigmaPairs (upair empty pt) fun t => if t = empty then A1 else A2 :=
  hasSigmaPairs_of_defFun1
    (DefFun.ite (DefRel.eq_apply (DefFun.proj 0) DefFun.empty)
      (DefFun.const A1) (DefFun.const A2))

/-- One-component operators whose single fibre (over `{pt}`) is `F X`. -/
noncomputable def op1 (F : (Nat → V) → V) : (Nat → V) → Nat → V :=
  fun X _ => famOf (fun _ => F X) unitSet (hasGraph_const _ _)

/-- The single index set. -/
noncomputable def is1 : Nat → V := fun _ => unitSet

theorem defTupleOp_op1 {k : Nat} {F : (Nat → V) → V}
    (hExt : ∀ X Y, (∀ m, m < k → X m = Y m) → F X = F Y)
    (hDef : DefFun k fun xs => F (padTuple xs)) :
    DefTupleOp k (op1 F) :=
  ⟨fun X Y hXY _ _ => famOf_congr _ _ fun _ _ => hExt X Y hXY,
    fun _ _ => DefFun.famOf_apply_curry hDef.weaken DefFun.unitSet⟩

theorem acc_op1 {kI : Nat} {IsI : Nat → V} {F : (Nat → V) → V} {A : V} (h : AccRead w kI IsI F A) :
    AccTuple w kI IsI 1 is1 (op1 F) A := by
  intro X hX m _ i hi x hx
  have hi' : i ∈ˢ (unitSet : V) := hi
  simp only [op1] at hx ⊢
  rw [app_famOf hi'] at hx
  obtain ⟨B, g, hB, hg, hs⟩ := h X hX x hx
  exact ⟨B, g, hB, hg, fun X' hX' h' => by rw [app_famOf hi']; exact hs X' hX' h'⟩

theorem maps_op1 {kI : Nat} {IsI : Nat → V} {F : (Nat → V) → V}
    (h : ∀ X, InTupleSpace w kI IsI X → F X ∈ˢ (strictU w : V)) :
    ∀ X, InTupleSpace w kI IsI X → InTupleSpace w 1 is1 (op1 F X) :=
  fun X hX _ _ => famOf_mem_famSpace fun _ _ => h X hX

theorem hole_mem {k : Nat} {Is X : Nat → V} (hX : InTupleSpace w k Is X) {m : Nat} (hm : m < k)
    {i : V} (hi : i ∈ˢ Is m) : app (X m) i ∈ˢ (tg w : V) :=
  mem_tg_of_mem_strictU (famSpace_app (hX m hm) hi)

theorem hole1_mem {X : Nat → V} {k : Nat} (hX : InTupleSpace w k is1 X) {m : Nat} (hm : m < k) :
    app (X m) pt ∈ˢ (tg w : V) :=
  hole_mem hX hm pt_mem_unitSet

variable (hw : w ≠ 0)
include hw

theorem pt_mem_tg : (pt : V) ∈ˢ (tg w : V) :=
  (tg_isGrothendieck hw).transitive (unitSet_mem_tg w) pt_mem_unitSet

theorem nilV_mem : (kpair empty empty : V) ∈ˢ (tg w : V) :=
  (tg_isGrothendieck hw).kpair_mem (empty_mem_tg w) (empty_mem_tg w)

theorem tag_image_mem {S : V} (hS : S ∈ˢ (tg w : V)) :
    image (kpair pt) S (hasImage_kpair_pt S) ∈ˢ (tg w : V) :=
  (tg_isGrothendieck hw).image_mem_of_def hS
    (fun _ hx => (tg_isGrothendieck hw).kpair_mem (pt_mem_tg hw)
      ((tg_isGrothendieck hw).transitive hS hx))
    (hasImage_kpair_pt S)
    (DefFunOn.of_defFun1 (DefFun.kpair_apply DefFun.pt (DefFun.proj 0)))

/-- A tagged image is strict: its members are pairs. -/
theorem tag_image_mem_strictU {S : V} (hS : S ∈ˢ (tg w : V)) :
    image (kpair pt) S (hasImage_kpair_pt S) ∈ˢ (strictU w : V) :=
  (mem_strictU_pos hw).mpr ⟨tag_image_mem hw hS, strict_of_kpairs fun z hz => by
    obtain ⟨x, -, rfl⟩ := mem_image.mp hz
    exact ⟨pt, x, rfl⟩⟩

theorem nil_or_mem {S : V} (hS : S ∈ˢ (tg w : V)) :
    binUnion (sing (kpair empty empty)) (image (kpair pt) S (hasImage_kpair_pt S)) ∈ˢ
      (strictU w : V) :=
  (mem_strictU_pos hw).mpr ⟨(tg_isGrothendieck hw).binUnion_mem
    ((tg_isGrothendieck hw).sing_mem (nilV_mem hw)) (tag_image_mem hw hS),
    strict_of_kpairs fun z hz => by
      rcases mem_binUnion.mp hz with h | h
      · exact ⟨empty, empty, mem_sing.mp h⟩
      · obtain ⟨x, -, rfl⟩ := mem_image.mp h
        exact ⟨pt, x, rfl⟩⟩

omit hw in
open Classical in
/-- The two-tag product bound is a set of the level. -/
theorem prodA_mem (hw : w ≠ 0) {A1 A2 : V} (h1 : A1 ∈ˢ (tg w : V)) (h2 : A2 ∈ˢ (tg w : V)) :
    sigmaPairs (upair empty pt) (fun t => if t = empty then A1 else A2)
      (hasSigmaPairs_ite A1 A2) ∈ˢ (tg w : V) := by
  have hU := tg_isGrothendieck (V := V) hw
  refine hU.sigmaPairs_mem (hU.upair_mem (empty_mem_tg w) (pt_mem_tg hw))
    (fun t _ => ?_) (hasSigmaPairs_ite A1 A2)
  by_cases h : t = empty
  · simp only [h, ite_true]; exact h1
  · simp only [h, ite_false]; exact h2

/-! ### `List α` (flat): `nil | cons : α → List α → List α` -/

/-- `List α`'s fibre. -/
noncomputable def listF (α : V) (X : Nat → V) : V :=
  binUnion (sing (kpair empty empty))
    (image (kpair pt) (sigmaPairs α (fun _ => app (X 0) pt) (hasSigmaPairs_const _ _))
      (hasImage_kpair_pt _))

theorem list_closed {α : V} (hα : α ∈ˢ (tg w : V)) :
    ∃ L, IsClosedTuple w 1 is1 (op1 (listF α)) L := by
  have hdef : DefTupleOp 1 (op1 (listF α)) := defTupleOp_op1
    (fun X Y hXY => by
      simp only [listF]
      rw [image_ext (sigmaPairs_congr _ _ fun _ _ => by rw [hXY 0 Nat.zero_lt_one]) _ _
        (fun _ _ => rfl)])
    ((DefFun.binUnion_apply (DefFun.sing_apply (DefFun.kpair_apply DefFun.empty DefFun.empty))
      (DefFun.image_apply_curry (F := fun x _ => kpair pt x)
        (h := fun _ => hasImage_kpair_pt _)
        (DefFun.kpair_apply DefFun.pt (DefFun.proj 0))
        (DefFun.sigmaPairs_apply_curry (B := fun _ (xs : Fin 1 → V) => app (xs 0) pt)
          (h := fun _ => hasSigmaPairs_const _ _)
          (DefFun.const α)
          (DefFun.app_apply (DefFun.proj 0) DefFun.pt).weaken))).congr
      fun xs => by
        simp only [listF, padTuple_lt _ Nat.zero_lt_one]
        exact congrArg (binUnion (sing (kpair empty empty)))
          (image_ext (sigmaPairs_congr _ _ fun _ _ => rfl) _ _ fun _ _ => rfl))
  refine closed_of_acc hw (A := unitSet) (unitSet_mem_tg w) hdef
    (maps_op1 fun X hX => nil_or_mem hw ((tg_isGrothendieck hw).sigmaPairs_mem hα
      (fun _ _ => hole1_mem hX Nat.zero_lt_one) (hasSigmaPairs_const _ _)))
    (acc_op1 ?_)
  exact accRead_binUnion (accRead_const _ _)
    (accRead_image (kpair pt) (hImg := fun _ => hasImage_kpair_pt _)
      (accRead_sigma (C := α) (A := unitSet) (G := fun _ X => app (X 0) pt)
        (hS := fun _ => hasSigmaPairs_const _ _) fun _ _ =>
        accRead_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet))

/-! ### Binary trees (flat, two recursive fields): `leaf | node : T → T → T` -/

noncomputable def treeF (X : Nat → V) : V :=
  binUnion (sing (kpair empty empty))
    (image (kpair pt) (sigmaPairs (app (X 0) pt) (fun _ => app (X 0) pt)
      (hasSigmaPairs_const _ _)) (hasImage_kpair_pt _))

theorem tree_closed : ∃ L : Nat → V, IsClosedTuple w 1 is1 (op1 treeF) L := by
  have hdef : DefTupleOp 1 (op1 treeF) := defTupleOp_op1
    (fun X Y hXY => by
      simp only [treeF]
      rw [image_ext (sigmaPairs_ext (by rw [hXY 0 Nat.zero_lt_one]) _ _ fun _ _ => by
        rw [hXY 0 Nat.zero_lt_one]) _ _ (fun _ _ => rfl)])
    ((DefFun.binUnion_apply (DefFun.sing_apply (DefFun.kpair_apply DefFun.empty DefFun.empty))
      (DefFun.image_apply_curry (F := fun x _ => kpair pt x)
        (h := fun _ => hasImage_kpair_pt _)
        (DefFun.kpair_apply DefFun.pt (DefFun.proj 0))
        (DefFun.sigmaPairs_apply_curry (B := fun _ (xs : Fin 1 → V) => app (xs 0) pt)
          (h := fun _ => hasSigmaPairs_const _ _)
          (DefFun.app_apply (DefFun.proj 0) DefFun.pt)
          (DefFun.app_apply (DefFun.proj 0) DefFun.pt).weaken))).congr
      fun xs => by
        simp only [treeF, padTuple_lt _ Nat.zero_lt_one]
        exact congrArg (binUnion (sing (kpair empty empty)))
          (image_ext (sigmaPairs_ext rfl _ _ fun _ _ => rfl) _ _ fun _ _ => rfl))
  refine closed_of_acc hw (prodA_mem hw (unitSet_mem_tg w) (unitSet_mem_tg w)) hdef
    (maps_op1 fun X hX => nil_or_mem hw ((tg_isGrothendieck hw).sigmaPairs_mem
      (hole1_mem hX Nat.zero_lt_one) (fun _ _ => hole1_mem hX Nat.zero_lt_one)
      (hasSigmaPairs_const _ _))) (acc_op1 ?_)
  refine accRead_binUnion (accRead_const _ _)
    (accRead_image (kpair pt) (hImg := fun _ => hasImage_kpair_pt _) (accRead_prod ?_ ?_)) <;>
    exact accRead_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet

/-! ### Reflexive (infinitary): `zero | sup : (Nat → T) → T` -/

noncomputable def supF (X : Nat → V) : V :=
  binUnion (sing (kpair empty empty))
    (image (kpair pt) (piSet omega (fun _ => app (X 0) pt) (hasSigmaPairs_const _ _))
      (hasImage_kpair_pt _))

theorem sup_closed : ∃ L : Nat → V, IsClosedTuple w 1 is1 (op1 supF) L := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  have hU := tg_isGrothendieck (V := V) hw
  have hω : (omega : V) ∈ˢ (tg (w' + 1) : V) := omega_mem_tg_succ w'
  have hdef : DefTupleOp 1 (op1 supF) := defTupleOp_op1
    (fun X Y hXY => by
      simp only [supF]
      rw [image_ext (piSet_congr _ _ fun _ _ => by rw [hXY 0 Nat.zero_lt_one]) _ _
        (fun _ _ => rfl)])
    ((DefFun.binUnion_apply (DefFun.sing_apply (DefFun.kpair_apply DefFun.empty DefFun.empty))
      (DefFun.image_apply_curry (F := fun x _ => kpair pt x)
        (h := fun _ => hasImage_kpair_pt _)
        (DefFun.kpair_apply DefFun.pt (DefFun.proj 0))
        (DefFun.piSet_apply_curry (B := fun _ (xs : Fin 1 → V) => app (xs 0) pt)
          (h := fun _ => hasSigmaPairs_const _ _)
          DefFun.omega_const
          (DefFun.app_apply (DefFun.proj 0) DefFun.pt).weaken))).congr
      fun xs => by
        simp only [supF, padTuple_lt _ Nat.zero_lt_one]
        exact congrArg (binUnion (sing (kpair empty empty)))
          (image_ext (piSet_congr _ _ fun _ _ => rfl) _ _ fun _ _ => rfl))
  refine closed_of_acc hw (hU.sigmaPairs_mem hω (fun _ _ => unitSet_mem_tg _) (hasSigmaPairs_const _ _))
    hdef
    (maps_op1 fun X hX => nil_or_mem hw (hU.piSet_mem hω (fun _ _ => hole1_mem hX Nat.zero_lt_one)
      (hasSigmaPairs_const _ _)))
    (acc_op1 ?_)
  exact accRead_binUnion (accRead_const _ _)
    (accRead_image (kpair pt) (hImg := fun _ => hasImage_kpair_pt _)
      (accRead_pi (D := omega) (A := unitSet) (G := fun _ X => app (X 0) pt)
        (hS := fun _ => hasSigmaPairs_const _ _)
        (fun _ _ X Y hXY => by rw [hXY 0 Nat.zero_lt_one])
        ((DefFun.app_apply (DefFun.proj 0) DefFun.pt).weaken.congr fun v => by
          simp only [padTuple_lt _ Nat.zero_lt_one]; rfl)
        (fun _ _ => accRead_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet)))

/-! ### Nested, no keys: `Rose ::= node : List Rose → Rose` -/

/-- `List`'s JOINT operator at the instantiation: component `0` the
parameter (Rose's hole), component `1` List's own hole. -/
noncomputable def listJ : (Nat → V) → Nat → V :=
  op1 fun Z => binUnion (sing (kpair empty empty))
    (image (kpair pt)
      (sigmaPairs (app (Z 0) pt) (fun _ => app (Z 1) pt) (hasSigmaPairs_const _ _))
      (hasImage_kpair_pt _))

omit hw in
theorem listJ_def : DefTupleOp (1 + 1) (listJ : (Nat → V) → Nat → V) :=
  defTupleOp_op1
    (fun X Y hXY => by
      rw [image_ext (sigmaPairs_ext (by rw [hXY 0 (by omega)]) _ _ fun _ _ => by
        rw [hXY 1 (by omega)]) _ _ (fun _ _ => rfl)])
    ((DefFun.binUnion_apply (DefFun.sing_apply (DefFun.kpair_apply DefFun.empty DefFun.empty))
      (DefFun.image_apply_curry (F := fun x _ => kpair pt x)
        (h := fun _ => hasImage_kpair_pt _)
        (DefFun.kpair_apply DefFun.pt (DefFun.proj 0))
        (DefFun.sigmaPairs_apply_curry (B := fun _ (xs : Fin (1 + 1) → V) => app (xs 1) pt)
          (h := fun _ => hasSigmaPairs_const _ _)
          (DefFun.app_apply (DefFun.proj 0) DefFun.pt)
          (DefFun.app_apply (DefFun.proj 1) DefFun.pt).weaken))).congr
      fun xs => by
        simp only [padTuple_lt _ (by omega : 0 < 1 + 1), padTuple_lt _ (by omega : 1 < 1 + 1)]
        exact congrArg (binUnion (sing (kpair empty empty)))
          (image_ext (sigmaPairs_ext rfl _ _ fun _ _ => rfl) _ _ fun _ _ => rfl))

open Classical in
/-- Its support bound. -/
noncomputable def listA : V :=
  sigmaPairs (upair empty pt) (fun t => if t = empty then unitSet else unitSet)
    (hasSigmaPairs_ite unitSet unitSet)

omit hw in
theorem catT_is1 : catT 1 (is1 : Nat → V) is1 = is1 := by
  funext i; unfold catT is1; split <;> rfl

omit hw in
open Classical in
theorem listJ_acc : AccTuple w (1 + 1) (catT 1 is1 is1) 1 is1 (listJ : (Nat → V) → Nat → V) listA := by
  rw [catT_is1]
  refine acc_op1 (accRead_binUnion (accRead_const _ _)
    (accRead_image (kpair pt) (hImg := fun _ => hasImage_kpair_pt _) (accRead_prod ?_ ?_)))
  · exact accRead_hole (by omega) pt_mem_unitSet pt_mem_unitSet
  · exact accRead_hole (by omega) pt_mem_unitSet pt_mem_unitSet

theorem listJ_maps : ∀ X Y : Nat → V, InTupleSpace w 1 is1 X → InTupleSpace w 1 is1 Y →
    InTupleSpace w 1 is1 (listJ (catT 1 X Y)) := by
  intro X Y hX hY
  have hZ := catT_mem hX hY
  rw [catT_is1] at hZ
  exact maps_op1 (fun Z hZ => nil_or_mem hw ((tg_isGrothendieck hw).sigmaPairs_mem
    (hole1_mem hZ (by omega)) (fun _ _ => hole1_mem hZ (by omega))
    (hasSigmaPairs_const _ _))) _ hZ

/-- `Rose`'s operator: the field reads `⟦List⟧(X)` = List's least tuple
at the parameter `X` — the model's own nested reading, no key. -/
noncomputable def roseΦ (w : Nat) : (Nat → V) → Nat → V :=
  op1 fun X => image (kpair pt) (app (lfpP w 1 1 is1 listJ listJ_def X 0) pt) (hasImage_kpair_pt _)

theorem rose_closed : ∃ L : Nat → V, IsClosedTuple w 1 is1 (roseΦ w) L := by
  have hU := tg_isGrothendieck (V := V) hw
  have hLA : (listA : V) ∈ˢ (tg w : V) := prodA_mem hw (unitSet_mem_tg w) (unitSet_mem_tg w)
  have hΨ_ext : ∀ X Y : Nat → V, (∀ m, m < 1 → X m = Y m) →
      ∀ m, m < 1 → lfpP w 1 1 is1 listJ listJ_def X m = lfpP w 1 1 is1 listJ listJ_def Y m := by
    intro X Y hXY m hm
    unfold lfpP
    exact lfpTuple_congr (k := 1) (fun _ _ => rfl)
      (fun Z _ n hn => listJ_def.1 _ _ (fun j hj => by
        unfold catT; split
        · exact hXY j (by omega)
        · rfl) n (by omega)) hm
  have hroseDef : DefTupleOp 1 (roseΦ w) := defTupleOp_op1
    (fun X Y hXY => image_ext (by rw [hΨ_ext X Y hXY 0 Nat.zero_lt_one]) _ _ (fun _ _ => rfl))
    ((DefFun.image_apply_curry (F := fun x _ => kpair pt x)
      (h := fun _ => hasImage_kpair_pt _)
      (DefFun.kpair_apply DefFun.pt (DefFun.proj 0))
      (DefFun.app_apply (DefFun.lfpP_apply listJ_def Nat.zero_lt_one) DefFun.pt)).congr
      fun _ => rfl)
  -- List is accessible in its parameter (the nested case)
  have hP : AccTuple w 1 is1 1 is1 (lfpP w 1 1 is1 (listJ : (Nat → V) → Nat → V) listJ_def)
      (accPaths listA) :=
    lfpP_acc listJ_def (fun _ => hLA) (listJ_maps hw) listJ_acc
  have hPm : ∀ X : Nat → V, InTupleSpace w 1 is1 X →
      InTupleSpace w 1 is1 (lfpP w 1 1 is1 (listJ : (Nat → V) → Nat → V) listJ_def X) :=
    fun X _ => lfpTuple_mem _ _ _ _ (listJ_def.section X)
  refine closed_of_acc hw (A := sigmaPairs unitSet (fun _ => accPaths listA) (hasSigmaPairs_const _ _))
    (hU.sigmaPairs_mem (unitSet_mem_tg w) (fun _ _ => accPaths_mem hw hLA) (hasSigmaPairs_const _ _))
    hroseDef
    (maps_op1 fun X hX => tag_image_mem_strictU hw (hole1_mem (hPm X hX) Nat.zero_lt_one))
    (acc_op1 ?_)
  exact accRead_image (kpair pt) (hImg := fun _ => hasImage_kpair_pt _)
    (accRead_comp hΨ_ext (fun _ hm => DefFun.lfpP_apply listJ_def hm) hP hPm
      (accRead_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet))

end Instances

end ConLeche.SetTheory.AccessEx
