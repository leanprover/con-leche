module

public import ConLeche.SetModel.ClassFacts

public section

/-!
# Class facts on examples (CLASSCHECK experiment E1)

`ClassSys.good` (`ConLeche/SetModel/ClassFacts.lean`) instantiated on the
proof plan's worked cases (PROOFPLAN §3.2), at the set level:

* **F13** (`corner_nestind_f13_listrose`): `TL | node : List (RL TL)`,
  `RL α | node : α → List (RL α)`.  Classes by age: `λ := List (RL TL)`
  (index 0, free hole `z_ρ`), `ρ := RL TL` (index 1, free hole the member,
  reads `λ` true at `z_ρ := Y`), the member `TL` (index 2, reads `ρ` then `λ`
  true: `T_λ(T_ρ(X))`).  Type-valued: monotone, accessible, (W).
  `f13_member_reads` checks that the member's filled field IS
  `T_λ(T_ρ(X))`, and `f13_rho_reads` that `ρ`'s is `T_λ(Y)` — the stage read
  the concrete-key facts could not cover, here a ∀-instance.
* **Nested-in-nested `Prop` cycle** (`fp_nestnest_prop_cycle`):
  `Foo | mk : List (Tree Foo)`, `Tree α | node : List (Tree α) → Tree α`, at
  `w = 0`: monotone and (W) (the top tuple), no accessibility.
* **A mutual container** (`A α | nil | a : α → B α → A α`,
  `B α | b : A α → B α`, one block; `T | mk : A T`): the group `{A T, B T}` is
  ONE class with two components.

No fullness, no Bekić (`lfpTuple_mixT` is not used), and accessibility is
only ever asked of an operator over the WHOLE valuation space.
-/

namespace ConLeche.SetTheory.ClassFactsEx

universe u

variable {V : Type u} [SetTheory V]

/-! ## Operators with one fibre per position, over `{pt}` -/

/-- Every position is indexed by `{pt}`. -/
@[expose] noncomputable def is1 : Nat → V := fun _ => unitSet

/-- The operator whose position `m` has the single fibre `R m X`. -/
noncomputable def opR (R : Nat → (Nat → V) → V) : (Nat → V) → Nat → V :=
  fun X m => graph (fun _ => R m X) unitSet

/-- A hole read at `pt`. -/
@[expose] noncomputable def hole (m : Nat) (X : Nat → V) : V := app (X m) pt

/-- The empty valuation. -/
noncomputable def base0 : Nat → V := fun _ => graph (fun _ => empty) unitSet

theorem base0_mem {w K : Nat} : InTupleSpace w K (is1 : Nat → V) base0 :=
  fun _ _ => graph_mem_famSpace fun _ _ => empty_mem_univ w

theorem app_opR {R : Nat → (Nat → V) → V} {X : Nat → V} {m : Nat} {i : V}
    (hi : i ∈ˢ (is1 m : V)) : app (opR R X m) i = R m X := app_graph hi

theorem hole_le {K : Nat} {X Y : Nat → V} (h : TupleLe K is1 X Y) {m : Nat} (hm : m < K) :
    hole m X ⊆ˢ hole m Y := h m hm pt pt_mem_unitSet

theorem hole_mem {w K : Nat} {X : Nat → V} (hX : InTupleSpace w K is1 X) {m : Nat} (hm : m < K) :
    hole m X ∈ˢ (univ w : V) := famSpace_app (hX m hm) pt_mem_unitSet

theorem accRead_weaken {w K : Nat} {Is : Nat → V} {F : (Nat → V) → V} {A B : V}
    (h : AccRead w K Is F A) (hAB : A ⊆ˢ B) : AccRead w K Is F B := by
  intro X hX x hx
  obtain ⟨C, g, hC, hg, hs⟩ := h X hX x hx
  exact ⟨C, g, Subset.trans hC hAB, hg, hs⟩

/-- **A good operator from good readings.** -/
theorem opR_ok {w K : Nat} {R : Nat → (Nat → V) → V}
    (hmaps : ∀ X, InTupleSpace w K is1 X → ∀ m, m < K → R m X ∈ˢ (univ w : V))
    (hmono : ∀ X Y, InTupleSpace w K is1 X → InTupleSpace w K is1 Y → TupleLe K is1 X Y →
      ∀ m, m < K → R m X ⊆ˢ R m Y)
    (hacc : w ≠ 0 → ∃ A, A ∈ˢ (univ w : V) ∧ ∀ m, m < K → AccRead w K is1 (R m) A) :
    OpOk w K is1 (opR R) := by
  refine ⟨fun X hX m hm => graph_mem_famSpace fun _ _ => hmaps X hX m hm,
    fun X Y hX hY hXY m hm i hi => ?_, fun hw => ?_⟩
  · rw [app_opR hi, app_opR hi]; exact hmono X Y hX hY hXY m hm
  · obtain ⟨A, hA, h⟩ := hacc hw
    refine ⟨A, hA, fun X hX m hm i hi x hx => ?_⟩
    rw [app_opR hi] at hx
    obtain ⟨B, g, hB, hg, hs⟩ := h m hm X hX x hx
    exact ⟨B, g, hB, hg, fun X' hX' h' => by rw [app_opR hi]; exact hs X' hX' h'⟩

/-! ## Type-valued encodings (`w ≠ 0`) -/

/-- The nullary constructor's value. -/
@[expose] noncomputable def nilV : V := kpair empty empty

/-- A `nil`-or-tagged fibre. -/
@[expose] noncomputable def nilOr (S : V) : V := binUnion (sing nilV) (image (kpair pt) S)

open Classical in
/-- The support bound used by every reading below. -/
noncomputable def A0 : V :=
  binUnion unitSet (sigmaPairs (upair empty pt) fun t => if t = empty then unitSet else unitSet)

section Pos

variable {w : Nat} (hw : w ≠ 0)
include hw

theorem pt_mem_univ : (pt : V) ∈ˢ (univ w : V) :=
  (univ_isTGUniverse hw).transitive (unitSet_mem_univ w) pt_mem_unitSet

theorem tag_mem {S : V} (hS : S ∈ˢ (univ w : V)) : image (kpair pt) S ∈ˢ (univ w : V) :=
  (univ_isTGUniverse hw).image_mem hS fun _ hx =>
    (univ_isTGUniverse hw).kpair_mem (empty_mem_univ w) (pt_mem_univ hw)
      ((univ_isTGUniverse hw).transitive hS hx)

theorem nilOr_mem {S : V} (hS : S ∈ˢ (univ w : V)) : nilOr S ∈ˢ (univ w : V) :=
  (univ_isTGUniverse hw).binUnion_mem (empty_mem_univ w)
    ((univ_isTGUniverse hw).sing_mem (empty_mem_univ w)
      ((univ_isTGUniverse hw).kpair_mem (empty_mem_univ w) (empty_mem_univ w) (empty_mem_univ w)))
    (tag_mem hw hS)

theorem prod_mem {K : Nat} {X : Nat → V} (hX : InTupleSpace w K is1 X) {m n : Nat} (hm : m < K)
    (hn : n < K) : sigmaPairs (hole m X) (fun _ => hole n X) ∈ˢ (univ w : V) :=
  (univ_isTGUniverse hw).sigmaPairs_mem (hole_mem hX hm) fun _ _ => hole_mem hX hn

theorem A0_mem : (A0 : V) ∈ˢ (univ w : V) := by
  classical
  have hU := univ_isTGUniverse (V := V) hw
  refine hU.binUnion_mem (empty_mem_univ w) (unitSet_mem_univ w)
    (hU.sigmaPairs_mem (hU.upair_mem (empty_mem_univ w) (empty_mem_univ w) (pt_mem_univ hw))
      fun t _ => ?_)
  by_cases h : t = empty
  · simp only [h, if_true]; exact unitSet_mem_univ w
  · simp only [h, if_false]; exact unitSet_mem_univ w

end Pos

section Reads

variable {w K : Nat}

theorem acc_hole {m : Nat} (hm : m < K) : AccRead w K is1 (hole m) (A0 : V) :=
  accRead_weaken (accRead_hole hm pt_mem_unitSet pt_mem_unitSet)
    fun _ h => mem_binUnion.mpr (Or.inl h)

theorem acc_tagHole {m : Nat} (hm : m < K) :
    AccRead w K is1 (fun X => image (kpair pt) (hole m X)) (A0 : V) :=
  accRead_image _ (acc_hole hm)

theorem acc_tagProd {m n : Nat} (hm : m < K) (hn : n < K) :
    AccRead w K is1 (fun X => image (kpair pt) (sigmaPairs (hole m X) fun _ => hole n X)) (A0 : V) :=
  accRead_image _ (accRead_weaken (accRead_prod (accRead_hole hm pt_mem_unitSet pt_mem_unitSet)
    (accRead_hole hn pt_mem_unitSet pt_mem_unitSet)) fun _ h => mem_binUnion.mpr (Or.inr h))

theorem acc_nilOrProd {m n : Nat} (hm : m < K) (hn : n < K) :
    AccRead w K is1 (fun X => nilOr (sigmaPairs (hole m X) fun _ => hole n X)) (A0 : V) :=
  accRead_binUnion (accRead_const _ _) (acc_tagProd hm hn)

theorem prod_le {X Y : Nat → V} (h : TupleLe K is1 X Y) {m n : Nat} (hm : m < K) (hn : n < K) :
    sigmaPairs (hole m X) (fun _ => hole n X) ⊆ˢ sigmaPairs (hole m Y) (fun _ => hole n Y) := by
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sigmaPairs.mp hp
  exact mem_sigmaPairs.mpr ⟨a, hole_le h hm a ha, b, hole_le h hn b hb, rfl⟩

theorem image_le {f : V → V} {S T : V} (h : S ⊆ˢ T) : image f S ⊆ˢ image f T := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact mem_image.mpr ⟨x, h x hx, rfl⟩

theorem nilOr_le {S T : V} (h : S ⊆ˢ T) : nilOr S ⊆ˢ nilOr T := by
  intro y hy
  rcases mem_binUnion.mp hy with h1 | h1
  · exact mem_binUnion.mpr (Or.inl h1)
  · exact mem_binUnion.mpr (Or.inr (image_le h y h1))

end Reads

/-! ## One reading at one position -/

section One

variable {w K : Nat}

variable (w K) in
/-- A good reading: in the level, monotone, accessible (bound `A0`) at `w ≠ 0`. -/
def RdOk (r : (Nat → V) → V) : Prop :=
  (∀ X, InTupleSpace w K is1 X → r X ∈ˢ (univ w : V)) ∧
  (∀ X Y, InTupleSpace w K is1 X → InTupleSpace w K is1 Y → TupleLe K is1 X Y → r X ⊆ˢ r Y) ∧
  (w ≠ 0 → AccRead w K is1 r (A0 : V))

open Classical in
/-- The operator with the reading `r` at the positions `P`, empty elsewhere. -/
noncomputable def opAt (P : Nat → Prop) (r : (Nat → V) → V) : (Nat → V) → Nat → V :=
  opR fun m X => if P m then r X else empty

theorem opAt_ok {P : Nat → Prop} {r : (Nat → V) → V} (h : RdOk w K r) :
    OpOk w K is1 (opAt P r) := by
  classical
  refine opR_ok (fun X hX m _ => ?_) (fun X Y hX hY hXY m _ => ?_) (fun hw => ⟨A0, ?_, fun m _ => ?_⟩)
  · split
    · exact h.1 X hX
    · exact empty_mem_univ w
  · split
    · exact h.2.1 X Y hX hY hXY
    · exact Subset.refl _
  · -- the bound is in the level at `w ≠ 0`
    exact A0_mem hw
  · by_cases hP : P m
    · simp only [hP, if_true]; exact h.2.2 hw
    · simp only [hP, if_false]; exact accRead_const _ _

theorem rd_tagHole (hw : w ≠ 0) {m : Nat} (hm : m < K) :
    RdOk w K (fun X : Nat → V => image (kpair pt) (hole m X)) :=
  ⟨fun _ hX => tag_mem hw (hole_mem hX hm), fun _ _ _ _ h => image_le (hole_le h hm),
    fun _ => acc_tagHole hm⟩

theorem rd_tagProd (hw : w ≠ 0) {m n : Nat} (hm : m < K) (hn : n < K) :
    RdOk w K (fun X : Nat → V => image (kpair pt) (sigmaPairs (hole m X) fun _ => hole n X)) :=
  ⟨fun _ hX => tag_mem hw (prod_mem hw hX hm hn), fun _ _ _ _ h => image_le (prod_le h hm hn),
    fun _ => acc_tagProd hm hn⟩

theorem rd_nilOrProd (hw : w ≠ 0) {m n : Nat} (hm : m < K) (hn : n < K) :
    RdOk w K (fun X : Nat → V => nilOr (sigmaPairs (hole m X) fun _ => hole n X)) :=
  ⟨fun _ hX => nilOr_mem hw (prod_mem hw hX hm hn), fun _ _ _ _ h => nilOr_le (prod_le h hm hn),
    fun _ => acc_nilOrProd hm hn⟩

end One

/-! ## F13: `TL | node : List (RL TL)`, `RL α | node : α → List (RL α)` -/

/-- The readings.  Positions: `0` the member `TL`, `1` the class
`ρ = RL TL`, `2` the class `λ = List (RL TL)`. -/
@[expose] noncomputable def f13rd : Nat → (Nat → V) → V
  -- λ = List α at α := z_ρ: nil | cons (a : z_ρ) (l : λ)
  | 0 => fun X => nilOr (sigmaPairs (hole 1 X) fun _ => hole 2 X)
  -- ρ = RL TL: node (a : TL) (l : List (RL TL))
  | 1 => fun X => image (kpair pt) (sigmaPairs (hole 0 X) fun _ => hole 2 X)
  -- TL: node (l : List (RL TL))
  | _ => fun X => image (kpair pt) (hole 2 X)

/-- **The F13 class system.**  Classes by age: `0 = λ` (List, oldest, free
hole `z_ρ` — `RL` is younger, so `ρ` is a CYCLIC inner class), `1 = ρ`
(RL; free hole the member; reads `λ` true), `2 = TL` (the member block;
reads `ρ`, then `λ`, true). -/
@[expose] noncomputable def f13 (w : Nat) : ClassSys V where
  w := w
  K := 3
  Is := is1
  base := base0
  hbase := base0_mem
  grp := fun c m => m = 2 - c
  free := fun c m => (c = 0 ∧ m = 1) ∨ (c = 1 ∧ m = 0)
  Φ := fun c => opAt (fun m => m = 2 - c) (f13rd c)
  fl := fun c => if c = 1 then [0] else if c = 2 then [1, 0] else []

theorem f13_flat {w : Nat} (hw : w ≠ 0) : ∀ c, OpOk w 3 is1 ((f13 w : ClassSys V).Φ c) := by
  intro c
  refine opAt_ok ?_
  match c with
  | 0 => exact rd_nilOrProd hw (by omega) (by omega)
  | 1 => exact rd_tagProd hw (by omega) (by omega)
  | _ + 2 => exact rd_tagHole hw (by omega)

/-- **E1 on F13**: every class — `λ`, `ρ` and the member block — is good:
monotone, accessible, (W) at every frame. -/
theorem f13_good {w : Nat} (hw : w ≠ 0) : ∀ c, OpOk w 3 is1 ((f13 w : ClassSys V).T c) :=
  (f13 w).good (f13_flat hw)

/-- The member block's (W). -/
theorem f13_member_closed {w : Nat} (hw : w ≠ 0) {u : Nat → V} (hu : InTupleSpace w 3 is1 u) :
    ∃ L : Nat → V, IsClosedTuple w 3 is1 (secOp ((f13 w : ClassSys V).grp 2) ((f13 w : ClassSys V).free 2) (base0 : Nat → V)
      ((f13 w : ClassSys V).Ψ 2) u) L :=
  (f13 w).closed (f13_flat hw) 2 hu

/-- `classAcc λ` and `classAcc ρ`, in their free holes. -/
theorem f13_acc {w : Nat} (hw : w ≠ 0) (c : Nat) :
    ∃ A, A ∈ˢ (univ w : V) ∧ AccTuple w 3 is1 3 is1 ((f13 w : ClassSys V).car c) A :=
  (f13 w).car_acc (f13_flat hw) hw c

theorem f13_Ψ2 (w : Nat) (v : Nat → V) :
    (f13 w : ClassSys V).Ψ 2 v =
      opAt (fun m => m = 0) (f13rd 2) ((f13 w : ClassSys V).T 0 ((f13 w : ClassSys V).T 1 v)) := by
  unfold ClassSys.Ψ
  rw [show (f13 w : ClassSys V).fl 2 = [1, 0] from rfl]
  simp only [ClassSys.fillL, dif_pos (show (f13 w : ClassSys V).rk 1 < (f13 w : ClassSys V).rk 2 from Nat.lt_of_sub_eq_succ rfl),
    dif_pos (show (f13 w : ClassSys V).rk 0 < (f13 w : ClassSys V).rk 2 from Nat.lt_of_sub_eq_succ rfl)]
  rfl

theorem f13_Ψ1 (w : Nat) (v : Nat → V) :
    (f13 w : ClassSys V).Ψ 1 v = opAt (fun m => m = 1) (f13rd 1) ((f13 w : ClassSys V).T 0 v) := by
  unfold ClassSys.Ψ
  rw [show (f13 w : ClassSys V).fl 1 = [0] from rfl]
  simp only [ClassSys.fillL, dif_pos (show (f13 w : ClassSys V).rk 0 < (f13 w : ClassSys V).rk 1 from Nat.lt_of_sub_eq_succ rfl)]
  rfl

theorem f13_Ψ0 (w : Nat) (v : Nat → V) :
    (f13 w : ClassSys V).Ψ 0 v = opAt (fun m => m = 2) (f13rd 0) v := by
  unfold ClassSys.Ψ; rfl

/-- The class `λ` spliced in, read at its position: its carrier. -/
theorem f13_T0_2 (w : Nat) (u : Nat → V) :
    (f13 w : ClassSys V).T 0 u 2 = (f13 w : ClassSys V).car 0 u 2 := by
  rw [ClassSys.T_eq]; unfold cfixP
  exact mixT_apply_pos (show ((f13 w : ClassSys V).grp 0) 2 from rfl)

theorem f13_T1_1 (w : Nat) (u : Nat → V) :
    (f13 w : ClassSys V).T 1 u 1 = (f13 w : ClassSys V).car 1 u 1 := by
  rw [ClassSys.T_eq]; unfold cfixP
  exact mixT_apply_pos (show ((f13 w : ClassSys V).grp 1) 1 from rfl)

theorem f13_T0_0 (w : Nat) (u : Nat → V) : (f13 w : ClassSys V).T 0 u 0 = u 0 := by
  rw [ClassSys.T_eq]; unfold cfixP
  exact mixT_apply_neg (show ¬ ((f13 w : ClassSys V).grp 0) 0 by simp [f13])

theorem app_opAt_pos {P : Nat → Prop} {r : (Nat → V) → V} {X : Nat → V} {m : Nat} (h : P m) :
    app (opAt P r X m) pt = r X := by
  classical
  unfold opAt; rw [app_opR pt_mem_unitSet, if_pos h]

theorem app_opAt_neg {P : Nat → Prop} {r : (Nat → V) → V} {X : Nat → V} {m : Nat} (h : ¬ P m) :
    app (opAt P r X m) pt = empty := by
  classical
  unfold opAt; rw [app_opR pt_mem_unitSet, if_neg h]

/-- **The member reads `T_λ(T_ρ(X))`**: its filled field is `λ`'s carrier
at the frame where `ρ`'s carrier (at the member tuple) has been spliced in. -/
theorem f13_member_reads (w : Nat) (v : Nat → V) :
    app ((f13 w : ClassSys V).Ψ 2 v 0) pt =
      image (kpair pt) (app ((f13 w : ClassSys V).car 0 ((f13 w : ClassSys V).T 1 v) 2) pt) := by
  rw [f13_Ψ2, app_opAt_pos (P := fun m => m = 0) rfl]
  show image (kpair pt) (app ((f13 w : ClassSys V).T 0 _ 2) pt) = _
  rw [f13_T0_2]

/-- **`ρ` reads `T_λ(Y)`**: its filled `List` field is `λ`'s carrier at the
frame whose `z_ρ` is `ρ`'s OWN stage — a ∀-instance of `λ`'s fact. -/
theorem f13_rho_reads (w : Nat) (v : Nat → V) :
    app ((f13 w : ClassSys V).Ψ 1 v 1) pt =
      image (kpair pt) (sigmaPairs (hole 0 v) fun _ => app ((f13 w : ClassSys V).car 0 v 2) pt) := by
  rw [f13_Ψ1, app_opAt_pos (P := fun m => m = 1) rfl]
  show image (kpair pt) (sigmaPairs (app ((f13 w : ClassSys V).T 0 v 0) pt)
    fun _ => app ((f13 w : ClassSys V).T 0 v 2) pt) = _
  rw [f13_T0_0, f13_T0_2]; rfl

/-! ## The nested-in-nested `Prop` cycle, at `w = 0`

`Foo | mk : List (Tree Foo)`, `Tree α | node : List (Tree α) → Tree α`, every
type a `Prop`: fibres are subsets of `{pt}`, every injection is `pt`. -/

/-- `nil`-or-point. -/
@[expose] noncomputable def ptOr (S : V) : V := binUnion unitSet (image (fun _ => pt) S)

theorem sub_unit_mem {S : V} (h : S ⊆ˢ unitSet) : S ∈ˢ (univ 0 : V) := by
  rw [univ_zero]; exact mem_univZero.mpr h

theorem image_pt_sub (S : V) : image (fun _ => (pt : V)) S ⊆ˢ unitSet := by
  intro y hy
  obtain ⟨_, _, rfl⟩ := mem_image.mp hy
  exact pt_mem_unitSet

theorem ptOr_sub (S : V) : ptOr S ⊆ˢ unitSet := by
  intro y hy
  rcases mem_binUnion.mp hy with h | h
  · exact h
  · exact image_pt_sub S y h

theorem rd0_ptOr {m n : Nat} (hm : m < 3) (hn : n < 3) :
    RdOk 0 3 (fun X : Nat → V => ptOr (sigmaPairs (hole m X) fun _ => hole n X)) :=
  ⟨fun _ _ => sub_unit_mem (ptOr_sub _), fun _ _ _ _ h y hy => by
    rcases mem_binUnion.mp hy with h1 | h1
    · exact mem_binUnion.mpr (Or.inl h1)
    · exact mem_binUnion.mpr (Or.inr (image_le (prod_le h hm hn) y h1)), fun h => absurd rfl h⟩

theorem rd0_ptHole {m : Nat} (hm : m < 3) :
    RdOk 0 3 (fun X : Nat → V => image (fun _ => pt) (hole m X)) :=
  ⟨fun _ _ => sub_unit_mem (image_pt_sub _), fun _ _ _ _ h => image_le (hole_le h hm),
    fun h => absurd rfl h⟩

/-- The readings: `0 = λ = List (Tree Foo)`, `1 = τ = Tree Foo`, `2 = Foo`. -/
@[expose] noncomputable def nnrd : Nat → (Nat → V) → V
  | 0 => fun X => ptOr (sigmaPairs (hole 1 X) fun _ => hole 2 X)
  | 1 => fun X => image (fun _ => pt) (hole 2 X)
  | _ => fun X => image (fun _ => pt) (hole 2 X)

/-- The nested-in-nested class system (same shape as F13: `λ` oldest with
the cyclic `z_τ` free, `τ` reads `λ` at its own stage, `Foo` reads `τ`
then `λ`). -/
@[expose] noncomputable def nn : ClassSys V where
  w := 0
  K := 3
  Is := is1
  base := base0
  hbase := base0_mem
  grp := fun c m => m = 2 - c
  free := fun c m => (c = 0 ∧ m = 1) ∨ (c = 1 ∧ m = 0)
  Φ := fun c => opAt (fun m => m = 2 - c) (nnrd c)
  fl := fun c => if c = 1 then [0] else if c = 2 then [1, 0] else []

theorem nn_flat : ∀ c, OpOk 0 3 is1 ((nn : ClassSys V).Φ c) := by
  intro c
  refine opAt_ok ?_
  match c with
  | 0 => exact rd0_ptOr (by omega) (by omega)
  | 1 => exact rd0_ptHole (by omega)
  | _ + 2 => exact rd0_ptHole (by omega)

/-- **E1 on the `Prop` cycle**: every class monotone, (W) by the top tuple;
no accessibility anywhere. -/
theorem nn_good : ∀ c, OpOk 0 3 is1 ((nn : ClassSys V).T c) := nn.good nn_flat

theorem nn_member_closed {u : Nat → V} (hu : InTupleSpace 0 3 is1 u) :
    ∃ L : Nat → V, IsClosedTuple 0 3 is1 (secOp ((nn : ClassSys V).grp 2) ((nn : ClassSys V).free 2)
      (base0 : Nat → V) ((nn : ClassSys V).Ψ 2) u) L :=
  nn.closed nn_flat 2 hu

/-! ## A mutual container: `A α | nil | a : α → B α → A α`, `B α | b : A α → B α`; `T | mk : A T`

Positions: `0` the member `T`, `1` `A T`, `2` `B T`.  The group `{A T, B T}`
(one block, one key) is ONE class (`0`) with two components. -/

section Mutual

variable {w : Nat}

open Classical in
/-- Two readings at two positions. -/
noncomputable def opAt2 (P1 P2 : Nat → Prop) (r1 r2 : (Nat → V) → V) : (Nat → V) → Nat → V :=
  opR fun m X => if P1 m then r1 X else if P2 m then r2 X else empty

theorem opAt2_ok {K : Nat} {P1 P2 : Nat → Prop} {r1 r2 : (Nat → V) → V} (h1 : RdOk w K r1)
    (h2 : RdOk w K r2) : OpOk w K is1 (opAt2 P1 P2 r1 r2) := by
  classical
  refine opR_ok (fun X hX m _ => ?_) (fun X Y hX hY hXY m _ => ?_) (fun hw => ⟨A0, A0_mem hw, fun m _ => ?_⟩)
  · split
    · exact h1.1 X hX
    · split
      · exact h2.1 X hX
      · exact empty_mem_univ w
  · split
    · exact h1.2.1 X Y hX hY hXY
    · split
      · exact h2.2.1 X Y hX hY hXY
      · exact Subset.refl _
  · by_cases hP1 : P1 m
    · simp only [hP1, if_true]; exact h1.2.2 hw
    · by_cases hP2 : P2 m
      · simp only [hP1, hP2, if_true, if_false]; exact h2.2.2 hw
      · simp only [hP1, hP2, if_false]; exact accRead_const _ _

/-- The mutual-container system: class `0` the group `{A T, B T}` (free: the
member), class `1` the member block (reads the group true). -/
noncomputable def mutc (w : Nat) : ClassSys V where
  w := w
  K := 3
  Is := is1
  base := base0
  hbase := base0_mem
  grp := fun c m => if c = 0 then m = 1 ∨ m = 2 else m = 0
  free := fun c m => c = 0 ∧ m = 0
  Φ := fun c => if c = 0 then
      opAt2 (fun m => m = 1) (fun m => m = 2)
        (fun X => nilOr (sigmaPairs (hole 0 X) fun _ => hole 2 X))
        (fun X => image (kpair pt) (hole 1 X))
    else opAt (fun m => m = 0) (fun X => image (kpair pt) (hole 1 X))
  fl := fun c => if c = 0 then [] else [0]

theorem mutc_flat (hw : w ≠ 0) : ∀ c, OpOk w 3 is1 ((mutc w : ClassSys V).Φ c) := by
  intro c
  by_cases hc : c = 0
  · simp only [mutc, hc, if_true]
    exact opAt2_ok (rd_nilOrProd hw (by omega) (by omega)) (rd_tagHole hw (by omega))
  · simp only [mutc, hc, if_false]
    exact opAt_ok (rd_tagHole hw (by omega))

/-- **E1 on a mutual container**: the group's fact is ONE class's, both
components at once (`lfpP_acc_group` at the group). -/
theorem mutc_good (hw : w ≠ 0) : ∀ c, OpOk w 3 is1 ((mutc w : ClassSys V).T c) :=
  (mutc w).good (mutc_flat hw)

theorem mutc_member_closed (hw : w ≠ 0) {u : Nat → V} (hu : InTupleSpace w 3 is1 u) :
    ∃ L : Nat → V, IsClosedTuple w 3 is1 (secOp ((mutc w : ClassSys V).grp 1) ((mutc w : ClassSys V).free 1)
      (base0 : Nat → V) ((mutc w : ClassSys V).Ψ 1) u) L :=
  (mutc w).closed (mutc_flat hw) 1 hu

end Mutual

end ConLeche.SetTheory.ClassFactsEx
