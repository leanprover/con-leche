import ConLeche.SetModel.HoleOp
import ConLeche.SetModel.TupleContainer
import ConLeche.SetModel.NarrowTreeList
import ConLeche.Model.Inductives.FixWitness

/-!
# R23PROBE / R3: (W) for a NESTED hole-operator block through the kit

`treeD` (`Tree ::= node (List Tree)`, `SetModel/HoleOp.lean`) at `w ≠ 0`:

1. the TRANSIENT wide operator `Ψ = uPhi wideD` on 2 components (Tree,
   the key `List Tree`), read off the derivation: Tree's `cont LIST (hole 0)`
   field becomes `hole 1`; the key's constructors are `listD`'s with
   `param ↦ hole 0`, `hole 0 ↦ hole 1`;
2. `IsClosedTuple` for `Ψ` from `tupleContainer_closed_exists` (shapes
   read off the constructors: NarrowTreeList's `shp`/`posns`/`tgtC`);
3. `closedTuple_composeAt` composes the key away;
4. `composeAt Ψ 1 = uPhi treeD` ON THE TUPLE SPACE (`compose_eq_treeD`),
   by `lfpTuple_one` + `lfpTuple_congr` — the key's section IS `listD`'s
   operator at the parameter `X 0` (the set-level substitution law,
   definitional here) and the container's value IS its lfp (its clause's
   `leaf`);
5. `isClosedTuple_congr` transports the closed tuple: (W) for `treeD`.

Plus `listD`'s own (W) at `w ≠ 0` (a flat block: the kit at width 1), so
`⟦Tree⟧`'s fibre law holds at EVERY level with no hypothesis.
-/

open ConLeche.SetTheory

universe u
variable {V : Type u} [ConLeche.SetTheory V]

namespace R23

theorem uinj_mem_univ {w : Nat} (hw : w ≠ 0) (j : Nat) {fs : List V}
    (h : ∀ x, x ∈ fs → x ∈ˢ (univ w : V)) : uinj w j fs ∈ˢ (univ w : V) := by
  rw [uinj_pos hw]
  exact ConLeche.Model.inj_mem_univ hw (ConLeche.Model.mkTower_mem_univ hw h)

/-! ## `listD`'s fibre law at an arbitrary tuple, and its (W) -/

theorem mem_listD_uPhi {w : Nat} (ρ : Nat → V) (α : V) (X : Nat → V) {x : V} :
    x ∈ˢ app (uPhi (listD (V := V) w) ρ α X 0) pt ↔
      x = uinj w 0 [] ∨ ∃ h t, h ∈ˢ α ∧ t ∈ˢ app (X 0) pt ∧ x = uinj w 1 [h, t] := by
  rw [mem_uPhi (listD w) ρ α X (show (pt : V) ∈ˢ (listD (V := V) w).Is 0 from pt_mem_unitSet)]
  constructor
  · rintro ⟨j, fs, ct, hct, hf, -, rfl⟩
    match j, fs, hct, hf with
    | 0, [], _, _ => exact Or.inl rfl
    | 1, [h, t], rfl, hf => exact Or.inr ⟨h, t, hf.1, hf.2.1, rfl⟩
  · rintro (rfl | ⟨h, t, hh, ht, rfl⟩)
    · exact ⟨0, [], _, rfl, trivial, rfl, rfl⟩
    · exact ⟨1, [h, t], _, rfl, ⟨hh, ht, trivial⟩, rfl, rfl⟩

/-- The list builder over NarrowTreeList's shapes, at `uinj`. -/
noncomputable def lsMkU (w : Nat) (a g : V) : V :=
  Tower.natFibre (fun j => if j = 1 then uinj w 0 [] else uinj w 1 [ssnd a, app g (vnat 0)]) (sfst a)

theorem lsMkU_nil (w : Nat) (g : V) : lsMkU w (kpair (vnat 1) pt) g = uinj (V := V) w 0 [] := by
  unfold lsMkU; rw [sfst_kpair, Tower.natFibre_vnat, if_pos rfl]

theorem lsMkU_cons (w : Nat) (h g : V) :
    lsMkU w (kpair (vnat 2) h) g = uinj (V := V) w 1 [h, app g (vnat 0)] := by
  unfold lsMkU; rw [sfst_kpair, Tower.natFibre_vnat, if_neg (by omega), ssnd_kpair]

/-- **`listD`'s (W) at `w ≠ 0`** — the kit at width 1, the head in the shape. -/
theorem listD_closed_pos {w : Nat} (hw : w ≠ 0) (ρ : Nat → V) {α : V} (hα : α ∈ˢ (univ w : V)) :
    (listD (V := V) w).Closed ρ α := by
  have hU := univ_isTGUniverse (V := V) hw
  refine tupleContainer_closed_exists hw (Is := unitIs) (uPhi (listD w) ρ α) (fun _ _ => lsShapes α)
    lsPos (fun _ _ => 0) (fun _ _ => pt) (fun _ => lsMkU w) ?hA ?hB ?htgt ?hmkU ?helim
  case hA =>
    intro m hm i hi
    have hnilS : (kpair (vnat 1) pt : V) ∈ˢ (univ w : V) :=
      hU.kpair_mem (vnat_mem_univ_pos hw 1) (vnat_mem_univ_pos hw 1) (pt_mem_univ hw)
    show lsShapes α ∈ˢ (univ w : V)
    unfold lsShapes
    exact hU.binUnion_mem hnilS (hU.sing_mem hnilS hnilS)
      (hU.image_mem hα fun h hh => hU.kpair_mem hα (vnat_mem_univ_pos hw 2) (hU.transitive hα hh))
  case hB =>
    intro m hm i a hi ha
    rcases mem_lsShapes.mp ha with rfl | ⟨h, hh, rfl⟩
    · rw [lsPos_nil]; exact hU.empty_mem hα
    · rw [lsPos_cons]; exact hU.sing_mem (vnat_mem_univ_pos hw 0) (vnat_mem_univ_pos hw 0)
  case htgt => exact fun m hm i a p hi ha hp => ⟨Nat.one_pos, pt_mem_unitSet⟩
  case hmkU =>
    intro m hm i a g hi ha hg
    rcases mem_lsShapes.mp ha with rfl | ⟨h, hh, rfl⟩
    · rw [lsMkU_nil]; exact uinj_mem_univ hw 0 (by simp)
    · rw [lsMkU_cons]
      refine uinj_mem_univ hw 1 fun x hx => ?_
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hU.transitive hα hh
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact app_mem_univ hw hg _
        · exact absurd hx List.not_mem_nil
  case helim =>
    intro X hX m hm i hi x hx
    obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
    obtain rfl := mem_unitSet_iff.mp hi
    rcases (mem_listD_uPhi ρ α X).mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · refine ⟨kpair (vnat 1) pt, mem_lsShapes.mpr (Or.inl rfl), graph (fun _ => pt) empty, ?_, ?_⟩
      · rw [lsPos_nil]; exact graph_mem_piSet fun p hp => absurd hp (not_mem_empty p)
      · rw [lsMkU_nil]
    · refine ⟨kpair (vnat 2) h, mem_lsShapes.mpr (Or.inr ⟨h, hh, rfl⟩),
        graph (fun _ => t) (sing (vnat 0)), ?_, ?_⟩
      · rw [lsPos_cons]; exact graph_mem_piSet fun p hp => ht
      · rw [lsMkU_cons, app_graph (mem_sing.mpr rfl)]

/-- `listD`'s (W) at EVERY level and parameter. -/
theorem listD_closedAll (w : Nat) (ρ : Nat → V) : (listD (V := V) w).ClosedAll ρ := by
  intro α hα
  by_cases hw : w = 0
  · subst hw; exact uPhi_closed_zero _ _ hα
  · exact listD_closed_pos hw ρ hα

/-! ## The transient wide operator -/

/-- **The wide datum**, read off `treeD`'s derivation: component 0 is
Tree with its `cont LIST (hole 0)` field replaced by the key's hole
`hole 1`; component 1 is the key `List Tree`: `listD`'s constructors
with `param ↦ hole 0`, `listD`'s `hole 0 ↦ hole 1`. -/
noncomputable def wideD (w : Nat) : UBlock V w 2 where
  Is := unitIs
  ctors := fun c =>
    if c = 0 then [uctor [holeF 1] (pos_cons (pos_holeF (by decide)) pos_nil)]
    else [uctor [] pos_nil,
      uctor [holeF 0, holeF 1] (pos_cons (pos_holeF (by decide)) (pos_cons (pos_holeF (by decide)) pos_nil))]

theorem mem_wideD_zero {w : Nat} (ρ : Nat → V) (α : V) (X : Nat → V) {x : V} :
    x ∈ˢ app (uPhi (wideD (V := V) w) ρ α X 0) pt ↔ ∃ l, l ∈ˢ app (X 1) pt ∧ x = uinj w 0 [l] := by
  rw [mem_uPhi (wideD w) ρ α X (show (pt : V) ∈ˢ (wideD (V := V) w).Is 0 from pt_mem_unitSet)]
  constructor
  · rintro ⟨j, fs, ct, hct, hf, -, rfl⟩
    match j, fs, hct, hf with
    | 0, [l], rfl, hf => exact ⟨l, hf.1, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨0, [l], _, rfl, ⟨hl, trivial⟩, rfl, rfl⟩

theorem mem_wideD_one {w : Nat} (ρ : Nat → V) (α : V) (X : Nat → V) {x : V} :
    x ∈ˢ app (uPhi (wideD (V := V) w) ρ α X 1) pt ↔
      x = uinj w 0 [] ∨ ∃ h t, h ∈ˢ app (X 0) pt ∧ t ∈ˢ app (X 1) pt ∧ x = uinj w 1 [h, t] := by
  rw [mem_uPhi (wideD w) ρ α X (show (pt : V) ∈ˢ (wideD (V := V) w).Is 1 from pt_mem_unitSet)]
  constructor
  · rintro ⟨j, fs, ct, hct, hf, -, rfl⟩
    match j, fs, hct, hf with
    | 0, [], _, _ => exact Or.inl rfl
    | 1, [h, t], rfl, hf => exact Or.inr ⟨h, t, hf.1, hf.2.1, rfl⟩
  · rintro (rfl | ⟨h, t, hh, ht, rfl⟩)
    · exact ⟨0, [], _, rfl, trivial, rfl, rfl⟩
    · exact ⟨1, [h, t], _, rfl, ⟨hh, ht, trivial⟩, rfl, rfl⟩

open Classical in
/-- The wide builder. -/
noncomputable def mkW (w : Nat) (m : Nat) (a g : V) : V :=
  if m = 0 then uinj w 0 [app g (vnat 0)]
  else if a = (vnat 1 : V) then uinj w 0 []
  else uinj w 1 [app g (vnat 0), app g (vnat 1)]

open Classical in
/-- **(W) for the wide operator** — the kit at width 2. -/
theorem wide_closed {w : Nat} (hw : w ≠ 0) (ρ : Nat → V) (α : V) :
    ∃ L, IsClosedTuple w 2 unitIs (uPhi (wideD (V := V) w) ρ α) L := by
  have hU := univ_isTGUniverse (V := V) hw
  have hv : ∀ j : Nat, (vnat j : V) ∈ˢ (univ w : V) := fun j => vnat_mem_univ_pos hw j
  refine tupleContainer_closed_exists hw (Is := unitIs) (uPhi (wideD w) ρ α) shp posns tgtC
    (fun _ _ => pt) (mkW w) ?hA ?hB ?htgt ?hmkU ?helim
  case hA =>
    intro m hm i hi
    match m, hm with
    | 0, _ => exact hU.sing_mem (hv 0) (hv 0)
    | 1, _ => exact hU.upair_mem (hv 1) (hv 1) (hv 2)
  case hB =>
    intro m hm i a hi ha
    have hcases : a = (vnat 0 : V) ∨ a = (vnat 1 : V) ∨ a = (vnat 2 : V) := by
      match m, hm with
      | 0, _ => exact Or.inl (mem_sing.mp ha)
      | 1, _ => rcases mem_upair.mp ha with h | h
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr h)
    rcases hcases with rfl | rfl | rfl
    · rw [posns_vnat]; exact hU.sing_mem (hv 0) (hv 0)
    · rw [posns_vnat]; exact hU.empty_mem (hv 0)
    · rw [posns_vnat]; exact hU.upair_mem (hv 0) (hv 0) (hv 1)
  case htgt =>
    intro m hm i a p hi ha hp
    refine ⟨?_, pt_mem_unitSet⟩
    unfold tgtC
    split
    · omega
    · split <;> omega
  case hmkU =>
    intro m hm i a g hi ha hg
    have hg' := app_mem_univ hw hg
    unfold mkW
    split
    · exact uinj_mem_univ hw 0 (by simpa using hg' _)
    · split
      · exact uinj_mem_univ hw 0 (by simp)
      · exact uinj_mem_univ hw 1 (by simpa using ⟨hg' _, hg' _⟩)
  case helim =>
    intro X hX m hm i hi x hx
    obtain rfl := mem_unitSet_iff.mp hi
    match m, hm with
    | 0, _ =>
      obtain ⟨l, hl, rfl⟩ := (mem_wideD_zero ρ α X).mp hx
      refine ⟨vnat 0, mem_sing.mpr rfl, graph (fun _ => l) (sing (vnat 0)), ?_, ?_⟩
      · rw [posns_vnat]
        refine graph_mem_piSet fun p hp => ?_
        obtain rfl := mem_sing.mp hp
        show l ∈ˢ app (X (tgtC (vnat 0) (vnat 0))) pt
        rw [show tgtC (vnat 0 : V) (vnat 0) = 1 from by unfold tgtC; rw [if_pos rfl]]
        exact hl
      · show _ = mkW w 0 (vnat 0) _
        unfold mkW
        rw [if_pos rfl, app_graph (mem_sing.mpr rfl)]
    | 1, _ =>
      rcases (mem_wideD_one ρ α X).mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
      · refine ⟨vnat 1, mem_upair.mpr (Or.inl rfl), graph (fun _ => pt) empty, ?_, ?_⟩
        · rw [posns_vnat]
          exact graph_mem_piSet fun p hp => absurd hp (not_mem_empty p)
        · show _ = mkW w 1 (vnat 1) _
          unfold mkW
          rw [if_neg (by omega), if_pos rfl]
      · refine ⟨vnat 2, mem_upair.mpr (Or.inr rfl),
          graph (fun p => if p = (vnat 0 : V) then h else t) (upair (vnat 0) (vnat 1)), ?_, ?_⟩
        · rw [posns_vnat]
          refine graph_mem_piSet fun p hp => ?_
          rcases mem_upair.mp hp with rfl | rfl
          · rw [if_pos rfl]
            show h ∈ˢ app (X (tgtC (vnat 2) (vnat 0))) pt
            rw [show tgtC (vnat 2 : V) (vnat 0) = 0 from by
              unfold tgtC; rw [if_neg (vnat_ne (by omega)), if_pos rfl]]
            exact hh
          · rw [if_neg (vnat_ne (by omega))]
            show t ∈ˢ app (X (tgtC (vnat 2) (vnat 1))) pt
            rw [show tgtC (vnat 2 : V) (vnat 1) = 1 from by
              unfold tgtC; rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega))]]
            exact ht
        · show _ = mkW w 1 (vnat 2) _
          unfold mkW
          rw [if_neg (by omega), if_neg (vnat_ne (by omega)),
            app_graph (mem_upair.mpr (Or.inl rfl)), app_graph (mem_upair.mpr (Or.inr rfl)),
            if_pos rfl, if_neg (vnat_ne (by omega))]

/-! ## Composing the key away, and `Ψ^(1) = treeD`'s operator -/

/-- **The key's section IS the container's operator at the instantiation**
(the set-level substitution law, definitional for the hole operator):
`Ψ`'s component 1 with component 0 held at `X` is `listD`'s operator at
the parameter `X 0 pt`, whatever the frames. -/
theorem wide_sec_eq_listD {w : Nat} (ρ ρ' : Nat → V) (α : V) (X : Nat → V) (Y : Nat → V) :
    uPhi (wideD (V := V) w) ρ α (updTuple X 1 (Y 0)) 1 = uPhi (listD w) ρ' (app (X 0) pt) Y 0 := by
  unfold uPhi
  congr 1
  funext t
  congr 1
  funext j
  match j with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- The key's least pre-fixed family IS the container's carrier at
the instantiation (its clause's `leaf`): `lfpTuple_one` + `lfpTuple_congr`. -/
theorem key_lfp_eq {w : Nat} (ρ : Nat → V) (α : V) {X : Nat → V} :
    lfpFamSet w (unitIs (V := V) 1) (secF w unitIs (uPhi (wideD (V := V) w) ρ α) X 1) =
      (listD w).carrier (fun _ => empty) (app (X 0) pt) 0 := by
  rw [← lfpTuple_one]
  unfold UBlock.carrier
  refine lfpTuple_congr (fun _ _ => rfl) (fun Y hY m hm => ?_) Nat.one_pos
  obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
  show app (secF w unitIs _ X 1) (Y 0) = _
  rw [app_secF (hY 0 Nat.one_pos)]
  exact wide_sec_eq_listD ρ _ α X Y

/-- **`Ψ^(1) = treeD`'s operator**, everywhere (no space premise needed). -/
theorem compose_eq_treeD {w : Nat} (hW : (listD (V := V) w).ClosedAll fun _ => empty)
    (ρ ρ' : Nat → V) (α β : V) (X : Nat → V) :
    composeAt w unitIs (uPhi (wideD (V := V) w) ρ α) 1 X 0 = uPhi (treeD w hW) ρ' β X 0 := by
  unfold composeAt
  rw [key_lfp_eq]
  unfold uPhi
  congr 1
  funext t
  congr 1
  funext j
  match j with
  | 0 => rfl
  | _ + 1 => rfl

/-- **(W) for the NESTED block `treeD` at `w ≠ 0`**: the wide closed
tuple (kit at width 2), the key composed away (`closedTuple_composeAt`),
the composed operator identified with `treeD`'s on the space. -/
theorem treeD_closed_pos {w : Nat} (hw : w ≠ 0) (hW : (listD (V := V) w).ClosedAll fun _ => empty)
    (ρ : Nat → V) (β : V) : (treeD w hW).Closed ρ β := by
  obtain ⟨L, hL⟩ := wide_closed hw (V := V) (fun _ => empty) empty
  have hmono : ∀ X Y, InTupleSpace w (1 + 1) unitIs X → InTupleSpace w (1 + 1) unitIs Y →
      TupleLe (1 + 1) unitIs X Y →
      TupleLe 1 unitIs (uPhi (wideD (V := V) w) (fun _ => empty) empty X)
        (uPhi (wideD w) (fun _ => empty) empty Y) :=
    fun X Y hX hY hXY m hm =>
      uPhi_mono (wideD w) (fun _ => empty) (empty_mem_univ w) X Y hX hY hXY m (by omega)
  have hC := closedTuple_composeAt (k := 1) hmono hL
  refine ⟨L, (isClosedTuple_congr (fun _ _ => rfl) (fun X _ m hm => ?_)).mp hC⟩
  obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
  exact compose_eq_treeD hW _ ρ _ β X

/-- `treeD`'s (W) at EVERY level. -/
theorem treeD_closed (w : Nat) (ρ : Nat → V) {β : V} (hβ : β ∈ˢ (univ w : V)) :
    (treeD (V := V) w (listD_closedAll w _)).Closed ρ β := by
  by_cases hw : w = 0
  · subst hw
    exact uPhi_closed_zero _ _ hβ
  · exact treeD_closed_pos hw _ ρ β

/-- **`⟦Tree⟧`'s fibre law at EVERY level, no hypothesis left.** -/
theorem mem_TREE_all (w : Nat) {x : V} :
    x ∈ˢ TREE w (listD_closedAll w _) ↔
      ∃ l, l ∈ˢ LIST w (TREE w (listD_closedAll (V := V) w _)) ∧ x = uinj w 0 [l] :=
  mem_TREE _ (treeD_closed w _ (empty_mem_univ w))

end R23

#print axioms R23.listD_closedAll
#print axioms R23.wide_closed
#print axioms R23.compose_eq_treeD
#print axioms R23.treeD_closed_pos
#print axioms R23.treeD_closed
#print axioms R23.mem_TREE_all
