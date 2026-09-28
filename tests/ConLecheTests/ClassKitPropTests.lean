module

public import ConLeche.SetModel.ClassKit
public import ConLecheTests.ClassFactsTests

public section

/-!
# The class kit at `Prop` (CLASSCHECK lane P3c)

`ClassKit` instantiated on the nested-in-nested `Prop` cycle of experiment
E1 (`nn`, `ConLecheTests/ClassFactsTests.lean`): `Foo | mk : List (Tree Foo)`,
`Tree α | node : List (Tree α) → Tree α`, every type a `Prop` (`w = 0`).
Same shape as the F13 kit (`ClassKitTests.lean`): nodes = classes
`0 = λ = List (Tree Foo)`, `1 = τ = Tree Foo`, `2 = Foo`, depth `2 - b`,
the member's call into `λ` at layer `1` of `extN`.

What is new at `Prop`: every injection is `pt`, so a major has MANY
decodings (`λ`'s `nil` and every `cons a l` inject to the same `pt`,
`nn_decodings_not_unique`).  The kit's induction needs no uniqueness —
`ClassKit.claim_step` inducts over the carrier's lfp, the decoding being
the one the fibre law hands out — so `nnkit_ind` holds unchanged; only
the recursor's `huniq` reads uniqueness, and at `Prop` it is the licence's
(or `ℓ = 0`'s) business (`ClassPres.uniq`).
-/

namespace ConLeche.SetTheory.ClassKitPropEx

open ConLeche.SetTheory.ClassFactsEx

universe u

variable {V : Type u} [SetTheory V]

/-- A node's frame, read at its operator. -/
noncomputable def vOf (b : Nat) (u Y : Nat → V) : Nat → V :=
  mixT ((nn : ClassSys V).grp b) (nrmT ((nn : ClassSys V).free b) base0 u) Y

/-- The spines: `λ`'s `nil`/`cons a l`, `τ`'s `node l`, `Foo`'s `mk l`. -/
def kFits : Nat → (Nat → V) → (Nat → V) → V → Nat → Nat → List V → Prop
  | 0, u, Y, _, c, j, fs => c = 2 ∧ ((j = 0 ∧ fs = []) ∨
      (j = 1 ∧ ∃ a l, fs = [a, l] ∧ a ∈ˢ app (u 1) pt ∧ l ∈ˢ app (Y 2) pt))
  | 1, u, Y, _, c, j, fs => c = 1 ∧ j = 0 ∧ ∃ l, fs = [l] ∧
      l ∈ˢ app ((nn : ClassSys V).car 0 (vOf 1 u Y) 2) pt
  | 2, u, Y, _, c, j, fs => c = 0 ∧ j = 0 ∧ ∃ l, fs = [l] ∧
      l ∈ˢ app ((nn : ClassSys V).car 0 ((nn : ClassSys V).T 1 (vOf 2 u Y)) 2) pt
  | _, _, _, _, _, _, _ => False

/-- The injections: every one is the point. -/
noncomputable def kinj (_ _ : Nat) (_ : List V) : V := pt

/-- Node `b`'s clause. -/
noncomputable def kcl (b : Nat) : SClause V (Nat → V) where
  w := 0
  N := 3
  Is := is1
  Φ := fun u => secOp ((nn : ClassSys V).grp b) ((nn : ClassSys V).free b) base0
    ((nn : ClassSys V).Ψ b) u
  Fits := kFits b
  inj := kinj

/-- The predecessors: the recursive fields' majors. -/
noncomputable def kpred (d : NDec V) : V :=
  match d.cls, d.fs with
  | 0, [a, l] => upair (nenc 1 1 pt a) (nenc 0 2 pt l)
  | 1, [l] => sing (nenc 0 2 pt l)
  | 2, [l] => sing (nenc 0 2 pt l)
  | _, _ => empty

/-- The admissible frames: the free holes hold `G`-elements. -/
def kAdm : Nat → (Nat → Nat → V → V → Prop) → (Nat → V) → Prop
  | 0, G, u => InTupleSpace 0 3 is1 u ∧ ∀ y, y ∈ˢ app (u 1) pt → G 1 1 pt y
  | 1, G, u => InTupleSpace 0 3 is1 u ∧ ∀ y, y ∈ˢ app (u 0) pt → G 2 0 pt y
  | _, _, u => InTupleSpace 0 3 is1 u

/-- The TRUE frames. -/
noncomputable def kfr : Nat → Nat → V
  | 0 => (nn : ClassSys V).car 1 ((nn : ClassSys V).car 2 base0)
  | 1 => (nn : ClassSys V).car 2 base0
  | _ => base0

/-! ### Reading the operators -/

theorem vOf_mem {b : Nat} {u Y : Nat → V} (hu : InTupleSpace 0 3 is1 u)
    (hY : InTupleSpace 0 3 is1 Y) : InTupleSpace 0 3 is1 (vOf b u Y) :=
  mixT_mem (nrmT_mem base0_mem hu) hY

theorem vOf_grp {b : Nat} {u Y : Nat → V} {m : Nat} (h : m = 2 - b) : vOf b u Y m = Y m :=
  mixT_apply_pos (G := (nn : ClassSys V).grp b) h

theorem vOf_free {b : Nat} {u Y : Nat → V} {m : Nat} (hg : ¬ m = 2 - b)
    (hf : (b = 0 ∧ m = 1) ∨ (b = 1 ∧ m = 0)) : vOf b u Y m = u m := by
  unfold vOf
  rw [mixT_apply_neg (G := (nn : ClassSys V).grp b) hg]
  exact mixT_apply_pos (G := (nn : ClassSys V).free b) hf

theorem nn_Ψ2 (v : Nat → V) :
    (nn : ClassSys V).Ψ 2 v =
      opAt (fun m => m = 0) (nnrd 2) ((nn : ClassSys V).T 0 ((nn : ClassSys V).T 1 v)) := by
  unfold ClassSys.Ψ
  rw [show (nn : ClassSys V).fl 2 = [1, 0] from rfl]
  simp only [ClassSys.fillL, dif_pos (show (1 : Nat) < 2 by omega),
    dif_pos (show (0 : Nat) < 2 by omega)]
  rfl

theorem nn_Ψ1 (v : Nat → V) :
    (nn : ClassSys V).Ψ 1 v = opAt (fun m => m = 1) (nnrd 1) ((nn : ClassSys V).T 0 v) := by
  unfold ClassSys.Ψ
  rw [show (nn : ClassSys V).fl 1 = [0] from rfl]
  simp only [ClassSys.fillL, dif_pos (show (0 : Nat) < 1 by omega)]
  rfl

theorem nn_Ψ0 (v : Nat → V) : (nn : ClassSys V).Ψ 0 v = opAt (fun m => m = 2) (nnrd 0) v := by
  unfold ClassSys.Ψ; rfl

theorem nn_T0_2 (u : Nat → V) : (nn : ClassSys V).T 0 u 2 = (nn : ClassSys V).car 0 u 2 := by
  rw [ClassSys.T_eq]; unfold cfix
  exact mixT_apply_pos (show ((nn : ClassSys V).grp 0) 2 from rfl)

theorem nn_T1_1 (u : Nat → V) : (nn : ClassSys V).T 1 u 1 = (nn : ClassSys V).car 1 u 1 := by
  rw [ClassSys.T_eq]; unfold cfix
  exact mixT_apply_pos (show ((nn : ClassSys V).grp 1) 1 from rfl)

theorem mem_image_pt {S x : V} : x ∈ˢ image (fun _ => (pt : V)) S ↔ x = pt ∧ ∃ y, y ∈ˢ S := by
  rw [mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨rfl, y, hy⟩
  · rintro ⟨rfl, y, hy⟩; exact ⟨y, hy, rfl⟩

theorem mem_ptOr {S x : V} : x ∈ˢ ptOr S ↔ x = pt := by
  unfold ptOr
  constructor
  · intro h
    rcases mem_binUnion.mp h with h | h
    · exact mem_unitSet_iff.mp h
    · exact (mem_image_pt.mp h).1
  · rintro rfl; exact mem_binUnion.mpr (Or.inl pt_mem_unitSet)

theorem nn_Ψ_app (b : Nat) (hb : b < 3) (v : Nat → V) (c : Nat) :
    app ((nn : ClassSys V).Ψ b v c) pt =
      if c = 2 - b then
        (if b = 0 then ptOr (sigmaPairs (hole 1 v) fun _ => hole 2 v)
         else if b = 1 then image (fun _ => pt) (app ((nn : ClassSys V).car 0 v 2) pt)
         else image (fun _ => pt) (app ((nn : ClassSys V).car 0 ((nn : ClassSys V).T 1 v) 2) pt))
      else empty := by
  match b, hb with
  | 0, _ =>
    rw [nn_Ψ0]
    by_cases hc : c = 2
    · rw [if_pos hc, app_opAt_pos (P := fun m => m = 2) hc]; rfl
    · rw [if_neg hc, app_opAt_neg (P := fun m => m = 2) hc]
  | 1, _ =>
    rw [nn_Ψ1]
    by_cases hc : c = 1
    · rw [if_pos hc, app_opAt_pos (P := fun m => m = 1) hc]
      show image (fun _ => pt) (app ((nn : ClassSys V).T 0 v 2) pt) = _
      rw [nn_T0_2]; rfl
    · rw [if_neg hc, app_opAt_neg (P := fun m => m = 1) hc]
  | 2, _ =>
    rw [nn_Ψ2]
    by_cases hc : c = 0
    · rw [if_pos hc, app_opAt_pos (P := fun m => m = 0) hc]
      show image (fun _ => pt) (app ((nn : ClassSys V).T 0 _ 2) pt) = _
      rw [nn_T0_2]; rfl
    · rw [if_neg hc, app_opAt_neg (P := fun m => m = 0) hc]

/-- **The fibre law** of every node's clause. -/
theorem kcl_fibre (b : Nat) (hb : b < 3) (u : Nat → V) (Y : Nat → V) (c : Nat) (t x : V)
    (ht : t ∈ˢ (is1 c : V)) :
    x ∈ˢ app ((kcl b).Φ u Y c) t ↔ ∃ j fs, (kcl b).Fits u Y t c j fs ∧ x = (kcl b).inj c j fs := by
  have htp := mem_unitSet_iff.mp ht
  subst htp
  show x ∈ˢ app ((nn : ClassSys V).Ψ b (vOf b u Y) c) pt ↔ ∃ j fs, kFits b u Y pt c j fs ∧ x = pt
  rw [nn_Ψ_app b hb]
  match b, hb with
  | 0, _ =>
    by_cases hc : c = 2
    · subst hc
      rw [if_pos (by decide : (2 : Nat) = 2 - 0), if_pos rfl, mem_ptOr]
      -- every major has the `nil` decoding (and possibly many `cons` ones)
      constructor
      · rintro rfl; exact ⟨0, [], ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩
      · rintro ⟨_, _, _, rfl⟩; rfl
    · rw [if_neg hc]
      exact ⟨fun h => absurd h (not_mem_empty _), fun ⟨_, _, ⟨h, _⟩, _⟩ => absurd h hc⟩
  | 1, _ =>
    by_cases hc : c = 1
    · subst hc
      rw [if_pos (by decide : (1 : Nat) = 2 - 1), if_neg (by decide : ¬ (1 : Nat) = 0), if_pos rfl,
        mem_image_pt]
      constructor
      · rintro ⟨rfl, l, hl⟩; exact ⟨0, [l], ⟨rfl, rfl, l, rfl, hl⟩, rfl⟩
      · rintro ⟨j, fs, ⟨-, rfl, l, rfl, hl⟩, rfl⟩; exact ⟨rfl, l, hl⟩
    · rw [if_neg hc]
      exact ⟨fun h => absurd h (not_mem_empty _), fun ⟨_, _, ⟨h, _⟩, _⟩ => absurd h hc⟩
  | 2, _ =>
    by_cases hc : c = 0
    · subst hc
      rw [if_pos (by decide : (0 : Nat) = 2 - 2), if_neg (by decide : ¬ (2 : Nat) = 0),
        if_neg (by decide : ¬ (2 : Nat) = 1), mem_image_pt]
      constructor
      · rintro ⟨rfl, l, hl⟩; exact ⟨0, [l], ⟨rfl, rfl, l, rfl, hl⟩, rfl⟩
      · rintro ⟨j, fs, ⟨-, rfl, l, rfl, hl⟩, rfl⟩; exact ⟨rfl, l, hl⟩
    · rw [if_neg hc]
      exact ⟨fun h => absurd h (not_mem_empty _), fun ⟨_, _, ⟨h, _⟩, _⟩ => absurd h hc⟩

/-- Every node's clause holds at every frame of the space (E1 at `w = 0`:
mono, (W) by the top tuple). -/
theorem kcl_ok {b : Nat} (hb : b < 3) {u : Nat → V} (hu : InTupleSpace 0 3 is1 u) :
    (kcl b).OkAt u where
  mono := (secOp_ok base0_mem ((nn : ClassSys V).Ψ_ok nn_flat b) hu).2.1
  closed := (nn : ClassSys V).closed nn_flat b hu
  fibre := fun X _ c _ t ht x => kcl_fibre b hb u X c t x ht

/-! ### The kit -/

theorem kAdm_space {b : Nat} {G : Nat → Nat → V → V → Prop} {u : Nat → V} (h : kAdm b G u) :
    InTupleSpace 0 3 is1 u :=
  match b, h with
  | 0, h => h.1
  | 1, h => h.1
  | _ + 2, h => h

theorem kfr_mem (b : Nat) : InTupleSpace 0 3 is1 (kfr b : Nat → V) :=
  match b with
  | 0 => lfpTuple_mem _ _ _ _
  | 1 => lfpTuple_mem _ _ _ _
  | _ + 2 => base0_mem

theorem nrmT_free2 (u : Nat → V) : nrmT ((nn : ClassSys V).free 2) base0 u = base0 := by
  funext m
  unfold nrmT
  exact mixT_apply_neg (G := (nn : ClassSys V).free 2) (by simp [nn])

/-- `classMono λ` at its free hole `z_τ` (position `1`). -/
theorem car0_mono {v v' : Nat → V} (hv : InTupleSpace 0 3 is1 v)
    (hv' : InTupleSpace 0 3 is1 v') (h : app (v 1) pt ⊆ˢ app (v' 1) pt) {l : V}
    (hl : l ∈ˢ app ((nn : ClassSys V).car 0 v 2) pt) :
    l ∈ˢ app ((nn : ClassSys V).car 0 v' 2) pt := by
  refine (nn : ClassSys V).car_mono nn_flat 0 hv hv' (fun m _ hf => ?_) 2
    (show (2 : Nat) < 3 by omega) pt pt_mem_unitSet l hl
  rcases hf with ⟨-, rfl⟩ | ⟨h1, -⟩
  · intro i hi
    rw [mem_unitSet_iff.mp hi]; exact h
  · exact absurd h1 (by decide)

theorem nn_trans : ∀ b, b < 3 → ∀ G : Nat → Nat → V → V → Prop,
    (∀ b' c t y, G b' c t y → y ∈ˢ app ((kcl b').carrier (kfr b') c) t) →
    ∀ ρ, kAdm b G ρ → ∀ Y, InTupleSpace 0 3 is1 Y →
    TupleLe 3 is1 Y ((kcl b).carrier (kfr b)) →
    ∀ t c j fs, c < 3 → kFits b ρ Y t c j fs →
      kFits b (kfr b) ((kcl b).carrier (kfr b)) t c j fs := by
  intro b hb G hG ρ hρ Y hY hle t c j fs _ hf
  have hρm := kAdm_space hρ
  match b, hb, hρ, hle, hf with
  | 0, _, hρ, hle, hf =>
    obtain ⟨rfl, hnil | ⟨rfl, a, l, rfl, ha, hl⟩⟩ := hf
    · exact ⟨rfl, Or.inl hnil⟩
    · exact ⟨rfl, Or.inr ⟨rfl, a, l, rfl, hG _ _ _ _ (hρ.2 a ha),
        hle 2 (by omega) pt pt_mem_unitSet l hl⟩⟩
  | 1, _, _, hle, hf =>
    obtain ⟨rfl, rfl, l, rfl, hl⟩ := hf
    refine ⟨rfl, rfl, l, rfl, ?_⟩
    refine car0_mono (vOf_mem hρm hY) (vOf_mem (kfr_mem 1) (lfpTuple_mem _ _ _ _)) ?_ hl
    rw [vOf_grp rfl, vOf_grp rfl]
    exact hle 1 (by omega) pt pt_mem_unitSet
  | 2, _, _, hle, hf =>
    obtain ⟨rfl, rfl, l, rfl, hl⟩ := hf
    refine ⟨rfl, rfl, l, rfl, ?_⟩
    have hT := (nn : ClassSys V).good nn_flat 1
    have hv : InTupleSpace 0 3 is1 (vOf 2 ρ Y) := vOf_mem hρm hY
    have hv' : InTupleSpace 0 3 is1 (vOf 2 (kfr 2) ((kcl 2 : SClause V (Nat → V)).carrier (kfr 2))) :=
      vOf_mem (kfr_mem 2) (lfpTuple_mem _ _ _ _)
    have hle' : TupleLe 3 is1 (vOf 2 ρ Y)
        (vOf 2 (kfr 2) ((kcl 2 : SClause V (Nat → V)).carrier (kfr 2))) := by
      unfold vOf
      rw [nrmT_free2, nrmT_free2]
      exact mixT_le2 (TupleLe.refl _ _ _) hle
    have hTle := hT.2.1 _ _ hv hv' hle'
    exact car0_mono (hT.1 _ hv) (hT.1 _ hv') (hTle 1 (show (1 : Nat) < 3 by omega) pt pt_mem_unitSet) hl

/-- **The member's call, at layer `1` of `extN`**: `Foo`'s field lands in
`λ` at the frame holding `τ`'s TRUE carrier at the member's stage `Y`. -/
theorem nnkit_member_call {G : Nat → Nat → V → V → Prop} {ρ Y : Nat → V}
    (hρ : InTupleSpace 0 3 is1 ρ) (hY : InTupleSpace 0 3 is1 Y) :
    kAdm 0 (extN 3 (kcl : Nat → SClause V (Nat → V)) (fun b => 2 - b) kAdm G 2 Y 1)
      ((nn : ClassSys V).T 1 (vOf 2 ρ Y)) := by
  have hv : InTupleSpace 0 3 is1 (vOf 2 ρ Y) := vOf_mem hρ hY
  refine ⟨((nn : ClassSys V).good nn_flat 1).1 _ hv, fun y hy => ?_⟩
  rw [nn_T1_1] at hy
  refine Or.inr ⟨by omega, by decide, show (1 : Nat) < 3 by omega, pt_mem_unitSet, vOf 2 ρ Y,
    ⟨hv, fun y' hy' => Or.inr ⟨rfl, show (0 : Nat) < 3 by omega, pt_mem_unitSet, ?_⟩⟩, hy⟩
  rw [vOf_grp rfl] at hy'
  exact hy'

theorem nn_calls : ∀ b, b < 3 → ∀ (G : Nat → Nat → V → V → Prop) ρ, kAdm b G ρ →
    ∀ Y, InTupleSpace 0 3 is1 Y →
    ∀ c t j fs, c < 3 → t ∈ˢ (is1 c : V) → kFits b ρ Y t c j fs →
    ∀ u, u ∈ˢ kpred ⟨b, c, t, j, fs⟩ → ∃ b' c' t' y, b' < 3 ∧ c' < 3 ∧
      t' ∈ˢ (is1 c' : V) ∧ u = nenc b' c' t' y ∧
      ((b' = b ∧ y ∈ˢ app (Y c') t') ∨ G b' c' t' y ∨
        (2 - b < 2 - b' ∧ ∃ n ρ', kAdm b' (extN 3 kcl (fun b => 2 - b) kAdm G b Y n) ρ' ∧
          y ∈ˢ app ((kcl b').carrier ρ' c') t')) := by
  intro b hb G ρ hρ Y hY c t j fs _ _ hf u hu
  have hρm := kAdm_space hρ
  match b, hb, hρ, hf with
  | 0, _, hρ, hf =>
    obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, a, l, rfl, ha, hl⟩⟩ := hf
    · exact absurd hu (not_mem_empty _)
    · rcases mem_upair.mp hu with rfl | rfl
      · exact ⟨1, 1, pt, a, by omega, by omega, pt_mem_unitSet, rfl, Or.inr (Or.inl (hρ.2 a ha))⟩
      · exact ⟨0, 2, pt, l, by omega, by omega, pt_mem_unitSet, rfl, Or.inl ⟨rfl, hl⟩⟩
  | 1, _, _, hf =>
    obtain ⟨rfl, rfl, l, rfl, hl⟩ := hf
    obtain rfl := mem_sing.mp hu
    -- `τ`'s `List` field: `λ` at the frame holding `τ`'s own stage (layer 0)
    refine ⟨0, 2, pt, l, by omega, by omega, pt_mem_unitSet, rfl, Or.inr (Or.inr
      ⟨by decide, 0, vOf 1 ρ Y, ⟨vOf_mem hρm hY, fun y hy => ?_⟩, hl⟩)⟩
    rw [vOf_grp rfl] at hy
    exact Or.inr ⟨rfl, show (1 : Nat) < 3 by omega, pt_mem_unitSet, hy⟩
  | 2, _, _, hf =>
    obtain ⟨rfl, rfl, l, rfl, hl⟩ := hf
    obtain rfl := mem_sing.mp hu
    exact ⟨0, 2, pt, l, by omega, by omega, pt_mem_unitSet, rfl, Or.inr (Or.inr
      ⟨by decide, 1, _, nnkit_member_call hρm hY, hl⟩)⟩

theorem nn_top : ∀ b, b < 3 → ∀ G : Nat → Nat → V → V → Prop,
    (∀ b' c t y, b' < 3 → 2 - b' < 2 - b → c < 3 → t ∈ˢ (is1 c : V) →
      y ∈ˢ app ((kcl b').carrier (kfr b') c) t → G b' c t y) →
    kAdm b G (kfr b) := by
  intro b hb G h
  match b, hb with
  | 0, _ => exact ⟨kfr_mem 0, fun y hy => h 1 1 pt y (by omega) (by omega) (by omega) pt_mem_unitSet hy⟩
  | 1, _ => exact ⟨kfr_mem 1, fun y hy => h 2 0 pt y (by omega) (by omega) (by omega) pt_mem_unitSet hy⟩
  | 2, _ => exact kfr_mem 2

/-- **The class kit at `Prop`, one node per class.** -/
noncomputable def nnkit : ClassKit V (Nat → V) where
  nC := 3
  cl := kcl
  fr := kfr
  dp := fun b => 2 - b
  D := 3
  hD := fun b _ => by omega
  Adm := kAdm
  pred := kpred
  ok := fun _ hb _ _ hρ => kcl_ok hb (kAdm_space hρ)
  trans := nn_trans
  calls := nn_calls
  top := nn_top

/-- **The majors' induction at `Prop`.** -/
theorem nnkit_ind : ∀ P : V → Prop,
    (∀ u, u ∈ˢ (nnkit : ClassKit V (Nat → V)).U →
      (∃ d, nnkit.Dec u d ∧ ∀ j, j ∈ˢ nnkit.pred d → P j) → P u) →
    ∀ u, u ∈ˢ (nnkit : ClassKit V (Nat → V)).U → P u :=
  nnkit.ind

/-- **Decodings are not unique at `Prop`**: at `λ`'s true frame, whenever
`τ`'s true carrier and `λ`'s own carrier are inhabited, the major
`nenc 0 2 pt pt` has the `nil` decoding and a `cons` decoding. -/
theorem nn_decodings_not_unique {a l : V}
    (ha : a ∈ˢ app ((kfr 0 : Nat → V) 1) pt)
    (hl : l ∈ˢ app ((nnkit : ClassKit V (Nat → V)).KT 0 2) pt) :
    (nnkit : ClassKit V (Nat → V)).Dec (nenc 0 2 pt pt) ⟨0, 2, pt, 0, []⟩ ∧
      (nnkit : ClassKit V (Nat → V)).Dec (nenc 0 2 pt pt) ⟨0, 2, pt, 1, [a, l]⟩ :=
  ⟨⟨show (0 : Nat) < 3 by omega, show (2 : Nat) < 3 by omega, pt_mem_unitSet, ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩,
    ⟨show (0 : Nat) < 3 by omega, show (2 : Nat) < 3 by omega, pt_mem_unitSet,
      ⟨rfl, Or.inr ⟨rfl, a, l, rfl, ha, hl⟩⟩, rfl⟩⟩

end ConLeche.SetTheory.ClassKitPropEx
