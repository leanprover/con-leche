module

public import ConLeche.SetModel.ClassKit
public import ConLecheTests.ClassFactsTests

public section

/-!
# The class kit on F13 (CLASSCHECK experiment E2)

`ClassKit` (`ConLeche/SetModel/ClassKit.lean`) instantiated on F13
(`TL | node : List (RL TL)`, `RL α | node : α → List (RL α)`), one node per
class, over the class system `f13` of experiment E1
(`ConLecheTests/ClassFactsTests.lean`):

* nodes = classes: `0 = λ = List (RL TL)`, `1 = ρ = RL TL`, `2 = TL`; depth
  `2 - b` (older = deeper); a node's clause is its class's operator at a
  frame (`secOp`), its carrier `ccar`, frames are valuations;
* `trans` is E1's `classMono` (`car_mono`, at the free holes only) and the
  fill's monotonicity (`good`);
* `calls`: `λ`'s head is a parameter element (case 2), its tail its own;
  `ρ`'s `List` field lands in `λ` at the frame holding `ρ`'s own stage
  (case 3, layer 0 — the old kit's case); the member's field lands in `λ`
  at the frame holding `ρ`'s TRUE carrier at the member's stage — case 3
  at LAYER 1 of `extN` (`f13kit_member_call`), the call the old
  `NestKit.calls` could not express.

`f13kit_ind` is the majors' induction.
-/

namespace ConLeche.SetTheory.ClassKitEx

open ConLeche.SetTheory.ClassFactsEx

universe u

variable {V : Type u} [SetTheory V]

section F13

variable (w : Nat)

/-- A node's frame, read at its operator: the group from the stage, the
free holes from the frame, the rest `base0`. -/
noncomputable def vOf (b : Nat) (u Y : Nat → V) : Nat → V :=
  mixT ((f13 w : ClassSys V).grp b) (nrmT ((f13 w : ClassSys V).free b) base0 u) Y

/-- The spines: `λ`'s `nil`/`cons a l`, `ρ`'s `node a l`, `TL`'s `node l`. -/
def kFits : Nat → (Nat → V) → (Nat → V) → V → Nat → Nat → List V → Prop
  | 0, u, Y, _, c, j, fs => c = 2 ∧ ((j = 0 ∧ fs = []) ∨
      (j = 1 ∧ ∃ a l, fs = [a, l] ∧ a ∈ˢ app (u 1) pt ∧ l ∈ˢ app (Y 2) pt))
  | 1, u, Y, _, c, j, fs => c = 1 ∧ j = 0 ∧ ∃ a l, fs = [a, l] ∧ a ∈ˢ app (u 0) pt ∧
      l ∈ˢ app ((f13 w : ClassSys V).car 0 (vOf w 1 u Y) 2) pt
  | 2, u, Y, _, c, j, fs => c = 0 ∧ j = 0 ∧ ∃ l, fs = [l] ∧
      l ∈ˢ app ((f13 w : ClassSys V).car 0 ((f13 w : ClassSys V).T 1 (vOf w 2 u Y)) 2) pt
  | _, _, _, _, _, _, _ => False

/-- The injections. -/
noncomputable def kinj (c j : Nat) (fs : List V) : V :=
  if c = 2 ∧ j = 0 then nilV else
    match fs with
    | [a, l] => kpair pt (kpair a l)
    | [l] => kpair pt l
    | _ => empty

/-- Node `b`'s clause. -/
noncomputable def kcl (b : Nat) : SClause V (Nat → V) where
  w := w
  N := 3
  Is := is1
  Φ := fun u => secOp ((f13 w : ClassSys V).grp b) ((f13 w : ClassSys V).free b) base0
    ((f13 w : ClassSys V).Ψ b) u
  Fits := kFits w b
  inj := kinj

/-- The predecessors (the recursive calls' majors). -/
noncomputable def kpred (d : NDec V) : V :=
  match d.cls, d.fs with
  | 0, [a, l] => upair (nenc 1 1 pt a) (nenc 0 2 pt l)
  | 1, [a, l] => upair (nenc 2 0 pt a) (nenc 0 2 pt l)
  | 2, [l] => sing (nenc 0 2 pt l)
  | _, _ => empty

/-- The admissible frames: the free holes hold `G`-elements of the class
they are the hole of. -/
def kAdm : Nat → (Nat → Nat → V → V → Prop) → (Nat → V) → Prop
  | 0, G, u => InTupleSpace w 3 is1 u ∧ ∀ y, y ∈ˢ app (u 1) pt → G 1 1 pt y
  | 1, G, u => InTupleSpace w 3 is1 u ∧ ∀ y, y ∈ˢ app (u 0) pt → G 2 0 pt y
  | _, _, u => InTupleSpace w 3 is1 u

/-- The TRUE frames: `TL`'s is irrelevant (no free hole), `ρ`'s holds `TL`'s
carrier, `λ`'s holds `ρ`'s true carrier. -/
noncomputable def kfr : Nat → Nat → V
  | 0 => (f13 w : ClassSys V).car 1 ((f13 w : ClassSys V).car 2 base0)
  | 1 => (f13 w : ClassSys V).car 2 base0
  | _ => base0

/-! ### Reading the operators -/

variable {w}

theorem vOf_mem {b : Nat} {u Y : Nat → V} (hu : InTupleSpace w 3 is1 u)
    (hY : InTupleSpace w 3 is1 Y) : InTupleSpace w 3 is1 (vOf w b u Y) :=
  mixT_mem (nrmT_mem base0_mem hu) hY

theorem vOf_grp {b : Nat} {u Y : Nat → V} {m : Nat} (h : m = 2 - b) : vOf w b u Y m = Y m :=
  mixT_apply_pos (G := (f13 w : ClassSys V).grp b) h

theorem vOf_free {b : Nat} {u Y : Nat → V} {m : Nat} (hg : ¬ m = 2 - b)
    (hf : (b = 0 ∧ m = 1) ∨ (b = 1 ∧ m = 0)) : vOf w b u Y m = u m := by
  unfold vOf
  rw [mixT_apply_neg (G := (f13 w : ClassSys V).grp b) hg]
  exact mixT_apply_pos (G := (f13 w : ClassSys V).free b) hf

theorem mem_nilOr {S x : V} : x ∈ˢ nilOr S ↔ x = nilV ∨ ∃ p, p ∈ˢ S ∧ x = kpair pt p := by
  unfold nilOr
  rw [mem_binUnion, mem_sing, mem_image]

theorem mem_tagProd {A B x : V} :
    x ∈ˢ image (kpair pt) (sigmaPairs A fun _ => B) ↔ ∃ a l, a ∈ˢ A ∧ l ∈ˢ B ∧ x = kpair pt (kpair a l) := by
  rw [mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨a, ha, l, hl, rfl⟩ := mem_sigmaPairs.mp hp
    exact ⟨a, l, ha, hl, rfl⟩
  · rintro ⟨a, l, ha, hl, rfl⟩
    exact ⟨_, mem_sigmaPairs.mpr ⟨a, ha, l, hl, rfl⟩, rfl⟩

theorem kpair_pt_ne_nilV (p : V) : kpair pt p ≠ (nilV : V) := by
  intro h
  exact pt_ne_empty (kpair_inj h).1

theorem kinj_pair {c j : Nat} (h : ¬ (c = 2 ∧ j = 0)) (a l : V) :
    kinj c j [a, l] = kpair pt (kpair a l) := by
  unfold kinj; rw [if_neg h]

theorem kinj_one {c j : Nat} (h : ¬ (c = 2 ∧ j = 0)) (l : V) : kinj c j [l] = kpair pt l := by
  unfold kinj; rw [if_neg h]

theorem kinj_nil (fs : List V) : kinj 2 0 fs = nilV := by
  unfold kinj; rw [if_pos ⟨rfl, rfl⟩]

theorem f13_Ψ0_app (v : Nat → V) (c : Nat) :
    app ((f13 w : ClassSys V).Ψ 0 v c) pt =
      if c = 2 then nilOr (sigmaPairs (hole 1 v) fun _ => hole 2 v) else empty := by
  rw [f13_Ψ0]
  by_cases hc : c = 2
  · rw [if_pos hc, app_opAt_pos (P := fun m => m = 2) hc]; rfl
  · rw [if_neg hc, app_opAt_neg (P := fun m => m = 2) hc]

theorem f13_Ψ1_app (v : Nat → V) (c : Nat) :
    app ((f13 w : ClassSys V).Ψ 1 v c) pt =
      if c = 1 then image (kpair pt) (sigmaPairs (hole 0 v)
        fun _ => app ((f13 w : ClassSys V).car 0 v 2) pt) else empty := by
  by_cases hc : c = 1
  · subst hc; rw [if_pos rfl]; exact f13_rho_reads w v
  · rw [if_neg hc, f13_Ψ1, app_opAt_neg (P := fun m => m = 1) hc]

theorem f13_Ψ2_app (v : Nat → V) (c : Nat) :
    app ((f13 w : ClassSys V).Ψ 2 v c) pt =
      if c = 0 then image (kpair pt)
        (app ((f13 w : ClassSys V).car 0 ((f13 w : ClassSys V).T 1 v) 2) pt) else empty := by
  by_cases hc : c = 0
  · subst hc; rw [if_pos rfl]; exact f13_member_reads w v
  · rw [if_neg hc, f13_Ψ2, app_opAt_neg (P := fun m => m = 0) hc]

/-- **The fibre law** of every node's clause. -/
theorem kcl_fibre (b : Nat) (hb : b < 3) (u : Nat → V) (Y : Nat → V) (c : Nat) (t x : V)
    (ht : t ∈ˢ (is1 c : V)) :
    x ∈ˢ app ((kcl w b).Φ u Y c) t ↔ ∃ j fs, (kcl w b).Fits u Y t c j fs ∧ x = (kcl w b).inj c j fs := by
  have htp := mem_unitSet_iff.mp ht
  subst htp
  show x ∈ˢ app ((f13 w : ClassSys V).Ψ b (vOf w b u Y) c) pt ↔ ∃ j fs, kFits w b u Y pt c j fs ∧ x = kinj c j fs
  match b, hb with
  | 0, _ =>
    rw [f13_Ψ0_app]
    by_cases hc : c = 2
    · subst hc
      rw [if_pos rfl, mem_nilOr]
      unfold hole
      rw [vOf_free (by decide) (Or.inl ⟨rfl, rfl⟩), vOf_grp rfl]
      constructor
      · rintro (rfl | ⟨p, hp, rfl⟩)
        · exact ⟨0, [], ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, (kinj_nil _).symm⟩
        · obtain ⟨a, ha, l, hl, rfl⟩ := mem_sigmaPairs.mp hp
          exact ⟨1, [a, l], ⟨rfl, Or.inr ⟨rfl, a, l, rfl, ha, hl⟩⟩, (kinj_pair (by decide) a l).symm⟩
      · rintro ⟨j, fs, ⟨-, (⟨rfl, rfl⟩ | ⟨rfl, a, l, rfl, ha, hl⟩)⟩, rfl⟩
        · exact Or.inl (kinj_nil _)
        · refine Or.inr ⟨kpair a l, mem_sigmaPairs.mpr ⟨a, ha, l, hl, rfl⟩, kinj_pair (by decide) a l⟩
    · rw [if_neg hc]
      exact ⟨fun h => absurd h (not_mem_empty _), fun ⟨_, _, ⟨h, _⟩, _⟩ => absurd h hc⟩
  | 1, _ =>
    rw [f13_Ψ1_app]
    by_cases hc : c = 1
    · subst hc
      rw [if_pos rfl, mem_tagProd]
      unfold hole
      rw [vOf_free (by decide) (Or.inr ⟨rfl, rfl⟩)]
      constructor
      · rintro ⟨a, l, ha, hl, rfl⟩
        exact ⟨0, [a, l], ⟨rfl, rfl, a, l, rfl, ha, hl⟩, (kinj_pair (by decide) a l).symm⟩
      · rintro ⟨j, fs, ⟨-, rfl, a, l, rfl, ha, hl⟩, rfl⟩
        exact ⟨a, l, ha, hl, kinj_pair (by decide) a l⟩
    · rw [if_neg hc]
      exact ⟨fun h => absurd h (not_mem_empty _), fun ⟨_, _, ⟨h, _⟩, _⟩ => absurd h hc⟩
  | 2, _ =>
    rw [f13_Ψ2_app]
    by_cases hc : c = 0
    · subst hc
      rw [if_pos rfl, mem_image]
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨0, [l], ⟨rfl, rfl, l, rfl, hl⟩, (kinj_one (by decide) l).symm⟩
      · rintro ⟨j, fs, ⟨-, rfl, l, rfl, hl⟩, rfl⟩
        exact ⟨l, hl, kinj_one (by decide) l⟩
    · rw [if_neg hc]
      exact ⟨fun h => absurd h (not_mem_empty _), fun ⟨_, _, ⟨h, _⟩, _⟩ => absurd h hc⟩

theorem kcl_carrier (b : Nat) (u : Nat → V) : (kcl w b).carrier u = (f13 w : ClassSys V).car b u := by rfl

/-- Every node's clause holds at every frame of the space (E1: mono, (W)). -/
theorem kcl_ok (hw : w ≠ 0) {b : Nat} (hb : b < 3) {u : Nat → V} (hu : InTupleSpace w 3 is1 u) :
    (kcl w b).OkAt u where
  mono := (secOp_ok base0_mem ((f13 w : ClassSys V).Ψ_ok (f13_flat hw) b) hu).2.1
  closed := (f13 w : ClassSys V).closed (f13_flat hw) b hu
  fibre := fun X _ c _ t ht x => kcl_fibre b hb u X c t x ht

/-! ### The kit -/

theorem kAdm_space {b : Nat} {G : Nat → Nat → V → V → Prop} {u : Nat → V} (h : kAdm w b G u) :
    InTupleSpace w 3 is1 u :=
  match b, h with
  | 0, h => h.1
  | 1, h => h.1
  | _ + 2, h => h

theorem kfr_mem (b : Nat) : InTupleSpace w 3 is1 (kfr w b : Nat → V) :=
  match b with
  | 0 => lfpTuple_mem _ _ _ _
  | 1 => lfpTuple_mem _ _ _ _
  | _ + 2 => base0_mem

theorem nrmT_free2 (u : Nat → V) : nrmT ((f13 w : ClassSys V).free 2) base0 u = base0 := by
  funext m
  unfold nrmT
  exact mixT_apply_neg (G := (f13 w : ClassSys V).free 2) (by simp [f13])

/-- `classMono λ` at its free hole `z_ρ` (position `1`). -/
theorem car0_mono (hw : w ≠ 0) {v v' : Nat → V} (hv : InTupleSpace w 3 is1 v)
    (hv' : InTupleSpace w 3 is1 v') (h : app (v 1) pt ⊆ˢ app (v' 1) pt) {l : V}
    (hl : l ∈ˢ app ((f13 w : ClassSys V).car 0 v 2) pt) :
    l ∈ˢ app ((f13 w : ClassSys V).car 0 v' 2) pt := by
  refine (f13 w : ClassSys V).car_mono (f13_flat hw) 0 hv hv' (fun m _ hf => ?_) 2 (show (2 : Nat) < 3 by omega) pt
    pt_mem_unitSet l hl
  rcases hf with ⟨-, rfl⟩ | ⟨h1, -⟩
  · intro i hi
    rw [mem_unitSet_iff.mp hi]; exact h
  · exact absurd h1 (by decide)

theorem f13_trans (hw : w ≠ 0) : ∀ b, b < 3 → ∀ G : Nat → Nat → V → V → Prop,
    (∀ b' c t y, G b' c t y → y ∈ˢ app ((kcl w b').carrier (kfr w b') c) t) →
    ∀ ρ, kAdm w b G ρ → ∀ Y, InTupleSpace w 3 is1 Y →
    TupleLe 3 is1 Y ((kcl w b).carrier (kfr w b)) →
    ∀ t c j fs, c < 3 → kFits w b ρ Y t c j fs →
      kFits w b (kfr w b) ((kcl w b).carrier (kfr w b)) t c j fs := by
  intro b hb G hG ρ hρ Y hY hle t c j fs _ hf
  have hρm := kAdm_space hρ
  match b, hb, hρ, hle, hf with
  | 0, _, hρ, hle, hf =>
    obtain ⟨rfl, hnil | ⟨rfl, a, l, rfl, ha, hl⟩⟩ := hf
    · exact ⟨rfl, Or.inl hnil⟩
    · exact ⟨rfl, Or.inr ⟨rfl, a, l, rfl, hG _ _ _ _ (hρ.2 a ha),
        hle 2 (by omega) pt pt_mem_unitSet l hl⟩⟩
  | 1, _, hρ, hle, hf =>
    obtain ⟨rfl, rfl, a, l, rfl, ha, hl⟩ := hf
    refine ⟨rfl, rfl, a, l, rfl, hG _ _ _ _ (hρ.2 a ha), ?_⟩
    refine car0_mono hw (vOf_mem hρm hY) (vOf_mem (kfr_mem 1) (lfpTuple_mem _ _ _ _)) ?_ hl
    rw [vOf_grp rfl, vOf_grp rfl]
    exact hle 1 (by omega) pt pt_mem_unitSet
  | 2, _, _, hle, hf =>
    obtain ⟨rfl, rfl, l, rfl, hl⟩ := hf
    refine ⟨rfl, rfl, l, rfl, ?_⟩
    have hT := ((f13 w : ClassSys V).good (f13_flat hw) 1)
    have hv : InTupleSpace w 3 is1 (vOf w 2 ρ Y) := vOf_mem hρm hY
    have hv' : InTupleSpace w 3 is1 (vOf w 2 (kfr w 2) ((kcl w 2 : SClause V (Nat → V)).carrier (kfr w 2))) :=
      vOf_mem (kfr_mem 2) (lfpTuple_mem _ _ _ _)
    have hle' : TupleLe 3 is1 (vOf w 2 ρ Y) (vOf w 2 (kfr w 2) ((kcl w 2 : SClause V (Nat → V)).carrier (kfr w 2))) := by
      unfold vOf
      rw [nrmT_free2, nrmT_free2]
      exact mixT_le2 (TupleLe.refl _ _ _) hle
    have hTle := hT.2.1 _ _ hv hv' hle'
    exact car0_mono hw (hT.1 _ hv) (hT.1 _ hv') (hTle 1 (show (1 : Nat) < 3 by omega) pt pt_mem_unitSet) hl

/-- **The member's call, at layer `1` of `extN`**: `TL`'s field lands in
`λ` at the frame holding `ρ`'s TRUE carrier at the member's stage `Y`; those
elements are `ρ`'s at a frame admissible for layer `0` (they hold `Y`). -/
theorem f13kit_member_call (hw : w ≠ 0) {G : Nat → Nat → V → V → Prop} {ρ Y : Nat → V}
    (hρ : InTupleSpace w 3 is1 ρ) (hY : InTupleSpace w 3 is1 Y) :
    kAdm w 0 (extN 3 (kcl w : Nat → SClause V (Nat → V)) (fun b => 2 - b) (kAdm w) G 2 Y 1)
      ((f13 w : ClassSys V).T 1 (vOf w 2 ρ Y)) := by
  have hv : InTupleSpace w 3 is1 (vOf w 2 ρ Y) := vOf_mem hρ hY
  refine ⟨((f13 w : ClassSys V).good (f13_flat hw) 1).1 _ hv, fun y hy => ?_⟩
  rw [f13_T1_1] at hy
  refine Or.inr ⟨by omega, by decide, show (1 : Nat) < 3 by omega, pt_mem_unitSet, vOf w 2 ρ Y,
    ⟨hv, fun y' hy' => Or.inr ⟨rfl, show (0 : Nat) < 3 by omega, pt_mem_unitSet, ?_⟩⟩, hy⟩
  rw [vOf_grp rfl] at hy'
  exact hy'

theorem f13_calls (hw : w ≠ 0) : ∀ b, b < 3 → ∀ (G : Nat → Nat → V → V → Prop) ρ, kAdm w b G ρ →
    ∀ Y, InTupleSpace w 3 is1 Y →
    ∀ c t j fs, c < 3 → t ∈ˢ (is1 c : V) → kFits w b ρ Y t c j fs →
    ∀ u, u ∈ˢ kpred ⟨b, c, t, j, fs⟩ → ∃ b' c' t' y, b' < 3 ∧ c' < 3 ∧
      t' ∈ˢ (is1 c' : V) ∧ u = nenc b' c' t' y ∧
      ((b' = b ∧ y ∈ˢ app (Y c') t') ∨ G b' c' t' y ∨
        (2 - b < 2 - b' ∧ ∃ n ρ', kAdm w b' (extN 3 (kcl w) (fun b => 2 - b) (kAdm w) G b Y n) ρ' ∧
          y ∈ˢ app ((kcl w b').carrier ρ' c') t')) := by
  intro b hb G ρ hρ Y hY c t j fs _ _ hf u hu
  have hρm := kAdm_space hρ
  match b, hb, hρ, hf with
  | 0, _, hρ, hf =>
    obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, a, l, rfl, ha, hl⟩⟩ := hf
    · exact absurd hu (not_mem_empty _)
    · rcases mem_upair.mp hu with rfl | rfl
      · exact ⟨1, 1, pt, a, by omega, by omega, pt_mem_unitSet, rfl, Or.inr (Or.inl (hρ.2 a ha))⟩
      · exact ⟨0, 2, pt, l, by omega, by omega, pt_mem_unitSet, rfl, Or.inl ⟨rfl, hl⟩⟩
  | 1, _, hρ, hf =>
    obtain ⟨rfl, rfl, a, l, rfl, ha, hl⟩ := hf
    rcases mem_upair.mp hu with rfl | rfl
    · exact ⟨2, 0, pt, a, by omega, by omega, pt_mem_unitSet, rfl, Or.inr (Or.inl (hρ.2 a ha))⟩
    · -- `ρ`'s `List` field: `λ` at the frame holding `ρ`'s own stage (layer 0)
      refine ⟨0, 2, pt, l, by omega, by omega, pt_mem_unitSet, rfl, Or.inr (Or.inr
        ⟨by decide, 0, vOf w 1 ρ Y, ⟨vOf_mem hρm hY, fun y hy => ?_⟩, hl⟩)⟩
      rw [vOf_grp rfl] at hy
      exact Or.inr ⟨rfl, show (1 : Nat) < 3 by omega, pt_mem_unitSet, hy⟩
  | 2, _, _, hf =>
    obtain ⟨rfl, rfl, l, rfl, hl⟩ := hf
    obtain rfl := mem_sing.mp hu
    exact ⟨0, 2, pt, l, by omega, by omega, pt_mem_unitSet, rfl, Or.inr (Or.inr
      ⟨by decide, 1, _, f13kit_member_call hw hρm hY, hl⟩)⟩

theorem f13_top : ∀ b, b < 3 → ∀ G : Nat → Nat → V → V → Prop,
    (∀ b' c t y, b' < 3 → 2 - b' < 2 - b → c < 3 → t ∈ˢ (is1 c : V) →
      y ∈ˢ app ((kcl w b').carrier (kfr w b') c) t → G b' c t y) →
    kAdm w b G (kfr w b) := by
  intro b hb G h
  match b, hb with
  | 0, _ => exact ⟨kfr_mem 0, fun y hy => h 1 1 pt y (by omega) (by omega) (by omega) pt_mem_unitSet hy⟩
  | 1, _ => exact ⟨kfr_mem 1, fun y hy => h 2 0 pt y (by omega) (by omega) (by omega) pt_mem_unitSet hy⟩
  | 2, _ => exact kfr_mem 2

/-- **E2 on F13: the class kit, one node per class.** -/
noncomputable def f13kit (hw : w ≠ 0) : ClassKit V (Nat → V) where
  nC := 3
  cl := kcl w
  fr := kfr w
  dp := fun b => 2 - b
  D := 3
  hD := fun b _ => by omega
  Adm := kAdm w
  pred := kpred
  ok := fun _ hb _ _ hρ => kcl_ok hw hb (kAdm_space hρ)
  trans := f13_trans hw
  calls := f13_calls hw
  top := f13_top

/-- **The majors' induction on F13.** -/
theorem f13kit_ind (hw : w ≠ 0) : ∀ P : V → Prop,
    (∀ u, u ∈ˢ (f13kit hw : ClassKit V (Nat → V)).U →
      (∃ d, (f13kit hw).Dec u d ∧ ∀ j, j ∈ˢ (f13kit hw).pred d → P j) → P u) →
    ∀ u, u ∈ˢ (f13kit hw : ClassKit V (Nat → V)).U → P u :=
  (f13kit hw).ind

end F13

end ConLeche.SetTheory.ClassKitEx
