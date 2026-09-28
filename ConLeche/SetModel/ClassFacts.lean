module

public import ConLeche.SetModel.Access

@[expose] public section

/-!
# Class facts: monotonicity and accessibility of a class, by rank

The CLASSCHECK proof plan's class facts (`classMono`/`classAcc`, PROOFPLAN
§2.4/§3), at the set level: no `Expr`, no frames, no fullness, no Bekić.

**One valuation space.**  Every hole of the block — the members' and one
per class component — is a position `m < K` of ONE tuple space
(`InTupleSpace w K Is`).  A class `c` owns the positions `grp c` (its
group: the container's components at one key); `free c` are its FREE
holes (the member holes and its cyclic inner classes).  Its FLAT operator
`Φ c` reads the whole valuation (the abstracted crests' fields, T4 of the
plan: monotone, and accessible, in ALL holes at once — every hole ranges
over its whole space).

**The class, as a function of its free holes** (`cfix`, `ccar`).  At a
valuation `u`, class `c`'s carrier is the least tuple of
`Y ↦ Ψ (mixT (grp c) (nrmT (free c) u) Y)`: its own group is the lfp
variable, its free holes read `u`, everything else a fixed `base`, and
`Ψ` is `Φ c` after the COHERENT FILL (`fillL`): every class the
coherent valuation reads TRUE is spliced in, in order, as ITS carrier at
the valuation so far.  A class read true is strictly OLDER (smaller index)
— the definition (`ClassSys.T`) is by well-founded recursion on the class
index, which is exactly the plan's "strong induction on container age".

**The facts** (`ClassSys.good`), by strong induction on the index:
every `T c` (the valuation with `c`'s carrier spliced in) maps the space
into itself, is monotone, and at `w ≠ 0` is accessible with a bound in
`univ w` (`OpOk`).  The class's own lfp gets its closed tuple from
`closed_of_acc` (`w ≠ 0`) or `closedTuple_zero` (`w = 0`), its
monotonicity in the frame from leastness (`ccar_mono_free`: only the FREE
positions matter), its accessibility from `lfpP_acc_group` (`ccar_acc`)
— every hole ranges over its whole space, so no accessibility at a fixed
hole value is ever asked; a class read true enters by COMPOSITION
(`OpOk.comp`, `accRead_comp`).  The member block is a class like any
other (`ClassSys.closed`: its (W)).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## Operators on one tuple space: maps, monotone, accessible -/

section Alg

variable {w K : Nat} {Is : Nat → V}

theorem AccTuple.weaken {kI kO : Nat} {IsO : Nat → V} {Φ : (Nat → V) → Nat → V} {A B : V}
    (h : AccTuple w kI Is kO IsO Φ A) (hAB : A ⊆ˢ B) : AccTuple w kI Is kO IsO Φ B := by
  intro X hX m hm i hi x hx
  obtain ⟨C, g, hC, hg, hs⟩ := h X hX m hm i hi x hx
  exact ⟨C, g, Subset.trans hC hAB, hg, hs⟩

/-- **Composition** of accessible operators on one space. -/
theorem AccTuple.comp {Ψ Φ : (Nat → V) → Nat → V} {A1 A2 : V}
    (hΨ : AccTuple w K Is K Is Ψ A1) (hmaps : MapsTuple w K Is Ψ)
    (hΦ : AccTuple w K Is K Is Φ A2) :
    AccTuple w K Is K Is (fun X => Φ (Ψ X)) (sigmaPairs A2 fun _ => A1) := by
  intro X hX m hm i hi
  exact accRead_comp (G := fun Z => app (Φ Z m) i) hΨ hmaps
    (fun Z hZ x hx => hΦ Z hZ m hm i hi x hx) X hX

/-- The identity is accessible (one support item, the element itself). -/
theorem accTuple_id : AccTuple w K Is K Is (fun X => X) unitSet :=
  fun _ _ m hm i hi x hx => ⟨unitSet, fun _ => (m, i, x), Subset.refl _,
    fun _ _ => ⟨hm, hi, hx⟩, fun _ _ h => (h pt pt_mem_unitSet).2.2⟩

/-- A constant is accessible (empty support). -/
theorem accTuple_const (C : Nat → V) (A : V) : AccTuple w K Is K Is (fun _ => C) A :=
  fun _ _ _ _ _ _ _ hx => ⟨empty, fun _ => (0, empty, empty), empty_subset _,
    fun _ ha => absurd ha (not_mem_empty _), fun _ _ _ => hx⟩

/-- Two operators spliced along a group. -/
theorem accTuple_mixT {G : Nat → Prop} {Φ1 Φ2 : (Nat → V) → Nat → V} {A1 A2 : V}
    (h1 : AccTuple w K Is K Is Φ1 A1) (h2 : AccTuple w K Is K Is Φ2 A2) :
    AccTuple w K Is K Is (fun X => mixT G (Φ1 X) (Φ2 X)) (binUnion A1 A2) := by
  classical
  intro X hX m hm i hi x (hx : x ∈ˢ app (mixT G (Φ1 X) (Φ2 X) m) i)
  by_cases hG : G m
  · have e : ∀ Z, mixT G (Φ1 Z) (Φ2 Z) m = Φ2 Z m := fun Z => by unfold mixT; rw [if_pos hG]
    rw [e] at hx
    obtain ⟨B, g, hB, hg, hs⟩ := h2 X hX m hm i hi x hx
    exact ⟨B, g, fun a ha => mem_binUnion.mpr (Or.inr (hB a ha)), hg,
      fun X' hX' h' => show x ∈ˢ app (mixT G (Φ1 X') (Φ2 X') m) i by rw [e]; exact hs X' hX' h'⟩
  · have e : ∀ Z, mixT G (Φ1 Z) (Φ2 Z) m = Φ1 Z m := fun Z => by unfold mixT; rw [if_neg hG]
    rw [e] at hx
    obtain ⟨B, g, hB, hg, hs⟩ := h1 X hX m hm i hi x hx
    exact ⟨B, g, fun a ha => mem_binUnion.mpr (Or.inl (hB a ha)), hg,
      fun X' hX' h' => show x ∈ˢ app (mixT G (Φ1 X') (Φ2 X') m) i by rw [e]; exact hs X' hX' h'⟩

omit [SetTheory V] in
theorem mixT_apply_pos {G : Nat → Prop} {C Y : Nat → V} {m : Nat} (h : G m) : mixT G C Y m = Y m := by
  unfold mixT; rw [if_pos h]

omit [SetTheory V] in
theorem mixT_apply_neg {G : Nat → Prop} {C Y : Nat → V} {m : Nat} (h : ¬ G m) : mixT G C Y m = C m := by
  unfold mixT; rw [if_neg h]

/-- `mixT` is monotone in both tuples. -/
theorem mixT_le2 {G : Nat → Prop} {C C' Y Y' : Nat → V} (hC : TupleLe K Is C C')
    (hY : TupleLe K Is Y Y') : TupleLe K Is (mixT G C Y) (mixT G C' Y') := by
  intro m hm; unfold mixT; split
  · exact hY m hm
  · exact hC m hm

variable (w K Is) in
/-- **A good operator** on the valuation space: it maps the space into
itself, is monotone, and at a positive level is accessible with a bound
of the level. -/
def OpOk (Φ : (Nat → V) → Nat → V) : Prop :=
  MapsTuple w K Is Φ ∧ MonoTuple w K Is Φ ∧
    (w ≠ 0 → ∃ A, A ∈ˢ (univ w : V) ∧ AccTuple w K Is K Is Φ A)

theorem OpOk.id : OpOk w K Is (fun X => X) :=
  ⟨fun _ hX => hX, fun _ _ _ _ h => h, fun _ => ⟨unitSet, unitSet_mem_univ w, accTuple_id⟩⟩

theorem OpOk.const {C : Nat → V} (hC : InTupleSpace w K Is C) : OpOk w K Is (fun _ => C) :=
  ⟨fun _ _ => hC, fun _ _ _ _ _ => TupleLe.refl K Is C,
    fun _ => ⟨empty, empty_mem_univ w, accTuple_const C empty⟩⟩

theorem OpOk.comp {Ψ Φ : (Nat → V) → Nat → V} (hΨ : OpOk w K Is Ψ) (hΦ : OpOk w K Is Φ) :
    OpOk w K Is (fun X => Φ (Ψ X)) := by
  refine ⟨fun X hX => hΦ.1 _ (hΨ.1 X hX),
    fun X Y hX hY hXY => hΦ.2.1 _ _ (hΨ.1 X hX) (hΨ.1 Y hY) (hΨ.2.1 X Y hX hY hXY), fun hw => ?_⟩
  obtain ⟨A1, hA1, h1⟩ := hΨ.2.2 hw
  obtain ⟨A2, hA2, h2⟩ := hΦ.2.2 hw
  exact ⟨_, (univ_isTGUniverse hw).sigmaPairs_mem hA2 fun _ _ => hA1, h1.comp hΨ.1 h2⟩

theorem OpOk.mixT {G : Nat → Prop} {Φ1 Φ2 : (Nat → V) → Nat → V} (h1 : OpOk w K Is Φ1)
    (h2 : OpOk w K Is Φ2) : OpOk w K Is (fun X => mixT G (Φ1 X) (Φ2 X)) := by
  refine ⟨fun X hX => mixT_mem (h1.1 X hX) (h2.1 X hX),
    fun X Y hX hY hXY => mixT_le2 (h1.2.1 X Y hX hY hXY) (h2.2.1 X Y hX hY hXY), fun hw => ?_⟩
  obtain ⟨A1, hA1, a1⟩ := h1.2.2 hw
  obtain ⟨A2, hA2, a2⟩ := h2.2.2 hw
  exact ⟨_, (univ_isTGUniverse hw).binUnion_mem hA1 hA1 hA2, accTuple_mixT a1 a2⟩

/-- **(W) of a good operator**: at `w ≠ 0` by accessibility, at `w = 0`
the top tuple. -/
theorem OpOk.closed {Φ : (Nat → V) → Nat → V} (h : OpOk w K Is Φ) :
    ∃ L, IsClosedTuple w K Is Φ L := by
  by_cases hw : w = 0
  · subst hw; exact closedTuple_zero h.1
  · obtain ⟨A, hA, hacc⟩ := h.2.2 hw
    exact closed_of_acc hw hA h.1 hacc

end Alg

/-! ## A class at a frame: its carrier as a function of its free holes -/

section CFix

variable (w K : Nat) (Is : Nat → V) (G F : Nat → Prop) (base : Nat → V)
  (Ψ : (Nat → V) → Nat → V)

/-- The class's NORMALISED frame: `u` at the free positions, `base`
elsewhere. -/
noncomputable def nrmT (u : Nat → V) : Nat → V := mixT F base u

/-- The class's operator at the frame `u`: its group the lfp variable,
its free holes `u`, the rest `base`, then `Ψ` (the flat operator after
the coherent fill). -/
noncomputable def secOp (u : Nat → V) : (Nat → V) → Nat → V :=
  fun Y => Ψ (mixT G (nrmT F base u) Y)

/-- **The class's carrier at the frame `u`** — `T_c(ζ)` of the plan. -/
noncomputable def ccar (u : Nat → V) : Nat → V := lfpTuple w K Is (secOp G F base Ψ u)

/-- The frame with the class's group spliced in as its carrier: the
coherent fill's step. -/
noncomputable def cfix (u : Nat → V) : Nat → V := mixT G u (ccar w K Is G F base Ψ u)

variable {w K Is G F base Ψ}

theorem nrmT_mem (hbase : InTupleSpace w K Is base) {u : Nat → V} (hu : InTupleSpace w K Is u) :
    InTupleSpace w K Is (nrmT F base u) := mixT_mem hbase hu

theorem secOp_ok (hbase : InTupleSpace w K Is base) (hΨ : OpOk w K Is Ψ) {u : Nat → V}
    (hu : InTupleSpace w K Is u) : OpOk w K Is (secOp G F base Ψ u) :=
  OpOk.comp (Ψ := fun Y => mixT G (nrmT F base u) Y) (Φ := Ψ)
    (OpOk.mixT (G := G) (OpOk.const (nrmT_mem hbase hu)) OpOk.id) hΨ

/-- **(W) of the class at every frame** (the member block's (W) is the
case of the youngest class). -/
theorem secOp_closed (hbase : InTupleSpace w K Is base) (hΨ : OpOk w K Is Ψ) {u : Nat → V}
    (hu : InTupleSpace w K Is u) : ∃ L, IsClosedTuple w K Is (secOp G F base Ψ u) L :=
  (secOp_ok hbase hΨ hu).closed

/-- **`classMono`**: the carrier grows with the FREE holes (the other
positions of the frame are never read). -/
theorem ccar_mono_free (hbase : InTupleSpace w K Is base) (hΨ : OpOk w K Is Ψ)
    {u u' : Nat → V} (hu : InTupleSpace w K Is u) (hu' : InTupleSpace w K Is u')
    (hle : ∀ m, m < K → F m → FamLe (Is m) (u m) (u' m)) :
    TupleLe K Is (ccar w K Is G F base Ψ u) (ccar w K Is G F base Ψ u') := by
  have hok' := secOp_ok (G := G) (F := F) hbase hΨ hu'
  have hL' := lfpTuple_mem w K Is (secOp G F base Ψ u')
  have hcl' := lfpTuple_closed hok'.closed hok'.2.1
  refine lfpTuple_le ⟨hL', ?_⟩
  have hnrm : TupleLe K Is (nrmT F base u) (nrmT F base u') := by
    intro m hm; unfold nrmT mixT; split
    · exact hle m hm ‹_›
    · exact FamLe.refl _ _
  have h1 := hΨ.2.1 _ _ (mixT_mem (G := G) (nrmT_mem hbase hu) hL')
    (mixT_mem (G := G) (nrmT_mem hbase hu') hL') (mixT_le2 (G := G) hnrm (TupleLe.refl K Is _))
  exact fun m hm => (h1 m hm).trans (hcl' m hm)

/-- **`classAcc`**: the carrier is accessible in the frame, with the
bound `accPaths A` of the flat operator's bound `A` — by
`lfpP_acc_group` at the parameter "the frame", all holes free. -/
theorem ccar_acc (hbase : InTupleSpace w K Is base) (hΨ : OpOk w K Is Ψ)
    {A : V} (hacc : AccTuple w K Is K Is Ψ A) :
    AccTuple w K Is K Is (ccar w K Is G F base Ψ) (accPaths A) := by
  classical
  haveI : Nonempty (Nat × V × V) := ⟨(0, empty, empty)⟩
  have key := lfpP_acc_group (P := Nat → V) (O := Nat × V × V) (w := w) (kY := K)
    (IsY := fun _ => Is) (Sp := InTupleSpace w K Is) (Rp := fun _ _ => True)
    (HasP := fun p o => F o.1 ∧ InTup K Is p o) (G := fun _ => True)
    (Θ := secOp G F base Ψ) (A := fun _ => A)
    (fun _ _ _ _ _ => rfl)
    (fun p hp => secOp_closed hbase hΨ hp)
    (fun p hp => (secOp_ok hbase hΨ hp).2.1)
    (by
      intro p Y hp hY m hm _ i hi x hx
      have hv := mixT_mem (G := G) (nrmT_mem (F := F) hbase hp) hY
      obtain ⟨B, g, hB, hg, hs⟩ := hacc _ hv m hm i hi x hx
      refine ⟨sep B fun a => G (g a).1 ∨ F (g a).1,
        fun a => if G (g a).1 then .inr (g a) else .inl (g a),
        Subset.trans sep_subset hB, ?_, ?_⟩
      · intro a ha
        obtain ⟨haB, hGF⟩ := mem_sep.mp ha
        obtain ⟨h1, h2, h3⟩ := hg a haB
        by_cases hG : G (g a).1
        · simp only [hG, if_true, ItemIn]
          exact ⟨trivial, h1, h2, by rw [mixT_apply_pos hG] at h3; exact h3⟩
        · have hF := hGF.resolve_left hG
          simp only [hG, if_false, ItemIn]
          refine ⟨hF, h1, h2, ?_⟩
          rw [mixT_apply_neg hG] at h3
          unfold nrmT at h3
          rw [mixT_apply_pos hF] at h3
          exact h3
      · intro p' Y' _ hp' hY' h'
        refine hs _ (mixT_mem (nrmT_mem hbase hp') hY') fun a haB => ?_
        obtain ⟨h1, h2, h3⟩ := hg a haB
        by_cases hG : G (g a).1
        · have := h' a (mem_sep.mpr ⟨haB, Or.inl hG⟩)
          simp only [hG, if_true, ItemIn] at this
          exact ⟨h1, h2, by rw [mixT_apply_pos hG]; exact this.2.2.2⟩
        · by_cases hF : F (g a).1
          · have := h' a (mem_sep.mpr ⟨haB, Or.inr hF⟩)
            simp only [hG, if_false, ItemIn] at this
            refine ⟨h1, h2, ?_⟩
            rw [mixT_apply_neg hG]; unfold nrmT; rw [mixT_apply_pos hF]
            exact this.2.2.2
          · refine ⟨h1, h2, ?_⟩
            rw [mixT_apply_neg hG] at h3 ⊢
            unfold nrmT at h3 ⊢
            rw [mixT_apply_neg hF] at h3 ⊢
            exact h3)
  intro u hu m hm i hi x hx
  obtain ⟨B, g, hB, hg, hs⟩ := key u hu m hm trivial i hi x hx
  exact ⟨B, g, hB, fun b hb => (hg b hb).2, fun u' hu' h' =>
    hs u' trivial hu' fun b hb => ⟨(hg b hb).1, h' b hb⟩⟩

/-- **The class spliced into the frame is a good operator.** -/
theorem cfix_ok (hbase : InTupleSpace w K Is base) (hΨ : OpOk w K Is Ψ) :
    OpOk w K Is (cfix w K Is G F base Ψ) := by
  have hcar : OpOk w K Is (ccar w K Is G F base Ψ) := by
    refine ⟨fun u _ => lfpTuple_mem _ _ _ _, fun u u' hu hu' hle =>
      ccar_mono_free hbase hΨ hu hu' fun m hm _ => hle m hm, fun hw => ?_⟩
    obtain ⟨A, hA, hacc⟩ := hΨ.2.2 hw
    exact ⟨accPaths A, accPaths_mem hw hA, ccar_acc hbase hΨ hacc⟩
  exact OpOk.mixT (G := G) OpOk.id hcar

variable (w K Is G F base Ψ) in
/-- The class spliced into the frame at the positions `P` only (a fill
writes the class it reads coherently, not its whole group). -/
noncomputable def cfixP (P : Nat → Prop) (u : Nat → V) : Nat → V :=
  mixT P u (ccar w K Is G F base Ψ u)

/-- **… at any positions, a good operator.** -/
theorem cfixP_ok (P : Nat → Prop) (hbase : InTupleSpace w K Is base) (hΨ : OpOk w K Is Ψ) :
    OpOk w K Is (cfixP w K Is G F base Ψ P) := by
  have hcar : OpOk w K Is (ccar w K Is G F base Ψ) := by
    refine ⟨fun u _ => lfpTuple_mem _ _ _ _, fun u u' hu hu' hle =>
      ccar_mono_free hbase hΨ hu hu' fun m hm _ => hle m hm, fun hw => ?_⟩
    obtain ⟨A, hA, hacc⟩ := hΨ.2.2 hw
    exact ⟨accPaths A, accPaths_mem hw hA, ccar_acc hbase hΨ hacc⟩
  exact OpOk.mixT (G := P) OpOk.id hcar

end CFix

/-! ## A system of classes, by rank -/

/-- **A class system** over one valuation space: per class `c` its group
`grp c`, its free holes `free c`, its flat operator `Φ c` (the abstracted
crests' fields over the whole valuation) and its FILL LIST `fl c` — the
classes its coherent valuation reads, in splicing order — with a RANK
`rk` (the class check's order of coherent reads; by default the index,
E1's container age): only the fill entries of a smaller rank are
spliced, each at its positions `spl` (by default its group). -/
structure ClassSys (V : Type u) [SetTheory V] where
  w : Nat
  K : Nat
  Is : Nat → V
  base : Nat → V
  hbase : InTupleSpace w K Is base
  grp : Nat → Nat → Prop
  free : Nat → Nat → Prop
  Φ : Nat → (Nat → V) → Nat → V
  fl : Nat → List Nat
  rk : Nat → Nat := fun c => c
  spl : Nat → Nat → Prop := grp

namespace ClassSys

/-- The coherent fill along a list of classes. -/
noncomputable def fillL (T : Nat → (Nat → V) → Nat → V) : List Nat → (Nat → V) → Nat → V
  | [], v => v
  | d :: ds, v => fillL T ds (T d v)

variable (S : ClassSys V)

/-- **Class `c` spliced into a frame**, by well-founded recursion on the
class's rank (a class read coherently has a smaller one). -/
noncomputable def T : Nat → (Nat → V) → Nat → V
  | c => cfixP S.w S.K S.Is (S.grp c) (S.free c) S.base
      (fun v => S.Φ c (fillL (fun d => if _h : S.rk d < S.rk c then T d else fun v => v) (S.fl c) v))
      (S.spl c)
termination_by c => S.rk c

/-- Class `c`'s operator after the coherent fill. -/
noncomputable def Ψ (c : Nat) : (Nat → V) → Nat → V :=
  fun v => S.Φ c (fillL (fun d => if _h : S.rk d < S.rk c then S.T d else fun v => v) (S.fl c) v)

theorem T_eq (c : Nat) :
    S.T c = cfixP S.w S.K S.Is (S.grp c) (S.free c) S.base (S.Ψ c) (S.spl c) := by
  rw [T]; rfl

/-- **Class `c`'s carrier at a frame** (`T_c(ζ)`). -/
noncomputable def car (c : Nat) (u : Nat → V) : Nat → V :=
  ccar S.w S.K S.Is (S.grp c) (S.free c) S.base (S.Ψ c) u

theorem fillL_ok {T : Nat → (Nat → V) → Nat → V} (hT : ∀ d, OpOk S.w S.K S.Is (T d)) :
    ∀ ds, OpOk S.w S.K S.Is (fillL T ds)
  | [] => OpOk.id
  | d :: ds => (hT d).comp (fillL_ok hT ds)

/-- **The class facts, by age.**  If every class's flat operator is good,
every class spliced into the frame is good: it maps, is monotone, and is
accessible at `w ≠ 0` — composition through the older classes it reads
true, accessibility only ever over the whole space. -/
theorem good (hΦ : ∀ c, OpOk S.w S.K S.Is (S.Φ c)) : ∀ c, OpOk S.w S.K S.Is (S.T c) := by
  suffices h : ∀ r c, S.rk c = r → OpOk S.w S.K S.Is (S.T c) from fun c => h _ c rfl
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro c hr
    rw [T_eq]
    refine cfixP_ok _ S.hbase (OpOk.comp (Φ := S.Φ c)
      (Ψ := fillL (fun d => if _h : S.rk d < S.rk c then S.T d else fun v => v) (S.fl c))
      (S.fillL_ok (fun d => ?_) (S.fl c)) (hΦ c))
    by_cases h : S.rk d < S.rk c
    · simp only [dif_pos h]; exact ih _ (hr ▸ h) d rfl
    · simp only [dif_neg h]; exact OpOk.id

/-- Class `c`'s filled operator is good. -/
theorem Ψ_ok (hΦ : ∀ c, OpOk S.w S.K S.Is (S.Φ c)) (c : Nat) : OpOk S.w S.K S.Is (S.Ψ c) :=
  OpOk.comp (Φ := S.Φ c)
    (Ψ := fillL (fun d => if _h : S.rk d < S.rk c then S.T d else fun v => v) (S.fl c))
    (S.fillL_ok (fun d => by
    by_cases h : S.rk d < S.rk c
    · simp only [dif_pos h]; exact S.good hΦ d
    · simp only [dif_neg h]; exact OpOk.id) (S.fl c)) (hΦ c)

/-- **(W)** of every class (and the member block) at every frame. -/
theorem closed (hΦ : ∀ c, OpOk S.w S.K S.Is (S.Φ c)) (c : Nat) {u : Nat → V}
    (hu : InTupleSpace S.w S.K S.Is u) :
    ∃ L, IsClosedTuple S.w S.K S.Is (secOp (S.grp c) (S.free c) S.base (S.Ψ c) u) L :=
  secOp_closed S.hbase (S.Ψ_ok hΦ c) hu

/-- **`classMono`**, at the free holes. -/
theorem car_mono (hΦ : ∀ c, OpOk S.w S.K S.Is (S.Φ c)) (c : Nat) {u u' : Nat → V}
    (hu : InTupleSpace S.w S.K S.Is u) (hu' : InTupleSpace S.w S.K S.Is u')
    (hle : ∀ m, m < S.K → S.free c m → FamLe (S.Is m) (u m) (u' m)) :
    TupleLe S.K S.Is (S.car c u) (S.car c u') :=
  ccar_mono_free S.hbase (S.Ψ_ok hΦ c) hu hu' hle

/-- **`classAcc`**. -/
theorem car_acc (hΦ : ∀ c, OpOk S.w S.K S.Is (S.Φ c)) (hw : S.w ≠ 0) (c : Nat) :
    ∃ A, A ∈ˢ (univ S.w : V) ∧ AccTuple S.w S.K S.Is S.K S.Is (S.car c) A := by
  obtain ⟨A, hA, hacc⟩ := (S.Ψ_ok hΦ c).2.2 hw
  exact ⟨accPaths A, accPaths_mem hw hA, ccar_acc S.hbase (S.Ψ_ok hΦ c) hacc⟩

end ClassSys

end ConLeche.SetTheory
