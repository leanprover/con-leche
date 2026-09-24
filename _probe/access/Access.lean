import ConLeche.SetTheory.Derive.LfpTuple
import ConLeche.SetTheory.Derive.Universe
import ConLeche.SetTheory.Derive.Sigma
import ConLeche.SetModel.Iter

/-!
# Lane ACCESS (spike): (W) from accessibility, ordinal-free

`Acc w kI IsI kO IsO Φ A`: every element of an output fibre of `Φ X`
has a SUPPORT in `X` indexed by a subset of the FIXED set `A` (at most
`A`-many elements of `X`'s fibres) such that the element is in `Φ X'`
for EVERY tuple `X'` of the space containing them.  The bound must be
uniform: "every element has SOME small support" (κ-accessibility) is
too weak — `Φ X = {∅} ∪ {x ∪ {x}} ∪ {⋃ s | s ⊆ X small}` has the
universe's ordinals as its least fixed point.

`closed_of_acc`: at `w ≠ 0`, an `A`-accessible `Φ` with `A ∈ univ w`
that maps the tuple space into itself has a closed tuple — no
monotonicity, no ordinals, no cardinals.  Iteration runs along Lean-level
Brouwer trees `BT` (`node : (V → BT) → BT`); the union over all trees is
made small by coding a tree as its set of `A`-paths (a subset of the
small set `pathsA A`), on which the stage depends only.
-/

namespace ConLeche.SetTheory

open ConLeche.SetTheory.Tower (natUnion mem_natUnion natUnion_mem_univ_pos)

universe u

variable {V : Type u} [SetTheory V]

/-! ## The notion -/

/-- An occurrence `(m, i, y)` is an element of the tuple `X`. -/
def InTup (k : Nat) (Is X : Nat → V) (t : Nat × V × V) : Prop :=
  t.1 < k ∧ t.2.1 ∈ˢ Is t.1 ∧ t.2.2 ∈ˢ app (X t.1) t.2.1

/-- **`A`-accessibility** of an operator from `kI`-tuples over `IsI` to
`kO`-tuples over `IsO`. -/
def Acc (w kI : Nat) (IsI : Nat → V) (kO : Nat) (IsO : Nat → V)
    (Φ : (Nat → V) → Nat → V) (A : V) : Prop :=
  ∀ X, InTupleSpace w kI IsI X → ∀ m, m < kO → ∀ i, i ∈ˢ IsO m → ∀ x, x ∈ˢ app (Φ X m) i →
    ∃ (B : V) (g : V → Nat × V × V), B ⊆ˢ A ∧ (∀ a, a ∈ˢ B → InTup kI IsI X (g a)) ∧
      ∀ X', InTupleSpace w kI IsI X' → (∀ a, a ∈ˢ B → InTup kI IsI X' (g a)) →
        x ∈ˢ app (Φ X' m) i

theorem Acc.mono_A {w kI kO : Nat} {IsI IsO : Nat → V} {Φ : (Nat → V) → Nat → V} {A A' : V}
    (h : Acc w kI IsI kO IsO Φ A) (hA : A ⊆ˢ A') : Acc w kI IsI kO IsO Φ A' := by
  intro X hX m hm i hi x hx
  obtain ⟨B, g, hB, hg, hs⟩ := h X hX m hm i hi x hx
  exact ⟨B, g, Subset.trans hB hA, hg, hs⟩

/-! ## Paths over `A` -/

/-- Paths of length `n` over `A`: nested pairs, `pt` the empty path. -/
noncomputable def pathsN (A : V) : Nat → V
  | 0 => unitSet
  | n + 1 => sigmaPairs A fun _ => pathsN A n

/-- All finite paths over `A`. -/
noncomputable def pathsA (A : V) : V := natUnion (pathsN A)

theorem pt_mem_pathsA (A : V) : (pt : V) ∈ˢ pathsA A :=
  mem_natUnion.mpr ⟨0, pt_mem_unitSet⟩

theorem kpair_mem_pathsA {A a p : V} (ha : a ∈ˢ A) (hp : p ∈ˢ pathsA A) :
    kpair a p ∈ˢ pathsA A := by
  obtain ⟨n, hn⟩ := mem_natUnion.mp hp
  exact mem_natUnion.mpr ⟨n + 1, mem_sigmaPairs.mpr ⟨a, ha, p, hn, rfl⟩⟩

theorem pathsA_mem {w : Nat} (hw : w ≠ 0) {A : V} (hA : A ∈ˢ (univ w : V)) :
    pathsA A ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  refine natUnion_mem_univ_pos hw fun n => ?_
  induction n with
  | zero => exact unitSet_mem_univ w
  | succ n ih => exact hU.sigmaPairs_mem hA fun _ _ => ih

/-! ## Brouwer trees and stages -/

/-- Lean-level Brouwer trees branching over `V`. -/
inductive BT (V : Type u) : Type u
  | leaf : BT V
  | node : (V → BT V) → BT V

section Iter

variable (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) (A : V)

/-- The empty tuple. -/
noncomputable def emptyTup : Nat → V := fun m => graph (fun _ => empty) (Is m)

/-- The fibrewise union of an `A`-indexed family of tuples. -/
noncomputable def unionTup (F : V → Nat → V) : Nat → V :=
  fun m => graph (fun i => sUnion (image (fun a => app (F a m) i) A)) (Is m)

/-- The stage at a tree: `Φ` of the union of the subtrees' stages. -/
noncomputable def stage : BT V → Nat → V
  | .leaf => emptyTup Is
  | .node f => Φ (unionTup Is A fun a => stage (f a))

/-- A tree's code: its set of `A`-paths. -/
noncomputable def code : BT V → V
  | .leaf => empty
  | .node f => binUnion unitSet (sUnion (image (fun a => image (kpair a) (code (f a))) A))

/-- The chosen tree of a code. -/
noncomputable def pick (c : V) : BT V :=
  open Classical in if h : ∃ T, code A T = c then Classical.choose h else .leaf

/-- **The limit tuple**: the union of the stages over all codes. -/
noncomputable def limTup : Nat → V :=
  fun m => graph (fun i => sUnion (image (fun c => app (stage Is Φ A (pick A c) m) i)
    (power (pathsA A)))) (Is m)

variable {w k Is Φ A}

theorem mem_code_node {f : V → BT V} {p : V} :
    p ∈ˢ code A (.node f) ↔ p = pt ∨ ∃ a, a ∈ˢ A ∧ ∃ q, q ∈ˢ code A (f a) ∧ p = kpair a q := by
  simp only [code]
  rw [mem_binUnion, mem_unitSet_iff, mem_sUnion]
  constructor
  · rintro (h | ⟨s, hs, hp⟩)
    · exact Or.inl h
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp hs
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
      exact Or.inr ⟨a, ha, q, hq, rfl⟩
  · rintro (h | ⟨a, ha, q, hq, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, mem_image.mpr ⟨a, ha, rfl⟩, mem_image.mpr ⟨q, hq, rfl⟩⟩

theorem code_sub : ∀ T : BT V, code A T ⊆ˢ pathsA A
  | .leaf => by simp only [code]; exact empty_subset _
  | .node f => by
    intro p hp
    rcases mem_code_node.mp hp with rfl | ⟨a, ha, q, hq, rfl⟩
    · exact pt_mem_pathsA A
    · exact kpair_mem_pathsA ha (code_sub (f a) q hq)

/-- The stage depends on the tree only through its code. -/
theorem stage_eq_of_code : ∀ T T' : BT V, code A T = code A T' →
    stage Is Φ A T = stage Is Φ A T'
  | .leaf, .leaf, _ => rfl
  | .leaf, .node f, h => by
    exfalso
    have : (pt : V) ∈ˢ code A (.node f) := mem_code_node.mpr (Or.inl rfl)
    rw [← h] at this
    simp only [code] at this
    exact not_mem_empty _ this
  | .node f, .leaf, h => by
    exfalso
    have : (pt : V) ∈ˢ code A (.node f) := mem_code_node.mpr (Or.inl rfl)
    rw [h] at this
    simp only [code] at this
    exact not_mem_empty _ this
  | .node f, .node f', h => by
    have hsub : ∀ a, a ∈ˢ A → code A (f a) = code A (f' a) := by
      intro a ha
      apply Subset.antisymm
      · intro q hq
        have : kpair a q ∈ˢ code A (.node f') := h ▸ mem_code_node.mpr (Or.inr ⟨a, ha, q, hq, rfl⟩)
        rcases mem_code_node.mp this with h1 | ⟨a', _, q', hq', h2⟩
        · exact absurd h1.symm (pt_ne_kpair a q)
        · obtain ⟨rfl, rfl⟩ := kpair_inj h2; exact hq'
      · intro q hq
        have : kpair a q ∈ˢ code A (.node f) := h ▸ mem_code_node.mpr (Or.inr ⟨a, ha, q, hq, rfl⟩)
        rcases mem_code_node.mp this with h1 | ⟨a', _, q', hq', h2⟩
        · exact absurd h1.symm (pt_ne_kpair a q)
        · obtain ⟨rfl, rfl⟩ := kpair_inj h2; exact hq'
    simp only [stage]
    congr 1
    funext m
    unfold unionTup
    congr 1
    funext i
    congr 1
    exact image_congr fun a ha => by
      show app (stage Is Φ A (f a) m) i = app (stage Is Φ A (f' a) m) i
      rw [stage_eq_of_code (f a) (f' a) (hsub a ha)]

theorem emptyTup_mem : InTupleSpace w k Is (emptyTup Is) :=
  fun _ _ => graph_mem_famSpace fun _ _ => empty_mem_univ w

theorem stage_mem (hw : w ≠ 0) (hA : A ∈ˢ (univ w : V)) (hmaps : MapsTuple w k Is Φ) :
    ∀ T : BT V, InTupleSpace w k Is (stage Is Φ A T)
  | .leaf => emptyTup_mem
  | .node f => by
    simp only [stage]
    refine hmaps _ fun m hm => graph_mem_famSpace fun i hi => ?_
    exact (univ_isTGUniverse hw).famUnion_mem hA fun a _ =>
      famSpace_app (stage_mem hw hA hmaps (f a) m hm) hi

theorem mem_limTup {m : Nat} {i y : V} (hi : i ∈ˢ Is m) :
    y ∈ˢ app (limTup Is Φ A m) i ↔ ∃ T : BT V, y ∈ˢ app (stage Is Φ A T m) i := by
  unfold limTup
  rw [app_graph hi, mem_sUnion]
  constructor
  · rintro ⟨s, hs, hy⟩
    obtain ⟨c, -, rfl⟩ := mem_image.mp hs
    exact ⟨_, hy⟩
  · rintro ⟨T, hT⟩
    refine ⟨_, mem_image.mpr ⟨code A T, mem_power.mpr (code_sub T), rfl⟩, ?_⟩
    have hex : ∃ T', code A T' = code A T := ⟨T, rfl⟩
    have : pick A (code A T) = Classical.choose hex := by unfold pick; exact dif_pos hex
    rw [this, stage_eq_of_code _ _ (Classical.choose_spec hex)]
    exact hT

theorem limTup_mem (hw : w ≠ 0) (hA : A ∈ˢ (univ w : V)) (hmaps : MapsTuple w k Is Φ) :
    InTupleSpace w k Is (limTup Is Φ A) := by
  intro m hm
  refine graph_mem_famSpace fun i hi => ?_
  have hU := univ_isTGUniverse (V := V) hw
  exact hU.famUnion_mem (hU.power_mem (pathsA_mem hw hA)) fun c _ =>
    famSpace_app (stage_mem hw hA hmaps _ m hm) hi

theorem mem_unionTup {F : V → Nat → V} {m : Nat} {i y : V} (hi : i ∈ˢ Is m) :
    y ∈ˢ app (unionTup Is A F m) i ↔ ∃ a, a ∈ˢ A ∧ y ∈ˢ app (F a m) i := by
  unfold unionTup
  rw [app_graph hi, mem_sUnion]
  constructor
  · rintro ⟨s, hs, hy⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hs
    exact ⟨a, ha, hy⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨_, mem_image.mpr ⟨a, ha, rfl⟩, hy⟩

/-- **(W) from accessibility.**  At a positive level, an operator that
maps the tuple space into itself and is `A`-accessible for a set `A` of
the level has a closed tuple.  No monotonicity is used. -/
theorem closed_of_acc (hw : w ≠ 0) (hA : A ∈ˢ (univ w : V)) (hmaps : MapsTuple w k Is Φ)
    (hacc : Acc w k Is k Is Φ A) : ∃ L, IsClosedTuple w k Is Φ L := by
  refine ⟨limTup Is Φ A, limTup_mem hw hA hmaps, ?_⟩
  intro m hm i hi x hx
  obtain ⟨B, g, hBA, hgL, hsupp⟩ := hacc _ (limTup_mem hw hA hmaps) m hm i hi x hx
  -- every support element lies in some stage: choose its tree
  have hT : ∀ a, a ∈ˢ B → ∃ T : BT V, (g a).2.2 ∈ˢ app (stage Is Φ A T (g a).1) (g a).2.1 :=
    fun a ha => (mem_limTup (hgL a ha).2.1).mp (hgL a ha).2.2
  classical
  let f : V → BT V := fun a => if h : a ∈ˢ B then Classical.choose (hT a h) else .leaf
  have hstage : x ∈ˢ app (stage Is Φ A (.node f) m) i := by
    simp only [stage]
    refine hsupp _ (stage_mem hw hA hmaps (.node f) |> fun _ => ?_) ?_
    · intro m' hm'
      refine graph_mem_famSpace fun i' hi' => ?_
      exact (univ_isTGUniverse hw).famUnion_mem hA fun a _ =>
        famSpace_app (stage_mem hw hA hmaps (f a) m' hm') hi'
    · intro a ha
      refine ⟨(hgL a ha).1, (hgL a ha).2.1, (mem_unionTup (hgL a ha).2.1).mpr ⟨a, hBA a ha, ?_⟩⟩
      have : f a = Classical.choose (hT a ha) := dif_pos ha
      rw [this]
      exact Classical.choose_spec (hT a ha)
  exact (mem_limTup hi).mpr ⟨_, hstage⟩

end Iter


/-! ## Accessibility implies monotonicity -/

theorem Acc.monoTuple {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V} {A : V}
    (h : Acc w k Is k Is Φ A) : MonoTuple w k Is Φ := by
  intro X Y hX hY hXY m hm i hi x hx
  obtain ⟨B, g, -, hg, hs⟩ := h X hX m hm i hi x hx
  exact hs Y hY fun a ha => ⟨(hg a ha).1, (hg a ha).2.1, hXY _ (hg a ha).1 _ (hg a ha).2.1 _ (hg a ha).2.2⟩

/-! ## Readings: accessibility of one fibre -/

/-- A READING `F` (a set depending on the tuple) is `A`-accessible. -/
def AccR (w kI : Nat) (IsI : Nat → V) (F : (Nat → V) → V) (A : V) : Prop :=
  ∀ X, InTupleSpace w kI IsI X → ∀ x, x ∈ˢ F X →
    ∃ (B : V) (g : V → Nat × V × V), B ⊆ˢ A ∧ (∀ a, a ∈ˢ B → InTup kI IsI X (g a)) ∧
      ∀ X', InTupleSpace w kI IsI X' → (∀ a, a ∈ˢ B → InTup kI IsI X' (g a)) → x ∈ˢ F X'

section Readings

variable {w kI : Nat} {IsI : Nat → V}

theorem acc_of_accR {kO : Nat} {IsO : Nat → V} {Φ : (Nat → V) → Nat → V} {A : V}
    (h : ∀ m, m < kO → ∀ i, i ∈ˢ IsO m → AccR w kI IsI (fun X => app (Φ X m) i) A) :
    Acc w kI IsI kO IsO Φ A :=
  fun X hX m hm i hi x hx => h m hm i hi X hX x hx

theorem accR_of_acc {kO : Nat} {IsO : Nat → V} {Φ : (Nat → V) → Nat → V} {A : V}
    (h : Acc w kI IsI kO IsO Φ A) {m : Nat} (hm : m < kO) {i : V} (hi : i ∈ˢ IsO m) :
    AccR w kI IsI (fun X => app (Φ X m) i) A :=
  fun X hX x hx => h X hX m hm i hi x hx

theorem AccR.mono_A {F : (Nat → V) → V} {A A' : V} (h : AccR w kI IsI F A) (hA : A ⊆ˢ A') :
    AccR w kI IsI F A' := by
  intro X hX x hx
  obtain ⟨B, g, hB, hg, hs⟩ := h X hX x hx
  exact ⟨B, g, Subset.trans hB hA, hg, hs⟩

/-- Skolemisation of supports over a set of positions. -/
theorem skolem_supp {S : V} {Q : V → V → (V → Nat × V × V) → Prop}
    (h : ∀ a, a ∈ˢ S → ∃ B g, Q a B g) :
    ∃ (Bf : V → V) (gf : V → V → Nat × V × V), ∀ a, a ∈ˢ S → Q a (Bf a) (gf a) := by
  classical
  refine ⟨fun a => if h' : a ∈ˢ S then Classical.choose (h a h') else empty,
    fun a => if h' : a ∈ˢ S then Classical.choose (Classical.choose_spec (h a h'))
      else fun _ => (0, empty, empty), fun a ha => ?_⟩
  simp only [dif_pos ha]
  exact Classical.choose_spec (Classical.choose_spec (h a ha))

/-- The glued support: `B := Σ a ∈ B0, Bf a`, `g ⟨a, q⟩ := gf a q`. -/
theorem mem_glue {B0 : V} {Bf : V → V} {p : V} :
    p ∈ˢ sigmaPairs B0 Bf ↔ ∃ a, a ∈ˢ B0 ∧ ∃ q, q ∈ˢ Bf a ∧ p = kpair a q :=
  mem_sigmaPairs

/-- **Constant** readings (the hole-free fields). -/
theorem accR_const (C A : V) : AccR w kI IsI (fun _ => C) A := fun _ _ _ hx =>
  ⟨empty, fun _ => (0, empty, empty), empty_subset _, fun _ ha => absurd ha (not_mem_empty _),
    fun _ _ _ => hx⟩

/-- **A hole** read at a fixed index. -/
theorem accR_hole {m : Nat} (hm : m < kI) {e A : V} (he : e ∈ˢ IsI m) (hA : (pt : V) ∈ˢ A) :
    AccR w kI IsI (fun X => app (X m) e) A := fun _ _ x hx =>
  ⟨unitSet, fun _ => (m, e, x), fun _ ha => (mem_unitSet_iff.mp ha) ▸ hA,
    fun _ _ => ⟨hm, he, hx⟩, fun _ _ h => (h pt pt_mem_unitSet).2.2⟩

/-- **A sum over a fixed index set** (constructors, or a hole-free first
component). -/
theorem accR_sUnion {C A : V} {G : V → (Nat → V) → V} (hG : ∀ c, c ∈ˢ C → AccR w kI IsI (G c) A) :
    AccR w kI IsI (fun X => sUnion (image (fun c => G c X) C)) A := by
  intro X hX x hx
  obtain ⟨s, hs, hxs⟩ := mem_sUnion.mp hx
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hs
  obtain ⟨B, g, hB, hg, hsupp⟩ := hG c hc X hX x hxs
  exact ⟨B, g, hB, hg, fun X' hX' h' =>
    mem_sUnion.mpr ⟨_, mem_image.mpr ⟨c, hc, rfl⟩, hsupp X' hX' h'⟩⟩

theorem accR_binUnion {A : V} {G H : (Nat → V) → V} (hG : AccR w kI IsI G A) (hH : AccR w kI IsI H A) :
    AccR w kI IsI (fun X => binUnion (G X) (H X)) A := by
  intro X hX x hx
  rcases mem_binUnion.mp hx with h | h
  · obtain ⟨B, g, hB, hg, hs⟩ := hG X hX x h
    exact ⟨B, g, hB, hg, fun X' hX' h' => mem_binUnion.mpr (Or.inl (hs X' hX' h'))⟩
  · obtain ⟨B, g, hB, hg, hs⟩ := hH X hX x h
    exact ⟨B, g, hB, hg, fun X' hX' h' => mem_binUnion.mpr (Or.inr (hs X' hX' h'))⟩

/-- **Images** (constructor tags, injections). -/
theorem accR_image {A : V} {G : (Nat → V) → V} (h : V → V) (hG : AccR w kI IsI G A) :
    AccR w kI IsI (fun X => image h (G X)) A := by
  intro X hX x hx
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
  obtain ⟨B, g, hB, hg, hs⟩ := hG X hX y hy
  exact ⟨B, g, hB, hg, fun X' hX' h' => mem_image.mpr ⟨y, hs X' hX' h', rfl⟩⟩

/-- **A hole-free first component** (Σ over a constant set). -/
theorem accR_sigma {C A : V} {G : V → (Nat → V) → V} (hG : ∀ c, c ∈ˢ C → AccR w kI IsI (G c) A) :
    AccR w kI IsI (fun X => sigmaPairs C fun c => G c X) A := by
  intro X hX x hx
  obtain ⟨c, hc, y, hy, rfl⟩ := mem_sigmaPairs.mp hx
  obtain ⟨B, g, hB, hg, hs⟩ := hG c hc X hX y hy
  exact ⟨B, g, hB, hg, fun X' hX' h' => mem_sigmaPairs.mpr ⟨c, hc, y, hs X' hX' h', rfl⟩⟩

/-- **A dependent telescope over a hole-free first field**: the bound is
the union of the later fields' bounds, so a FRAME-DEPENDENT bound is
made uniform structurally (no shadow telescope) — the only premise is
that no later field depends on a HOLE-typed field (U4), i.e. a
hole-reading field enters as `accR_prod`, never as a `Σ`-index. -/
theorem accR_sigmaDep {C : V} {Af : V → V} {G : V → (Nat → V) → V}
    (hG : ∀ c, c ∈ˢ C → AccR w kI IsI (G c) (Af c)) :
    AccR w kI IsI (fun X => sigmaPairs C fun c => G c X) (sUnion (image Af C)) :=
  accR_sigma fun c hc => (hG c hc).mono_A fun _ ha =>
    mem_sUnion.mpr ⟨Af c, mem_image.mpr ⟨c, hc, rfl⟩, ha⟩

theorem sUnion_image_mem {w' : Nat} (hw : w' ≠ 0) {C : V} {Af : V → V} (hC : C ∈ˢ (univ w' : V))
    (hA : ∀ c, c ∈ˢ C → Af c ∈ˢ (univ w' : V)) : sUnion (image Af C) ∈ˢ (univ w' : V) :=
  (univ_isTGUniverse hw).famUnion_mem hC hA

/-- **A Π-tower over a hole-free domain** (the reflexive case): the
support of `f` is the glued supports of its values, indexed by
`Σ d ∈ D, A`. -/
theorem accR_pi {D A : V} {G : V → (Nat → V) → V} (hG : ∀ d, d ∈ˢ D → AccR w kI IsI (G d) A) :
    AccR w kI IsI (fun X => piSet D fun d => G d X) (sigmaPairs D fun _ => A) := by
  intro X hX f hf
  obtain ⟨Bf, gf, hsk⟩ := skolem_supp (S := D)
    (Q := fun d B g => B ⊆ˢ A ∧ (∀ a, a ∈ˢ B → InTup kI IsI X (g a)) ∧
      ∀ X', InTupleSpace w kI IsI X' → (∀ a, a ∈ˢ B → InTup kI IsI X' (g a)) → app f d ∈ˢ G d X')
    fun d hd => hG d hd X hX _ (app_mem_of_mem_piSet hf hd)
  refine ⟨sigmaPairs D Bf, fun p => gf (sfst p) (ssnd p), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨d, hd, q, hq, rfl⟩ := mem_glue.mp hp
    exact mem_sigmaPairs.mpr ⟨d, hd, q, (hsk d hd).1 q hq, rfl⟩
  · intro p hp
    obtain ⟨d, hd, q, hq, rfl⟩ := mem_glue.mp hp
    simp only [sfst_kpair, ssnd_kpair]
    exact (hsk d hd).2.1 q hq
  · intro X' hX' h'
    rw [← eq_graph_app_of_mem_piSet hf]
    refine graph_mem_piSet fun d hd => (hsk d hd).2.2 X' hX' fun q hq => ?_
    have := h' (kpair d q) (mem_sigmaPairs.mpr ⟨d, hd, q, hq, rfl⟩)
    simpa only [sfst_kpair, ssnd_kpair] using this

open Classical in
/-- **A pair of two hole-reading components** (a non-dependent product),
supports tagged by `∅`/`pt`. -/
theorem accR_prod {A1 A2 : V} {G H : (Nat → V) → V} (hG : AccR w kI IsI G A1) (hH : AccR w kI IsI H A2) :
    AccR w kI IsI (fun X => sigmaPairs (G X) fun _ => H X)
      (sigmaPairs (upair empty pt) fun t => if t = empty then A1 else A2) := by
  classical
  intro X hX x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sigmaPairs.mp hx
  obtain ⟨B1, g1, hB1, hg1, hs1⟩ := hG X hX y hy
  obtain ⟨B2, g2, hB2, hg2, hs2⟩ := hH X hX z hz
  have hne : (pt : V) ≠ empty := pt_ne_empty
  refine ⟨sigmaPairs (upair empty pt) (fun t => if t = empty then B1 else B2),
    fun p => if sfst p = empty then g1 (ssnd p) else g2 (ssnd p), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨t, ht, q, hq, rfl⟩ := mem_sigmaPairs.mp hp
    refine mem_sigmaPairs.mpr ⟨t, ht, q, ?_, rfl⟩
    by_cases h : t = empty
    · simp only [h, if_true] at hq ⊢; exact hB1 q hq
    · simp only [h, if_false] at hq ⊢; exact hB2 q hq
  · intro p hp
    obtain ⟨t, ht, q, hq, rfl⟩ := mem_sigmaPairs.mp hp
    simp only [sfst_kpair, ssnd_kpair]
    by_cases h : t = empty
    · simp only [h, if_true] at hq ⊢; exact hg1 q hq
    · simp only [h, if_false] at hq ⊢; exact hg2 q hq
  · intro X' hX' h'
    refine mem_sigmaPairs.mpr ⟨y, hs1 X' hX' fun q hq => ?_, z, hs2 X' hX' fun q hq => ?_, rfl⟩
    · have := h' (kpair empty q) (mem_sigmaPairs.mpr ⟨empty, mem_upair_left _ _, q, by simpa using hq, rfl⟩)
      simpa only [sfst_kpair, ssnd_kpair, if_true] using this
    · have := h' (kpair pt q) (mem_sigmaPairs.mpr ⟨pt, mem_upair.mpr (Or.inr rfl), q, by simpa [hne] using hq, rfl⟩)
      simpa only [sfst_kpair, ssnd_kpair, hne, if_false] using this

/-- **Composition**: a reading of an accessible operator's output is
accessible in the operator's input (supports glued, `Σ A2, A1`). -/
theorem accR_comp {kY : Nat} {IsY : Nat → V} {Ψ : (Nat → V) → Nat → V} {A1 A2 : V}
    {G : (Nat → V) → V}
    (hΨ : Acc w kI IsI kY IsY Ψ A1) (hmaps : ∀ X, InTupleSpace w kI IsI X → InTupleSpace w kY IsY (Ψ X))
    (hG : AccR w kY IsY G A2) :
    AccR w kI IsI (fun X => G (Ψ X)) (sigmaPairs A2 fun _ => A1) := by
  intro X hX x hx
  obtain ⟨B2, g2, hB2, hg2, hs2⟩ := hG (Ψ X) (hmaps X hX) x hx
  obtain ⟨Bf, gf, hsk⟩ := skolem_supp (S := B2)
    (Q := fun b B g => B ⊆ˢ A1 ∧ (∀ a, a ∈ˢ B → InTup kI IsI X (g a)) ∧
      ∀ X', InTupleSpace w kI IsI X' → (∀ a, a ∈ˢ B → InTup kI IsI X' (g a)) →
        (g2 b).2.2 ∈ˢ app (Ψ X' (g2 b).1) (g2 b).2.1)
    fun b hb => hΨ X hX _ (hg2 b hb).1 _ (hg2 b hb).2.1 _ (hg2 b hb).2.2
  refine ⟨sigmaPairs B2 Bf, fun p => gf (sfst p) (ssnd p), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨b, hb, q, hq, rfl⟩ := mem_glue.mp hp
    exact mem_sigmaPairs.mpr ⟨b, hB2 b hb, q, (hsk b hb).1 q hq, rfl⟩
  · intro p hp
    obtain ⟨b, hb, q, hq, rfl⟩ := mem_glue.mp hp
    simp only [sfst_kpair, ssnd_kpair]
    exact (hsk b hb).2.1 q hq
  · intro X' hX' h'
    refine hs2 (Ψ X') (hmaps X' hX') fun b hb => ⟨(hg2 b hb).1, (hg2 b hb).2.1, ?_⟩
    refine (hsk b hb).2.2 X' hX' fun q hq => ?_
    have := h' (kpair b q) (mem_sigmaPairs.mpr ⟨b, hb, q, hq, rfl⟩)
    simpa only [sfst_kpair, ssnd_kpair] using this

end Readings


/-! ## The least tuple in a parameter (the nested case) -/

/-- Concatenation of a `kX`-tuple and a tuple. -/
def catT (kX : Nat) (X Y : Nat → V) : Nat → V := fun i => if i < kX then X i else Y (i - kX)

section Param

variable {w kX kY : Nat} {IsX IsY : Nat → V}

theorem catT_mem {X Y : Nat → V} (hX : InTupleSpace w kX IsX X) (hY : InTupleSpace w kY IsY Y) :
    InTupleSpace w (kX + kY) (catT kX IsX IsY) (catT kX X Y) := by
  intro m hm
  unfold catT
  by_cases h : m < kX
  · simp only [h, if_true]; exact hX m h
  · simp only [h, if_false]; exact hY (m - kX) (by omega)

theorem inTup_catT {X Y : Nat → V} {t : Nat × V × V} :
    InTup (kX + kY) (catT kX IsX IsY) (catT kX X Y) t ↔
      (t.1 < kX ∧ InTup kX IsX X t) ∨ (kX ≤ t.1 ∧ InTup kY IsY Y (t.1 - kX, t.2.1, t.2.2)) := by
  obtain ⟨c, i, y⟩ := t
  unfold InTup catT
  by_cases h : c < kX
  · rw [if_pos h, if_pos h]
    constructor
    · rintro ⟨-, h2, h3⟩; exact Or.inl ⟨h, h, h2, h3⟩
    · rintro (⟨-, -, h2, h3⟩ | ⟨h1, -⟩)
      · exact ⟨by omega, h2, h3⟩
      · omega
  · rw [if_neg h, if_neg h]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact Or.inr ⟨by omega, by omega, h2, h3⟩
    · rintro (⟨h1, -⟩ | ⟨-, h1, h2, h3⟩)
      · omega
      · exact ⟨by omega, h2, h3⟩

variable (w kX kY IsX IsY) in
/-- The least tuple of `Θ` at the parameter `X`: `Θ`'s section at `X`. -/
noncomputable def lfpP (Θ : (Nat → V) → Nat → V) (X : Nat → V) : Nat → V :=
  lfpTuple w kY IsY (fun Y => Θ (catT kX X Y))

/-- **The section at a parameter** inherits accessibility. -/
theorem Acc.section {kO : Nat} {IsO : Nat → V} {Θ : (Nat → V) → Nat → V} {A : V}
    (h : Acc w (kX + kY) (catT kX IsX IsY) kO IsO Θ A) {X : Nat → V} (hX : InTupleSpace w kX IsX X) :
    Acc w kY IsY kO IsO (fun Y => Θ (catT kX X Y)) A := by
  intro Y hY m hm i hi x hx
  obtain ⟨B, g, hB, hg, hs⟩ := h _ (catT_mem hX hY) m hm i hi x hx
  refine ⟨sep B fun a => kX ≤ (g a).1, fun a => ((g a).1 - kX, (g a).2.1, (g a).2.2),
    Subset.trans sep_subset hB, ?_, ?_⟩
  · intro a ha
    obtain ⟨haB, hle⟩ := mem_sep.mp ha
    rcases inTup_catT.mp (hg a haB) with ⟨h1, -⟩ | ⟨-, h2⟩
    · omega
    · exact h2
  · intro Y' hY' h'
    refine hs _ (catT_mem hX hY') fun a ha => ?_
    rcases inTup_catT.mp (hg a ha) with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact inTup_catT.mpr (Or.inl ⟨h1, h2⟩)
    · exact inTup_catT.mpr (Or.inr ⟨h1, h' a (mem_sep.mpr ⟨ha, h1⟩)⟩)

/-- **THE NESTED CASE: the least tuple is accessible in its parameter.**
If the joint operator `Θ` (parameter components first, then its own) is
`A`-accessible and maps the space into itself, then `X ↦ lfp_Y Θ(X, Y)`
is `pathsA A`-accessible — no key, no wide operator, no container
presentation.  (W) of each section and its monotonicity come from
`closed_of_acc` / `Acc.monoTuple`. -/
theorem lfpP_acc (hw : w ≠ 0) {Θ : (Nat → V) → Nat → V} {A : V} (hA : A ∈ˢ (univ w : V))
    (hmaps : ∀ X Y, InTupleSpace w kX IsX X → InTupleSpace w kY IsY Y →
      InTupleSpace w kY IsY (Θ (catT kX X Y)))
    (hacc : Acc w (kX + kY) (catT kX IsX IsY) kY IsY Θ A) :
    Acc w kX IsX kY IsY (lfpP w kX kY IsY Θ) (pathsA A) := by
  -- (W) and monotonicity of every section
  have hcl : ∀ X, InTupleSpace w kX IsX X → ∃ L, IsClosedTuple w kY IsY (fun Y => Θ (catT kX X Y)) L :=
    fun X hX => closed_of_acc hw hA (fun Y hY => hmaps X Y hX hY) (hacc.section hX)
  have hmono : ∀ X, InTupleSpace w kX IsX X → MonoTuple w kY IsY (fun Y => Θ (catT kX X Y)) :=
    fun X hX => (hacc.section hX).monoTuple
  intro X hX
  -- the property proved by induction over the least tuple at `X`
  let P : Nat → V → V → Prop := fun m i y =>
    ∃ (B : V) (g : V → Nat × V × V), B ⊆ˢ pathsA A ∧ (∀ a, a ∈ˢ B → InTup kX IsX X (g a)) ∧
      ∀ X', InTupleSpace w kX IsX X' → (∀ a, a ∈ˢ B → InTup kX IsX X' (g a)) →
        y ∈ˢ app (lfpP w kX kY IsY Θ X' m) i
  have hind := lfpTuple_induction (hcl X hX) (hmono X hX) P ?_
  · intro m hm i hi y hy
    exact hind m hm i hi y hy
  intro m hm i hi y hy
  have hS := sepTuple_mem w kY IsY (fun Y => Θ (catT kX X Y)) P
  obtain ⟨B0, g0, hB0, hg0, hs0⟩ := hacc _ (catT_mem hX hS) m hm i hi y hy
  -- the sub-support of every support position: a leaf in `X`, or `P`'s
  obtain ⟨Bf, gf, hsk⟩ := skolem_supp (S := B0)
    (Q := fun a B g => B ⊆ˢ pathsA A ∧ (∀ q, q ∈ˢ B → InTup kX IsX X (g q)) ∧
      ∀ X', InTupleSpace w kX IsX X' → (∀ q, q ∈ˢ B → InTup kX IsX X' (g q)) →
        InTup (kX + kY) (catT kX IsX IsY) (catT kX X' (lfpP w kX kY IsY Θ X')) (g0 a))
    (by
      intro a ha
      rcases inTup_catT.mp (hg0 a ha) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨unitSet, fun _ => g0 a, fun q hq => ?_, fun _ _ => h2, fun X' _ h' => ?_⟩
        · rw [mem_unitSet_iff.mp hq]; exact pt_mem_pathsA A
        · exact inTup_catT.mpr (Or.inl ⟨h1, h' pt pt_mem_unitSet⟩)
      · obtain ⟨h2a, h2b, h2c⟩ := h2
        have hmem := h2c
        simp only [sepTuple] at hmem
        rw [app_graph h2b, mem_sep] at hmem
        obtain ⟨B, g, hB, hg, hs⟩ := hmem.2
        exact ⟨B, g, hB, hg, fun X' hX' h' =>
          inTup_catT.mpr (Or.inr ⟨h1, h2a, h2b, hs X' hX' h'⟩)⟩)
  refine ⟨sigmaPairs B0 Bf, fun p => gf (sfst p) (ssnd p), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, q, hq, rfl⟩ := mem_glue.mp hp
    exact kpair_mem_pathsA (hB0 a ha) ((hsk a ha).1 q hq)
  · intro p hp
    obtain ⟨a, ha, q, hq, rfl⟩ := mem_glue.mp hp
    simp only [sfst_kpair, ssnd_kpair]
    exact (hsk a ha).2.1 q hq
  · intro X' hX' h'
    have hL' := lfpTuple_mem w kY IsY (fun Y => Θ (catT kX X' Y))
    refine lfpTuple_closed (hcl X' hX') (hmono X' hX') m hm i hi y ?_
    refine hs0 _ (catT_mem hX' hL') fun a ha => (hsk a ha).2.2 X' hX' fun q hq => ?_
    have := h' (kpair a q) (mem_sigmaPairs.mpr ⟨a, ha, q, hq, rfl⟩)
    simpa only [sfst_kpair, ssnd_kpair] using this

end Param


/-! ## Instances -/

section Instances

variable {w : Nat}

/-- One-component operators whose single fibre (over `{pt}`) is `F X`. -/
noncomputable def op1 (F : (Nat → V) → V) : (Nat → V) → Nat → V :=
  fun X _ => graph (fun _ => F X) unitSet

/-- The single index set. -/
noncomputable def is1 : Nat → V := fun _ => unitSet

theorem acc_op1 {kI : Nat} {IsI : Nat → V} {F : (Nat → V) → V} {A : V} (h : AccR w kI IsI F A) :
    Acc w kI IsI 1 is1 (op1 F) A := by
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
  exact accR_binUnion (accR_const _ _) (accR_image _ (accR_sigma fun _ _ =>
    accR_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet))

/-! ### Binary trees (flat, two recursive fields): `leaf | node : T → T → T` -/

noncomputable def treeF (X : Nat → V) : V :=
  binUnion (sing (kpair empty empty)) (image (kpair pt) (sigmaPairs (app (X 0) pt) fun _ => app (X 0) pt))

theorem tree_closed : ∃ L : Nat → V, IsClosedTuple w 1 is1 (op1 treeF) L := by
  refine closed_of_acc hw (prodA_mem hw (unitSet_mem_univ w) (unitSet_mem_univ w))
    (maps_op1 fun X hX => nil_or_mem hw ((univ_isTGUniverse hw).sigmaPairs_mem
      (hole1_mem hX Nat.zero_lt_one) fun _ _ => hole1_mem hX Nat.zero_lt_one)) (acc_op1 ?_)
  refine accR_binUnion (accR_const _ _) (accR_image _ (accR_prod ?_ ?_)) <;>
    exact accR_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet

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
  exact accR_binUnion (accR_const _ _) (accR_image _ (accR_pi fun _ _ =>
    accR_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet))

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
theorem listJ_acc : Acc w (1 + 1) (catT 1 is1 is1) 1 is1 (listJ : (Nat → V) → Nat → V) listA := by
  rw [catT_is1]
  refine acc_op1 (accR_binUnion (accR_const _ _) (accR_image _ (accR_prod ?_ ?_)))
  · exact accR_hole (by omega) pt_mem_unitSet pt_mem_unitSet
  · exact accR_hole (by omega) pt_mem_unitSet pt_mem_unitSet

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
  have hP : Acc w 1 is1 1 is1 (lfpP w 1 1 is1 (listJ : (Nat → V) → Nat → V)) (pathsA listA) :=
    lfpP_acc hw hLA (listJ_maps hw) listJ_acc
  have hPm : ∀ X : Nat → V, InTupleSpace w 1 is1 X →
      InTupleSpace w 1 is1 (lfpP w 1 1 is1 (listJ : (Nat → V) → Nat → V) X) :=
    fun X _ => lfpTuple_mem _ _ _ _
  refine closed_of_acc hw (A := sigmaPairs unitSet fun _ => pathsA listA)
    (hU.sigmaPairs_mem (unitSet_mem_univ w) fun _ _ => pathsA_mem hw hLA)
    (maps_op1 fun X hX => tag_image_mem hw (hole1_mem (hPm X hX) Nat.zero_lt_one)) (acc_op1 ?_)
  exact accR_image _ (accR_comp hP hPm (accR_hole Nat.zero_lt_one pt_mem_unitSet pt_mem_unitSet))

end Instances

/-! ### `Prop` blocks (`w = 0`): the top tuple, no accessibility needed -/

theorem prop_closed_top {k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    (hmaps : MapsTuple 0 k Is Φ) : ∃ L, IsClosedTuple 0 k Is Φ L := by
  have htop : InTupleSpace 0 k Is (fun m => graph (fun _ => unitSet) (Is m)) := fun m _ =>
    graph_mem_famSpace fun _ _ => unitSet_mem_univ 0
  refine ⟨_, htop, fun m hm i hi x hx => ?_⟩
  show x ∈ˢ app (graph (fun _ => unitSet) (Is m)) i
  rw [app_graph hi]
  have := famSpace_app (hmaps _ htop m hm) hi
  rw [univ_zero] at this
  exact mem_univZero.mp this x hx

end ConLeche.SetTheory

#print axioms ConLeche.SetTheory.closed_of_acc
#print axioms ConLeche.SetTheory.lfpP_acc
#print axioms ConLeche.SetTheory.rose_closed
#print axioms ConLeche.SetTheory.sup_closed
