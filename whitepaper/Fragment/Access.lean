module

public import Fragment.IndLib
public import Fragment.LfpSet

@[expose] public section

/-!
# A closed family from accessibility

Where does a closed family of an inductive block's operator come from?
Its fibres must be *members* of the universe — types, not proper
classes — and that is the strength of the universe (an inaccessible
cardinal).  The notion that transfers it is **accessibility with a
bound `A`** (`AccFam`): every element the operator produces from a
family `W` has a *support* in `W` — a subfamily indexed by a subset of
the one fixed set `A` — such that the element is produced from *every*
family in the universe containing that support.  Membership of an
element depends on at most `A`-many elements of the input, and on
nothing else.  (The bound must be uniform: "every element has *some*
small support" would admit `X ↦ {∅} ∪ {x ∪ {x}} ∪ {⋃ s | s ⊆ X small}`,
whose least fixed point is the universe's ordinals.)

**The theorem** (`closed_of_acc`): an accessible operator that maps
families in the universe to families in the universe has a closed
family in the universe.  **The proof** iterates the operator along
well-founded trees branching over the sets: the stage at a leaf is
the empty family, the stage at a node is `Φ` of the union of its
subtrees' stages; the closed family is the union of all stages.  It
is closed by accessibility — an element `Φ` produces from the union
has a support of at most `A`-many elements, each in some stage, and
the node with those stages as subtrees produces it.  It is in the
universe because every stage is (the universe is closed under
`A`-indexed unions) and the union over all trees is really a union
over a set: a stage depends on its tree only through the tree's
*code* — its set of finite paths over `A`, a subset of the set of all
such paths, which is a countable union of members of the universe, so
a member — and the codes are a member of the universe (its power set).
No monotonicity, no ordinals, no cardinals.

Accessibility implies monotonicity (`AccFam.mono`), so `closed_of_acc`
and `AccFam.mono` are what `lfpFamSet` (`LfpSet.lean`) asks for.
Where accessibility comes from — the block's operator is accessible by
positivity — is the environment section's business.

Con-leche: `ConLeche/SetModel/Access.lean` — `AccTuple`,
`accPathsN`/`accPaths`, `BT`, `AccIter.stage`/`code`/`pick`/`limTup`,
`closed_of_acc`, `AccTuple.monoTuple`; this file mirrors its
definitions and proof, line by line, over Lean-level families
(`ι → V`) instead of tuples of graphs.  Con-leche's ordered pair of a
path step is Kuratowski's (`kpair`); the fragment's is the tagged
tuple it has anyway.
-/

namespace Fragment
open SetLib UnivLib IndLib

universe u v w

variable {V : Type u} [IndLib V] {ι : Type v} {κ : Type w}

/-! ## The notion -/

/-- An occurrence `(i, y)` is an element of the family `W`.
Con-leche: `InTup`. -/
def InFam (W : ι → V) (t : ι × V) : Prop := t.2 ∈ˢ W t.1

/-- **Accessibility with the bound `A`** of an operator from families
over `ι` to families over `κ`: every element `x` the operator
produces at `j` from a family `W` in the universe has a support — a
subset `B` of `A` and occurrences `g a ∈ W` for `a ∈ B` — such that
`x` is produced at `j` from every family `W'` in the universe
containing the support.  Con-leche: `AccTuple`,
`ConLeche/SetModel/Access.lean`. -/
def AccFam (n : Nat) (Φ : (ι → V) → κ → V) (A : V) : Prop :=
  ∀ W, InUniv n W → ∀ j x, x ∈ˢ Φ W j →
    ∃ (B : V) (g : V → ι × V), B ⊆ˢ A ∧ (∀ a, a ∈ˢ B → InFam W (g a)) ∧
      ∀ W', InUniv n W' → (∀ a, a ∈ˢ B → InFam W' (g a)) → x ∈ˢ Φ W' j

/-- **Accessible operators are monotone**: the support in `W` is in
the larger `W'`.  Con-leche: `AccTuple.monoTuple`. -/
theorem AccFam.mono {n : Nat} {Φ : (ι → V) → ι → V} {A : V} (h : AccFam n Φ A) : MonoFam n Φ := by
  intro W W' hW hW' hle i x hx
  obtain ⟨B, g, -, hg, hs⟩ := h W hW i x hx
  exact hs W' hW' fun a ha => hle _ _ (hg a ha)

/-! ## Paths over `A` -/

/-- A step of a path: the pair `(a, q)` as a tagged tuple — injective,
never the point.  Con-leche: `kpair`. -/
def pcons (a q : V) : V := tag 0 (tuple [a, q])

theorem pcons_inj {a q a' q' : V} (h : pcons a q = pcons a' q') : a = a' ∧ q = q' := by
  have h := tuple_inj (tag_inj h).2
  simp only [List.cons.injEq, and_true] at h
  exact h

theorem pcons_ne_pt {a q : V} : pcons a q ≠ pt := tag_ne_pt

theorem pcons_mem_univ {n : Nat} {a q : V} (hn : n ≠ 0) (ha : a ∈ˢ univ n) (hq : q ∈ˢ univ n) :
    pcons a q ∈ˢ (univ n : V) := by
  refine tag_mem_univ hn (tuple_mem_univ hn fun x hx => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hq

/-- Paths of length `k` over `A`: the empty path is the point, a
longer path a step onto a shorter one.  Con-leche: `accPathsN`. -/
noncomputable def accPathsN (A : V) : Nat → V
  | 0 => one
  | k + 1 => famUnion A fun a => image (pcons a) (accPathsN A k)

/-- All finite paths over `A`: the countable union.  Con-leche:
`accPaths`. -/
noncomputable def accPaths (A : V) : V := natUnion (accPathsN A)

theorem pt_mem_accPaths (A : V) : (pt : V) ∈ˢ accPaths A :=
  mem_natUnion.mpr ⟨0, mem_one.mpr rfl⟩

theorem pcons_mem_accPaths {A a p : V} (ha : a ∈ˢ A) (hp : p ∈ˢ accPaths A) :
    pcons a p ∈ˢ accPaths A := by
  obtain ⟨k, hk⟩ := mem_natUnion.mp hp
  exact mem_natUnion.mpr ⟨k + 1, mem_famUnion.mpr ⟨a, ha, mem_image.mpr ⟨p, hk, rfl⟩⟩⟩

theorem accPathsN_mem_univ {n : Nat} {A : V} (hn : n ≠ 0) (hA : A ∈ˢ univ n) :
    ∀ k, accPathsN A k ∈ˢ (univ n : V)
  | 0 => one_mem_univ n
  | k + 1 =>
    famUnion_mem_univ hn hA fun _ ha =>
      image_mem_univ hn (accPathsN_mem_univ hn hA k) fun _ hq =>
        pcons_mem_univ hn (univ_trans hn hA ha) (univ_trans hn (accPathsN_mem_univ hn hA k) hq)

/-- The set of finite paths over a member of a positive universe is a
member: the one use of `ω`.  Con-leche: `accPaths_mem`. -/
theorem accPaths_mem_univ {n : Nat} {A : V} (hn : n ≠ 0) (hA : A ∈ˢ univ n) :
    accPaths A ∈ˢ (univ n : V) := natUnion_mem_univ hn (accPathsN_mem_univ hn hA)

/-! ## Well-founded trees, stages and codes -/

/-- Lean-level well-founded trees branching over the sets: a leaf, or
a node with a subtree for every set.  Con-leche: `BT`. -/
inductive BT (V : Type u) : Type u
  | leaf : BT V
  | node : (V → BT V) → BT V

namespace AccIter

variable (Φ : (ι → V) → ι → V) (A : V)

/-- The fibrewise union of an `A`-indexed family of families.
Con-leche: `unionTup`. -/
noncomputable def unionFam (F : V → ι → V) : ι → V := fun i => famUnion A fun a => F a i

/-- **The stage at a tree**: the empty family at a leaf, `Φ` of the
union of the subtrees' stages at a node.  Con-leche: `stage`. -/
noncomputable def stage : BT V → ι → V
  | .leaf => fun _ => empty
  | .node f => Φ (unionFam A fun a => stage (f a))

/-- **A tree's code**: its set of paths over `A` — the empty path at a
node, and a step `a` onto every path of the subtree at `a`.
Con-leche: `code`. -/
noncomputable def code : BT V → V
  | .leaf => empty
  | .node f => binUnion one (famUnion A fun a => image (pcons a) (code (f a)))

open Classical in
/-- A tree with the given code, if any.  Con-leche: `pick`. -/
noncomputable def pick (c : V) : BT V :=
  if h : ∃ T, code A T = c then Classical.choose h else .leaf

/-- **The limit family**: the union of the stages over all codes.
Con-leche: `limTup`. -/
noncomputable def limFam : ι → V :=
  fun i => famUnion (power (accPaths A)) fun c => stage Φ A (pick A c) i

variable {Φ A}

theorem mem_unionFam {F : V → ι → V} {i : ι} {y : V} :
    y ∈ˢ unionFam A F i ↔ ∃ a, a ∈ˢ A ∧ y ∈ˢ F a i := by
  unfold unionFam; exact mem_famUnion

theorem mem_code_node {f : V → BT V} {p : V} :
    p ∈ˢ code A (.node f) ↔ p = pt ∨ ∃ a, a ∈ˢ A ∧ ∃ q, q ∈ˢ code A (f a) ∧ p = pcons a q := by
  simp only [code]
  rw [mem_binUnion, mem_one, mem_famUnion]
  simp only [mem_image]

/-- A code is a set of paths over `A`.  Con-leche: `code_sub`. -/
theorem code_sub : ∀ T : BT V, code A T ⊆ˢ accPaths A
  | .leaf => by simp only [code]; exact empty_sub _
  | .node f => by
    intro p hp
    rcases mem_code_node.mp hp with rfl | ⟨a, ha, q, hq, rfl⟩
    · exact pt_mem_accPaths A
    · exact pcons_mem_accPaths ha (code_sub (f a) q hq)

/-- **The stage depends on the tree only through its code.**
Con-leche: `stage_eq_of_code`. -/
theorem stage_eq_of_code : ∀ T T' : BT V, code A T = code A T' → stage Φ A T = stage Φ A T'
  | .leaf, .leaf, _ => rfl
  | .leaf, .node f, h => by
    exfalso
    have : (pt : V) ∈ˢ code A (.node f) := mem_code_node.mpr (Or.inl rfl)
    rw [← h] at this
    exact not_mem_empty _ this
  | .node f, .leaf, h => by
    exfalso
    have : (pt : V) ∈ˢ code A (.node f) := mem_code_node.mpr (Or.inl rfl)
    rw [h] at this
    exact not_mem_empty _ this
  | .node f, .node f', h => by
    have hsub : ∀ a, a ∈ˢ A → code A (f a) = code A (f' a) := by
      intro a ha
      apply Sub.antisymm
      · intro q hq
        have : pcons a q ∈ˢ code A (.node f') :=
          h ▸ mem_code_node.mpr (Or.inr ⟨a, ha, q, hq, rfl⟩)
        rcases mem_code_node.mp this with h1 | ⟨a', _, q', hq', h2⟩
        · exact absurd h1 pcons_ne_pt
        · obtain ⟨rfl, rfl⟩ := pcons_inj h2; exact hq'
      · intro q hq
        have : pcons a q ∈ˢ code A (.node f) :=
          h ▸ mem_code_node.mpr (Or.inr ⟨a, ha, q, hq, rfl⟩)
        rcases mem_code_node.mp this with h1 | ⟨a', _, q', hq', h2⟩
        · exact absurd h1 pcons_ne_pt
        · obtain ⟨rfl, rfl⟩ := pcons_inj h2; exact hq'
    simp only [stage]
    congr 1
    funext i
    exact famUnion_congr fun a ha => by
      show stage Φ A (f a) i = stage Φ A (f' a) i
      rw [stage_eq_of_code (f a) (f' a) (hsub a ha)]

variable {n : Nat}

/-- Every stage is in the universe: the universe is closed under
`A`-indexed unions.  Con-leche: `stage_mem`. -/
theorem stage_mem (hn : n ≠ 0) (hA : A ∈ˢ (univ n : V)) (hmaps : MapsFam n Φ) :
    ∀ T : BT V, InUniv n (stage Φ A T)
  | .leaf => fun _ => empty_mem_univ n
  | .node f => by
    simp only [stage]
    exact hmaps _ fun i => famUnion_mem_univ hn hA fun a _ => stage_mem hn hA hmaps (f a) i

/-- The members of the limit family: the members of some stage.
Con-leche: `mem_limTup`. -/
theorem mem_limFam {i : ι} {y : V} : y ∈ˢ limFam Φ A i ↔ ∃ T : BT V, y ∈ˢ stage Φ A T i := by
  unfold limFam
  rw [mem_famUnion]
  constructor
  · rintro ⟨c, -, hy⟩
    exact ⟨_, hy⟩
  · rintro ⟨T, hT⟩
    refine ⟨code A T, mem_power.mpr (code_sub T), ?_⟩
    have hex : ∃ T', code A T' = code A T := ⟨T, rfl⟩
    have : pick A (code A T) = Classical.choose hex := by unfold pick; exact dif_pos hex
    rw [this, stage_eq_of_code _ _ (Classical.choose_spec hex)]
    exact hT

/-- The limit family is in the universe: a union over the codes, a
member of the universe as the power set of the paths.  Con-leche:
`limTup_mem`. -/
theorem limFam_mem (hn : n ≠ 0) (hA : A ∈ˢ (univ n : V)) (hmaps : MapsFam n Φ) :
    InUniv n (limFam Φ A) := fun i =>
  famUnion_mem_univ hn (power_mem_univ hn (accPaths_mem_univ hn hA)) fun _ _ =>
    stage_mem hn hA hmaps _ i

/-- **A closed family from accessibility.**  At a positive universe,
an operator that maps families in the universe to families in the
universe and is accessible with a bound `A` in the universe has a
closed family in the universe: the limit family.  An element `Φ`
produces from it has a support, each occurrence in some stage; the
node whose subtree at `a` is a tree of the occurrence `g a`'s stage
has that support in the union of its subtrees' stages, so its stage
produces the element, which is therefore in the limit.  No
monotonicity is used.  Con-leche: `closed_of_acc`,
`ConLeche/SetModel/Access.lean`. -/
theorem closed_of_acc (hn : n ≠ 0) (hA : A ∈ˢ (univ n : V)) (hmaps : MapsFam n Φ)
    (hacc : AccFam n Φ A) : ∃ L, IsClosedFam n Φ L := by
  refine ⟨limFam Φ A, limFam_mem hn hA hmaps, ?_⟩
  intro i x hx
  obtain ⟨B, g, hBA, hgL, hsupp⟩ := hacc _ (limFam_mem hn hA hmaps) i x hx
  -- every occurrence of the support lies in some stage: choose its tree
  have hT : ∀ a, a ∈ˢ B → ∃ T : BT V, (g a).2 ∈ˢ stage Φ A T (g a).1 :=
    fun a ha => mem_limFam.mp (hgL a ha)
  classical
  let f : V → BT V := fun a => if h : a ∈ˢ B then Classical.choose (hT a h) else .leaf
  have hstage : x ∈ˢ stage Φ A (.node f) i := by
    simp only [stage]
    refine hsupp _ (fun i' => famUnion_mem_univ hn hA fun a _ => stage_mem hn hA hmaps (f a) i') ?_
    intro a ha
    refine mem_unionFam.mpr ⟨a, hBA a ha, ?_⟩
    have : f a = Classical.choose (hT a ha) := dif_pos ha
    rw [this]
    exact Classical.choose_spec (hT a ha)
  exact mem_limFam.mpr ⟨_, hstage⟩

end AccIter

export AccIter (closed_of_acc)

end Fragment
