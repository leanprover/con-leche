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

open Classical in
/-- The first component of a path step (`pcons`), the point off them. -/
noncomputable def pfst (b : V) : V :=
  if h : ∃ a q : V, pcons a q = b then Classical.choose h else pt

open Classical in
/-- The second component of a path step, the point off them. -/
noncomputable def psnd (b : V) : V :=
  if h : ∃ a q : V, pcons a q = b then Classical.choose (Classical.choose_spec h) else pt

theorem pfst_pcons (a q : V) : pfst (pcons a q) = a := by
  unfold pfst
  have h : ∃ a' q' : V, pcons a' q' = pcons a q := ⟨a, q, rfl⟩
  rw [dite_eq_left h]
  exact (pcons_inj (Classical.choose_spec (Classical.choose_spec h))).1

theorem psnd_pcons (a q : V) : psnd (pcons a q) = q := by
  unfold psnd
  have h : ∃ a' q' : V, pcons a' q' = pcons a q := ⟨a, q, rfl⟩
  rw [dite_eq_left h]
  exact (pcons_inj (Classical.choose_spec (Classical.choose_spec h))).2

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
    have : pick A (code A T) = Classical.choose hex := by unfold pick; exact dite_eq_left hex
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
    have : f a = Classical.choose (hT a ha) := dite_eq_left ha
    rw [this]
    exact Classical.choose_spec (hT a ha)
  exact mem_limFam.mpr ⟨_, hstage⟩

end AccIter

export AccIter (closed_of_acc)

/-! ## The nested case: the least family is accessible in its parameter

A container field of a nested block ranges over the container's family
read at the nested position set to the block's approximant — a least
fixed point in its OWN family, with the approximant as a PARAMETER.
The block's accessibility needs the container value's dependence on
that parameter to be bounded, and here is where it comes from: when
the container's operator is accessible JOINTLY in the parameter and
its own family, with one bound `A`, the least fixed point as a
function of the parameter is accessible with the bound `accPaths A`.
The support of a member of the least fixed point at `X` is read off
its own induction: a member produced by the operator has a support of
at most `A`-many occurrences, each either an occurrence in `X` (a
leaf) or a member of the least fixed point whose support in `X` the
induction hypothesis gives; the paths glue them (`pcons`).  The
family's closedness at every parameter is `closed_of_acc` of the
section — at a proposition the constant family `{pt}`
(`closedFam_zero`), so the nested case holds in both regimes, and the
bound need be a member of the universe only above a proposition.
Con-leche (which states it above a proposition only): `lfpP_acc`,
`ConLeche/SetModel/Access.lean` ("THE NESTED CASE: the least tuple is accessible in its parameter"),
with the parameter and own components of a tuple here a sum type of
indices. -/

section Param

variable [Nonempty ι] [Nonempty κ] {n : Nat}

omit [Nonempty ι] [Nonempty κ] in
/-- A family over a sum of index types from one over each.  Con-leche:
`catT`. -/
theorem InUniv.elim {X : ι → V} {Y : κ → V} (hX : InUniv n X) (hY : InUniv n Y) :
    InUniv n (Sum.elim X Y) := by
  intro i
  cases i with
  | inl i => exact hX i
  | inr j => exact hY j

omit [Nonempty ι] in
/-- **The section at a parameter** of a jointly accessible operator is
accessible: the support's occurrences in the parameter are already
held, the others are occurrences in the own family.  Con-leche:
`AccTuple.section`. -/
theorem AccFam.section {Θ : (ι ⊕ κ → V) → κ → V} {A : V} (h : AccFam n Θ A) {X : ι → V}
    (hX : InUniv n X) : AccFam n (fun Y => Θ (Sum.elim X Y)) A := by
  intro Y hY j x hx
  obtain ⟨B, g, hB, hg, hs⟩ := h _ (hX.elim hY) j x hx
  classical
  refine ⟨sep B fun a => ∃ j', (g a).1 = Sum.inr j',
    fun a => ((match (g a).1 with | .inl _ => Classical.ofNonempty | .inr j' => j'), (g a).2),
    sep_sub.trans hB, ?_, ?_⟩
  · intro a ha
    obtain ⟨haB, j', hj'⟩ := mem_sep.mp ha
    have := hg a haB
    unfold InFam at this ⊢
    rw [hj'] at this
    simpa [hj'] using this
  · intro Y' hY' h'
    refine hs _ (hX.elim hY') fun a ha => ?_
    have := hg a ha
    unfold InFam at this ⊢
    cases hga : (g a).1 with
    | inl i => rw [hga] at this; simpa using this
    | inr j' =>
      have := h' a (mem_sep.mpr ⟨ha, j', hga⟩)
      unfold InFam at this
      simpa [hga] using this

omit [Nonempty ι] [Nonempty κ] in
/-- **The least family of `Θ` at the parameter `X`**: the least fixed
point of `Θ`'s section at `X` — a container's family at an
instantiation.  Con-leche: `lfpP`. -/
noncomputable def lfpP (n : Nat) (Θ : (ι ⊕ κ → V) → κ → V) (X : ι → V) : κ → V :=
  lfpFamSet n fun Y => Θ (Sum.elim X Y)

omit [Nonempty κ] in
/-- Supports chosen for every code of a set (skolemisation).
Con-leche: `skolem_supp`. -/
theorem skolem_supp {S : V} {Q : V → V → (V → ι × V) → Prop}
    (h : ∀ a, a ∈ˢ S → ∃ B g, Q a B g) :
    ∃ (Bf : V → V) (gf : V → V → ι × V), ∀ a, a ∈ˢ S → Q a (Bf a) (gf a) := by
  classical
  refine ⟨fun a => if h' : a ∈ˢ S then Classical.choose (h a h') else empty,
    fun a => if h' : a ∈ˢ S then Classical.choose (Classical.choose_spec (h a h'))
      else fun _ => (Classical.ofNonempty, pt), fun a ha => ?_⟩
  simp only [dite_eq_left ha]
  exact Classical.choose_spec (Classical.choose_spec (h a ha))

/-- **The nested case: the least family is accessible in its
parameter.**  If the joint operator (the parameter's indices on the
left, its own on the right) is `A`-accessible and maps families in
the universe to families in the universe, then `X ↦ lfpP Θ X` is
`accPaths A`-accessible: by induction over the least family at `X`, a
member's support is the paths through the operator's support — a leaf
for an occurrence in `X`, the induction hypothesis' support below an
occurrence in the least family — and every parameter holding it
produces the member by the closedness of its least family.  The bound
must be a member of the universe only above a proposition, where the
section's closed family is `closed_of_acc`'s; at a proposition it is
`{pt}` (`closedFam_zero`).  Con-leche: `lfpP_acc` (above a
proposition). -/
theorem lfpP_acc {Θ : (ι ⊕ κ → V) → κ → V} {A : V} (hA : n ≠ 0 → A ∈ˢ (univ n : V))
    (hmaps : ∀ X Y, InUniv n X → InUniv n Y → InUniv n (Θ (Sum.elim X Y)))
    (hacc : AccFam n Θ A) : AccFam n (lfpP n Θ) (accPaths A) := by
  -- the closed family and the monotonicity of every section
  have hcl : ∀ X, InUniv n X → ∃ L, IsClosedFam n (fun Y => Θ (Sum.elim X Y)) L := by
    intro X hX
    by_cases hn : n = 0
    · subst hn
      exact closedFam_zero fun Y hY => hmaps X Y hX hY
    · exact closed_of_acc hn (hA hn) (fun Y hY => hmaps X Y hX hY) (hacc.section hX)
  have hmono : ∀ X, InUniv n X → MonoFam n (fun Y => Θ (Sum.elim X Y)) :=
    fun X hX => (hacc.section hX).mono
  intro X hX
  -- the property, proved by induction over the least family at `X`
  let P : κ → V → Prop := fun j y =>
    ∃ (B : V) (g : V → ι × V), B ⊆ˢ accPaths A ∧ (∀ a, a ∈ˢ B → InFam X (g a)) ∧
      ∀ X', InUniv n X' → (∀ a, a ∈ˢ B → InFam X' (g a)) → y ∈ˢ lfpP n Θ X' j
  refine lfpFamSet_induction (hcl X hX) (hmono X hX) P ?_
  intro j y hy
  have hS := sepFam_mem n (fun Y => Θ (Sum.elim X Y)) P
  obtain ⟨B0, g0, hB0, hg0, hs0⟩ := hacc _ (hX.elim hS) j y hy
  -- the sub-support below every code: a leaf in `X`, or the induction hypothesis'
  obtain ⟨Bf, gf, hsk⟩ := skolem_supp (S := B0)
    (Q := fun a B g => B ⊆ˢ accPaths A ∧ (∀ q, q ∈ˢ B → InFam X (g q)) ∧
      ∀ X', InUniv n X' → (∀ q, q ∈ˢ B → InFam X' (g q)) →
        InFam (Sum.elim X' (lfpP n Θ X')) (g0 a))
    (by
      intro a ha
      have hin := hg0 a ha
      unfold InFam at hin
      cases hga : (g0 a).1 with
      | inl i =>
        rw [hga] at hin
        simp only [Sum.elim_inl] at hin
        refine ⟨one, fun _ => (i, (g0 a).2), fun q hq => ?_, fun _ _ => hin, fun X' _ h' => ?_⟩
        · rw [mem_one.mp hq]; exact pt_mem_accPaths A
        · unfold InFam
          rw [hga, Sum.elim_inl]
          exact h' pt (mem_one.mpr rfl)
      | inr j' =>
        rw [hga] at hin
        simp only [Sum.elim_inr, sepFam, mem_sep] at hin
        obtain ⟨B, g, hB, hg, hs⟩ := hin.2
        refine ⟨B, g, hB, hg, fun X' hX' h' => ?_⟩
        unfold InFam
        rw [hga, Sum.elim_inr]
        exact hs X' hX' h')
  refine ⟨famUnion B0 fun a => image (pcons a) (Bf a), fun p => gf (pfst p) (psnd p), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, hp⟩ := mem_famUnion.mp hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact pcons_mem_accPaths (hB0 a ha) ((hsk a ha).1 q hq)
  · intro p hp
    obtain ⟨a, ha, hp⟩ := mem_famUnion.mp hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    show InFam X (gf (pfst (pcons a q)) (psnd (pcons a q)))
    rw [pfst_pcons, psnd_pcons]
    exact (hsk a ha).2.1 q hq
  · intro X' hX' h'
    have hL' := lfpFamSet_mem n fun Y => Θ (Sum.elim X' Y)
    refine lfpFamSet_closed (hcl X' hX') (hmono X' hX') j y ?_
    refine hs0 _ (hX'.elim hL') fun a ha => (hsk a ha).2.2 X' hX' fun q hq => ?_
    have := h' (pcons a q) (mem_famUnion.mpr ⟨a, ha, mem_image.mpr ⟨q, hq, rfl⟩⟩)
    show InFam X' (gf a q)
    rwa [show gf a q = gf (pfst (pcons a q)) (psnd (pcons a q)) by rw [pfst_pcons, psnd_pcons]]

end Param

end Fragment
