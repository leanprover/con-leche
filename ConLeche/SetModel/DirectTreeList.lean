module

public import ConLeche.SetModel.RecGraph
public import ConLeche.SetTheory.Derive.BekicTreeList
@[expose] public section

/-!
# The DIRECT nested route, experiment (task #314 DR-1): `Tree := node (List Tree)`

The falsifying experiment of DESIGN §DR.1 (e), in the pure set model.
The container `List` is given as a datum-shaped operator in its
parameter — `LOp α Y` (`BekicTreeList.lean`), with `⟦List⟧ α :=
lfpSet` of `Y ↦ LOp α Y` — and the block's COMPOSED operator is
`X ↦ TOp (⟦List⟧ X)`: the family variable sits inside the container's
parameter, which is what makes the block nested.  Its least fixed
point `T*` (`treeT`) is the carrier; `L* := ⟦List⟧ T*` (`treeL`) is
the mimic recursor's domain — the reading of the restored motive
domain `List (Tree α)`, a set that exists already, not something
constructed.

**What is ASSUMED of the container**, exactly (the K.26 shape, DESIGN
§DR.1 (b)): the map action in the parameter at the FUNCTOR level —
`LOp_mono`, `α ⊆ α' → LOp α Y ⊆ LOp α' Y` — from which the map action
on the carrier (`listL_mono`, the inclusion `⟦List⟧ α ⊆ ⟦List⟧ α'`)
follows by leastness; the constructor decomposition `mem_LOp`
(`IndRep.fibre`); the injectivity of the constructors (`IndRep.mkInj`:
`mkNil ≠ mkCons`, `mkCons` injective); the closure of the bounding set
`U` under the constructors (the closed member, (W)).  NOT assumed:
anything about `List.rec` — the container's recursor is not consulted
by the existence proof.

**The engine** is the existing recursion theorem
`recGraph_exists_unique` (`RecGraph.lean`), instantiated ONCE over the
disjoint union of the two restored motive domains,

    I := {0} × T*  ∪  {1} × L*

(one component per motive of the stream's `Tree.rec`), with the
predecessor relation read off the constructors — `pred (0, node a) =
{(1, a)}`, `pred (1, cons h t) = {(0, h), (1, t)}`, `pred (1, nil) =
∅` — the bound `B` the motives' fibres and the step `st` the minors.
Every index is accessible (`acc_all`): by the composed operator's lfp
induction for the tree component, with the CONTAINER's lfp induction
at the parameter `S := {accessible trees}` inside it (`accL_of_param`)
— the two inductions nest, and no map action is needed there.  The
recursor is the graph's selector `recSel`; its three ι rules
(`rule_node`, `rule_nil`, `rule_cons`) are the stream's, and
`fold_agree` says that any fold on `L*` satisfying `List.rec`'s two
rule shapes with `Tree.rec` in the `cons` minor IS the selector's
`L*`-component — which is how the mimic leaf, spelled THROUGH
`List.rec`, is identified with the recursor the engine built.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The carriers -/

section Defs

variable (w : Nat) (U : V) (mkT : V → V) (mkNil : V) (mkCons : V → V → V)

/-- The container's functor at parameter `α`, as a set-function on the
universe. -/
noncomputable def listF (α : V) : V := graph (fun Y => LOp U mkNil mkCons α Y) (univ w)

/-- `⟦List⟧ α`: the container's carrier at the parameter `α`. -/
noncomputable def listL (α : V) : V := lfpSet w (listF w U mkNil mkCons α)

/-- **The composed operator** `X ↦ TOp (⟦List⟧ X)`. -/
noncomputable def treeF : V := graph (fun X => TOp U mkT (listL w U mkNil mkCons X)) (univ w)

/-- `T*`: the block's carrier, the least fixed point of the composed
operator. -/
noncomputable def treeT : V := lfpSet w (treeF w U mkT mkNil mkCons)

/-- `L* := ⟦List⟧ T*`: the mimic recursor's domain. -/
noncomputable def treeL : V := listL w U mkNil mkCons (treeT w U mkT mkNil mkCons)

end Defs

section Carrier

variable {w : Nat} {U : V} {mkT : V → V} {mkNil : V} {mkCons : V → V → V}

theorem app_listF {α Y : V} (hY : Y ∈ˢ (univ w : V)) :
    app (listF w U mkNil mkCons α) Y = LOp U mkNil mkCons α Y :=
  app_graph hY

theorem listF_mono (α : V) : MonoIn w (listF w U mkNil mkCons α) := by
  intro X Y hX hY hle
  rw [app_listF hX, app_listF hY]
  exact LOp_mono (Subset.refl _) hle

theorem listF_maps (hU : U ∈ˢ (univ w : V)) (α : V) : MapsIn w (listF w U mkNil mkCons α) := by
  intro X hX
  rw [app_listF hX]
  exact LOp_mem_univ hU _ _

theorem listF_closed (hU : U ∈ˢ (univ w : V)) (α : V) :
    ∃ L, IsClosedIn w (listF w U mkNil mkCons α) L :=
  ⟨U, hU, by rw [app_listF hU]; exact LOp_subset_U⟩

theorem listL_mem_univ (α : V) : listL w U mkNil mkCons α ∈ˢ (univ w : V) :=
  lfpSet_mem_univ _ _

/-- The container's fixed-point equation at a parameter. -/
theorem listL_eq (hU : U ∈ˢ (univ w : V)) (α : V) :
    LOp U mkNil mkCons α (listL w U mkNil mkCons α) = listL w U mkNil mkCons α := by
  have := lfpSet_eq (F := listF w U mkNil mkCons α) (listF_closed hU α) (listF_mono α)
    (listF_maps hU α)
  rwa [app_listF (lfpSet_mem_univ _ _)] at this

/-- The container's structural induction at a parameter. -/
theorem listL_induction (hU : U ∈ˢ (univ w : V)) (α : V) (P : V → Prop)
    (hP : ∀ x, x ∈ˢ LOp U mkNil mkCons α (sep (listL w U mkNil mkCons α) P) → P x) :
    ∀ x, x ∈ˢ listL w U mkNil mkCons α → P x := by
  refine lfpSet_induction (listF_closed hU α) (listF_mono α) P fun x hx => hP x ?_
  rwa [app_listF (univ_sep_mem (lfpSet_mem_univ _ _))] at hx

/-- **The map action on the carrier, from the map action on the
functor** (`LOp_mono`, the assumed K.26 fact): `⟦List⟧` is monotone in
its parameter, by leastness. -/
theorem listL_mono (hU : U ∈ˢ (univ w : V)) {α α' : V} (hα : α ⊆ˢ α') :
    listL w U mkNil mkCons α ⊆ˢ listL w U mkNil mkCons α' := by
  refine lfpSet_subset ⟨listL_mem_univ α', ?_⟩
  rw [app_listF (listL_mem_univ α')]
  intro x hx
  rw [← listL_eq hU α']
  exact LOp_mono hα (Subset.refl _) x hx

theorem app_treeF {X : V} (hX : X ∈ˢ (univ w : V)) :
    app (treeF w U mkT mkNil mkCons) X = TOp U mkT (listL w U mkNil mkCons X) :=
  app_graph hX

/-- **The composed operator is monotone** — the one place the map
action in the parameter is used. -/
theorem treeF_mono (hU : U ∈ˢ (univ w : V)) : MonoIn w (treeF w U mkT mkNil mkCons) := by
  intro X Y hX hY hle
  rw [app_treeF hX, app_treeF hY]
  exact TOp_mono (listL_mono hU hle)

theorem treeF_maps (hU : U ∈ˢ (univ w : V)) : MapsIn w (treeF w U mkT mkNil mkCons) := by
  intro X hX
  rw [app_treeF hX]
  exact TOp_mem_univ hU _

/-- The closed member (W): the bounding set itself. -/
theorem treeF_closed (hU : U ∈ˢ (univ w : V)) :
    ∃ L, IsClosedIn w (treeF w U mkT mkNil mkCons) L :=
  ⟨U, hU, by rw [app_treeF hU]; exact TOp_subset_U⟩

theorem treeT_mem_univ : treeT w U mkT mkNil mkCons ∈ˢ (univ w : V) :=
  lfpSet_mem_univ _ _

/-- `T* = TOp L*`: the carrier is a fixed point of the composed
operator. -/
theorem treeT_eq (hU : U ∈ˢ (univ w : V)) :
    TOp U mkT (treeL w U mkT mkNil mkCons) = treeT w U mkT mkNil mkCons := by
  have := lfpSet_eq (F := treeF w U mkT mkNil mkCons) (treeF_closed hU) (treeF_mono hU)
    (treeF_maps hU)
  rwa [app_treeF (lfpSet_mem_univ _ _)] at this

/-- Structural induction on the composed carrier. -/
theorem treeT_induction (hU : U ∈ˢ (univ w : V)) (P : V → Prop)
    (hP : ∀ x, x ∈ˢ TOp U mkT (listL w U mkNil mkCons (sep (treeT w U mkT mkNil mkCons) P)) →
      P x) :
    ∀ x, x ∈ˢ treeT w U mkT mkNil mkCons → P x := by
  refine lfpSet_induction (treeF_closed hU) (treeF_mono hU) P fun x hx => hP x ?_
  rwa [app_treeF (univ_sep_mem (lfpSet_mem_univ _ _))] at hx

/-- `L* = LOp T* L*`. -/
theorem treeL_eq (hU : U ∈ˢ (univ w : V)) :
    LOp U mkNil mkCons (treeT w U mkT mkNil mkCons) (treeL w U mkT mkNil mkCons)
      = treeL w U mkT mkNil mkCons :=
  listL_eq hU _

end Carrier

/-! ## The recursion: the index set, the predecessors, the bound, the step -/

section Rec

variable (w : Nat) (U : V) (mkT : V → V) (mkNil : V) (mkCons : V → V → V)

/-- The index set of the simultaneous recursion: the disjoint union of
the two restored motive domains, `{0} × T* ∪ {1} × L*`. -/
noncomputable def treeIdxSet : V :=
  binUnion (image (kpair (vnat 0)) (treeT w U mkT mkNil mkCons))
    (image (kpair (vnat 1)) (treeL w U mkT mkNil mkCons))

/-- The predecessor relation, read off the constructors. -/
def TreeRel (p q : V) : Prop :=
  (∃ a, p = kpair (vnat 0) (mkT a) ∧ q = kpair (vnat 1) a) ∨
  (∃ h t, p = kpair (vnat 1) (mkCons h t) ∧ (q = kpair (vnat 0) h ∨ q = kpair (vnat 1) t))

/-- The predecessor sets. -/
noncomputable def treePred (p : V) : V :=
  sep (treeIdxSet w U mkT mkNil mkCons) (TreeRel mkT mkCons p)

variable (M₁ M₂ : V → V) (node : V → V → V) (nil : V) (cons : V → V → V → V → V)

open Classical in
/-- The bound: the motives' fibres. -/
noncomputable def treeB (p : V) : V :=
  if h : ∃ x, p = kpair (vnat 0) x then M₁ (Classical.choose h)
  else if h : ∃ l, p = kpair (vnat 1) l then M₂ (Classical.choose h)
  else empty

open Classical in
/-- The step: the minors at the predecessors' values. -/
noncomputable def treeSt (p g : V) : V :=
  if h : ∃ a, p = kpair (vnat 0) (mkT a) then
    node (Classical.choose h) (app g (kpair (vnat 1) (Classical.choose h)))
  else if p = kpair (vnat 1) mkNil then nil
  else if h : ∃ q : V × V, p = kpair (vnat 1) (mkCons q.1 q.2) then
    cons (Classical.choose h).1 (Classical.choose h).2
      (app g (kpair (vnat 0) (Classical.choose h).1))
      (app g (kpair (vnat 1) (Classical.choose h).2))
  else empty

/-- **The recursor**: the graph's selector.  `treeRec … (0, x)` is
`Tree.rec … x`, `treeRec … (1, l)` is `Tree.rec_1 … l`. -/
noncomputable def treeRec (ℓ : Nat) (i : V) : V :=
  recSel (recGraph ℓ (treeIdxSet w U mkT mkNil mkCons) (treePred w U mkT mkNil mkCons)
    (treeB M₁ M₂) (treeSt mkT mkNil mkCons node nil cons)) i

end Rec

section RecFacts

variable {w : Nat} {U : V} {mkT : V → V} {mkNil : V} {mkCons : V → V → V}

local notation "T*" => treeT w U mkT mkNil mkCons
local notation "L*" => treeL w U mkT mkNil mkCons
local notation "I*" => treeIdxSet w U mkT mkNil mkCons

theorem mem_treeIdxSet {p : V} :
    p ∈ˢ I* ↔ (∃ x, x ∈ˢ T* ∧ p = kpair (vnat 0) x) ∨ (∃ l, l ∈ˢ L* ∧ p = kpair (vnat 1) l) := by
  unfold treeIdxSet
  rw [mem_binUnion, mem_image, mem_image]

theorem tree_mem_idx {x : V} (hx : x ∈ˢ T*) : kpair (vnat 0) x ∈ˢ I* :=
  mem_treeIdxSet.mpr (Or.inl ⟨x, hx, rfl⟩)

theorem list_mem_idx {l : V} (hl : l ∈ˢ L*) : kpair (vnat 1) l ∈ˢ I* :=
  mem_treeIdxSet.mpr (Or.inr ⟨l, hl, rfl⟩)

theorem vnat0_ne_vnat1 : (vnat 0 : V) ≠ vnat 1 := fun h => Nat.zero_ne_one (vnat_inj h)

theorem treePred_subset (p : V) : treePred w U mkT mkNil mkCons p ⊆ˢ I* := sep_subset

theorem mem_treePred {p q : V} :
    q ∈ˢ treePred w U mkT mkNil mkCons p ↔ q ∈ˢ I* ∧ TreeRel mkT mkCons p q := mem_sep

/-! ### The constructors' predecessors, under injectivity -/

variable (hT : ∀ a a', mkT a = mkT a' → a = a')
  (hC : ∀ h t h' t', mkCons h t = mkCons h' t' → h = h' ∧ t = t')
  (hNC : ∀ h t, mkNil ≠ mkCons h t)

include hT in
theorem mem_treePred_node {a q : V} :
    q ∈ˢ treePred w U mkT mkNil mkCons (kpair (vnat 0) (mkT a)) ↔
      q ∈ˢ I* ∧ q = kpair (vnat 1) a := by
  rw [mem_treePred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inl ⟨a, rfl, h⟩⟩
  rcases h with ⟨a', h₁, h₂⟩ | ⟨h', t', h₁, -⟩
  · obtain ⟨-, h₁⟩ := kpair_inj h₁
    rw [h₂, hT a a' h₁]
  · exact absurd (kpair_inj h₁).1 vnat0_ne_vnat1

include hNC in
theorem mem_treePred_nil {q : V} :
    ¬ q ∈ˢ treePred w U mkT mkNil mkCons (kpair (vnat 1) mkNil) := by
  intro h
  rw [mem_treePred] at h
  rcases h.2 with ⟨a', h₁, -⟩ | ⟨h', t', h₁, -⟩
  · exact vnat0_ne_vnat1 (kpair_inj h₁).1.symm
  · exact hNC h' t' (kpair_inj h₁).2

include hC in
theorem mem_treePred_cons {h t q : V} :
    q ∈ˢ treePred w U mkT mkNil mkCons (kpair (vnat 1) (mkCons h t)) ↔
      q ∈ˢ I* ∧ (q = kpair (vnat 0) h ∨ q = kpair (vnat 1) t) := by
  rw [mem_treePred]
  refine and_congr_right fun _ => ⟨fun hq => ?_, fun hq => Or.inr ⟨h, t, rfl, hq⟩⟩
  rcases hq with ⟨a', h₁, -⟩ | ⟨h', t', h₁, h₂⟩
  · exact absurd (kpair_inj h₁).1.symm vnat0_ne_vnat1
  · obtain ⟨rfl, rfl⟩ := hC _ _ _ _ (kpair_inj h₁).2
    exact h₂

/-! ### The bound and the step compute -/

variable {M₁ M₂ : V → V} {node : V → V → V} {nil : V} {cons : V → V → V → V → V}

theorem treeB_tree (x : V) : treeB M₁ M₂ (kpair (vnat 0) x) = M₁ x := by
  unfold treeB
  rw [dif_pos ⟨x, rfl⟩]
  have := Classical.choose_spec (⟨x, rfl⟩ : ∃ y, kpair (vnat 0 : V) x = kpair (vnat 0) y)
  exact congrArg M₁ (kpair_inj this).2.symm

theorem treeB_list (l : V) : treeB M₁ M₂ (kpair (vnat 1) l) = M₂ l := by
  unfold treeB
  rw [dif_neg (fun ⟨_, h⟩ => vnat0_ne_vnat1 (kpair_inj h).1.symm), dif_pos ⟨l, rfl⟩]
  have := Classical.choose_spec (⟨l, rfl⟩ : ∃ y, kpair (vnat 1 : V) l = kpair (vnat 1) y)
  exact congrArg M₂ (kpair_inj this).2.symm

include hT in
theorem treeSt_node (a g : V) :
    treeSt mkT mkNil mkCons node nil cons (kpair (vnat 0) (mkT a)) g
      = node a (app g (kpair (vnat 1) a)) := by
  unfold treeSt
  rw [dif_pos ⟨a, rfl⟩]
  have := Classical.choose_spec (⟨a, rfl⟩ : ∃ y, kpair (vnat 0 : V) (mkT a) = kpair (vnat 0) (mkT y))
  rw [← hT _ _ (kpair_inj this).2]

theorem treeSt_nil (g : V) :
    treeSt mkT mkNil mkCons node nil cons (kpair (vnat 1) mkNil) g = nil := by
  unfold treeSt
  rw [dif_neg (fun ⟨_, h⟩ => vnat0_ne_vnat1 (kpair_inj h).1.symm), if_pos rfl]

include hC hNC in
theorem treeSt_cons (h t g : V) :
    treeSt mkT mkNil mkCons node nil cons (kpair (vnat 1) (mkCons h t)) g
      = cons h t (app g (kpair (vnat 0) h)) (app g (kpair (vnat 1) t)) := by
  unfold treeSt
  rw [dif_neg (fun ⟨_, h⟩ => vnat0_ne_vnat1 (kpair_inj h).1.symm),
    if_neg (fun h' => hNC h t (kpair_inj h').2.symm), dif_pos ⟨(h, t), rfl⟩]
  have hs := Classical.choose_spec
    (⟨(h, t), rfl⟩ : ∃ q : V × V, kpair (vnat 1 : V) (mkCons h t) = kpair (vnat 1) (mkCons q.1 q.2))
  obtain ⟨h₁, h₂⟩ := hC _ _ _ _ (kpair_inj hs).2
  rw [← h₁, ← h₂]

/-! ### The recursion theorem's hypotheses -/

variable (hU : U ∈ˢ (univ w : V)) (hTU : ∀ l, l ∈ˢ U → mkT l ∈ˢ U)
  (hNilU : mkNil ∈ˢ U) (hConsU : ∀ h t, h ∈ˢ U → t ∈ˢ U → mkCons h t ∈ˢ U)
  {ℓ : Nat}
  -- (the local notations are not expanded inside `variable` binders:
  -- the carriers are spelled out here)
  (hM₁ : ∀ x, x ∈ˢ treeT w U mkT mkNil mkCons → M₁ x ∈ˢ (univ ℓ : V))
  (hM₂ : ∀ l, l ∈ˢ treeL w U mkT mkNil mkCons → M₂ l ∈ˢ (univ ℓ : V))
  (hnode : ∀ a ih, a ∈ˢ treeL w U mkT mkNil mkCons → ih ∈ˢ M₂ a → node a ih ∈ˢ M₁ (mkT a))
  (hnil : nil ∈ˢ M₂ mkNil)
  (hcons : ∀ h t ih₁ ih₂, h ∈ˢ treeT w U mkT mkNil mkCons → t ∈ˢ treeL w U mkT mkNil mkCons →
    ih₁ ∈ˢ M₁ h → ih₂ ∈ˢ M₂ t → cons h t ih₁ ih₂ ∈ˢ M₂ (mkCons h t))

include hU in
theorem treeT_subset_U : T* ⊆ˢ U := by
  intro x hx
  rw [← treeT_eq hU] at hx
  exact TOp_subset_U x hx

include hU in
theorem treeL_subset_U : L* ⊆ˢ U := by
  intro x hx
  rw [← treeL_eq hU] at hx
  exact LOp_subset_U x hx

include hU hTU in
/-- `node a ∈ T*` for `a ∈ L*`. -/
theorem mkT_mem_treeT {a : V} (ha : a ∈ˢ L*) : mkT a ∈ˢ T* := by
  rw [← treeT_eq hU]
  exact mkT_mem_TOp hTU (treeL_subset_U hU) ha

include hU hNilU in
theorem mkNil_mem_treeL : mkNil ∈ˢ L* := by
  rw [← treeL_eq hU]
  exact mkNil_mem_LOp hNilU _ _

include hU hConsU in
theorem mkCons_mem_treeL {h t : V} (hh : h ∈ˢ T*) (ht : t ∈ˢ L*) : mkCons h t ∈ˢ L* := by
  rw [← treeL_eq hU]
  exact mkCons_mem_LOp hConsU (treeT_subset_U hU) (treeL_subset_U hU) hh ht

include hU in
/-- Every tree is a `node`. -/
theorem treeT_cases {x : V} (hx : x ∈ˢ T*) : ∃ a, a ∈ˢ L* ∧ x = mkT a := by
  rw [← treeT_eq hU] at hx
  exact (mem_TOp.mp hx).2

include hU in
/-- Every list is `nil` or a `cons`. -/
theorem treeL_cases {l : V} (hl : l ∈ˢ L*) :
    l = mkNil ∨ ∃ h t, h ∈ˢ T* ∧ t ∈ˢ L* ∧ l = mkCons h t := by
  rw [← treeL_eq hU] at hl
  exact (mem_LOp.mp hl).2

include hM₁ hM₂ in
theorem treeB_mem_univ : ∀ i, i ∈ˢ I* → treeB M₁ M₂ i ∈ˢ (univ ℓ : V) := by
  intro i hi
  rcases mem_treeIdxSet.mp hi with ⟨x, hx, rfl⟩ | ⟨l, hl, rfl⟩
  · rw [treeB_tree]; exact hM₁ x hx
  · rw [treeB_list]; exact hM₂ l hl

local notation "G*" => recGraph ℓ I* (treePred w U mkT mkNil mkCons)
  (treeB M₁ M₂) (treeSt mkT mkNil mkCons node nil cons)
local notation "R*" => treeRec w U mkT mkNil mkCons M₁ M₂ node nil cons ℓ

include hM₁ hM₂ in
/-- The graph's fibres lie in the bound. -/
theorem treeGraph_subset_B {i v : V} (hi : i ∈ˢ I*) (hv : v ∈ˢ app G* i) :
    v ∈ˢ treeB M₁ M₂ i := by
  rw [app_recGraph_eq (treeB_mem_univ hM₁ hM₂) (fun i _ => treePred_subset i) hi] at hv
  exact (mem_recGraphFibre.mp hv).1

include hT hC hNC hU hM₁ hM₂ hnode hnil hcons in
/-- **The step is typed**: at every index, the minor at the
predecessors' graph values lands in the motive's fibre. -/
theorem treeSt_mem :
    ∀ i, i ∈ˢ I* → ∀ g, g ∈ˢ piSet (treePred w U mkT mkNil mkCons i) (fun j => app G* j) →
      treeSt mkT mkNil mkCons node nil cons i g ∈ˢ treeB M₁ M₂ i := by
  intro i hi g hg
  have hval : ∀ j, j ∈ˢ treePred w U mkT mkNil mkCons i → app g j ∈ˢ treeB M₁ M₂ j :=
    fun j hj => treeGraph_subset_B hM₁ hM₂ (treePred_subset i j hj) (app_mem_of_mem_piSet hg hj)
  rcases mem_treeIdxSet.mp hi with ⟨x, hx, rfl⟩ | ⟨l, hl, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := treeT_cases hU hx
    rw [treeSt_node hT, treeB_tree]
    have := hval (kpair (vnat 1) a) ((mem_treePred_node hT).mpr ⟨list_mem_idx ha, rfl⟩)
    rw [treeB_list] at this
    exact hnode a _ ha this
  · rcases treeL_cases hU hl with rfl | ⟨h, t, hh, ht, rfl⟩
    · rw [treeSt_nil, treeB_list]; exact hnil
    · rw [treeSt_cons hC hNC, treeB_list]
      have h₁ := hval (kpair (vnat 0) h) ((mem_treePred_cons hC).mpr ⟨tree_mem_idx hh, Or.inl rfl⟩)
      have h₂ := hval (kpair (vnat 1) t) ((mem_treePred_cons hC).mpr ⟨list_mem_idx ht, Or.inr rfl⟩)
      rw [treeB_tree] at h₁
      rw [treeB_list] at h₂
      exact hcons h t _ _ hh ht h₁ h₂

/-! ### Accessibility: the two nested inductions -/

local notation "Acc*" => accFam I* (treePred w U mkT mkNil mkCons) (fun _ => True)

/-- The `Acc` family's introduction rule: an index all of whose
predecessors are accessible is. -/
theorem treeAcc_intro {i : V} (hi : i ∈ˢ I*)
    (h : ∀ j, j ∈ˢ treePred w U mkT mkNil mkCons i → ∃ y, y ∈ˢ app Acc* j) :
    (pt : V) ∈ˢ app Acc* i := by
  unfold accFam
  rw [← app_lfpFamSet_eq ⟨_, accStep_closed⟩ (accStep_mono fun i _ => treePred_subset i)
    accStep_maps hi, app_app_accStep (lfpFamSet_mem _ _ _) hi]
  exact pt_mem_truthVal ⟨trivial, h⟩

include hC hNC hU hNilU hConsU in
/-- **The container's induction at the parameter of accessible trees**:
every list over a set `S` of accessible trees is a list over `T*` and
accessible.  `listL_induction` at the parameter `S`. -/
theorem treeAccL_of_param {S : V} (hS : S ⊆ˢ T*)
    (hacc : ∀ x, x ∈ˢ S → ∃ y, y ∈ˢ app Acc* (kpair (vnat 0) x)) :
    ∀ a, a ∈ˢ listL w U mkNil mkCons S → a ∈ˢ L* ∧ ∃ y, y ∈ˢ app Acc* (kpair (vnat 1) a) := by
  refine listL_induction hU S _ fun a ha => ?_
  obtain ⟨-, ha⟩ := mem_LOp.mp ha
  rcases ha with rfl | ⟨h, t, hh, ht, rfl⟩
  · refine ⟨mkNil_mem_treeL hU hNilU, pt, treeAcc_intro (list_mem_idx (mkNil_mem_treeL hU hNilU))
      fun j hj => absurd hj (mem_treePred_nil hNC)⟩
  · obtain ⟨ht, hacct⟩ := (mem_sep.mp ht).2
    have hhT := hS h hh
    refine ⟨mkCons_mem_treeL hU hConsU hhT ht, pt,
      treeAcc_intro (list_mem_idx (mkCons_mem_treeL hU hConsU hhT ht)) fun j hj => ?_⟩
    rcases ((mem_treePred_cons hC).mp hj).2 with rfl | rfl
    · exact hacc h hh
    · exact hacct

include hT hC hNC hU hTU hNilU hConsU in
/-- **Every tree is accessible**: the composed operator's induction,
with the container's induction at the accessible trees inside. -/
theorem treeAcc_tree : ∀ x, x ∈ˢ T* → ∃ y, y ∈ˢ app Acc* (kpair (vnat 0) x) := by
  refine treeT_induction hU _ fun x hx => ?_
  obtain ⟨-, a, ha, rfl⟩ := mem_TOp.mp hx
  obtain ⟨haL, hacca⟩ := treeAccL_of_param hC hNC hU hNilU hConsU sep_subset
    (fun x hx => (mem_sep.mp hx).2) a ha
  refine ⟨pt, treeAcc_intro (tree_mem_idx (mkT_mem_treeT hU hTU haL)) fun j hj => ?_⟩
  obtain ⟨-, rfl⟩ := (mem_treePred_node hT).mp hj
  exact hacca

include hT hC hNC hU hTU hNilU hConsU in
/-- **Every index is accessible.** -/
theorem treeAcc_all : ∀ i, i ∈ˢ I* → ∃ y, y ∈ˢ app Acc* i := by
  intro i hi
  rcases mem_treeIdxSet.mp hi with ⟨x, hx, rfl⟩ | ⟨l, hl, rfl⟩
  · exact treeAcc_tree hT hC hNC hU hTU hNilU hConsU x hx
  · exact (treeAccL_of_param hC hNC hU hNilU hConsU (Subset.refl _)
      (treeAcc_tree hT hC hNC hU hTU hNilU hConsU) l hl).2

/-! ### The recursor exists: the recursion theorem, instantiated -/

include hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons in
/-- **The recursion theorem at the nested block**: at every index of
the disjoint union, the graph has exactly one value. -/
theorem treeGraph_unique :
    ∀ i, i ∈ˢ I* → (∃ v, v ∈ˢ app G* i) ∧
      ∀ v v', v ∈ˢ app G* i → v' ∈ˢ app G* i → v = v' := by
  intro i hi
  obtain ⟨y, hy⟩ := treeAcc_all hT hC hNC hU hTU hNilU hConsU i hi
  exact recGraph_exists_unique (treeB_mem_univ hM₁ hM₂) (fun i _ => treePred_subset i)
    (treeSt_mem hT hC hNC hU hM₁ hM₂ hnode hnil hcons) i hi y hy

include hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons in
/-- **Typing**: the recursor's value lies in the motive's fibre. -/
theorem treeRec_mem {i : V} (hi : i ∈ˢ I*) :
    R* i ∈ˢ treeB M₁ M₂ i :=
  treeGraph_subset_B hM₁ hM₂ hi
    (recSel_mem (treeGraph_unique hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons i hi).1)

include hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons in
/-- The recursion equation at an index, in the engine's form. -/
theorem treeRec_eq {i : V} (hi : i ∈ˢ I*) :
    R* i
      = treeSt mkT mkNil mkCons node nil cons i
          (graph (fun j => R* j)
            (treePred w U mkT mkNil mkCons i)) :=
  recSel_eq (treeB_mem_univ hM₁ hM₂) (fun i _ => treePred_subset i) hi
    (treeGraph_unique hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons i hi).1
    fun j hj => treeGraph_unique hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons j
      (treePred_subset i j hj)

/-! ### The stream's three ι rules -/

include hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons in
/-- `Tree.rec … (node a) = node a (Tree.rec_1 … a)`. -/
theorem treeRec_node {a : V} (ha : a ∈ˢ L*) :
    R* (kpair (vnat 0) (mkT a))
      = node a (R* (kpair (vnat 1) a)) := by
  rw [treeRec_eq hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons
    (tree_mem_idx (mkT_mem_treeT hU hTU ha)), treeSt_node hT,
    app_graph ((mem_treePred_node hT).mpr ⟨list_mem_idx ha, rfl⟩)]

include hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons in
/-- `Tree.rec_1 … nil = nil`. -/
theorem treeRec_nil :
    R* (kpair (vnat 1) mkNil) = nil := by
  rw [treeRec_eq hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons
    (list_mem_idx (mkNil_mem_treeL hU hNilU)), treeSt_nil]

include hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons in
/-- `Tree.rec_1 … (cons h t) = cons h t (Tree.rec … h) (Tree.rec_1 … t)`. -/
theorem treeRec_cons {h t : V} (hh : h ∈ˢ T*) (ht : t ∈ˢ L*) :
    R* (kpair (vnat 1) (mkCons h t))
      = cons h t
          (R* (kpair (vnat 0) h))
          (R* (kpair (vnat 1) t)) := by
  rw [treeRec_eq hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons
    (list_mem_idx (mkCons_mem_treeL hU hConsU hh ht)), treeSt_cons hC hNC,
    app_graph ((mem_treePred_cons hC).mpr ⟨tree_mem_idx hh, Or.inl rfl⟩),
    app_graph ((mem_treePred_cons hC).mpr ⟨list_mem_idx ht, Or.inr rfl⟩)]

/-! ### The mimic leaf, spelled through `List.rec`, is the engine's second component -/

include hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons in
/-- **Fold agreement (C3)**: any function on `L*` satisfying the
container's two rule shapes — `List.rec`'s, with `Tree.rec … h` at the
`cons` minor's parameter position — is the recursor's `L*`-component.
This is what identifies the mimic leaf `λ … l, List.rec M₂ nil (λ h t
ih, cons h t (Tree.rec … h) ih) l` with the engine's `Tree.rec_1`; one
induction on the container at the parameter `T*`. -/
theorem treeRec_fold_agree (F : V → V) (hF₀ : F mkNil = nil)
    (hF₁ : ∀ h t, h ∈ˢ T* → t ∈ˢ L* →
      F (mkCons h t) = cons h t (R*
        (kpair (vnat 0) h)) (F t)) :
    ∀ l, l ∈ˢ L* → F l = R* (kpair (vnat 1) l) := by
  refine listL_induction hU _ _ fun l hl => ?_
  obtain ⟨-, hl⟩ := mem_LOp.mp hl
  rcases hl with rfl | ⟨h, t, hh, ht, rfl⟩
  · rw [hF₀, treeRec_nil hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons]
  · obtain ⟨ht, ih⟩ := mem_sep.mp ht
    rw [hF₁ h t hh ht, ih, treeRec_cons hT hC hNC hU hTU hNilU hConsU hM₁ hM₂ hnode hnil hcons hh ht]

end RecFacts

end ConLeche.SetTheory
