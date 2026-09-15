module

public import ConLeche.SetModel.RecGraph
public import ConLeche.SetTheory.Derive.BekicTreeList
@[expose] public section

/-!
# The DIRECT nested route, experiment (task #314 DR-1): `P4 := mk (P4C P4)`

The second falsifying instance of DESIGN §DR.1 (e), in the pure set
model — the composition is TWICE nested: `P4` nests through the
container `P4C`, and `P4C` itself nests through `Array`, which nests
through `List`.  `⟦List⟧ β` is the least fixed point of `LOp`
(`BekicTreeList.lean`), `⟦Array⟧ β := AOp β` is NOT a fixed point at
all (`Array` has no recursive field), and `P4C`'s COMPOSED operator
reads `⟦Array⟧` at its own family variable; the block's composed
operator is `X ↦ P4Op (⟦P4C⟧ X)`, whose least fixed point `P4*`
(`p4T`) is the carrier.  The four restored motive domains — `P4`,
`P4C P4`, `Array (P4C P4)`, `List (P4C P4)` — are `p4T`, `p4C1`,
`p4C2`, `p4C3`: sets that exist already, not things constructed.

**What is ASSUMED of the containers**, exactly (the K.26 shape): the
map action in the parameter at the FUNCTOR level (`LOp_mono`, and
`p4COp_mono` built from it), from which the map action on the carriers
(`p4ListL_mono`, `p4ArrayL_mono`, `p4CL_mono`) follows by leastness;
the constructor decompositions `mem_LOp`, `mem_p4ArrayL`,
`mem_p4COp`, `mem_p4Op`; the injectivity of the constructors and the
disjointness of the two constructor pairs (`text`/`append`,
`mkNil`/`mkCons`); the closure of the bounding set `U` under all six
constructors.  NOT assumed: anything about `List.rec`, `Array.rec` or
`P4C.rec` — no container recursor is consulted by the existence proof.

**The engine** is `recGraph_exists_unique` (`RecGraph.lean`),
instantiated ONCE over the disjoint union of the four restored motive
domains,

    I := {0} × P4*  ∪  {1} × p4C1  ∪  {2} × p4C2  ∪  {3} × p4C3

with the predecessor relation read off the six ι rules, the bound `B`
the motives' fibres and the step `st` the minors.  Every index is
accessible (`p4Acc_all`) by THREE nested lfp inductions: the composed
operator's for the `P4` component, the container `P4C`'s at the
parameter of accessible `P4`-values inside it (`p4AccC_of_param`), and
`List`'s at the parameter of accessible `P4C`-values inside THAT
(`p4AccL_of_param`) — no map action is needed there.  The recursor is
the graph's selector `recSel`; its six ι rules are the stream's, and
`p4Rec_fold_agree` says that any three folds satisfying `P4C`'s own
recursor FAMILY's rule shapes, with `P4.rec` at the parameter
position, ARE the selector's three container components — which is how
the mimic leaf, spelled through `P4C.rec`, `P4C.rec_1`, `P4C.rec_2`,
is identified with the recursor the engine built.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The carriers -/

section Defs

variable (w : Nat) (U : V) (mkP4 : V → V) (text : V → V) (append : V → V) (amk : V → V)
  (mkNil : V) (mkCons : V → V → V)

/-- The `List` container's functor at the parameter `β`. -/
noncomputable def p4ListF (β : V) : V := graph (fun Y => LOp U mkNil mkCons β Y) (univ w)

/-- `⟦List⟧ β`. -/
noncomputable def p4ListL (β : V) : V := lfpSet w (p4ListF w U mkNil mkCons β)

/-- **`Array`'s operator**: one constructor `amk`, its one field a
`⟦List⟧ β`. -/
noncomputable def p4AOp (β : V) : V :=
  sep U fun x => ∃ l, l ∈ˢ p4ListL w U mkNil mkCons β ∧ x = amk l

/-- `⟦Array⟧ β`.  `Array` has no recursive field, so this is the
operator itself — no least fixed point. -/
noncomputable def p4ArrayL (β : V) : V := p4AOp w U amk mkNil mkCons β

/-- **`P4C`'s composed operator**: `text` reads the parameter `α`,
`append` reads `⟦Array⟧` at the family variable `Y`. -/
noncomputable def p4COp (α Y : V) : V :=
  sep U fun x =>
    (∃ s, s ∈ˢ α ∧ x = text s) ∨ (∃ ps, ps ∈ˢ p4ArrayL w U amk mkNil mkCons Y ∧ x = append ps)

/-- `P4C`'s functor at the parameter `α`. -/
noncomputable def p4CF (α : V) : V :=
  graph (fun Y => p4COp w U text append amk mkNil mkCons α Y) (univ w)

/-- `⟦P4C⟧ α`. -/
noncomputable def p4CL (α : V) : V := lfpSet w (p4CF w U text append amk mkNil mkCons α)

/-- **`P4`'s operator**: one constructor `mkP4`, its one field read at
the container. -/
noncomputable def p4Op (XC : V) : V := sep U fun x => ∃ a, a ∈ˢ XC ∧ x = mkP4 a

/-- **The block's composed operator** `X ↦ P4Op (⟦P4C⟧ X)`. -/
noncomputable def p4F : V :=
  graph (fun X => p4Op U mkP4 (p4CL w U text append amk mkNil mkCons X)) (univ w)

/-- `P4*`: the block's carrier. -/
noncomputable def p4T : V := lfpSet w (p4F w U mkP4 text append amk mkNil mkCons)

/-- The restored motive domain `P4C P4`. -/
noncomputable def p4C1 : V :=
  p4CL w U text append amk mkNil mkCons (p4T w U mkP4 text append amk mkNil mkCons)

/-- The restored motive domain `Array (P4C P4)`. -/
noncomputable def p4C2 : V :=
  p4ArrayL w U amk mkNil mkCons (p4C1 w U mkP4 text append amk mkNil mkCons)

/-- The restored motive domain `List (P4C P4)`. -/
noncomputable def p4C3 : V :=
  p4ListL w U mkNil mkCons (p4C1 w U mkP4 text append amk mkNil mkCons)

end Defs

section Carrier

variable {w : Nat} {U : V} {mkP4 : V → V} {text : V → V} {append : V → V} {amk : V → V}
  {mkNil : V} {mkCons : V → V → V}

/-! ### The `List` container -/

theorem app_p4ListF {β Y : V} (hY : Y ∈ˢ (univ w : V)) :
    app (p4ListF w U mkNil mkCons β) Y = LOp U mkNil mkCons β Y :=
  app_graph hY

theorem p4ListF_mono (β : V) : MonoIn w (p4ListF w U mkNil mkCons β) := by
  intro X Y hX hY hle
  rw [app_p4ListF hX, app_p4ListF hY]
  exact LOp_mono (Subset.refl _) hle

theorem p4ListF_maps (hU : U ∈ˢ (univ w : V)) (β : V) :
    MapsIn w (p4ListF w U mkNil mkCons β) := by
  intro X hX
  rw [app_p4ListF hX]
  exact LOp_mem_univ hU _ _

theorem p4ListF_closed (hU : U ∈ˢ (univ w : V)) (β : V) :
    ∃ L, IsClosedIn w (p4ListF w U mkNil mkCons β) L :=
  ⟨U, hU, by rw [app_p4ListF hU]; exact LOp_subset_U⟩

theorem p4ListL_mem_univ (β : V) : p4ListL w U mkNil mkCons β ∈ˢ (univ w : V) :=
  lfpSet_mem_univ _ _

/-- The container's fixed-point equation at a parameter. -/
theorem p4ListL_eq (hU : U ∈ˢ (univ w : V)) (β : V) :
    LOp U mkNil mkCons β (p4ListL w U mkNil mkCons β) = p4ListL w U mkNil mkCons β := by
  have h := lfpSet_eq (F := p4ListF w U mkNil mkCons β) (p4ListF_closed hU β) (p4ListF_mono β)
    (p4ListF_maps hU β)
  rw [app_p4ListF (lfpSet_mem_univ _ _)] at h
  exact h

/-- The container's structural induction at a parameter. -/
theorem p4ListL_induction (hU : U ∈ˢ (univ w : V)) (β : V) (P : V → Prop)
    (hP : ∀ x, x ∈ˢ LOp U mkNil mkCons β (sep (p4ListL w U mkNil mkCons β) P) → P x) :
    ∀ x, x ∈ˢ p4ListL w U mkNil mkCons β → P x := by
  refine lfpSet_induction (p4ListF_closed hU β) (p4ListF_mono β) P fun x hx => hP x ?_
  rwa [app_p4ListF (univ_sep_mem (lfpSet_mem_univ _ _))] at hx

/-- **The map action on the carrier**, from `LOp_mono`, by leastness. -/
theorem p4ListL_mono (hU : U ∈ˢ (univ w : V)) {β β' : V} (hβ : β ⊆ˢ β') :
    p4ListL w U mkNil mkCons β ⊆ˢ p4ListL w U mkNil mkCons β' := by
  refine lfpSet_subset ⟨p4ListL_mem_univ β', ?_⟩
  rw [app_p4ListF (p4ListL_mem_univ β')]
  intro x hx
  rw [← p4ListL_eq hU β']
  exact LOp_mono hβ (Subset.refl _) x hx

theorem p4ListL_subset_U (hU : U ∈ˢ (univ w : V)) (β : V) :
    p4ListL w U mkNil mkCons β ⊆ˢ U := by
  intro x hx
  rw [← p4ListL_eq hU β] at hx
  exact LOp_subset_U x hx

/-! ### The `Array` container: no fixed point -/

theorem mem_p4ArrayL {β x : V} :
    x ∈ˢ p4ArrayL w U amk mkNil mkCons β ↔
      x ∈ˢ U ∧ ∃ l, l ∈ˢ p4ListL w U mkNil mkCons β ∧ x = amk l := mem_sep

theorem p4ArrayL_subset_U {β : V} : p4ArrayL w U amk mkNil mkCons β ⊆ˢ U := sep_subset

theorem p4ArrayL_mem_univ (hU : U ∈ˢ (univ w : V)) (β : V) :
    p4ArrayL w U amk mkNil mkCons β ∈ˢ (univ w : V) := univ_sep_mem hU

/-- **The map action on `⟦Array⟧`**, from the one on `⟦List⟧`. -/
theorem p4ArrayL_mono (hU : U ∈ˢ (univ w : V)) {β β' : V} (hβ : β ⊆ˢ β') :
    p4ArrayL w U amk mkNil mkCons β ⊆ˢ p4ArrayL w U amk mkNil mkCons β' := by
  intro x hx
  obtain ⟨hxU, l, hl, hx⟩ := mem_p4ArrayL.mp hx
  exact mem_p4ArrayL.mpr ⟨hxU, l, p4ListL_mono hU hβ l hl, hx⟩

theorem amk_mem_p4ArrayL (hU : U ∈ˢ (univ w : V)) (hAmU : ∀ l, l ∈ˢ U → amk l ∈ˢ U)
    {β l : V} (hl : l ∈ˢ p4ListL w U mkNil mkCons β) :
    amk l ∈ˢ p4ArrayL w U amk mkNil mkCons β :=
  mem_p4ArrayL.mpr ⟨hAmU l (p4ListL_subset_U hU β l hl), l, hl, rfl⟩

/-! ### The `P4C` container, composed through `Array` -/

theorem mem_p4COp {α Y x : V} :
    x ∈ˢ p4COp w U text append amk mkNil mkCons α Y ↔
      x ∈ˢ U ∧ ((∃ s, s ∈ˢ α ∧ x = text s) ∨
        (∃ ps, ps ∈ˢ p4ArrayL w U amk mkNil mkCons Y ∧ x = append ps)) := mem_sep

theorem p4COp_subset_U {α Y : V} : p4COp w U text append amk mkNil mkCons α Y ⊆ˢ U := sep_subset

theorem p4COp_mono (hU : U ∈ˢ (univ w : V)) {α α' Y Y' : V} (hα : α ⊆ˢ α') (hY : Y ⊆ˢ Y') :
    p4COp w U text append amk mkNil mkCons α Y
      ⊆ˢ p4COp w U text append amk mkNil mkCons α' Y' := by
  intro x hx
  obtain ⟨hxU, hx⟩ := mem_p4COp.mp hx
  refine mem_p4COp.mpr ⟨hxU, ?_⟩
  rcases hx with ⟨s, hs, hx⟩ | ⟨ps, hps, hx⟩
  · exact Or.inl ⟨s, hα s hs, hx⟩
  · exact Or.inr ⟨ps, p4ArrayL_mono hU hY ps hps, hx⟩

theorem app_p4CF {α Y : V} (hY : Y ∈ˢ (univ w : V)) :
    app (p4CF w U text append amk mkNil mkCons α) Y
      = p4COp w U text append amk mkNil mkCons α Y :=
  app_graph hY

theorem p4CF_mono (hU : U ∈ˢ (univ w : V)) (α : V) :
    MonoIn w (p4CF w U text append amk mkNil mkCons α) := by
  intro X Y hX hY hle
  rw [app_p4CF hX, app_p4CF hY]
  exact p4COp_mono hU (Subset.refl _) hle

theorem p4CF_maps (hU : U ∈ˢ (univ w : V)) (α : V) :
    MapsIn w (p4CF w U text append amk mkNil mkCons α) := by
  intro X hX
  rw [app_p4CF hX]
  exact univ_sep_mem hU

theorem p4CF_closed (hU : U ∈ˢ (univ w : V)) (α : V) :
    ∃ L, IsClosedIn w (p4CF w U text append amk mkNil mkCons α) L :=
  ⟨U, hU, by rw [app_p4CF hU]; exact p4COp_subset_U⟩

theorem p4CL_mem_univ (α : V) :
    p4CL w U text append amk mkNil mkCons α ∈ˢ (univ w : V) := lfpSet_mem_univ _ _

theorem p4CL_eq (hU : U ∈ˢ (univ w : V)) (α : V) :
    p4COp w U text append amk mkNil mkCons α (p4CL w U text append amk mkNil mkCons α)
      = p4CL w U text append amk mkNil mkCons α := by
  have h := lfpSet_eq (F := p4CF w U text append amk mkNil mkCons α) (p4CF_closed hU α)
    (p4CF_mono hU α) (p4CF_maps hU α)
  rw [app_p4CF (lfpSet_mem_univ _ _)] at h
  exact h

theorem p4CL_induction (hU : U ∈ˢ (univ w : V)) (α : V) (P : V → Prop)
    (hP : ∀ x, x ∈ˢ p4COp w U text append amk mkNil mkCons α
        (sep (p4CL w U text append amk mkNil mkCons α) P) → P x) :
    ∀ x, x ∈ˢ p4CL w U text append amk mkNil mkCons α → P x := by
  refine lfpSet_induction (p4CF_closed hU α) (p4CF_mono hU α) P fun x hx => hP x ?_
  rwa [app_p4CF (univ_sep_mem (lfpSet_mem_univ _ _))] at hx

/-- **The map action on `⟦P4C⟧`**, by leastness. -/
theorem p4CL_mono (hU : U ∈ˢ (univ w : V)) {α α' : V} (hα : α ⊆ˢ α') :
    p4CL w U text append amk mkNil mkCons α ⊆ˢ p4CL w U text append amk mkNil mkCons α' := by
  refine lfpSet_subset ⟨p4CL_mem_univ α', ?_⟩
  rw [app_p4CF (p4CL_mem_univ α')]
  intro x hx
  rw [← p4CL_eq hU α']
  exact p4COp_mono hU hα (Subset.refl _) x hx

theorem p4CL_subset_U (hU : U ∈ˢ (univ w : V)) (α : V) :
    p4CL w U text append amk mkNil mkCons α ⊆ˢ U := by
  intro x hx
  rw [← p4CL_eq hU α] at hx
  exact p4COp_subset_U x hx

/-! ### The block's composed operator -/

theorem mem_p4Op {XC x : V} :
    x ∈ˢ p4Op U mkP4 XC ↔ x ∈ˢ U ∧ ∃ a, a ∈ˢ XC ∧ x = mkP4 a := mem_sep

theorem p4Op_subset_U {XC : V} : p4Op U mkP4 XC ⊆ˢ U := sep_subset

theorem p4Op_mono {XC XC' : V} (h : XC ⊆ˢ XC') : p4Op U mkP4 XC ⊆ˢ p4Op U mkP4 XC' := by
  intro x hx
  obtain ⟨hxU, a, ha, hx⟩ := mem_p4Op.mp hx
  exact mem_p4Op.mpr ⟨hxU, a, h a ha, hx⟩

theorem app_p4F {X : V} (hX : X ∈ˢ (univ w : V)) :
    app (p4F w U mkP4 text append amk mkNil mkCons) X
      = p4Op U mkP4 (p4CL w U text append amk mkNil mkCons X) :=
  app_graph hX

/-- **The composed operator is monotone** — the one place the map
action in the parameter is used. -/
theorem p4F_mono (hU : U ∈ˢ (univ w : V)) :
    MonoIn w (p4F w U mkP4 text append amk mkNil mkCons) := by
  intro X Y hX hY hle
  rw [app_p4F hX, app_p4F hY]
  exact p4Op_mono (p4CL_mono hU hle)

theorem p4F_maps (hU : U ∈ˢ (univ w : V)) :
    MapsIn w (p4F w U mkP4 text append amk mkNil mkCons) := by
  intro X hX
  rw [app_p4F hX]
  exact univ_sep_mem hU

/-- The closed member (W): the bounding set itself. -/
theorem p4F_closed (hU : U ∈ˢ (univ w : V)) :
    ∃ L, IsClosedIn w (p4F w U mkP4 text append amk mkNil mkCons) L :=
  ⟨U, hU, by rw [app_p4F hU]; exact p4Op_subset_U⟩

theorem p4T_mem_univ : p4T w U mkP4 text append amk mkNil mkCons ∈ˢ (univ w : V) :=
  lfpSet_mem_univ _ _

/-! ### The four restored motive domains -/

/-- `P4* = P4Op (⟦P4C⟧ P4*)`. -/
theorem p4T_eq (hU : U ∈ˢ (univ w : V)) :
    p4Op U mkP4 (p4C1 w U mkP4 text append amk mkNil mkCons)
      = p4T w U mkP4 text append amk mkNil mkCons := by
  have h := lfpSet_eq (F := p4F w U mkP4 text append amk mkNil mkCons) (p4F_closed hU)
    (p4F_mono hU) (p4F_maps hU)
  rw [app_p4F (lfpSet_mem_univ _ _)] at h
  exact h

/-- Structural induction on the composed carrier. -/
theorem p4T_induction (hU : U ∈ˢ (univ w : V)) (P : V → Prop)
    (hP : ∀ x, x ∈ˢ p4Op U mkP4 (p4CL w U text append amk mkNil mkCons
        (sep (p4T w U mkP4 text append amk mkNil mkCons) P)) → P x) :
    ∀ x, x ∈ˢ p4T w U mkP4 text append amk mkNil mkCons → P x := by
  refine lfpSet_induction (p4F_closed hU) (p4F_mono hU) P fun x hx => hP x ?_
  rwa [app_p4F (univ_sep_mem (lfpSet_mem_univ _ _))] at hx

/-- `p4C1 = P4COp P4* p4C1`. -/
theorem p4C1_eq (hU : U ∈ˢ (univ w : V)) :
    p4COp w U text append amk mkNil mkCons (p4T w U mkP4 text append amk mkNil mkCons)
        (p4C1 w U mkP4 text append amk mkNil mkCons)
      = p4C1 w U mkP4 text append amk mkNil mkCons :=
  p4CL_eq hU _

/-- `p4C3 = LOp p4C1 p4C3`. -/
theorem p4C3_eq (hU : U ∈ˢ (univ w : V)) :
    LOp U mkNil mkCons (p4C1 w U mkP4 text append amk mkNil mkCons)
        (p4C3 w U mkP4 text append amk mkNil mkCons)
      = p4C3 w U mkP4 text append amk mkNil mkCons :=
  p4ListL_eq hU _

theorem p4T_subset_U (hU : U ∈ˢ (univ w : V)) :
    p4T w U mkP4 text append amk mkNil mkCons ⊆ˢ U := by
  intro x hx
  rw [← p4T_eq hU] at hx
  exact p4Op_subset_U x hx

theorem p4C1_subset_U (hU : U ∈ˢ (univ w : V)) :
    p4C1 w U mkP4 text append amk mkNil mkCons ⊆ˢ U := p4CL_subset_U hU _

theorem p4C2_subset_U : p4C2 w U mkP4 text append amk mkNil mkCons ⊆ˢ U := p4ArrayL_subset_U

theorem p4C3_subset_U (hU : U ∈ˢ (univ w : V)) :
    p4C3 w U mkP4 text append amk mkNil mkCons ⊆ˢ U := p4ListL_subset_U hU _

/-! ### The constructor decompositions -/

/-- Every `P4` is a `mkP4`. -/
theorem p4T_cases (hU : U ∈ˢ (univ w : V)) {x : V}
    (hx : x ∈ˢ p4T w U mkP4 text append amk mkNil mkCons) :
    ∃ a, a ∈ˢ p4C1 w U mkP4 text append amk mkNil mkCons ∧ x = mkP4 a := by
  rw [← p4T_eq hU] at hx
  exact (mem_p4Op.mp hx).2

/-- Every `P4C P4` is a `text` or an `append`. -/
theorem p4C1_cases (hU : U ∈ˢ (univ w : V)) {a : V}
    (ha : a ∈ˢ p4C1 w U mkP4 text append amk mkNil mkCons) :
    (∃ s, s ∈ˢ p4T w U mkP4 text append amk mkNil mkCons ∧ a = text s) ∨
      (∃ ps, ps ∈ˢ p4C2 w U mkP4 text append amk mkNil mkCons ∧ a = append ps) := by
  rw [← p4C1_eq hU] at ha
  exact (mem_p4COp.mp ha).2

/-- Every `Array (P4C P4)` is an `amk`. -/
theorem p4C2_cases {ps : V} (hps : ps ∈ˢ p4C2 w U mkP4 text append amk mkNil mkCons) :
    ∃ l, l ∈ˢ p4C3 w U mkP4 text append amk mkNil mkCons ∧ ps = amk l :=
  (mem_p4ArrayL.mp hps).2

/-- Every `List (P4C P4)` is `mkNil` or a `mkCons`. -/
theorem p4C3_cases (hU : U ∈ˢ (univ w : V)) {l : V}
    (hl : l ∈ˢ p4C3 w U mkP4 text append amk mkNil mkCons) :
    l = mkNil ∨ ∃ h t, h ∈ˢ p4C1 w U mkP4 text append amk mkNil mkCons ∧
      t ∈ˢ p4C3 w U mkP4 text append amk mkNil mkCons ∧ l = mkCons h t := by
  rw [← p4C3_eq hU] at hl
  exact (mem_LOp.mp hl).2

/-! ### The constructors land in the carriers -/

theorem mkP4_mem_p4T (hU : U ∈ˢ (univ w : V)) (hP4U : ∀ a, a ∈ˢ U → mkP4 a ∈ˢ U) {a : V}
    (ha : a ∈ˢ p4C1 w U mkP4 text append amk mkNil mkCons) :
    mkP4 a ∈ˢ p4T w U mkP4 text append amk mkNil mkCons := by
  rw [← p4T_eq hU]
  exact mem_p4Op.mpr ⟨hP4U a (p4C1_subset_U hU a ha), a, ha, rfl⟩

theorem text_mem_p4C1 (hU : U ∈ˢ (univ w : V)) (hTxU : ∀ s, s ∈ˢ U → text s ∈ˢ U) {s : V}
    (hs : s ∈ˢ p4T w U mkP4 text append amk mkNil mkCons) :
    text s ∈ˢ p4C1 w U mkP4 text append amk mkNil mkCons := by
  rw [← p4C1_eq hU]
  exact mem_p4COp.mpr ⟨hTxU s (p4T_subset_U hU s hs), Or.inl ⟨s, hs, rfl⟩⟩

theorem append_mem_p4C1 (hU : U ∈ˢ (univ w : V)) (hApU : ∀ ps, ps ∈ˢ U → append ps ∈ˢ U) {ps : V}
    (hps : ps ∈ˢ p4C2 w U mkP4 text append amk mkNil mkCons) :
    append ps ∈ˢ p4C1 w U mkP4 text append amk mkNil mkCons := by
  rw [← p4C1_eq hU]
  exact mem_p4COp.mpr ⟨hApU ps (p4C2_subset_U ps hps), Or.inr ⟨ps, hps, rfl⟩⟩

theorem amk_mem_p4C2 (hU : U ∈ˢ (univ w : V)) (hAmU : ∀ l, l ∈ˢ U → amk l ∈ˢ U) {l : V}
    (hl : l ∈ˢ p4C3 w U mkP4 text append amk mkNil mkCons) :
    amk l ∈ˢ p4C2 w U mkP4 text append amk mkNil mkCons :=
  amk_mem_p4ArrayL hU hAmU hl

theorem mkNil_mem_p4C3 (hU : U ∈ˢ (univ w : V)) (hNilU : mkNil ∈ˢ U) :
    mkNil ∈ˢ p4C3 w U mkP4 text append amk mkNil mkCons := by
  rw [← p4C3_eq hU]
  exact mkNil_mem_LOp hNilU _ _

theorem mkCons_mem_p4C3 (hU : U ∈ˢ (univ w : V))
    (hConsU : ∀ h t, h ∈ˢ U → t ∈ˢ U → mkCons h t ∈ˢ U) {h t : V}
    (hh : h ∈ˢ p4C1 w U mkP4 text append amk mkNil mkCons)
    (ht : t ∈ˢ p4C3 w U mkP4 text append amk mkNil mkCons) :
    mkCons h t ∈ˢ p4C3 w U mkP4 text append amk mkNil mkCons := by
  rw [← p4C3_eq hU]
  exact mkCons_mem_LOp hConsU (p4C1_subset_U hU) (p4C3_subset_U hU) hh ht

end Carrier

/-! ## The recursion: the index set, the predecessors, the bound, the step -/

section Rec

variable (w : Nat) (U : V) (mkP4 : V → V) (text : V → V) (append : V → V) (amk : V → V)
  (mkNil : V) (mkCons : V → V → V)

/-- The index set of the simultaneous recursion: the disjoint union of
the four restored motive domains. -/
noncomputable def p4IdxSet : V :=
  binUnion (image (kpair (vnat 0)) (p4T w U mkP4 text append amk mkNil mkCons))
    (binUnion (image (kpair (vnat 1)) (p4C1 w U mkP4 text append amk mkNil mkCons))
      (binUnion (image (kpair (vnat 2)) (p4C2 w U mkP4 text append amk mkNil mkCons))
        (image (kpair (vnat 3)) (p4C3 w U mkP4 text append amk mkNil mkCons))))

/-- The predecessor relation, read off the six ι rules. -/
def P4Rel (p q : V) : Prop :=
  (∃ a, p = kpair (vnat 0) (mkP4 a) ∧ q = kpair (vnat 1) a) ∨
  (∃ s, p = kpair (vnat 1) (text s) ∧ q = kpair (vnat 0) s) ∨
  (∃ ps, p = kpair (vnat 1) (append ps) ∧ q = kpair (vnat 2) ps) ∨
  (∃ l, p = kpair (vnat 2) (amk l) ∧ q = kpair (vnat 3) l) ∨
  (∃ h t, p = kpair (vnat 3) (mkCons h t) ∧ (q = kpair (vnat 1) h ∨ q = kpair (vnat 3) t))

/-- The predecessor sets. -/
noncomputable def p4Pred (p : V) : V :=
  sep (p4IdxSet w U mkP4 text append amk mkNil mkCons) (P4Rel mkP4 text append amk mkCons p)

variable (M₀ M₁ M₂ M₃ : V → V) (mk : V → V → V) (text' : V → V → V) (append' : V → V → V)
  (amk' : V → V → V) (nil : V) (cons : V → V → V → V → V)

open Classical in
/-- The bound: the motives' fibres, keyed on the component tag. -/
noncomputable def p4B (p : V) : V :=
  if h : ∃ x, p = kpair (vnat 0) x then M₀ (Classical.choose h)
  else if h : ∃ x, p = kpair (vnat 1) x then M₁ (Classical.choose h)
  else if h : ∃ x, p = kpair (vnat 2) x then M₂ (Classical.choose h)
  else if h : ∃ x, p = kpair (vnat 3) x then M₃ (Classical.choose h)
  else empty

open Classical in
/-- The step: the minors at the predecessors' values. -/
noncomputable def p4St (p g : V) : V :=
  if h : ∃ a, p = kpair (vnat 0) (mkP4 a) then
    mk (Classical.choose h) (app g (kpair (vnat 1) (Classical.choose h)))
  else if h : ∃ s, p = kpair (vnat 1) (text s) then
    text' (Classical.choose h) (app g (kpair (vnat 0) (Classical.choose h)))
  else if h : ∃ ps, p = kpair (vnat 1) (append ps) then
    append' (Classical.choose h) (app g (kpair (vnat 2) (Classical.choose h)))
  else if h : ∃ l, p = kpair (vnat 2) (amk l) then
    amk' (Classical.choose h) (app g (kpair (vnat 3) (Classical.choose h)))
  else if p = kpair (vnat 3) mkNil then nil
  else if h : ∃ q : V × V, p = kpair (vnat 3) (mkCons q.1 q.2) then
    cons (Classical.choose h).1 (Classical.choose h).2
      (app g (kpair (vnat 1) (Classical.choose h).1))
      (app g (kpair (vnat 3) (Classical.choose h).2))
  else empty

/-- **The recursor**: the graph's selector.  `p4Rec … (k, x)` is the
stream's `P4.rec_k … x` (`P4.rec` itself at `k = 0`). -/
noncomputable def p4Rec (ℓ : Nat) (i : V) : V :=
  recSel (recGraph ℓ (p4IdxSet w U mkP4 text append amk mkNil mkCons)
    (p4Pred w U mkP4 text append amk mkNil mkCons) (p4B M₀ M₁ M₂ M₃)
    (p4St mkP4 text append amk mkNil mkCons mk text' append' amk' nil cons)) i

end Rec

section RecFacts

variable {w : Nat} {U : V} {mkP4 : V → V} {text : V → V} {append : V → V} {amk : V → V}
  {mkNil : V} {mkCons : V → V → V}

local notation "C₀" => p4T w U mkP4 text append amk mkNil mkCons
local notation "C₁" => p4C1 w U mkP4 text append amk mkNil mkCons
local notation "C₂" => p4C2 w U mkP4 text append amk mkNil mkCons
local notation "C₃" => p4C3 w U mkP4 text append amk mkNil mkCons
local notation "I*" => p4IdxSet w U mkP4 text append amk mkNil mkCons

theorem mem_p4IdxSet {p : V} :
    p ∈ˢ I* ↔ (∃ x, x ∈ˢ C₀ ∧ p = kpair (vnat 0) x) ∨ (∃ a, a ∈ˢ C₁ ∧ p = kpair (vnat 1) a) ∨
      (∃ ps, ps ∈ˢ C₂ ∧ p = kpair (vnat 2) ps) ∨
      (∃ l, l ∈ˢ C₃ ∧ p = kpair (vnat 3) l) := by
  unfold p4IdxSet
  rw [mem_binUnion, mem_binUnion, mem_binUnion, mem_image, mem_image, mem_image, mem_image]

theorem p4_mem_idx0 {x : V} (hx : x ∈ˢ C₀) : kpair (vnat 0) x ∈ˢ I* :=
  mem_p4IdxSet.mpr (Or.inl ⟨x, hx, rfl⟩)

theorem p4_mem_idx1 {a : V} (ha : a ∈ˢ C₁) : kpair (vnat 1) a ∈ˢ I* :=
  mem_p4IdxSet.mpr (Or.inr (Or.inl ⟨a, ha, rfl⟩))

theorem p4_mem_idx2 {ps : V} (hps : ps ∈ˢ C₂) : kpair (vnat 2) ps ∈ˢ I* :=
  mem_p4IdxSet.mpr (Or.inr (Or.inr (Or.inl ⟨ps, hps, rfl⟩)))

theorem p4_mem_idx3 {l : V} (hl : l ∈ˢ C₃) : kpair (vnat 3) l ∈ˢ I* :=
  mem_p4IdxSet.mpr (Or.inr (Or.inr (Or.inr ⟨l, hl, rfl⟩)))

theorem p4Pred_subset (p : V) : p4Pred w U mkP4 text append amk mkNil mkCons p ⊆ˢ I* := sep_subset

theorem mem_p4Pred {p q : V} :
    q ∈ˢ p4Pred w U mkP4 text append amk mkNil mkCons p ↔
      q ∈ˢ I* ∧ P4Rel mkP4 text append amk mkCons p q := mem_sep

/-! ### The constructors' predecessors, under injectivity -/

variable (hP4 : ∀ a a', mkP4 a = mkP4 a' → a = a')
  (hTx : ∀ s s', text s = text s' → s = s')
  (hAp : ∀ ps ps', append ps = append ps' → ps = ps')
  (hAm : ∀ l l', amk l = amk l' → l = l')
  (hCo : ∀ h t h' t', mkCons h t = mkCons h' t' → h = h' ∧ t = t')
  (hTA : ∀ s ps, text s ≠ append ps)
  (hNC : ∀ h t, mkNil ≠ mkCons h t)

include hP4 in
theorem mem_p4Pred_mk {a q : V} :
    q ∈ˢ p4Pred w U mkP4 text append amk mkNil mkCons (kpair (vnat 0) (mkP4 a)) ↔
      q ∈ˢ I* ∧ q = kpair (vnat 1) a := by
  rw [mem_p4Pred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inl ⟨a, rfl, h⟩⟩
  rcases h with ⟨a', h₁, h₂⟩ | ⟨s, h₁, -⟩ | ⟨ps, h₁, -⟩ | ⟨l, h₁, -⟩ | ⟨hh, tt, h₁, -⟩
  · rw [h₂, hP4 a a' (kpair_inj h₁).2]
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)

include hTx hTA in
theorem mem_p4Pred_text {s q : V} :
    q ∈ˢ p4Pred w U mkP4 text append amk mkNil mkCons (kpair (vnat 1) (text s)) ↔
      q ∈ˢ I* ∧ q = kpair (vnat 0) s := by
  rw [mem_p4Pred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inr (Or.inl ⟨s, rfl, h⟩)⟩
  rcases h with ⟨a, h₁, -⟩ | ⟨s', h₁, h₂⟩ | ⟨ps, h₁, -⟩ | ⟨l, h₁, -⟩ | ⟨hh, tt, h₁, -⟩
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · rw [h₂, hTx s s' (kpair_inj h₁).2]
  · exact absurd (kpair_inj h₁).2 (hTA s ps)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)

include hAp hTA in
theorem mem_p4Pred_append {ps q : V} :
    q ∈ˢ p4Pred w U mkP4 text append amk mkNil mkCons (kpair (vnat 1) (append ps)) ↔
      q ∈ˢ I* ∧ q = kpair (vnat 2) ps := by
  rw [mem_p4Pred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inr (Or.inr (Or.inl ⟨ps, rfl, h⟩))⟩
  rcases h with ⟨a, h₁, -⟩ | ⟨s, h₁, -⟩ | ⟨ps', h₁, h₂⟩ | ⟨l, h₁, -⟩ | ⟨hh, tt, h₁, -⟩
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (kpair_inj h₁).2.symm (hTA s ps)
  · rw [h₂, hAp ps ps' (kpair_inj h₁).2]
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)

include hAm in
theorem mem_p4Pred_amk {l q : V} :
    q ∈ˢ p4Pred w U mkP4 text append amk mkNil mkCons (kpair (vnat 2) (amk l)) ↔
      q ∈ˢ I* ∧ q = kpair (vnat 3) l := by
  rw [mem_p4Pred]
  refine and_congr_right fun _ =>
    ⟨fun h => ?_, fun h => Or.inr (Or.inr (Or.inr (Or.inl ⟨l, rfl, h⟩)))⟩
  rcases h with ⟨a, h₁, -⟩ | ⟨s, h₁, -⟩ | ⟨ps, h₁, -⟩ | ⟨l', h₁, h₂⟩ | ⟨hh, tt, h₁, -⟩
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · rw [h₂, hAm l l' (kpair_inj h₁).2]
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)

include hNC in
theorem mem_p4Pred_nil {q : V} :
    ¬ q ∈ˢ p4Pred w U mkP4 text append amk mkNil mkCons (kpair (vnat 3) mkNil) := by
  intro h
  rw [mem_p4Pred] at h
  rcases h.2 with ⟨a, h₁, -⟩ | ⟨s, h₁, -⟩ | ⟨ps, h₁, -⟩ | ⟨l, h₁, -⟩ | ⟨hh, tt, h₁, -⟩
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact hNC hh tt (kpair_inj h₁).2

include hCo in
theorem mem_p4Pred_cons {h t q : V} :
    q ∈ˢ p4Pred w U mkP4 text append amk mkNil mkCons (kpair (vnat 3) (mkCons h t)) ↔
      q ∈ˢ I* ∧ (q = kpair (vnat 1) h ∨ q = kpair (vnat 3) t) := by
  rw [mem_p4Pred]
  refine and_congr_right fun _ =>
    ⟨fun hq => ?_, fun hq => Or.inr (Or.inr (Or.inr (Or.inr ⟨h, t, rfl, hq⟩)))⟩
  rcases hq with ⟨a, h₁, -⟩ | ⟨s, h₁, -⟩ | ⟨ps, h₁, -⟩ | ⟨l, h₁, -⟩ | ⟨h', t', h₁, h₂⟩
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · exact absurd (vnat_inj (kpair_inj h₁).1) (by decide)
  · obtain ⟨rfl, rfl⟩ := hCo _ _ _ _ (kpair_inj h₁).2
    exact h₂

/-! ### The bound and the step compute -/

variable {M₀ M₁ M₂ M₃ : V → V} {mk : V → V → V} {text' : V → V → V} {append' : V → V → V}
  {amk' : V → V → V} {nil : V} {cons : V → V → V → V → V}

theorem p4B_0 (x : V) : p4B M₀ M₁ M₂ M₃ (kpair (vnat 0) x) = M₀ x := by
  unfold p4B
  rw [dif_pos ⟨x, rfl⟩]
  have h := Classical.choose_spec (⟨x, rfl⟩ : ∃ y, kpair (vnat 0 : V) x = kpair (vnat 0) y)
  exact congrArg M₀ (kpair_inj h).2.symm

theorem p4B_1 (a : V) : p4B M₀ M₁ M₂ M₃ (kpair (vnat 1) a) = M₁ a := by
  unfold p4B
  rw [dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)), dif_pos ⟨a, rfl⟩]
  have h := Classical.choose_spec (⟨a, rfl⟩ : ∃ y, kpair (vnat 1 : V) a = kpair (vnat 1) y)
  exact congrArg M₁ (kpair_inj h).2.symm

theorem p4B_2 (ps : V) : p4B M₀ M₁ M₂ M₃ (kpair (vnat 2) ps) = M₂ ps := by
  unfold p4B
  rw [dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)),
    dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)), dif_pos ⟨ps, rfl⟩]
  have h := Classical.choose_spec (⟨ps, rfl⟩ : ∃ y, kpair (vnat 2 : V) ps = kpair (vnat 2) y)
  exact congrArg M₂ (kpair_inj h).2.symm

theorem p4B_3 (l : V) : p4B M₀ M₁ M₂ M₃ (kpair (vnat 3) l) = M₃ l := by
  unfold p4B
  rw [dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)),
    dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)),
    dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)), dif_pos ⟨l, rfl⟩]
  have h := Classical.choose_spec (⟨l, rfl⟩ : ∃ y, kpair (vnat 3 : V) l = kpair (vnat 3) y)
  exact congrArg M₃ (kpair_inj h).2.symm

include hP4 in
theorem p4St_mk (a g : V) :
    p4St mkP4 text append amk mkNil mkCons mk text' append' amk' nil cons
        (kpair (vnat 0) (mkP4 a)) g = mk a (app g (kpair (vnat 1) a)) := by
  unfold p4St
  rw [dif_pos ⟨a, rfl⟩]
  have h := Classical.choose_spec
    (⟨a, rfl⟩ : ∃ y, kpair (vnat 0 : V) (mkP4 a) = kpair (vnat 0) (mkP4 y))
  rw [← hP4 _ _ (kpair_inj h).2]

include hTx in
theorem p4St_text (s g : V) :
    p4St mkP4 text append amk mkNil mkCons mk text' append' amk' nil cons
        (kpair (vnat 1) (text s)) g = text' s (app g (kpair (vnat 0) s)) := by
  unfold p4St
  rw [dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)), dif_pos ⟨s, rfl⟩]
  have h := Classical.choose_spec
    (⟨s, rfl⟩ : ∃ y, kpair (vnat 1 : V) (text s) = kpair (vnat 1) (text y))
  rw [← hTx _ _ (kpair_inj h).2]

include hAp hTA in
theorem p4St_append (ps g : V) :
    p4St mkP4 text append amk mkNil mkCons mk text' append' amk' nil cons
        (kpair (vnat 1) (append ps)) g = append' ps (app g (kpair (vnat 2) ps)) := by
  unfold p4St
  rw [dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)),
    dif_neg (fun ⟨s, h⟩ => hTA s ps (kpair_inj h).2.symm), dif_pos ⟨ps, rfl⟩]
  have h := Classical.choose_spec
    (⟨ps, rfl⟩ : ∃ y, kpair (vnat 1 : V) (append ps) = kpair (vnat 1) (append y))
  rw [← hAp _ _ (kpair_inj h).2]

include hAm in
theorem p4St_amk (l g : V) :
    p4St mkP4 text append amk mkNil mkCons mk text' append' amk' nil cons
        (kpair (vnat 2) (amk l)) g = amk' l (app g (kpair (vnat 3) l)) := by
  unfold p4St
  rw [dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)),
    dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)),
    dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)), dif_pos ⟨l, rfl⟩]
  have h := Classical.choose_spec
    (⟨l, rfl⟩ : ∃ y, kpair (vnat 2 : V) (amk l) = kpair (vnat 2) (amk y))
  rw [← hAm _ _ (kpair_inj h).2]

theorem p4St_nil (g : V) :
    p4St mkP4 text append amk mkNil mkCons mk text' append' amk' nil cons
        (kpair (vnat 3) mkNil) g = nil := by
  unfold p4St
  rw [dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)),
    dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)),
    dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)),
    dif_neg (fun ⟨_, h⟩ => absurd (vnat_inj (kpair_inj h).1) (by decide)), if_pos rfl]

include hCo hNC in
theorem p4St_cons (h t g : V) :
    p4St mkP4 text append amk mkNil mkCons mk text' append' amk' nil cons
        (kpair (vnat 3) (mkCons h t)) g
      = cons h t (app g (kpair (vnat 1) h)) (app g (kpair (vnat 3) t)) := by
  unfold p4St
  rw [dif_neg (fun ⟨_, h'⟩ => absurd (vnat_inj (kpair_inj h').1) (by decide)),
    dif_neg (fun ⟨_, h'⟩ => absurd (vnat_inj (kpair_inj h').1) (by decide)),
    dif_neg (fun ⟨_, h'⟩ => absurd (vnat_inj (kpair_inj h').1) (by decide)),
    dif_neg (fun ⟨_, h'⟩ => absurd (vnat_inj (kpair_inj h').1) (by decide)),
    if_neg (fun h' => hNC h t (kpair_inj h').2.symm), dif_pos ⟨(h, t), rfl⟩]
  have hs := Classical.choose_spec
    (⟨(h, t), rfl⟩ :
      ∃ q : V × V, kpair (vnat 3 : V) (mkCons h t) = kpair (vnat 3) (mkCons q.1 q.2))
  obtain ⟨h₁, h₂⟩ := hCo _ _ _ _ (kpair_inj hs).2
  rw [← h₁, ← h₂]

/-! ### The recursion theorem's hypotheses -/

variable (hU : U ∈ˢ (univ w : V))
  (hP4U : ∀ a, a ∈ˢ U → mkP4 a ∈ˢ U)
  (hTxU : ∀ s, s ∈ˢ U → text s ∈ˢ U)
  (hApU : ∀ ps, ps ∈ˢ U → append ps ∈ˢ U)
  (hAmU : ∀ l, l ∈ˢ U → amk l ∈ˢ U)
  (hNilU : mkNil ∈ˢ U)
  (hConsU : ∀ h t, h ∈ˢ U → t ∈ˢ U → mkCons h t ∈ˢ U)
  {ℓ : Nat}
  -- (the local notations are not expanded inside `variable` binders:
  -- the carriers are spelled out here)
  (hM₀ : ∀ x, x ∈ˢ p4T w U mkP4 text append amk mkNil mkCons → M₀ x ∈ˢ (univ ℓ : V))
  (hM₁ : ∀ a, a ∈ˢ p4C1 w U mkP4 text append amk mkNil mkCons → M₁ a ∈ˢ (univ ℓ : V))
  (hM₂ : ∀ ps, ps ∈ˢ p4C2 w U mkP4 text append amk mkNil mkCons → M₂ ps ∈ˢ (univ ℓ : V))
  (hM₃ : ∀ l, l ∈ˢ p4C3 w U mkP4 text append amk mkNil mkCons → M₃ l ∈ˢ (univ ℓ : V))
  (hmk : ∀ a ih, a ∈ˢ p4C1 w U mkP4 text append amk mkNil mkCons → ih ∈ˢ M₁ a →
    mk a ih ∈ˢ M₀ (mkP4 a))
  (htext : ∀ s ih, s ∈ˢ p4T w U mkP4 text append amk mkNil mkCons → ih ∈ˢ M₀ s →
    text' s ih ∈ˢ M₁ (text s))
  (happend : ∀ ps ih, ps ∈ˢ p4C2 w U mkP4 text append amk mkNil mkCons → ih ∈ˢ M₂ ps →
    append' ps ih ∈ˢ M₁ (append ps))
  (hamk : ∀ l ih, l ∈ˢ p4C3 w U mkP4 text append amk mkNil mkCons → ih ∈ˢ M₃ l →
    amk' l ih ∈ˢ M₂ (amk l))
  (hnil : nil ∈ˢ M₃ mkNil)
  (hcons : ∀ h t ih₁ ih₃, h ∈ˢ p4C1 w U mkP4 text append amk mkNil mkCons →
    t ∈ˢ p4C3 w U mkP4 text append amk mkNil mkCons → ih₁ ∈ˢ M₁ h → ih₃ ∈ˢ M₃ t →
    cons h t ih₁ ih₃ ∈ˢ M₃ (mkCons h t))

local notation "G*" => recGraph ℓ I* (p4Pred w U mkP4 text append amk mkNil mkCons)
  (p4B M₀ M₁ M₂ M₃) (p4St mkP4 text append amk mkNil mkCons mk text' append' amk' nil cons)
local notation "R*" => p4Rec w U mkP4 text append amk mkNil mkCons M₀ M₁ M₂ M₃ mk text' append'
  amk' nil cons ℓ
local notation "Acc*" => accFam I* (p4Pred w U mkP4 text append amk mkNil mkCons) (fun _ => True)

include hM₀ hM₁ hM₂ hM₃ in
theorem p4B_mem_univ : ∀ i, i ∈ˢ I* → p4B M₀ M₁ M₂ M₃ i ∈ˢ (univ ℓ : V) := by
  intro i hi
  rcases mem_p4IdxSet.mp hi with ⟨x, hx, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨ps, hps, rfl⟩ | ⟨l, hl, rfl⟩
  · rw [p4B_0]; exact hM₀ x hx
  · rw [p4B_1]; exact hM₁ a ha
  · rw [p4B_2]; exact hM₂ ps hps
  · rw [p4B_3]; exact hM₃ l hl

include hM₀ hM₁ hM₂ hM₃ in
/-- The graph's fibres lie in the bound. -/
theorem p4Graph_subset_B {i v : V} (hi : i ∈ˢ I*) (hv : v ∈ˢ app G* i) :
    v ∈ˢ p4B M₀ M₁ M₂ M₃ i := by
  rw [app_recGraph_eq (p4B_mem_univ hM₀ hM₁ hM₂ hM₃) (fun i _ => p4Pred_subset i) hi] at hv
  exact (mem_recGraphFibre.mp hv).1

include hP4 hTx hAp hAm hCo hTA hNC hU hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- **The step is typed**: at every index, the minor at the
predecessors' graph values lands in the motive's fibre. -/
theorem p4St_mem :
    ∀ i, i ∈ˢ I* → ∀ g, g ∈ˢ piSet (p4Pred w U mkP4 text append amk mkNil mkCons i)
        (fun j => app G* j) →
      p4St mkP4 text append amk mkNil mkCons mk text' append' amk' nil cons i g
        ∈ˢ p4B M₀ M₁ M₂ M₃ i := by
  intro i hi g hg
  have hval : ∀ j, j ∈ˢ p4Pred w U mkP4 text append amk mkNil mkCons i →
      app g j ∈ˢ p4B M₀ M₁ M₂ M₃ j := fun j hj =>
    p4Graph_subset_B hM₀ hM₁ hM₂ hM₃ (p4Pred_subset i j hj) (app_mem_of_mem_piSet hg hj)
  rcases mem_p4IdxSet.mp hi with ⟨x, hx, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨ps, hps, rfl⟩ | ⟨l, hl, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := p4T_cases hU hx
    rw [p4St_mk hP4, p4B_0]
    have h := hval (kpair (vnat 1) a) ((mem_p4Pred_mk hP4).mpr ⟨p4_mem_idx1 ha, rfl⟩)
    rw [p4B_1] at h
    exact hmk a _ ha h
  · rcases p4C1_cases hU ha with ⟨s, hs, rfl⟩ | ⟨ps, hps, rfl⟩
    · rw [p4St_text hTx, p4B_1]
      have h := hval (kpair (vnat 0) s) ((mem_p4Pred_text hTx hTA).mpr ⟨p4_mem_idx0 hs, rfl⟩)
      rw [p4B_0] at h
      exact htext s _ hs h
    · rw [p4St_append hAp hTA, p4B_1]
      have h := hval (kpair (vnat 2) ps) ((mem_p4Pred_append hAp hTA).mpr ⟨p4_mem_idx2 hps, rfl⟩)
      rw [p4B_2] at h
      exact happend ps _ hps h
  · obtain ⟨l, hl, rfl⟩ := p4C2_cases hps
    rw [p4St_amk hAm, p4B_2]
    have h := hval (kpair (vnat 3) l) ((mem_p4Pred_amk hAm).mpr ⟨p4_mem_idx3 hl, rfl⟩)
    rw [p4B_3] at h
    exact hamk l _ hl h
  · rcases p4C3_cases hU hl with rfl | ⟨h, t, hh, ht, rfl⟩
    · rw [p4St_nil, p4B_3]; exact hnil
    · rw [p4St_cons hCo hNC, p4B_3]
      have h₁ := hval (kpair (vnat 1) h) ((mem_p4Pred_cons hCo).mpr ⟨p4_mem_idx1 hh, Or.inl rfl⟩)
      have h₃ := hval (kpair (vnat 3) t) ((mem_p4Pred_cons hCo).mpr ⟨p4_mem_idx3 ht, Or.inr rfl⟩)
      rw [p4B_1] at h₁
      rw [p4B_3] at h₃
      exact hcons h t _ _ hh ht h₁ h₃

/-! ### Accessibility: the three nested inductions -/

/-- The `Acc` family's introduction rule: an index all of whose
predecessors are accessible is. -/
theorem p4Acc_intro {i : V} (hi : i ∈ˢ I*)
    (h : ∀ j, j ∈ˢ p4Pred w U mkP4 text append amk mkNil mkCons i → ∃ y, y ∈ˢ app Acc* j) :
    (pt : V) ∈ˢ app Acc* i := by
  unfold accFam
  rw [← app_lfpFamSet_eq ⟨_, accStep_closed⟩ (accStep_mono fun i _ => p4Pred_subset i)
    accStep_maps hi, app_app_accStep (lfpFamSet_mem _ _ _) hi]
  exact pt_mem_truthVal ⟨trivial, h⟩

include hCo hNC hU hNilU hConsU in
/-- **`List`'s induction at the parameter of accessible `P4C`-values**:
every list over a set `S` of accessible `P4C P4`-values is a
`List (P4C P4)` and accessible. -/
theorem p4AccL_of_param {S : V}
    (hS : ∀ a, a ∈ˢ S → a ∈ˢ C₁ ∧ ∃ y, y ∈ˢ app Acc* (kpair (vnat 1) a)) :
    ∀ l, l ∈ˢ p4ListL w U mkNil mkCons S →
      l ∈ˢ C₃ ∧ ∃ y, y ∈ˢ app Acc* (kpair (vnat 3) l) := by
  refine p4ListL_induction hU S _ fun l hl => ?_
  obtain ⟨-, hl⟩ := mem_LOp.mp hl
  rcases hl with rfl | ⟨h, t, hh, ht, rfl⟩
  · exact ⟨mkNil_mem_p4C3 hU hNilU, pt,
      p4Acc_intro (p4_mem_idx3 (mkNil_mem_p4C3 hU hNilU))
        fun j hj => absurd hj (mem_p4Pred_nil hNC)⟩
  · obtain ⟨htC, hacct⟩ := (mem_sep.mp ht).2
    obtain ⟨hhC, hacch⟩ := hS h hh
    refine ⟨mkCons_mem_p4C3 hU hConsU hhC htC, pt,
      p4Acc_intro (p4_mem_idx3 (mkCons_mem_p4C3 hU hConsU hhC htC)) fun j hj => ?_⟩
    rcases ((mem_p4Pred_cons hCo).mp hj).2 with rfl | rfl
    · exact hacch
    · exact hacct

include hTx hAp hAm hCo hTA hNC hU hTxU hApU hAmU hNilU hConsU in
/-- **`P4C`'s induction at the parameter of accessible `P4`-values**,
with `List`'s induction inside its `append` case (the container is
itself nested): every `P4C` over a set `S` of accessible `P4`-values
is a `P4C P4` and accessible. -/
theorem p4AccC_of_param {S : V}
    (hS : ∀ x, x ∈ˢ S → x ∈ˢ C₀ ∧ ∃ y, y ∈ˢ app Acc* (kpair (vnat 0) x)) :
    ∀ a, a ∈ˢ p4CL w U text append amk mkNil mkCons S →
      a ∈ˢ C₁ ∧ ∃ y, y ∈ˢ app Acc* (kpair (vnat 1) a) := by
  refine p4CL_induction hU S _ fun a ha => ?_
  obtain ⟨-, ha⟩ := mem_p4COp.mp ha
  rcases ha with ⟨s, hs, rfl⟩ | ⟨ps, hps, rfl⟩
  · obtain ⟨hsC, haccs⟩ := hS s hs
    refine ⟨text_mem_p4C1 hU hTxU hsC, pt,
      p4Acc_intro (p4_mem_idx1 (text_mem_p4C1 hU hTxU hsC)) fun j hj => ?_⟩
    obtain ⟨-, rfl⟩ := (mem_p4Pred_text hTx hTA).mp hj
    exact haccs
  · obtain ⟨-, l, hl, rfl⟩ := mem_p4ArrayL.mp hps
    obtain ⟨hlC, haccl⟩ :=
      p4AccL_of_param hCo hNC hU hNilU hConsU (fun a ha => (mem_sep.mp ha).2) l hl
    have h2 : amk l ∈ˢ C₂ := amk_mem_p4C2 hU hAmU hlC
    have hacc2 : ∃ y, y ∈ˢ app Acc* (kpair (vnat 2) (amk l)) :=
      ⟨pt, p4Acc_intro (p4_mem_idx2 h2) fun j hj => by
        obtain ⟨-, rfl⟩ := (mem_p4Pred_amk hAm).mp hj
        exact haccl⟩
    refine ⟨append_mem_p4C1 hU hApU h2, pt,
      p4Acc_intro (p4_mem_idx1 (append_mem_p4C1 hU hApU h2)) fun j hj => ?_⟩
    obtain ⟨-, rfl⟩ := (mem_p4Pred_append hAp hTA).mp hj
    exact hacc2

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU in
/-- **Every `P4` is accessible**: the composed operator's induction,
with the two container inductions nested inside it. -/
theorem p4Acc_p4 : ∀ x, x ∈ˢ C₀ → ∃ y, y ∈ˢ app Acc* (kpair (vnat 0) x) := by
  refine p4T_induction hU _ fun x hx => ?_
  obtain ⟨-, a, ha, rfl⟩ := mem_p4Op.mp hx
  obtain ⟨haC, hacca⟩ := p4AccC_of_param hTx hAp hAm hCo hTA hNC hU hTxU hApU hAmU hNilU hConsU
    (fun x hx => mem_sep.mp hx) a ha
  refine ⟨pt, p4Acc_intro (p4_mem_idx0 (mkP4_mem_p4T hU hP4U haC)) fun j hj => ?_⟩
  obtain ⟨-, rfl⟩ := (mem_p4Pred_mk hP4).mp hj
  exact hacca

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU in
theorem p4Acc_c1 : ∀ a, a ∈ˢ C₁ → ∃ y, y ∈ˢ app Acc* (kpair (vnat 1) a) := fun a ha =>
  (p4AccC_of_param hTx hAp hAm hCo hTA hNC hU hTxU hApU hAmU hNilU hConsU
    (fun x hx => ⟨hx, p4Acc_p4 hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
      x hx⟩) a ha).2

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU in
theorem p4Acc_c3 : ∀ l, l ∈ˢ C₃ → ∃ y, y ∈ˢ app Acc* (kpair (vnat 3) l) := fun l hl =>
  (p4AccL_of_param hCo hNC hU hNilU hConsU
    (fun a ha => ⟨ha, p4Acc_c1 hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
      a ha⟩) l hl).2

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU in
theorem p4Acc_c2 : ∀ ps, ps ∈ˢ C₂ → ∃ y, y ∈ˢ app Acc* (kpair (vnat 2) ps) := by
  intro ps hps
  obtain ⟨l, hl, rfl⟩ := p4C2_cases hps
  exact ⟨pt, p4Acc_intro (p4_mem_idx2 hps) fun j hj => by
    obtain ⟨-, rfl⟩ := (mem_p4Pred_amk hAm).mp hj
    exact p4Acc_c3 hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU l hl⟩

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU in
/-- **Every index is accessible.** -/
theorem p4Acc_all : ∀ i, i ∈ˢ I* → ∃ y, y ∈ˢ app Acc* i := by
  intro i hi
  rcases mem_p4IdxSet.mp hi with ⟨x, hx, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨ps, hps, rfl⟩ | ⟨l, hl, rfl⟩
  · exact p4Acc_p4 hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU x hx
  · exact p4Acc_c1 hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU a ha
  · exact p4Acc_c2 hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU ps hps
  · exact p4Acc_c3 hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU l hl

/-! ### The recursor exists: the recursion theorem, instantiated -/

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
    hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- **The recursion theorem at the twice-nested block**: at every index
of the disjoint union, the graph has exactly one value. -/
theorem p4Graph_unique :
    ∀ i, i ∈ˢ I* → (∃ v, v ∈ˢ app G* i) ∧
      ∀ v v', v ∈ˢ app G* i → v' ∈ˢ app G* i → v = v' := by
  intro i hi
  obtain ⟨y, hy⟩ := p4Acc_all hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU i hi
  exact recGraph_exists_unique (p4B_mem_univ hM₀ hM₁ hM₂ hM₃) (fun i _ => p4Pred_subset i)
    (p4St_mem hP4 hTx hAp hAm hCo hTA hNC hU hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons)
    i hi y hy

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
    hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- **Typing**: the recursor's value lies in the motive's fibre. -/
theorem p4Rec_mem {i : V} (hi : i ∈ˢ I*) : R* i ∈ˢ p4B M₀ M₁ M₂ M₃ i :=
  p4Graph_subset_B hM₀ hM₁ hM₂ hM₃ hi (recSel_mem (p4Graph_unique hP4 hTx hAp hAm hCo hTA hNC hU
      hP4U hTxU hApU hAmU hNilU hConsU
      hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons i hi).1)

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
    hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- The recursion equation at an index, in the engine's form. -/
theorem p4Rec_eq {i : V} (hi : i ∈ˢ I*) :
    R* i = p4St mkP4 text append amk mkNil mkCons mk text' append' amk' nil cons i
        (graph (fun j => R* j) (p4Pred w U mkP4 text append amk mkNil mkCons i)) :=
  recSel_eq (p4B_mem_univ hM₀ hM₁ hM₂ hM₃) (fun i _ => p4Pred_subset i) hi
    (p4Graph_unique hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
        hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons i hi).1
    fun j hj => p4Graph_unique hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
        hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons j (p4Pred_subset i j hj)

/-! ### The stream's six ι rules -/

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
    hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- `P4.rec … (mk a) = mk a (P4.rec_1 … a)`. -/
theorem p4Rec_mk {a : V} (ha : a ∈ˢ C₁) :
    R* (kpair (vnat 0) (mkP4 a)) = mk a (R* (kpair (vnat 1) a)) := by
  rw [p4Rec_eq hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
      hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons (p4_mem_idx0 (mkP4_mem_p4T hU hP4U ha)),
          p4St_mk hP4,
    app_graph ((mem_p4Pred_mk hP4).mpr ⟨p4_mem_idx1 ha, rfl⟩)]

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
    hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- `P4.rec_1 … (text s) = text' s (P4.rec … s)` — the container's
PARAMETER position. -/
theorem p4Rec_text {s : V} (hs : s ∈ˢ C₀) :
    R* (kpair (vnat 1) (text s)) = text' s (R* (kpair (vnat 0) s)) := by
  rw [p4Rec_eq hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
      hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons (p4_mem_idx1 (text_mem_p4C1 hU hTxU hs)),
          p4St_text hTx,
    app_graph ((mem_p4Pred_text hTx hTA).mpr ⟨p4_mem_idx0 hs, rfl⟩)]

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
    hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- `P4.rec_1 … (append ps) = append' ps (P4.rec_2 … ps)`. -/
theorem p4Rec_append {ps : V} (hps : ps ∈ˢ C₂) :
    R* (kpair (vnat 1) (append ps)) = append' ps (R* (kpair (vnat 2) ps)) := by
  rw [p4Rec_eq hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
      hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons (p4_mem_idx1 (append_mem_p4C1 hU hApU hps)),
          p4St_append hAp hTA,
    app_graph ((mem_p4Pred_append hAp hTA).mpr ⟨p4_mem_idx2 hps, rfl⟩)]

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
    hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- `P4.rec_2 … (amk l) = amk' l (P4.rec_3 … l)`. -/
theorem p4Rec_amk {l : V} (hl : l ∈ˢ C₃) :
    R* (kpair (vnat 2) (amk l)) = amk' l (R* (kpair (vnat 3) l)) := by
  rw [p4Rec_eq hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
      hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons (p4_mem_idx2 (amk_mem_p4C2 hU hAmU hl)),
          p4St_amk hAm,
    app_graph ((mem_p4Pred_amk hAm).mpr ⟨p4_mem_idx3 hl, rfl⟩)]

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
    hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- `P4.rec_3 … nil = nil`. -/
theorem p4Rec_nil : R* (kpair (vnat 3) mkNil) = nil := by
  rw [p4Rec_eq hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
      hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons (p4_mem_idx3 (mkNil_mem_p4C3 hU hNilU)),
          p4St_nil]

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
    hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- `P4.rec_3 … (cons h t) = cons h t (P4.rec_1 … h) (P4.rec_3 … t)`. -/
theorem p4Rec_cons {h t : V} (hh : h ∈ˢ C₁) (ht : t ∈ˢ C₃) :
    R* (kpair (vnat 3) (mkCons h t))
      = cons h t (R* (kpair (vnat 1) h)) (R* (kpair (vnat 3) t)) := by
  rw [p4Rec_eq hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
      hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons (p4_mem_idx3 (mkCons_mem_p4C3 hU hConsU hh
          ht)), p4St_cons hCo hNC,
    app_graph ((mem_p4Pred_cons hCo).mpr ⟨p4_mem_idx1 hh, Or.inl rfl⟩),
    app_graph ((mem_p4Pred_cons hCo).mpr ⟨p4_mem_idx3 ht, Or.inr rfl⟩)]

/-! ### The mimic leaves, spelled through `P4C`'s recursor family -/

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
    hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- The `List` half of the fold agreement, at a parameter `S` of
`P4C P4`-values on which `F₁` already agrees. -/
theorem p4Rec_fold_list (F₁ F₃ : V → V) (hF₃n : F₃ mkNil = nil)
    (hF₃c : ∀ h t, h ∈ˢ C₁ → t ∈ˢ C₃ → F₃ (mkCons h t) = cons h t (F₁ h) (F₃ t))
    {S : V} (hS : ∀ a, a ∈ˢ S → a ∈ˢ C₁ ∧ F₁ a = R* (kpair (vnat 1) a)) :
    ∀ l, l ∈ˢ p4ListL w U mkNil mkCons S → l ∈ˢ C₃ ∧ F₃ l = R* (kpair (vnat 3) l) := by
  refine p4ListL_induction hU S _ fun l hl => ?_
  obtain ⟨-, hl⟩ := mem_LOp.mp hl
  rcases hl with rfl | ⟨h, t, hh, ht, rfl⟩
  · exact ⟨mkNil_mem_p4C3 hU hNilU, by rw [hF₃n, p4Rec_nil hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU
      hApU hAmU hNilU hConsU
      hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons]⟩
  · obtain ⟨htC, iht⟩ := (mem_sep.mp ht).2
    obtain ⟨hhC, ihh⟩ := hS h hh
    refine ⟨mkCons_mem_p4C3 hU hConsU hhC htC, ?_⟩
    rw [hF₃c h t hhC htC, ihh, iht, p4Rec_cons hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU
        hNilU hConsU
        hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons hhC htC]

include hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
    hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons in
/-- **Fold agreement (C3)**: any three functions satisfying the
container `P4C`'s OWN recursor family's rule shapes — `P4C.rec`,
`P4C.rec_1`, `P4C.rec_2`, with `P4.rec … s` at the parameter position
of the `text` minor — are the recursor's three container components.
This is what identifies the mimic leaf, spelled through `P4C`'s
recursor family at one choice of motives and minors, with the
`P4.rec_1`, `P4.rec_2`, `P4.rec_3` the engine built.  One
`p4CL_induction` at the parameter `P4*`, with the `List` induction
(`p4Rec_fold_list`) inside its `append` case. -/
theorem p4Rec_fold_agree (F₁ F₂ F₃ : V → V)
    (hF₁t : ∀ s, s ∈ˢ C₀ → F₁ (text s) = text' s (R* (kpair (vnat 0) s)))
    (hF₁a : ∀ ps, ps ∈ˢ C₂ → F₁ (append ps) = append' ps (F₂ ps))
    (hF₂ : ∀ l, l ∈ˢ C₃ → F₂ (amk l) = amk' l (F₃ l))
    (hF₃n : F₃ mkNil = nil)
    (hF₃c : ∀ h t, h ∈ˢ C₁ → t ∈ˢ C₃ → F₃ (mkCons h t) = cons h t (F₁ h) (F₃ t)) :
    (∀ a, a ∈ˢ C₁ → F₁ a = R* (kpair (vnat 1) a)) ∧
      (∀ ps, ps ∈ˢ C₂ → F₂ ps = R* (kpair (vnat 2) ps)) ∧
      (∀ l, l ∈ˢ C₃ → F₃ l = R* (kpair (vnat 3) l)) := by
  have h₁ : ∀ a, a ∈ˢ C₁ → F₁ a = R* (kpair (vnat 1) a) := by
    refine p4CL_induction hU (p4T w U mkP4 text append amk mkNil mkCons) _ fun a ha => ?_
    obtain ⟨-, ha⟩ := mem_p4COp.mp ha
    rcases ha with ⟨s, hs, rfl⟩ | ⟨ps, hps, rfl⟩
    · rw [hF₁t s hs, p4Rec_text hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
        hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons hs]
    · obtain ⟨-, l, hl, rfl⟩ := mem_p4ArrayL.mp hps
      obtain ⟨hlC, ihl⟩ :=
        p4Rec_fold_list hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
            hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons F₁ F₃ hF₃n hF₃c (fun a ha =>
                mem_sep.mp ha) l hl
      have h2 : amk l ∈ˢ C₂ := amk_mem_p4C2 hU hAmU hlC
      rw [hF₁a (amk l) h2, hF₂ l hlC, ihl, ← p4Rec_amk hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU
          hAmU hNilU hConsU
          hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons hlC, p4Rec_append hP4 hTx hAp hAm hCo
              hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
          hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons h2]
  have h₃ : ∀ l, l ∈ˢ C₃ → F₃ l = R* (kpair (vnat 3) l) := fun l hl =>
    (p4Rec_fold_list hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
        hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons F₁ F₃ hF₃n hF₃c (fun a ha => ⟨ha, h₁ a
            ha⟩) l hl).2
  refine ⟨h₁, fun ps hps => ?_, h₃⟩
  obtain ⟨l, hl, rfl⟩ := p4C2_cases hps
  rw [hF₂ l hl, h₃ l hl, p4Rec_amk hP4 hTx hAp hAm hCo hTA hNC hU hP4U hTxU hApU hAmU hNilU hConsU
      hM₀ hM₁ hM₂ hM₃ hmk htext happend hamk hnil hcons hl]

end RecFacts

end ConLeche.SetTheory
