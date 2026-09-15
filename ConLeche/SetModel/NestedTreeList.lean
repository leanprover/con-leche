module

public import ConLeche.SetModel.UnionRec
@[expose] public section

/-!
# The UNIFORM nested route, falsifying experiment (task #315): `Tree ::= node (List Tree)`

The nested half of the falsifying experiment.  The block

    inductive Tree where | node : List Tree → Tree

is modelled **uniformly**: there is ONE block, of ONE member, whose
operator is the *composite* of the node arm with the container's
carrier — no auxiliary block, no copy of `List`.  The container is an
**abstract, SAT-GUARDED datum** (`NestedSig` + `ContainerOk`): its
laws are stated only under the guard `α ∈ˢ univ w'`, `univ w'` being
the parameter's domain, exactly as the datum's `Sat` guard does.  That
is what distinguishes this experiment from the earlier ones
(`SetTheory/Derive/BekicTreeList.lean`,
`SetModel/DirectTreeList.lean`), whose container operators were TOTAL
and therefore could not falsify a domain condition.

**Hypotheses needed beyond the kit** — the complete list:

* **the level fact** `hw : S.w ≤ S.w'` — the family variable's value
  `app (X 0) pt` lies in `univ w` (the tuple space), while the
  container's guard asks for `univ w'`.  Without `hw` the container's
  laws cannot be invoked at the family variable's value AT ALL, so
  `listAt_mono`, `treeΦ_mono` and hence the carrier itself are
  unprovable.  Used at: `treeΦ_mono` (both parameters), `mem_treeT`,
  `mem_treeLs`, `treeAcc_tree` (the separated tuple's value), and
  everything downstream.  This is the uniform route's form of the
  direct lane's K.27 finding: *the fit of the family variable in the
  container's parameter domain is a level fact the kernel must record*.
* **the container's fibre at BOTH parameters** (`hLfibre`): the map
  action `listAt_mono` reads the fibre at `α` (to decompose) and at
  `α'` (to rebuild), each under its own guard.  The fibre is also read
  at the *family variable's value* — `S₀`, a separation of the carrier
  — inside `treeAccL_of_param`, not only at the carrier `treeT S`.
* `hLmono`, `hLmaps`, `hLcl` (the container's own fixed point), again
  guarded;
* the ambient bound `hUT : S.UT ∈ˢ univ S.w` together with
  `hNodeU : ∀ l, S.mkNode l ∈ˢ S.UT` — the honest form of `sep UT`:
  the bound is not assumed closed under a typing premise, it is total;
* injectivity `hNodeInj`, `hConsInj` and disjointness `hNilCons`, used
  only to compute the predecessor sets, the bound and the step.

**What is proved**: the composed operator is monotone and
space-preserving with a closed tuple (§ *The carrier*), so
`lfpTuple` applies; its fixed-point equations are `mem_treeT` and
`mem_treeLs`; every element of the two-class union — trees and the
PIN's values `List Tree`, the latter *not* a component of the tuple —
is accessible (`treeAcc_all`), by a tuple induction whose step runs
the CONTAINER's own induction at the parameter "accessible trees"
(`treeAccL_of_param`); and `recGraph_exists_unique` then yields the
simultaneous recursor with the stream's three ι rules
(`treeRec_node`, `treeRec_nil`, `treeRec_cons`) and its typing
(`recT_mem`, `recL_mem`).

The kit's `unionAcc_all` does NOT apply: it assumes every class is a
component of the tuple lfp, and the pin class is not.  The
generalisation that does is the kit's `unionAcc_of_classAcc`
(`UnionRec.lean`) — a class whose carrier comes with its own
accessibility proof.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The block's data: the tree side and the container datum -/

/-- The data of the nested block `Tree ::= node (List Tree)`: the tree
side (`UT`, `mkNode`) and the container datum (`mkNil`, `mkCons`, the
set-level family functor `LΦ` in the parameter, and the two levels —
`w` the value level, `w'` the container's parameter sort). -/
structure NestedSig (V : Type u) [SetTheory V] where
  /-- The value level: every carrier lives in `univ w`. -/
  w : Nat
  /-- The container's parameter sort level: `List`'s parameter domain
  is `univ w'`, and the datum's clauses are guarded by it. -/
  w' : Nat
  /-- The ambient bound of the tree carrier. -/
  UT : V
  /-- `Tree.node`. -/
  mkNode : V → V
  /-- `List.nil`. -/
  mkNil : V
  /-- `List.cons`. -/
  mkCons : V → V → V
  /-- The container's set-level family functor at a parameter value:
  `LΦ α` is a graph on `famSpace w unitSet` (`List` has no indices). -/
  LΦ : V → V

/-- The laws of the datum — the container's clauses **only under the
guard** `α ∈ˢ univ w'`, the tree side's bound total. -/
structure ContainerOk (S : NestedSig V) : Prop where
  /-- The ambient bound is a set of the value level. -/
  hUT : S.UT ∈ˢ (univ S.w : V)
  /-- Honest ambient bound: `sep UT` is all the node arm gets. -/
  hNodeU : ∀ l, S.mkNode l ∈ˢ S.UT
  /-- `Tree.node` is injective. -/
  hNodeInj : ∀ l l', S.mkNode l = S.mkNode l' → l = l'
  /-- `List.cons` is injective. -/
  hConsInj : ∀ h t h' t', S.mkCons h t = S.mkCons h' t' → h = h' ∧ t = t'
  /-- `List.nil` is not a `cons`. -/
  hNilCons : ∀ h t, S.mkNil ≠ S.mkCons h t
  /-- **Guarded**: the container is monotone at a parameter in the
  parameter's domain. -/
  hLmono : ∀ α, α ∈ˢ (univ S.w' : V) → MonoFam S.w unitSet (S.LΦ α)
  /-- **Guarded**: the container preserves the family space. -/
  hLmaps : ∀ α, α ∈ˢ (univ S.w' : V) → MapsFam S.w unitSet (S.LΦ α)
  /-- **Guarded**: the container has a closed family. -/
  hLcl : ∀ α, α ∈ˢ (univ S.w' : V) → ∃ L, IsClosedFam S.w unitSet (S.LΦ α) L
  /-- **Guarded**: the container's constructor decomposition. -/
  hLfibre : ∀ α, α ∈ˢ (univ S.w' : V) → ∀ Y, Y ∈ˢ famSpace S.w unitSet → ∀ x,
    x ∈ˢ app (app (S.LΦ α) Y) pt ↔
      (x = S.mkNil ∨ ∃ h t, h ∈ˢ α ∧ t ∈ˢ app Y pt ∧ x = S.mkCons h t)

/-- The index sets of the block: `List` and `Tree` are both
unindexed. -/
noncomputable def uIs : Nat → V := fun _ => unitSet

theorem uIs_apply (n : Nat) : (uIs n : V) = unitSet := rfl

/-- **The level fact.**  A value of the tuple space lies in `univ w`;
the container's guard asks for `univ w'`.  This is the ONLY bridge,
and it needs `hw`. -/
theorem mem_univ_w' {S : NestedSig V} (hw : S.w ≤ S.w') {x : V} (hx : x ∈ˢ (univ S.w : V)) :
    x ∈ˢ (univ S.w' : V) :=
  univ_mono hw x hx

/-! ## The container's carrier at a parameter, and its map action -/

/-- `⟦List⟧ α` — the container's LEAF at the parameter value `α`, the
datum's `leaf` clause shape. -/
noncomputable def listAt (S : NestedSig V) (α : V) : V :=
  app (lfpFamSet S.w unitSet (S.LΦ α)) pt

/-- **(P) the container's fixed-point equation at a guarded
parameter** — the constructor decomposition on the carrier. -/
theorem mem_listAt {S : NestedSig V} (hS : ContainerOk S) {α : V}
    (hα : α ∈ˢ (univ S.w' : V)) {x : V} :
    x ∈ˢ listAt S α ↔
      (x = S.mkNil ∨ ∃ h t, h ∈ˢ α ∧ t ∈ˢ listAt S α ∧ x = S.mkCons h t) := by
  constructor
  · intro hx
    refine (hS.hLfibre α hα _ (lfpFamSet_mem _ _ _) x).mp ?_
    exact lfpFamSet_fixed (hS.hLcl α hα) (hS.hLmono α hα) (hS.hLmaps α hα) pt pt_mem_unitSet x hx
  · intro hx
    exact lfpFamSet_closed (hS.hLcl α hα) (hS.hLmono α hα) pt pt_mem_unitSet x
      ((hS.hLfibre α hα _ (lfpFamSet_mem _ _ _) x).mpr hx)

/-- **(P) the container's map action, from `fibre` at BOTH
parameters**: the lfp at `α'` is closed for `LΦ α` when `α ⊆ α'`, so
leastness gives the inclusion.  Both guards are consumed. -/
theorem listAt_mono {S : NestedSig V} (hS : ContainerOk S) {α α' : V}
    (hα : α ∈ˢ (univ S.w' : V)) (hα' : α' ∈ˢ (univ S.w' : V)) (hsub : α ⊆ˢ α') :
    listAt S α ⊆ˢ listAt S α' := by
  have hcl : IsClosedFam S.w unitSet (S.LΦ α) (lfpFamSet S.w unitSet (S.LΦ α')) := by
    refine ⟨lfpFamSet_mem _ _ _, fun i hi x hx => ?_⟩
    obtain rfl := mem_unitSet_iff.mp hi
    refine lfpFamSet_closed (hS.hLcl α' hα') (hS.hLmono α' hα') pt pt_mem_unitSet x ?_
    refine (hS.hLfibre α' hα' _ (lfpFamSet_mem _ _ _) x).mpr ?_
    rcases (hS.hLfibre α hα _ (lfpFamSet_mem _ _ _) x).mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h, t, hsub h hh, ht, rfl⟩
  exact fun x hx => lfpFamSet_le hcl pt pt_mem_unitSet x hx

/-! ## The composed operator and the block's carrier -/

/-- The node arm at a parameter value: `{ node l | l ∈ ⟦List⟧ α }`,
inside the ambient bound. -/
noncomputable def nodeArm (S : NestedSig V) (α : V) : V :=
  sep S.UT fun x => ∃ l, l ∈ˢ listAt S α ∧ x = S.mkNode l

/-- **The composed operator** (`k = 1`): the container is composed into
`Tree`'s operator, the family variable sitting in the container's
parameter. -/
noncomputable def treeΦ (S : NestedSig V) (X : Nat → V) : Nat → V := fun n =>
  match n with
  | 0 => graph (fun _ => nodeArm S (app (X 0) pt)) unitSet
  | m + 1 => X (m + 1)

theorem app_treeΦ_zero (S : NestedSig V) (X : Nat → V) :
    app (treeΦ S X 0) pt = nodeArm S (app (X 0) pt) :=
  app_graph pt_mem_unitSet

/-- `treeCar S`: the block's carrier tuple. -/
noncomputable def treeCar (S : NestedSig V) : Nat → V :=
  lfpTuple S.w 1 uIs (treeΦ S)

/-- `T*`: the tree carrier. -/
noncomputable def treeT (S : NestedSig V) : V := app (treeCar S 0) pt

/-- `LT* = ⟦List⟧ T*`: the value of the pin `List Tree` — the second
class of the recursion, a set that exists already. -/
noncomputable def treeLs (S : NestedSig V) : V := listAt S (treeT S)

theorem treeCar_mem (S : NestedSig V) : InTupleSpace S.w 1 uIs (treeCar S) :=
  lfpTuple_mem _ _ _ _

theorem treeT_mem_univ (S : NestedSig V) : treeT S ∈ˢ (univ S.w : V) :=
  famSpace_app (treeCar_mem S 0 Nat.one_pos) pt_mem_unitSet

theorem treeT_mem_univ' {S : NestedSig V} (hw : S.w ≤ S.w') : treeT S ∈ˢ (univ S.w' : V) :=
  mem_univ_w' hw (treeT_mem_univ S)

/-- **Monotonicity of the composed operator** — the one place the map
action in the parameter is used, and the first place the level fact is
indispensable: the guards at both parameters are `hw` applied to the
tuple space's `univ w`. -/
theorem treeΦ_mono {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w') :
    MonoTuple S.w 1 uIs (treeΦ S) := by
  intro X Y hX hY hle m hm i hi x hx
  obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
  obtain rfl := mem_unitSet_iff.mp hi
  rw [app_treeΦ_zero] at hx ⊢
  obtain ⟨hxU, l, hl, rfl⟩ := mem_sep.mp hx
  refine mem_sep.mpr ⟨hxU, l, ?_, rfl⟩
  exact listAt_mono hS (mem_univ_w' hw (famSpace_app (hX 0 hm) pt_mem_unitSet))
    (mem_univ_w' hw (famSpace_app (hY 0 hm) pt_mem_unitSet))
    (hle 0 hm pt pt_mem_unitSet) l hl

theorem treeΦ_maps {S : NestedSig V} (hS : ContainerOk S) : MapsTuple S.w 1 uIs (treeΦ S) := by
  intro X _ m hm
  obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
  exact graph_mem_famSpace fun _ _ => univ_sep_mem hS.hUT

/-- **The closed tuple (W)**: the ambient bound itself, `sep UT ⊆ UT`.
No level fact is needed here — `UT ∈ˢ univ w` is the tuple space's own
condition. -/
theorem treeΦ_closed {S : NestedSig V} (hS : ContainerOk S) :
    ∃ L, IsClosedTuple S.w 1 uIs (treeΦ S) L := by
  refine ⟨fun _ => graph (fun _ => S.UT) unitSet,
    fun _ _ => graph_mem_famSpace fun _ _ => hS.hUT, fun m hm i hi x hx => ?_⟩
  obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
  obtain rfl := mem_unitSet_iff.mp hi
  rw [app_treeΦ_zero] at hx
  rw [app_graph pt_mem_unitSet]
  exact sep_subset x hx

/-! ## The two fixed-point equations -/

/-- `T* = { node l | l ∈ LT* }`. -/
theorem mem_treeT {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w') {x : V} :
    x ∈ˢ treeT S ↔ ∃ l, l ∈ˢ treeLs S ∧ x = S.mkNode l := by
  unfold treeT treeCar
  rw [← app_lfpTuple_eq (treeΦ_closed hS) (treeΦ_mono hS hw) (treeΦ_maps hS)
    Nat.one_pos pt_mem_unitSet, app_treeΦ_zero]
  unfold nodeArm
  rw [mem_sep]
  constructor
  · rintro ⟨-, l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨hS.hNodeU l, l, hl, rfl⟩

/-- `LT* = nil ∪ { cons h t | h ∈ T*, t ∈ LT* }` — the container's
fixed-point equation AT THE CARRIER, under the guard supplied by the
level fact. -/
theorem mem_treeLs {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w') {x : V} :
    x ∈ˢ treeLs S ↔
      x = S.mkNil ∨ ∃ h t, h ∈ˢ treeT S ∧ t ∈ˢ treeLs S ∧ x = S.mkCons h t :=
  mem_listAt hS (treeT_mem_univ' hw)

theorem mkNode_mem_treeT {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w')
    {l : V} (hl : l ∈ˢ treeLs S) : S.mkNode l ∈ˢ treeT S :=
  (mem_treeT hS hw).mpr ⟨l, hl, rfl⟩

theorem mkNil_mem_treeLs {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w') :
    S.mkNil ∈ˢ treeLs S :=
  (mem_treeLs hS hw).mpr (Or.inl rfl)

theorem mkCons_mem_treeLs {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w')
    {h t : V} (hh : h ∈ˢ treeT S) (ht : t ∈ˢ treeLs S) : S.mkCons h t ∈ˢ treeLs S :=
  (mem_treeLs hS hw).mpr (Or.inr ⟨h, t, hh, ht, rfl⟩)

/-! ## The recursion: two classes, one of them the PIN's values -/

/-- The two classes of the recursion, as a tuple of families over
`unitSet`: class `0` is the block's own component, class `1` is the
**pin's** values `LT*` — which is NOT a component of the tuple lfp. -/
noncomputable def treeClasses (S : NestedSig V) : Nat → V :=
  fun c => if c = 0 then treeCar S 0 else graph (fun _ => treeLs S) unitSet

theorem app_treeClasses_zero (S : NestedSig V) : app (treeClasses S 0) pt = treeT S := rfl

theorem app_treeClasses_one (S : NestedSig V) : app (treeClasses S 1) pt = treeLs S := by
  unfold treeClasses
  rw [if_neg (by omega : ¬ (1 = 0))]
  exact app_graph pt_mem_unitSet

/-- **The index set of the recursion**: the disjoint union of the two
classes, `{0} × T* ∪ {1} × LT*`. -/
noncomputable def treeIdx (S : NestedSig V) : V := unionSet 2 uIs (treeClasses S)

theorem mem_treeIdx {S : NestedSig V} {u : V} :
    u ∈ˢ treeIdx S ↔
      (∃ x, x ∈ˢ treeT S ∧ u = tagged 0 pt x) ∨ (∃ l, l ∈ˢ treeLs S ∧ u = tagged 1 pt l) := by
  unfold treeIdx
  rw [mem_unionSet]
  constructor
  · rintro ⟨c, hc, i, hi, x, hx, rfl⟩
    obtain rfl := mem_unitSet_iff.mp hi
    match c, hc with
    | 0, _ => exact Or.inl ⟨x, by rwa [app_treeClasses_zero] at hx, rfl⟩
    | 1, _ => exact Or.inr ⟨x, by rwa [app_treeClasses_one] at hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact ⟨0, by omega, pt, pt_mem_unitSet, x, by rwa [app_treeClasses_zero], rfl⟩
    · exact ⟨1, by omega, pt, pt_mem_unitSet, l, by rwa [app_treeClasses_one], rfl⟩

theorem tree_mem_treeIdx {S : NestedSig V} {x : V} (hx : x ∈ˢ treeT S) :
    tagged 0 pt x ∈ˢ treeIdx S :=
  mem_treeIdx.mpr (Or.inl ⟨x, hx, rfl⟩)

theorem list_mem_treeIdx {S : NestedSig V} {l : V} (hl : l ∈ˢ treeLs S) :
    tagged 1 pt l ∈ˢ treeIdx S :=
  mem_treeIdx.mpr (Or.inr ⟨l, hl, rfl⟩)

/-- The predecessor relation, read off the constructors. -/
def TreeRel (S : NestedSig V) (u v : V) : Prop :=
  (∃ l, u = tagged 0 pt (S.mkNode l) ∧ v = tagged 1 pt l) ∨
  (∃ h t, u = tagged 1 pt (S.mkCons h t) ∧ (v = tagged 0 pt h ∨ v = tagged 1 pt t))

/-- The predecessor sets, as a relation-defined separation of the
index set. -/
noncomputable def treePred (S : NestedSig V) (u : V) : V := relPred (treeIdx S) (TreeRel S) u

theorem treePred_subset (S : NestedSig V) (u : V) : treePred S u ⊆ˢ treeIdx S :=
  relPred_subset _ _ u

theorem mem_treePred {S : NestedSig V} {u v : V} :
    v ∈ˢ treePred S u ↔ v ∈ˢ treeIdx S ∧ TreeRel S u v := mem_relPred

theorem mem_treePred_node {S : NestedSig V} (hS : ContainerOk S) {l v : V} :
    v ∈ˢ treePred S (tagged 0 pt (S.mkNode l)) ↔ v ∈ˢ treeIdx S ∧ v = tagged 1 pt l := by
  rw [mem_treePred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inl ⟨l, rfl, h⟩⟩
  rcases h with ⟨l', h₁, h₂⟩ | ⟨h', t', h₁, -⟩
  · rw [h₂, hS.hNodeInj l l' (tagged_inj h₁).2.2]
  · exact absurd (tagged_inj h₁).1 (by omega)

theorem not_mem_treePred_nil {S : NestedSig V} (hS : ContainerOk S) {v : V} :
    ¬ v ∈ˢ treePred S (tagged 1 pt S.mkNil) := by
  intro h
  rcases (mem_treePred.mp h).2 with ⟨_, h₁, _⟩ | ⟨h', t', h₁, _⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact hS.hNilCons h' t' (tagged_inj h₁).2.2

theorem mem_treePred_cons {S : NestedSig V} (hS : ContainerOk S) {h t v : V} :
    v ∈ˢ treePred S (tagged 1 pt (S.mkCons h t)) ↔
      v ∈ˢ treeIdx S ∧ (v = tagged 0 pt h ∨ v = tagged 1 pt t) := by
  rw [mem_treePred]
  refine and_congr_right fun _ => ⟨fun hv => ?_, fun hv => Or.inr ⟨h, t, rfl, hv⟩⟩
  rcases hv with ⟨_, h₁, _⟩ | ⟨h', t', h₁, h₂⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · obtain ⟨rfl, rfl⟩ := hS.hConsInj _ _ _ _ (tagged_inj h₁).2.2
    exact h₂

/-! ## Accessibility: the tuple induction with the container's inside

The kit's `unionAcc_all` does not apply: it derives accessibility from
`lfpTuple_induction` alone, which reaches only classes that ARE
components of the tuple.  Class `1` here is the pin's values, reached
by the CONTAINER's own induction at a parameter. -/

/-- The accessibility family over the recursion's index set. -/
noncomputable def treeAccFam (S : NestedSig V) : V :=
  accFam (treeIdx S) (treePred S) (fun _ => True)

/-- The accessibility family's introduction rule. -/
theorem treeAcc_intro {S : NestedSig V} {u : V} (hu : u ∈ˢ treeIdx S)
    (h : ∀ v, v ∈ˢ treePred S u → ∃ y, y ∈ˢ app (treeAccFam S) v) :
    (pt : V) ∈ˢ app (treeAccFam S) u := by
  unfold treeAccFam accFam
  rw [← app_lfpFamSet_eq ⟨_, accStep_closed⟩
    (accStep_mono fun i _ => treePred_subset S i) accStep_maps hu,
    app_app_accStep (lfpFamSet_mem _ _ _) hu]
  exact pt_mem_truthVal ⟨trivial, h⟩

/-- **The container's induction at the parameter of accessible
trees**: every value of `⟦List⟧ S₀`, for a guarded set `S₀` of
accessible trees, is a value of the pin `LT*` and is accessible.  This
is `lfpFamSet_induction` at the parameter `S₀` — and it reads the
container's `fibre` at the FAMILY VARIABLE's value, not at the
carrier. -/
theorem treeAccL_of_param {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w')
    {S₀ : V} (hS₀ : S₀ ∈ˢ (univ S.w' : V)) (hsub : S₀ ⊆ˢ treeT S)
    (hacc : ∀ x, x ∈ˢ S₀ → ∃ y, y ∈ˢ app (treeAccFam S) (tagged 0 pt x)) :
    ∀ l, l ∈ˢ listAt S S₀ →
      l ∈ˢ treeLs S ∧ ∃ y, y ∈ˢ app (treeAccFam S) (tagged 1 pt l) := by
  intro l hl
  refine lfpFamSet_induction (hS.hLcl S₀ hS₀) (hS.hLmono S₀ hS₀)
    (fun _ z => z ∈ˢ treeLs S ∧ ∃ y, y ∈ˢ app (treeAccFam S) (tagged 1 pt z))
    ?_ pt pt_mem_unitSet l hl
  intro i hi x hx
  obtain rfl := mem_unitSet_iff.mp hi
  have hY : graph (fun i => sep (app (lfpFamSet S.w unitSet (S.LΦ S₀)) i)
      (fun z => z ∈ˢ treeLs S ∧ ∃ y, y ∈ˢ app (treeAccFam S) (tagged 1 pt z))) unitSet
      ∈ˢ famSpace S.w unitSet :=
    graph_mem_famSpace fun i hi => univ_sep_mem (famSpace_app (lfpFamSet_mem _ _ _) hi)
  rcases (hS.hLfibre S₀ hS₀ _ hY x).mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
  · exact ⟨mkNil_mem_treeLs hS hw, pt,
      treeAcc_intro (list_mem_treeIdx (mkNil_mem_treeLs hS hw))
        fun v hv => absurd hv (not_mem_treePred_nil hS)⟩
  · rw [app_graph pt_mem_unitSet] at ht
    obtain ⟨-, htL, hacct⟩ := mem_sep.mp ht
    have hhT := hsub h hh
    refine ⟨mkCons_mem_treeLs hS hw hhT htL, pt,
      treeAcc_intro (list_mem_treeIdx (mkCons_mem_treeLs hS hw hhT htL)) fun v hv => ?_⟩
    rcases ((mem_treePred_cons hS).mp hv).2 with rfl | rfl
    · exact hacc h hh
    · exact hacct

/-- **Every tree is accessible**: the composed operator's tuple
induction, with the container's induction at the accessible trees
inside.  The level fact appears here again, to guard the separated
tuple's value. -/
theorem treeAcc_tree {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w') :
    ∀ x, x ∈ˢ treeT S → ∃ y, y ∈ˢ app (treeAccFam S) (tagged 0 pt x) := by
  intro x hx
  refine lfpTuple_induction (treeΦ_closed hS) (treeΦ_mono hS hw)
    (fun _ _ z => ∃ y, y ∈ˢ app (treeAccFam S) (tagged 0 pt z)) ?_ 0 Nat.one_pos pt
    pt_mem_unitSet x hx
  intro m hm i hi z hz
  obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
  obtain rfl := mem_unitSet_iff.mp hi
  rw [app_treeΦ_zero] at hz
  obtain ⟨-, l, hl, rfl⟩ := mem_sep.mp hz
  have hsub := sepTuple_le S.w 1 uIs (treeΦ S)
    (fun _ _ z => ∃ y, y ∈ˢ app (treeAccFam S) (tagged 0 pt z)) 0 Nat.one_pos pt pt_mem_unitSet
  have hS₀ := mem_univ_w' hw (famSpace_app (sepTuple_mem S.w 1 uIs (treeΦ S)
    (fun _ _ z => ∃ y, y ∈ˢ app (treeAccFam S) (tagged 0 pt z)) 0 Nat.one_pos) pt_mem_unitSet)
  have hacc : ∀ y, y ∈ˢ app (sepTuple S.w 1 uIs (treeΦ S)
      (fun _ _ z => ∃ y, y ∈ˢ app (treeAccFam S) (tagged 0 pt z)) 0) pt →
      ∃ y', y' ∈ˢ app (treeAccFam S) (tagged 0 pt y) := by
    intro y hy
    unfold sepTuple at hy
    have hpt : (pt : V) ∈ˢ uIs 0 := pt_mem_unitSet
    rw [app_graph hpt] at hy
    exact (mem_sep.mp hy).2
  obtain ⟨hlL, haccl⟩ := treeAccL_of_param hS hw hS₀ hsub hacc l hl
  refine ⟨pt, treeAcc_intro (tree_mem_treeIdx (mkNode_mem_treeT hS hw hlL)) fun v hv => ?_⟩
  obtain ⟨-, rfl⟩ := (mem_treePred_node hS).mp hv
  exact haccl

/-- **Every index of the union is accessible** — the pin's class by
the container's induction at the carrier. -/
theorem treeAcc_all {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w') :
    ∀ u, u ∈ˢ treeIdx S → ∃ y, y ∈ˢ app (treeAccFam S) u := by
  refine unionAcc_of_classAcc (C := treeClasses S) fun c hc i hi x hx => ?_
  obtain rfl := mem_unitSet_iff.mp hi
  match c, hc with
  | 0, _ =>
    rw [app_treeClasses_zero] at hx
    exact treeAcc_tree hS hw x hx
  | 1, _ =>
    rw [app_treeClasses_one] at hx
    exact (treeAccL_of_param hS hw (treeT_mem_univ' hw) (Subset.refl _)
      (treeAcc_tree hS hw) x hx).2

/-! ## The bound and the step -/

open Classical in
/-- The bound: the two motives' fibres. -/
noncomputable def treeB (MT ML : V → V) (u : V) : V :=
  if h : ∃ x, u = tagged 0 pt x then MT (Classical.choose h)
  else if h : ∃ l, u = tagged 1 pt l then ML (Classical.choose h)
  else empty

open Classical in
/-- The step: the minors at the predecessors' values. -/
noncomputable def treeSt (S : NestedSig V) (mNode : V → V → V) (mNil : V)
    (mCons : V → V → V → V → V) (u g : V) : V :=
  if h : ∃ l, u = tagged 0 pt (S.mkNode l) then
    mNode (Classical.choose h) (app g (tagged 1 pt (Classical.choose h)))
  else if u = tagged 1 pt S.mkNil then mNil
  else if h : ∃ q : V × V, u = tagged 1 pt (S.mkCons q.1 q.2) then
    mCons (Classical.choose h).1 (Classical.choose h).2
      (app g (tagged 0 pt (Classical.choose h).1))
      (app g (tagged 1 pt (Classical.choose h).2))
  else empty

section Compute

variable {MT ML : V → V} {mNode : V → V → V} {mNil : V} {mCons : V → V → V → V → V}

theorem treeB_tree (x : V) : treeB MT ML (tagged 0 pt x) = MT x := by
  unfold treeB
  rw [dif_pos ⟨x, rfl⟩]
  have h := Classical.choose_spec (⟨x, rfl⟩ : ∃ y, (tagged 0 pt x : V) = tagged 0 pt y)
  exact congrArg MT (tagged_inj h).2.2.symm

theorem treeB_list (l : V) : treeB MT ML (tagged 1 pt l) = ML l := by
  unfold treeB
  rw [dif_neg (fun ⟨_, h⟩ => Nat.one_ne_zero (tagged_inj h).1), dif_pos ⟨l, rfl⟩]
  have h := Classical.choose_spec (⟨l, rfl⟩ : ∃ y, (tagged 1 pt l : V) = tagged 1 pt y)
  exact congrArg ML (tagged_inj h).2.2.symm

theorem treeSt_node {S : NestedSig V} (hS : ContainerOk S) (l g : V) :
    treeSt S mNode mNil mCons (tagged 0 pt (S.mkNode l)) g
      = mNode l (app g (tagged 1 pt l)) := by
  unfold treeSt
  rw [dif_pos ⟨l, rfl⟩]
  have h := Classical.choose_spec
    (⟨l, rfl⟩ : ∃ y, (tagged 0 pt (S.mkNode l) : V) = tagged 0 pt (S.mkNode y))
  rw [← hS.hNodeInj _ _ (tagged_inj h).2.2]

theorem treeSt_nil {S : NestedSig V} (g : V) :
    treeSt S mNode mNil mCons (tagged 1 pt S.mkNil) g = mNil := by
  unfold treeSt
  rw [dif_neg (fun ⟨_, h⟩ => Nat.one_ne_zero (tagged_inj h).1), if_pos rfl]

theorem treeSt_cons {S : NestedSig V} (hS : ContainerOk S) (h t g : V) :
    treeSt S mNode mNil mCons (tagged 1 pt (S.mkCons h t)) g
      = mCons h t (app g (tagged 0 pt h)) (app g (tagged 1 pt t)) := by
  unfold treeSt
  rw [dif_neg (fun ⟨_, h'⟩ => Nat.one_ne_zero (tagged_inj h').1),
    if_neg (fun h' => hS.hNilCons h t (tagged_inj h').2.2.symm), dif_pos ⟨(h, t), rfl⟩]
  have hs := Classical.choose_spec
    (⟨(h, t), rfl⟩ :
      ∃ q : V × V, (tagged 1 pt (S.mkCons h t) : V) = tagged 1 pt (S.mkCons q.1 q.2))
  obtain ⟨h₁, h₂⟩ := hS.hConsInj _ _ _ _ (tagged_inj hs).2.2
  rw [← h₁, ← h₂]

end Compute

/-! ## The recursor -/

/-- **The block's recursor**: the selector of the recursion graph over
the two-class union. -/
noncomputable def treeRec (S : NestedSig V) (MT ML : V → V) (mNode : V → V → V) (mNil : V)
    (mCons : V → V → V → V → V) (ℓ : Nat) (u : V) : V :=
  recSel (recGraph ℓ (treeIdx S) (treePred S) (treeB MT ML) (treeSt S mNode mNil mCons)) u

/-- `Tree.rec`. -/
noncomputable def recT (S : NestedSig V) (MT ML : V → V) (mNode : V → V → V) (mNil : V)
    (mCons : V → V → V → V → V) (ℓ : Nat) (x : V) : V :=
  treeRec S MT ML mNode mNil mCons ℓ (tagged 0 pt x)

/-- `Tree.rec_1` — the PIN's recursor, on `List Tree`. -/
noncomputable def recL (S : NestedSig V) (MT ML : V → V) (mNode : V → V → V) (mNil : V)
    (mCons : V → V → V → V → V) (ℓ : Nat) (l : V) : V :=
  treeRec S MT ML mNode mNil mCons ℓ (tagged 1 pt l)

section RecFacts

variable {S : NestedSig V} {ℓ : Nat} {MT ML : V → V} {mNode : V → V → V} {mNil : V}
  {mCons : V → V → V → V → V}
  (hS : ContainerOk S) (hw : S.w ≤ S.w')
  (hMT : ∀ x, x ∈ˢ treeT S → MT x ∈ˢ (univ ℓ : V))
  (hML : ∀ l, l ∈ˢ treeLs S → ML l ∈ˢ (univ ℓ : V))
  (hmNode : ∀ l ih, l ∈ˢ treeLs S → ih ∈ˢ ML l → mNode l ih ∈ˢ MT (S.mkNode l))
  (hmNil : mNil ∈ˢ ML S.mkNil)
  (hmCons : ∀ h t ih₁ ih₂, h ∈ˢ treeT S → t ∈ˢ treeLs S → ih₁ ∈ˢ MT h → ih₂ ∈ˢ ML t →
    mCons h t ih₁ ih₂ ∈ˢ ML (S.mkCons h t))

local notation "G*" => recGraph ℓ (treeIdx S) (treePred S) (treeB MT ML)
  (treeSt S mNode mNil mCons)

include hMT hML in
theorem treeB_mem_univ : ∀ u, u ∈ˢ treeIdx S → treeB MT ML u ∈ˢ (univ ℓ : V) := by
  intro u hu
  rcases mem_treeIdx.mp hu with ⟨x, hx, rfl⟩ | ⟨l, hl, rfl⟩
  · rw [treeB_tree]; exact hMT x hx
  · rw [treeB_list]; exact hML l hl

include hMT hML in
theorem treeGraph_subset_B {u v : V} (hu : u ∈ˢ treeIdx S) (hv : v ∈ˢ app G* u) :
    v ∈ˢ treeB MT ML u := by
  rw [app_recGraph_eq (treeB_mem_univ hMT hML) (fun u _ => treePred_subset S u) hu] at hv
  exact (mem_recGraphFibre.mp hv).1

include hS hw hMT hML hmNode hmNil hmCons in
/-- **The step is typed.** -/
theorem treeSt_mem :
    ∀ u, u ∈ˢ treeIdx S → ∀ g, g ∈ˢ piSet (treePred S u) (fun v => app G* v) →
      treeSt S mNode mNil mCons u g ∈ˢ treeB MT ML u := by
  intro u hu g hg
  have hval : ∀ v, v ∈ˢ treePred S u → app g v ∈ˢ treeB MT ML v := fun v hv =>
    treeGraph_subset_B hMT hML (treePred_subset S u v hv) (app_mem_of_mem_piSet hg hv)
  rcases mem_treeIdx.mp hu with ⟨x, hx, rfl⟩ | ⟨l, hl, rfl⟩
  · obtain ⟨l, hl, rfl⟩ := (mem_treeT hS hw).mp hx
    rw [treeSt_node hS, treeB_tree]
    have h := hval (tagged 1 pt l) ((mem_treePred_node hS).mpr ⟨list_mem_treeIdx hl, rfl⟩)
    rw [treeB_list] at h
    exact hmNode l _ hl h
  · rcases (mem_treeLs hS hw).mp hl with rfl | ⟨h, t, hh, ht, rfl⟩
    · rw [treeSt_nil, treeB_list]; exact hmNil
    · rw [treeSt_cons hS, treeB_list]
      have h₁ := hval (tagged 0 pt h) ((mem_treePred_cons hS).mpr ⟨tree_mem_treeIdx hh, Or.inl rfl⟩)
      have h₂ := hval (tagged 1 pt t) ((mem_treePred_cons hS).mpr ⟨list_mem_treeIdx ht, Or.inr rfl⟩)
      rw [treeB_tree] at h₁
      rw [treeB_list] at h₂
      exact hmCons h t _ _ hh ht h₁ h₂

include hS hw hMT hML hmNode hmNil hmCons in
/-- **The recursion theorem at the nested block**: the graph has
exactly one value at every index of the two-class union. -/
theorem treeGraph_unique :
    ∀ u, u ∈ˢ treeIdx S → (∃ v, v ∈ˢ app G* u) ∧
      ∀ v v', v ∈ˢ app G* u → v' ∈ˢ app G* u → v = v' := by
  intro u hu
  obtain ⟨y, hy⟩ := treeAcc_all hS hw u hu
  exact recGraph_exists_unique (treeB_mem_univ hMT hML) (fun u _ => treePred_subset S u)
    (treeSt_mem hS hw hMT hML hmNode hmNil hmCons) u hu y hy

include hS hw hMT hML hmNode hmNil hmCons in
/-- **Typing**: the recursor's value lies in the motive's fibre. -/
theorem treeRec_mem {u : V} (hu : u ∈ˢ treeIdx S) :
    treeRec S MT ML mNode mNil mCons ℓ u ∈ˢ treeB MT ML u :=
  treeGraph_subset_B hMT hML hu
    (recSel_mem (treeGraph_unique hS hw hMT hML hmNode hmNil hmCons u hu).1)

include hS hw hMT hML hmNode hmNil hmCons in
/-- `Tree.rec … x ∈ MT x`. -/
theorem recT_mem {x : V} (hx : x ∈ˢ treeT S) :
    recT S MT ML mNode mNil mCons ℓ x ∈ˢ MT x := by
  have h := treeRec_mem hS hw hMT hML hmNode hmNil hmCons (tree_mem_treeIdx hx)
  rwa [treeB_tree] at h

include hS hw hMT hML hmNode hmNil hmCons in
/-- `Tree.rec_1 … l ∈ ML l`. -/
theorem recL_mem {l : V} (hl : l ∈ˢ treeLs S) :
    recL S MT ML mNode mNil mCons ℓ l ∈ˢ ML l := by
  have h := treeRec_mem hS hw hMT hML hmNode hmNil hmCons (list_mem_treeIdx hl)
  rwa [treeB_list] at h

include hS hw hMT hML hmNode hmNil hmCons in
/-- The recursion equation, in the engine's form. -/
theorem treeRec_eq {u : V} (hu : u ∈ˢ treeIdx S) :
    treeRec S MT ML mNode mNil mCons ℓ u
      = treeSt S mNode mNil mCons u
          (graph (fun v => treeRec S MT ML mNode mNil mCons ℓ v) (treePred S u)) :=
  recSel_eq (treeB_mem_univ hMT hML) (fun u _ => treePred_subset S u) hu
    (treeGraph_unique hS hw hMT hML hmNode hmNil hmCons u hu).1
    fun v hv => treeGraph_unique hS hw hMT hML hmNode hmNil hmCons v (treePred_subset S u v hv)

/-! ### The stream's three ι rules -/

include hS hw hMT hML hmNode hmNil hmCons in
/-- `Tree.rec … (node l) = mNode l (Tree.rec_1 … l)`. -/
theorem treeRec_node {l : V} (hl : l ∈ˢ treeLs S) :
    recT S MT ML mNode mNil mCons ℓ (S.mkNode l)
      = mNode l (recL S MT ML mNode mNil mCons ℓ l) := by
  unfold recT recL
  rw [treeRec_eq hS hw hMT hML hmNode hmNil hmCons
    (tree_mem_treeIdx (mkNode_mem_treeT hS hw hl)), treeSt_node hS,
    app_graph ((mem_treePred_node hS).mpr ⟨list_mem_treeIdx hl, rfl⟩)]

include hS hw hMT hML hmNode hmNil hmCons in
/-- `Tree.rec_1 … nil = mNil`. -/
theorem treeRec_nil : recL S MT ML mNode mNil mCons ℓ S.mkNil = mNil := by
  unfold recL
  rw [treeRec_eq hS hw hMT hML hmNode hmNil hmCons
    (list_mem_treeIdx (mkNil_mem_treeLs hS hw)), treeSt_nil]

include hS hw hMT hML hmNode hmNil hmCons in
/-- `Tree.rec_1 … (cons h t) = mCons h t (Tree.rec … h) (Tree.rec_1 … t)`. -/
theorem treeRec_cons {h t : V} (hh : h ∈ˢ treeT S) (ht : t ∈ˢ treeLs S) :
    recL S MT ML mNode mNil mCons ℓ (S.mkCons h t)
      = mCons h t (recT S MT ML mNode mNil mCons ℓ h) (recL S MT ML mNode mNil mCons ℓ t) := by
  unfold recT recL
  rw [treeRec_eq hS hw hMT hML hmNode hmNil hmCons
    (list_mem_treeIdx (mkCons_mem_treeLs hS hw hh ht)), treeSt_cons hS,
    app_graph ((mem_treePred_cons hS).mpr ⟨tree_mem_treeIdx hh, Or.inl rfl⟩),
    app_graph ((mem_treePred_cons hS).mpr ⟨list_mem_treeIdx ht, Or.inr rfl⟩)]

end RecFacts

/-! ## (W) without the ambient bound: the auxiliary tuple's closed tuple

The `sep S.UT` bound is what makes `treeΦ_closed` cheap, and it is the
one place the experiment is *less* honest than the general route will
have to be.  This section shows abstractly how (W) is discharged
without it: the composed operator's closed member follows from a
closed TUPLE for the AUXILIARY two-member operator, by leastness of
the container's lfp — and, notably, **under no guard and no level fact
at all**. -/

/-- The composed operator without the ambient bound: the node arm is
the plain image of the container's carrier. -/
noncomputable def treeΦfree (S : NestedSig V) (X : Nat → V) : Nat → V := fun n =>
  match n with
  | 0 => graph (fun _ => image S.mkNode (listAt S (app (X 0) pt))) unitSet
  | m + 1 => X (m + 1)

/-- The AUXILIARY two-member operator: `Tree`/`List Tree` as a MUTUAL
pair — member `0` the node arm over member `1`, member `1` the
container at the parameter member `0`.  (This is the shape the modeled
route builds; the uniform route composes instead.) -/
noncomputable def auxΦ (S : NestedSig V) (X : Nat → V) : Nat → V := fun n =>
  match n with
  | 0 => graph (fun _ => image S.mkNode (app (X 1) pt)) unitSet
  | 1 => app (S.LΦ (app (X 0) pt)) (X 1)
  | m + 2 => X (m + 2)

theorem app_treeΦfree_zero (S : NestedSig V) (X : Nat → V) :
    app (treeΦfree S X 0) pt = image S.mkNode (listAt S (app (X 0) pt)) :=
  app_graph pt_mem_unitSet

theorem app_auxΦ_zero (S : NestedSig V) (X : Nat → V) :
    app (auxΦ S X 0) pt = image S.mkNode (app (X 1) pt) :=
  app_graph pt_mem_unitSet

theorem image_mono {f : V → V} {A B : V} (h : A ⊆ˢ B) : image f A ⊆ˢ image f B := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
  exact mem_image.mpr ⟨x, h x hx, rfl⟩

/-- **(W) reduced.**  A closed tuple for the auxiliary (mutual)
operator yields a closed tuple for the COMPOSED one at the tree
component: the container's carrier at the parameter `app (L 0) pt`
lies inside the auxiliary tuple's list component by LEASTNESS, so the
node arm's image lands where the auxiliary's does.  Neither a
container law nor the level fact is consumed — leastness
(`lfpFamSet_le`) is unconditional. -/
theorem closed_composed_of_closed_aux {S : NestedSig V} {L : Nat → V}
    (hL : IsClosedTuple S.w 2 uIs (auxΦ S) L) :
    IsClosedTuple S.w 1 uIs (treeΦfree S) (fun _ => L 0) := by
  have hLL : IsClosedFam S.w unitSet (S.LΦ (app (L 0) pt)) (L 1) :=
    ⟨hL.1 1 (by omega), fun i hi => hL.2 1 (by omega) i hi⟩
  have hle : listAt S (app (L 0) pt) ⊆ˢ app (L 1) pt :=
    fun z hz => lfpFamSet_le hLL pt pt_mem_unitSet z hz
  refine ⟨fun _ _ => hL.1 0 (by omega), fun m hm i hi z hz => ?_⟩
  obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
  obtain rfl := mem_unitSet_iff.mp hi
  rw [app_treeΦfree_zero] at hz
  refine hL.2 0 (by omega) pt pt_mem_unitSet z ?_
  rw [app_auxΦ_zero]
  exact image_mono hle z hz

end ConLeche.SetTheory
