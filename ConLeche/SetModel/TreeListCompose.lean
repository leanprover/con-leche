module

public import ConLeche.SetModel.NestedTreeList
public import ConLeche.SetTheory.Derive.LfpCompose
@[expose] public section

/-!
# The composed operator at `Tree ::= node (List Tree)` (task #315)

The pure Tree/List instance of the general composed operator
(`SetTheory/Derive/LfpCompose.lean`) — the uniform route's block with
`k = 1` member and `n = 1` pin, instantiated at the experiment's
AUXILIARY two-member operator `auxΦ` of `SetModel/NestedTreeList.lean`
(member `0` the node arm over member `1`, member `1` the container at
the parameter member `0`).

What it supplies:

* the three laws of `auxΦ` on the `2`-component tuple space
  (`auxΦ_mono`, `auxΦ_maps`, `auxΦ_closed`) — the only inputs the
  composed operator's whole theory takes.  Both hypotheses beyond the
  kit are consumed exactly where the experiment consumes them: the
  container's guarded clauses at the family variable's value, reached
  through the **level fact** `S.w ≤ S.w'` (`mem_univ_w'`), and the map
  action in the parameter (`LΦ_param_mono`, the fibre at BOTH
  parameters);
* **Bekić, nested form** at this block: the composed carrier's tree
  component IS the auxiliary carrier's (`composed_tree`);
* **the pin-leaf shape** (`pinsCar_tree`): the pin's carrier at the
  block's carrier is the CONTAINER's carrier at the tree carrier —
  `listAt S (treeT …)`, the shape the elimination's `pinLeaf` clause
  reads.  This is `pinsCar_lfp` followed by Bekić at the segment
  (`lfpTuple_seg`), whose section here is the container's own family
  functor at the tree carrier (`lfpTuple_one`);
* **the composed operator IS the experiment's operator below the
  auxiliary carrier** (`composeΦ_eq_treeΦfree`): the clamp is the
  identity there, so `composeΦ`'s node arm is the image of
  `listAt S (app (X 0) pt)` — `treeΦfree`.

The section step reads `lfpTuple_congr` (`LfpCompose.lean`): the least
pre-fixed tuple reads its operator only at the block's own positions,
so two operators agreeing below `k` have the same carrier there (the
pins' section and `oneTuple` of the container's functor differ above
`k`, and nothing may look).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The auxiliary operator's second component -/

theorem auxΦ_one (S : NestedSig V) (X : Nat → V) :
    auxΦ S X 1 = app (S.LΦ (app (X 0) pt)) (X 1) := rfl

/-- **The container's map action IN THE PARAMETER**, at a fixed family:
`α ⊆ α'` gives `LΦ α Y ≤ LΦ α' Y`.  Read off the fibre at BOTH
parameters, each under its own guard — the same two readings
`listAt_mono` takes. -/
theorem LΦ_param_mono {S : NestedSig V} (hS : ContainerOk S) {α α' : V}
    (hα : α ∈ˢ (univ S.w' : V)) (hα' : α' ∈ˢ (univ S.w' : V)) (hsub : α ⊆ˢ α')
    {Y : V} (hY : Y ∈ˢ famSpace S.w unitSet) :
    FamLe unitSet (app (S.LΦ α) Y) (app (S.LΦ α') Y) := by
  intro i hi x hx
  obtain rfl := mem_unitSet_iff.mp hi
  refine (hS.hLfibre α' hα' Y hY x).mpr ?_
  rcases (hS.hLfibre α hα Y hY x).mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨h, t, hsub h hh, ht, rfl⟩

/-! ## The auxiliary operator's three laws -/

/-- **Monotonicity of the auxiliary operator.**  Component `0` is the
image of the list component; component `1` is the container, monotone
in its family argument (`hLmono`) and in its parameter
(`LΦ_param_mono`) — every container clause read at the family
variable's value, which the LEVEL FACT puts in the parameter's
domain. -/
theorem auxΦ_mono {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w') :
    MonoTuple S.w 2 uIs (auxΦ S) := by
  intro X Y hX hY hle m hm
  have hX0 : app (X 0) pt ∈ˢ (univ S.w' : V) :=
    mem_univ_w' hw (famSpace_app (hX 0 (by omega)) pt_mem_unitSet)
  have hY0 : app (Y 0) pt ∈ˢ (univ S.w' : V) :=
    mem_univ_w' hw (famSpace_app (hY 0 (by omega)) pt_mem_unitSet)
  match m, hm with
  | 0, _ =>
    intro i hi x hx
    obtain rfl := mem_unitSet_iff.mp hi
    rw [app_auxΦ_zero] at hx ⊢
    exact image_mono (hle 1 (by omega) pt pt_mem_unitSet) x hx
  | 1, _ =>
    rw [auxΦ_one, auxΦ_one]
    exact FamLe.trans
      (hS.hLmono _ hX0 (X 1) (Y 1) (hX 1 (by omega)) (hY 1 (by omega)) (hle 1 (by omega)))
      (LΦ_param_mono hS hX0 hY0 (hle 0 (by omega) pt pt_mem_unitSet) (hY 1 (by omega)))

/-- **The auxiliary operator preserves the tuple space.**  Component
`0` by the ambient bound (the node arm's image lies in `S.UT`),
component `1` by the container's guarded `hLmaps`. -/
theorem auxΦ_maps {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w') :
    MapsTuple S.w 2 uIs (auxΦ S) := by
  intro X hX m hm
  match m, hm with
  | 0, _ =>
    refine graph_mem_famSpace fun _ _ => univ_mem_of_subset_mem hS.hUT fun z hz => ?_
    obtain ⟨l, -, rfl⟩ := mem_image.mp hz
    exact hS.hNodeU l
  | 1, _ =>
    rw [auxΦ_one]
    exact hS.hLmaps _ (mem_univ_w' hw (famSpace_app (hX 0 (by omega)) pt_mem_unitSet))
      (X 1) (hX 1 (by omega))

/-- **The auxiliary operator has a closed tuple**: the ambient bound
`S.UT` at the tree component, the container's own carrier at that
parameter at the list component.  The level fact appears once, to
guard the container's clauses at `S.UT`. -/
theorem auxΦ_closed {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w') :
    ∃ L, IsClosedTuple S.w 2 uIs (auxΦ S) L := by
  have hUT' : S.UT ∈ˢ (univ S.w' : V) := mem_univ_w' hw hS.hUT
  refine ⟨fun m => if m = 0 then graph (fun _ => S.UT) unitSet
      else lfpFamSet S.w unitSet (S.LΦ S.UT), fun m hm => ?_, fun m hm => ?_⟩
  · match m, hm with
    | 0, _ => exact graph_mem_famSpace fun _ _ => hS.hUT
    | 1, _ => exact lfpFamSet_mem _ _ _
  · match m, hm with
    | 0, _ =>
      intro i hi x hx
      obtain rfl := mem_unitSet_iff.mp hi
      rw [app_auxΦ_zero] at hx
      show x ∈ˢ app (graph (fun _ => S.UT) unitSet) pt
      rw [app_graph pt_mem_unitSet]
      obtain ⟨l, -, rfl⟩ := mem_image.mp hx
      exact hS.hNodeU l
    | 1, _ =>
      rw [auxΦ_one]
      show FamLe unitSet (app (S.LΦ (app (graph (fun _ => S.UT) unitSet) pt))
        (lfpFamSet S.w unitSet (S.LΦ S.UT))) (lfpFamSet S.w unitSet (S.LΦ S.UT))
      rw [app_graph pt_mem_unitSet]
      exact lfpFamSet_closed (hS.hLcl S.UT hUT') (hS.hLmono S.UT hUT')

/-! ## Bekić at the block: the composed carrier and the pin's leaf -/

/-- **The composed carrier's tree component IS the auxiliary
carrier's** — Bekić in the nested form at `k = n = 1`. -/
theorem composed_tree {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w') :
    lfpTuple S.w 1 uIs (composeΦ S.w 1 1 uIs (auxΦ S)) 0 = lfpTuple S.w 2 uIs (auxΦ S) 0 :=
  lfpTuple_composeΦ (auxΦ_mono hS hw) (auxΦ_closed hS hw) Nat.zero_lt_one

/-- **The pin-leaf shape.**  The pin's carrier at the block's carrier is
the CONTAINER's carrier at the tree carrier: `pinsCar` is the auxiliary
carrier's list component (`pinsCar_lfp`), that component is the least
pre-fixed family of its own segment section (`lfpTuple_seg`), and the
section is the container's family functor at the tree carrier
(`lfpTuple_one`). -/
theorem pinsCar_tree {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w') :
    app (pinsCar S.w 1 1 uIs (auxΦ S)
        (lfpTuple S.w 1 uIs (composeΦ S.w 1 1 uIs (auxΦ S))) 0) pt
      = listAt S (app (lfpTuple S.w 1 uIs (composeΦ S.w 1 1 uIs (auxΦ S)) 0) pt) := by
  have hmono := auxΦ_mono hS hw
  have hcl := auxΦ_closed hS hw
  have h1 : pinsCar S.w 1 1 uIs (auxΦ S)
      (lfpTuple S.w 1 uIs (composeΦ S.w 1 1 uIs (auxΦ S))) 0
      = lfpTuple S.w 2 uIs (auxΦ S) 1 := pinsCar_lfp hmono hcl Nat.zero_lt_one
  have h2 : lfpTuple S.w 2 uIs (auxΦ S) 1
      = lfpTuple S.w 1 (fun q => uIs (1 + q))
          (segSec (auxΦ S) 1 1 (lfpTuple S.w 2 uIs (auxΦ S))) 0 :=
    lfpTuple_seg (a := 1) (s := 1) (q := 0) hcl hmono (by omega) Nat.zero_lt_one
  have hsec : ∀ Y : Nat → V, ∀ m, m < 1 →
      segSec (auxΦ S) 1 1 (lfpTuple S.w 2 uIs (auxΦ S)) Y m
        = oneTuple (S.LΦ (app (lfpTuple S.w 2 uIs (auxΦ S) 0) pt)) Y m := by
    intro Y m hm
    obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
    show app (S.LΦ (app (segJoin 1 1 (lfpTuple S.w 2 uIs (auxΦ S)) Y 0) pt))
        (segJoin 1 1 (lfpTuple S.w 2 uIs (auxΦ S)) Y 1) = _
    rw [segJoin_lt _ _ Nat.zero_lt_one, segJoin_add (q := 0) _ _ Nat.zero_lt_one]
    rfl
  have h3 : lfpTuple S.w 1 (fun q => uIs (1 + q))
        (segSec (auxΦ S) 1 1 (lfpTuple S.w 2 uIs (auxΦ S))) 0
      = lfpTuple S.w 1 (fun q => uIs (1 + q))
          (oneTuple (S.LΦ (app (lfpTuple S.w 2 uIs (auxΦ S) 0) pt))) 0 :=
    lfpTuple_congr (fun _ _ => rfl) (fun Y _ m hm => hsec Y m hm) Nat.zero_lt_one
  have h4 : lfpTuple S.w 1 (fun q => uIs (1 + q))
        (oneTuple (S.LΦ (app (lfpTuple S.w 2 uIs (auxΦ S) 0) pt))) 0
      = lfpFamSet S.w unitSet (S.LΦ (app (lfpTuple S.w 2 uIs (auxΦ S) 0) pt)) :=
    lfpTuple_one S.w unitSet _
  rw [h1, h2, h3, h4, composed_tree hS hw]
  rfl

/-! ## The composed operator below the auxiliary carrier -/

/-- **The composed operator IS the experiment's operator there.**  Below
the auxiliary carrier the clamp is the identity, so the pin's carrier
at `X` is the container's carrier at `app (X 0) pt` and `composeΦ`'s
node arm is `treeΦfree`'s. -/
theorem composeΦ_eq_treeΦfree {S : NestedSig V} (hS : ContainerOk S) (hw : S.w ≤ S.w')
    {X : Nat → V} (hX : InTupleSpace S.w 1 uIs X)
    (hle : TupleLe 1 uIs X (lfpTuple S.w 2 uIs (auxΦ S))) :
    composeΦ S.w 1 1 uIs (auxΦ S) X 0 = treeΦfree S X 0 := by
  have hmono := auxΦ_mono hS hw
  have hcl := auxΦ_closed hS hw
  -- the clamp is the identity at the tree component
  have hmeet : app (meetT uIs X (lfpTuple S.w 2 uIs (auxΦ S)) 0) pt = app (X 0) pt :=
    Subset.antisymm (meetT_le_left (k := 1) X _ 0 Nat.zero_lt_one pt pt_mem_unitSet)
      (meetT_eq_of_le (k := 1) hle 0 Nat.zero_lt_one pt pt_mem_unitSet)
  -- the pins' section at `X` is the container's functor at that parameter
  have hsec : ∀ Y : Nat → V, ∀ m, m < 1 →
      pinsOp S.w 1 1 uIs (auxΦ S) X Y m = oneTuple (S.LΦ (app (X 0) pt)) Y m := by
    intro Y m hm
    obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
    show app (S.LΦ (app (segJoin 1 1 (meetT uIs X (lfpTuple S.w 2 uIs (auxΦ S))) Y 0) pt))
        (segJoin 1 1 (meetT uIs X (lfpTuple S.w 2 uIs (auxΦ S))) Y 1) = _
    rw [segJoin_lt _ _ Nat.zero_lt_one, segJoin_add (q := 0) _ _ Nat.zero_lt_one, hmeet]
    rfl
  have hpin : app (pinsCar S.w 1 1 uIs (auxΦ S) X 0) pt = listAt S (app (X 0) pt) := by
    have h3 : lfpTuple S.w 1 (fun q => uIs (1 + q)) (pinsOp S.w 1 1 uIs (auxΦ S) X) 0
        = lfpTuple S.w 1 (fun q => uIs (1 + q)) (oneTuple (S.LΦ (app (X 0) pt))) 0 :=
      lfpTuple_congr (fun _ _ => rfl) (fun Y _ m hm => hsec Y m hm) Nat.zero_lt_one
    have h4 : lfpTuple S.w 1 (fun q => uIs (1 + q)) (oneTuple (S.LΦ (app (X 0) pt))) 0
        = lfpFamSet S.w unitSet (S.LΦ (app (X 0) pt)) := lfpTuple_one S.w unitSet _
    show app (lfpTuple S.w 1 (fun q => uIs (1 + q)) (pinsOp S.w 1 1 uIs (auxΦ S) X) 0) pt = _
    rw [h3, h4]
    rfl
  show auxΦ S (extT S.w 1 1 uIs (auxΦ S) X) 0 = _
  refine famSpace_ext
    (auxΦ_maps hS hw _ (extT_mem (n := 1) (Ψ := auxΦ S) hX) 0 (by omega))
    (graph_mem_famSpace fun _ _ => ?_) fun i hi => ?_
  · exact univ_mem_of_subset_mem hS.hUT fun z hz => by
      obtain ⟨l, -, rfl⟩ := mem_image.mp hz; exact hS.hNodeU l
  · obtain rfl := mem_unitSet_iff.mp hi
    rw [app_auxΦ_zero, app_treeΦfree_zero, extT_add (q := 0) Nat.zero_lt_one, hpin]

end ConLeche.SetTheory
