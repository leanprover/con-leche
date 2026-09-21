module

public import ConLeche.SetModel.WfRec
public import ConLeche.SetModel.EnvClauseTreeList
public import ConLeche.SetModel.Iter
import ConLeche.SetModel.TupleContainer
@[expose] public section

/-!
# `Tree ::= node (List Tree)` NARROW, with ∈-recursion (falsifier F5)

The maintainer's formulation of nested inductives (2026-09-21),
falsified at the set level on the same block F0 took:

* **(ii) the block's meaning is the NARROW least fixed point**

      ⟦Tree⟧ = T* = lfp (X ↦ { node l | l ∈ ⟦List⟧ X })

  where the container's carrier at the hole is read ORDINARILY through
  its recorded env clause (`ListClause`, reused verbatim from
  `EnvClauseTreeList.lean`).  The wide tuple — the block plus a COPY of
  the container, official's auxiliary block — is **not recorded, not
  built and not identified with anything**: there is no second
  component, no `lfpTuple` at width ≥ 2, no `lfpTuple_seg_congr`, no
  `L 1 = ⟦List⟧ (L 0)`.  The copy's carrier of F0 is here simply
  `⟦List⟧ T*` — a *derived* set, equal to nothing by fiat.

* **(i)/(iii) recursion is ∈-recursion on the GLOBAL subterm relation**
  over the tagged union of the two majors' ORDINARY carriers
  (`ConLeche/SetModel/WfRec.lean`): predecessors are the ∈-smaller
  members of the union, accessibility is regularity, and the kit
  assumes nothing of the carriers but that they are sets.

What this costs, against F0, is recorded at the two `-- F5 FINDING:`
markers: the clause must record the constructor **encoding's depth**
(`TagDepth`) — injectivity is not enough, because ∈-depth is a
property of the representation — and (W) at the narrow operator needs
the container to be **finitary in its parameter**, which the clause as
written does not say and which this file proves by hand off the
`nil`/`cons` fibre law.  Everything else is strictly cheaper.

(W) is discharged **with no wide operator at all**: the ω-iterate
`iterU` of the narrow operator (`ConLeche/SetModel/Iter.lean`) is a
closed pre-fixed point, by the finitarity argument above.

Everything here is pure set theory over the bare `SetTheory`
interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The encoding-depth clause

-- F5 FINDING: `DESIGN-theory.md` §1.2's `mkZero`/`mkInj` do NOT
suffice for the ∈-recursion route.  `mkInj` says the injections are
injective; the recursion needs them to be ∈-DEEP — each field a
subterm of the constructed value.  That is a property of the
REPRESENTATION, so the block model has to record the encoding (or,
as here, its one consequence).  It is discharged for the standard
encoding at the end of this file (`tagDepth_stdInj`), and
`WfRec.lean`'s `mem_tc_inj_mkTower` discharges it for the official
`inj j (mkTower (fs ++ [pt]))` tower. -/
structure TagDepth (w : Nat) (inj : Nat → List V → V) : Prop where
  /-- Above `Prop`, every field of a constructor value is a subterm of it. -/
  depth : w ≠ 0 → ∀ (j : Nat) (fs : List V) (a : V), a ∈ fs → a ∈ˢ tc (inj j fs)

/-- F5's hypotheses: F0's — the container's env clause and the
member's tag laws — plus the encoding depth of both. -/
structure NarOk (S : TreeListSig V) : Prop where
  /-- F0's hypotheses, verbatim. -/
  ok : TreeListOk S
  /-- The member's constructor is ∈-deep. -/
  depthT : TagDepth S.w S.injT
  /-- The container's constructors are ∈-deep. -/
  depthL : TagDepth S.w S.injL

/-! ## What the container's clause says about its ORDINARY reading

Three consequences of `ListClause`, all at the *value* `app (LIST α) pt`
of the recorded family: it is a set of the level, it satisfies the
`nil`/`cons` fibre law, and it is MONOTONE in the parameter.  The last
is the one §1.2 does not state; it is derivable, by leastness against
the container's own carrier at the larger parameter. -/

namespace ListClause

variable {w : Nat} {LIST : V → V} {ΨL : V → (Nat → V) → Nat → V} {injL : Nat → List V → V}

/-- The recorded reading is a family over the one-point index set. -/
theorem fam (hC : ListClause w LIST ΨL injL) {α : V} (hα : α ∈ˢ (univ w : V)) :
    LIST α ∈ˢ famSpace w (unitSet : V) := by
  rw [hC.leaf α hα]
  exact lfpTuple_mem w 1 uIs (ΨL α) 0 Nat.one_pos

/-- **Formation of the ordinary reading**: `⟦List⟧ α` is a set of the
container's level. -/
theorem value_mem_univ (hC : ListClause w LIST ΨL injL) {α : V} (hα : α ∈ˢ (univ w : V)) :
    app (LIST α) pt ∈ˢ (univ w : V) :=
  famSpace_app (hC.fam hα) pt_mem_unitSet

/-- **The ordinary reading's fibre law** — the container's fixed-point
equation, read at the recorded family. -/
theorem mem_value (hC : ListClause w LIST ΨL injL) {α : V} (hα : α ∈ˢ (univ w : V)) {x : V} :
    x ∈ˢ app (LIST α) pt ↔
      x = injL 0 [] ∨ ∃ h, h ∈ˢ α ∧ ∃ t, t ∈ˢ app (LIST α) pt ∧ x = injL 1 [h, t] := by
  have hfix : app (ΨL α (lfpTuple w 1 uIs (ΨL α)) 0) pt = app (lfpTuple w 1 uIs (ΨL α) 0) pt :=
    app_lfpTuple_eq (hC.closed α hα) (hC.mono α hα) (hC.maps α hα) Nat.one_pos pt_mem_unitSet
  rw [hC.leaf α hα]
  refine Iff.trans ?_ (hC.fibre α hα _ (lfpTuple_mem w 1 uIs (ΨL α)) pt pt_mem_unitSet x)
  rw [hfix]

/-- **The container is MONOTONE in its parameter** — derived from the
clause as §1.2 states it (`leaf` + `fibre` + the functor clauses), by
leastness of the carrier at the smaller parameter against the carrier
at the larger one.  No strengthening of the clause is needed. -/
theorem value_mono (hC : ListClause w LIST ΨL injL) {α β : V} (hα : α ∈ˢ (univ w : V))
    (hβ : β ∈ˢ (univ w : V)) (hsub : α ⊆ˢ β) : app (LIST α) pt ⊆ˢ app (LIST β) pt := by
  have hLβ := lfpTuple_mem w 1 uIs (ΨL β)
  have hcl : IsClosedTuple w 1 uIs (ΨL α) (lfpTuple w 1 uIs (ΨL β)) := by
    refine ⟨hLβ, fun m hm i hi x hx => ?_⟩
    obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
    obtain rfl := mem_unitSet_iff.mp hi
    refine lfpTuple_closed (hC.closed β hβ) (hC.mono β hβ) 0 Nat.one_pos pt pt_mem_unitSet x ?_
    refine (hC.fibre β hβ _ hLβ pt pt_mem_unitSet x).mpr ?_
    rcases (hC.fibre α hα _ hLβ pt pt_mem_unitSet x).mp hx with h | ⟨h, hh, t, ht, hx'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, hsub h hh, t, ht, hx'⟩
  have h := lfpTuple_le hcl 0 Nat.one_pos pt pt_mem_unitSet
  rw [hC.leaf α hα, hC.leaf β hβ]
  exact h

end ListClause

/-! ## The NARROW operator

One component, one constructor: `Φ X = { node l | l ∈ ⟦List⟧ X }`,
with the container read ordinarily at the hole.  There is no copy. -/

variable {S : TreeListSig V}

/-- The narrow operator at the value level. -/
noncomputable def narΦ (S : TreeListSig V) (A : V) : V :=
  image (fun l => S.injT 0 [l]) (app (S.LIST A) pt)

theorem mem_narΦ {A x : V} :
    x ∈ˢ narΦ S A ↔ ∃ l, l ∈ˢ app (S.LIST A) pt ∧ x = S.injT 0 [l] := mem_image

/-- The narrow operator as a one-component tuple functor. -/
noncomputable def narΨ (S : TreeListSig V) (X : Nat → V) : Nat → V :=
  fun _ => graph (fun _ => narΦ S (app (X 0) pt)) unitSet

theorem app_narΨ (S : TreeListSig V) (X : Nat → V) (m : Nat) :
    app (narΨ S X m) pt = narΦ S (app (X 0) pt) := app_graph pt_mem_unitSet

theorem narΦ_mono (hS : NarOk S) {A B : V} (hA : A ∈ˢ (univ S.w : V)) (hB : B ∈ˢ (univ S.w : V))
    (h : A ⊆ˢ B) : narΦ S A ⊆ˢ narΦ S B := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := mem_narΦ.mp hx
  exact mem_narΦ.mpr ⟨l, hS.ok.list.value_mono hA hB h l hl, rfl⟩

theorem narΦ_mem_univ (hS : NarOk S) {A : V} (hA : A ∈ˢ (univ S.w : V)) :
    narΦ S A ∈ˢ (univ S.w : V) := by
  by_cases hw : S.w = 0
  · rw [hw, univ_zero]
    refine mem_univZero.mpr fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := mem_narΦ.mp hx
    rw [hS.ok.tree.mkZero hw 0 [l]]
    exact pt_mem_unitSet
  · have hU := univ_isTGUniverse (V := V) hw
    have hv := hS.ok.list.value_mem_univ hA
    exact hU.image_mem hv fun l hl => hS.ok.tree.memU hw l (hU.transitive hv hl)

theorem narΨ_mono (hS : NarOk S) : MonoTuple S.w 1 uIs (narΨ S) := by
  intro X Y hX hY hle m hm i hi x hx
  obtain rfl := mem_unitSet_iff.mp hi
  rw [app_narΨ] at hx ⊢
  exact narΦ_mono hS (famSpace_app (hX 0 Nat.one_pos) pt_mem_unitSet)
    (famSpace_app (hY 0 Nat.one_pos) pt_mem_unitSet)
    (hle 0 Nat.one_pos pt pt_mem_unitSet) x hx

theorem narΨ_maps (hS : NarOk S) : MapsTuple S.w 1 uIs (narΨ S) := by
  intro X hX m hm
  show graph (fun _ => narΦ S (app (X 0) pt)) unitSet ∈ˢ famSpace S.w (uIs m)
  exact graph_mem_famSpace fun _ _ =>
    narΦ_mem_univ hS (famSpace_app (hX 0 Nat.one_pos) pt_mem_unitSet)

/-! ## (W) with NO wide operator: the ω-iterate

The narrow operator's ω-iterate `⋃ₙ Φⁿ ∅` is a closed pre-fixed point.
Formation is `natUnion_mem_univ_pos`; closure is the FINITARITY of the
container in its parameter —

-- F5 FINDING: the clause of §1.2 does NOT record that the container
is finitary, and (W) at the narrow operator needs it: a value of
`⟦List⟧ (⋃ₙ Aₙ)` must already be a value of some `⟦List⟧ Aₙ`.  Here it
is proved by hand (`narTop_cont`), by the container's OWN lfp
induction off its `nil`/`cons` fibre law — i.e. from the *specific*
shape of this container, not from the clause.  An INFINITARY container
(`Stream`, `ω → α`) has no such stage bound, and for it the narrow
route must either record ω-cocontinuity in the clause or fall back on
a transient wide operator's closed tuple (`tupleContainer_closed_exists`
at the block+copy, F0's `blkΨ_closed`, whose component `0` bounds the
narrow operator by leastness).  This is the ONE place where the narrow
route is weaker than the wide one. -/

theorem narStage_mem_univ (hS : NarOk S) (n : Nat) : Tower.iterF (narΦ S) n ∈ˢ (univ S.w : V) := by
  induction n with
  | zero => exact empty_mem_univ S.w
  | succ n ih => exact narΦ_mem_univ hS ih

theorem narStage_succ_le (hS : NarOk S) (n : Nat) :
    Tower.iterF (narΦ S) n ⊆ˢ Tower.iterF (narΦ S) (n + 1) := by
  induction n with
  | zero => exact empty_subset _
  | succ n ih =>
    exact narΦ_mono hS (narStage_mem_univ hS n) (narStage_mem_univ hS (n + 1)) ih

theorem narStage_le (hS : NarOk S) {m n : Nat} (h : m ≤ n) :
    Tower.iterF (narΦ S) m ⊆ˢ Tower.iterF (narΦ S) n := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp h
    exact Subset.refl _
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact Subset.trans (ih (Nat.lt_succ_iff.mp hlt)) (narStage_succ_le hS n)
    · obtain rfl : m = n + 1 := Nat.le_antisymm h hge
      exact Subset.refl _

/-- The ω-iterate of the narrow operator. -/
noncomputable def narTop (S : TreeListSig V) : V := Tower.iterU (narΦ S)

theorem narTop_mem_univ (hS : NarOk S) (hw : S.w ≠ 0) : narTop S ∈ˢ (univ S.w : V) :=
  Tower.natUnion_mem_univ_pos hw (narStage_mem_univ hS)

/-- **Finitarity**: a list over the ω-iterate is a list over some
finite stage — by the container's own lfp induction. -/
theorem narTop_cont (hS : NarOk S) (hw : S.w ≠ 0) {l : V}
    (hl : l ∈ˢ app (S.LIST (narTop S)) pt) :
    ∃ n, l ∈ˢ app (S.LIST (Tower.iterF (narΦ S) n)) pt := by
  have hC := hS.ok.list
  have hα : narTop S ∈ˢ (univ S.w : V) := narTop_mem_univ hS hw
  have key : ∀ m, m < 1 → ∀ i, i ∈ˢ uIs m → ∀ x,
      x ∈ˢ app (lfpTuple S.w 1 uIs (S.ΨL (narTop S)) m) i →
      ∃ n, x ∈ˢ app (S.LIST (Tower.iterF (narΦ S) n)) pt := by
    refine lfpTuple_induction (hC.closed _ hα) (hC.mono _ hα)
      (fun _ _ x => ∃ n, x ∈ˢ app (S.LIST (Tower.iterF (narΦ S) n)) pt) ?_
    intro m hm i hi x hx
    obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
    obtain rfl := mem_unitSet_iff.mp hi
    rcases (hC.fibre _ hα _ (sepTuple_mem S.w 1 uIs (S.ΨL (narTop S)) _) pt pt_mem_unitSet x).mp hx
      with rfl | ⟨h, hh, t, ht, rfl⟩
    · exact ⟨0, (hC.mem_value (narStage_mem_univ hS 0)).mpr (Or.inl rfl)⟩
    · have hh' : h ∈ˢ Tower.iterU (narΦ S) := hh
      obtain ⟨mh, hmh⟩ := Tower.mem_iterU.mp hh'
      have hP : ∃ n, t ∈ˢ app (S.LIST (Tower.iterF (narΦ S) n)) pt := by
        unfold sepTuple at ht
        rw [app_graph (show (pt : V) ∈ˢ uIs 0 from pt_mem_unitSet)] at ht
        exact (mem_sep.mp ht).2
      obtain ⟨nt, hnt⟩ := hP
      refine ⟨max mh nt, (hC.mem_value (narStage_mem_univ hS (max mh nt))).mpr
        (Or.inr ⟨h, ?_, t, ?_, rfl⟩)⟩
      · exact narStage_le hS (Nat.le_max_left _ _) h hmh
      · exact hC.value_mono (narStage_mem_univ hS nt) (narStage_mem_univ hS (max mh nt))
          (narStage_le hS (Nat.le_max_right _ _)) t hnt
  refine key 0 Nat.one_pos pt pt_mem_unitSet l ?_
  rw [← hC.leaf _ hα]
  exact hl

theorem narΦ_narTop_sub (hS : NarOk S) (hw : S.w ≠ 0) : narΦ S (narTop S) ⊆ˢ narTop S := by
  refine Tower.iterU_closed_of fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := mem_narΦ.mp hx
  obtain ⟨n, hn⟩ := narTop_cont hS hw hl
  exact ⟨n, mem_narΦ.mpr ⟨l, hn, rfl⟩⟩

/-- **(W) for the narrow operator**, with no wide operator anywhere:
the ω-iterate is closed. -/
theorem narΨ_closed (hS : NarOk S) : ∃ L, IsClosedTuple S.w 1 uIs (narΨ S) L := by
  by_cases hw : S.w = 0
  · rw [hw]
    exact closedTuple_zero (hw ▸ narΨ_maps hS)
  have happ : app ((fun _ => graph (fun _ => narTop S) unitSet : Nat → V) 0) pt = narTop S :=
    app_graph pt_mem_unitSet
  refine ⟨fun _ => graph (fun _ => narTop S) unitSet,
    fun _ _ => graph_mem_famSpace fun _ _ => narTop_mem_univ hS hw, fun m hm i hi x hx => ?_⟩
  obtain rfl := mem_unitSet_iff.mp hi
  rw [app_narΨ, happ] at hx
  rw [app_graph pt_mem_unitSet]
  exact narΦ_narTop_sub hS hw x hx

/-- **(W), the ALTERNATIVE route** — NOT used by anything below,
recorded because it is the one the maintainer's ruling allows for an
INFINITARY container, and because it costs nothing here: F0's
transient two-component operator (the block plus a COPY of the
container) has a closed tuple, and its FIRST component already bounds
the narrow operator — the container's carrier at that component's
value lies below the copy's component, by leastness against it, and
`node` of that is back in the first component.  Nothing is identified
and no fixed point of the wide operator is taken: the copy serves as a
SET-SIZED BOUND and is discarded.  Unlike `narΨ_closed` this uses no
finitarity, so it is the route an infinitary container must take. -/
theorem narΨ_closed_of_wide (hS : NarOk S) : ∃ L, IsClosedTuple S.w 1 uIs (narΨ S) L := by
  obtain ⟨L, hLmem, hLle⟩ := blkΨ_closed hS.ok
  have hA : app (L 0) pt ∈ˢ (univ S.w : V) := famSpace_app (hLmem 0 (by omega)) pt_mem_unitSet
  have hsub : app (S.LIST (app (L 0) pt)) pt ⊆ˢ app (L 1) pt := by
    have hcl : IsClosedTuple S.w 1 uIs (S.ΨL (app (L 0) pt)) (fun _ => L 1) := by
      refine ⟨fun _ _ => hLmem 1 (by omega), fun m hm i hi x hx => ?_⟩
      obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
      obtain rfl := mem_unitSet_iff.mp hi
      have h1 := hLle 1 (by omega) pt pt_mem_unitSet x
      rw [app_blkΨ_one] at h1
      refine h1 ?_
      rcases (hS.ok.list.fibre _ hA _ (fun _ _ => hLmem 1 (by omega)) pt pt_mem_unitSet x).mp hx
        with rfl | ⟨h, hh, t, ht, rfl⟩
      · exact mem_listFib.mpr (Or.inl rfl)
      · exact mem_listFib.mpr (Or.inr ⟨h, t, hh, ht, rfl⟩)
    have hle := lfpTuple_le hcl 0 Nat.one_pos pt pt_mem_unitSet
    rw [hS.ok.list.leaf _ hA]
    exact hle
  refine ⟨fun _ => L 0, fun _ _ => hLmem 0 (by omega), fun m hm i hi x hx => ?_⟩
  obtain rfl := mem_unitSet_iff.mp hi
  rw [app_narΨ] at hx
  obtain ⟨l, hl, rfl⟩ := mem_narΦ.mp hx
  have h0 := hLle 0 (by omega) pt pt_mem_unitSet (S.injT 0 [l])
  rw [app_blkΨ_zero] at h0
  exact h0 (mem_nodeFib.mpr ⟨l, hsub l hl, rfl⟩)

/-! ## The carrier, the constructors, the elimination -/

/-- The block's carrier: the NARROW one-component least fixed point. -/
noncomputable def narCar (S : TreeListSig V) : Nat → V := lfpTuple S.w 1 uIs (narΨ S)

/-- `⟦Tree⟧ = T*`. -/
noncomputable def narT (S : TreeListSig V) : V := app (narCar S 0) pt

/-- `⟦List⟧ T*`, read ORDINARILY through the container's clause — a
derived set, not a component of anything. -/
noncomputable def narL (S : TreeListSig V) : V := app (S.LIST (narT S)) pt

theorem narT_mem_univ (S : TreeListSig V) : narT S ∈ˢ (univ S.w : V) :=
  famSpace_app (lfpTuple_mem S.w 1 uIs (narΨ S) 0 Nat.one_pos) pt_mem_unitSet

/-- The fixed-point equation of the narrow operator. -/
theorem narT_eq (hS : NarOk S) : narT S = narΦ S (narT S) :=
  (app_lfpTuple_eq (narΨ_closed hS) (narΨ_mono hS) (narΨ_maps hS)
    Nat.one_pos pt_mem_unitSet).symm.trans (app_narΨ S (narCar S) 0)

/-- `⟦Tree⟧ = { node l | l ∈ ⟦List⟧ ⟦Tree⟧ }` — the member's values,
with `node`'s domain read ordinarily. -/
theorem mem_narT (hS : NarOk S) {x : V} :
    x ∈ˢ narT S ↔ ∃ l, l ∈ˢ narL S ∧ x = S.injT 0 [l] := by
  rw [narT_eq hS]
  exact mem_narΦ

/-- **`Tree.node`'s typing**, with its domain read ordinarily. -/
theorem node_mem_narT (hS : NarOk S) {l : V} (hl : l ∈ˢ narL S) : S.injT 0 [l] ∈ˢ narT S :=
  (mem_narT hS).mpr ⟨l, hl, rfl⟩

/-- The container's fibre law at the pin — `⟦List⟧ ⟦Tree⟧`'s values. -/
theorem mem_narL (hS : NarOk S) {x : V} :
    x ∈ˢ narL S ↔
      x = S.injL 0 [] ∨ ∃ h, h ∈ˢ narT S ∧ ∃ t, t ∈ˢ narL S ∧ x = S.injL 1 [h, t] :=
  hS.ok.list.mem_value (narT_mem_univ S)

/-- `List.nil`'s value, read ordinarily at `Tree`. -/
theorem nil_mem_narL (hS : NarOk S) : S.injL 0 [] ∈ˢ narL S := (mem_narL hS).mpr (Or.inl rfl)

/-- `List.cons`'s value, read ordinarily at `Tree`. -/
theorem cons_mem_narL (hS : NarOk S) {h t : V} (hh : h ∈ˢ narT S) (ht : t ∈ˢ narL S) :
    S.injL 1 [h, t] ∈ˢ narL S := (mem_narL hS).mpr (Or.inr ⟨h, hh, t, ht, rfl⟩)

/-! ## (iii) The recursor family, by ∈-recursion

The recursion runs over the tagged union of the two majors' ORDINARY
carriers — `⟦Tree⟧` and `⟦List⟧ ⟦Tree⟧` — with the predecessors of a
tagged value being every union member whose payload is ∈-smaller
(`tcPred`).  Neither carrier is a component of a tuple lfp, and
nothing here needs them to be: `WfRecKit` asks only for the motives
and the step.

Two things are worth noting against F0's `UnionRecKit` instance:

* the predecessor set is NOT characterised.  `tcPred` of `node l`
  contains `l` but also every sub-tree and sub-list of `l`; the step
  reads the entries it wants out of the graph and ignores the rest, so
  only the POSITIVE memberships (`list_pred_node`, `tree_pred_cons`,
  `list_pred_cons` — each one line off the encoding-depth clause) are
  ever proved.  F0 had to pin the predecessor set down exactly at
  every constructor (`mem_blkPred_node`, `not_mem_blkPred_nil`,
  `mem_blkPred_cons`, then `blkPred_predsFrom`: ~70 lines);
* the motives and the step are F0's, unchanged (`blkB`, `blkSt` and
  their five laws are imported from `EnvClauseTreeList.lean`): the
  formulation changes the *recursion principle*, not the minors. -/

section Rec

variable {S : TreeListSig V} {ℓ : Nat} {M₀ M₁ : V → V} {mNode : V → V → V} {mNil : V}
  {mCons : V → V → V → V → V}

/-- **The two recursion classes**: the member's carrier and the
container's reading at the pin — ORDINARY sets, with no fixed-point
structure assumed of the second. -/
noncomputable def narC (S : TreeListSig V) : Nat → V
  | 0 => narCar S 0
  | _ + 1 => S.LIST (narT S)

theorem app_narC_zero (S : TreeListSig V) : app (narC S 0) pt = narT S := rfl

theorem app_narC_one (S : TreeListSig V) : app (narC S 1) pt = narL S := rfl

theorem mem_narIdx {u : V} :
    u ∈ˢ unionSet 2 uIs (narC S) ↔
      (∃ x, x ∈ˢ narT S ∧ u = tagged 0 pt x) ∨ (∃ l, l ∈ˢ narL S ∧ u = tagged 1 pt l) := by
  rw [mem_unionSet]
  constructor
  · rintro ⟨c, hc, i, hi, x, hx, rfl⟩
    obtain rfl := mem_unitSet_iff.mp hi
    match c, hc with
    | 0, _ => exact Or.inl ⟨x, hx, rfl⟩
    | 1, _ => exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact ⟨0, by omega, pt, pt_mem_unitSet, x, hx, rfl⟩
    · exact ⟨1, by omega, pt, pt_mem_unitSet, l, hl, rfl⟩

theorem tree_mem_narIdx {x : V} (hx : x ∈ˢ narT S) : tagged 0 pt x ∈ˢ unionSet 2 uIs (narC S) :=
  mem_narIdx.mpr (Or.inl ⟨x, hx, rfl⟩)

theorem list_mem_narIdx {l : V} (hl : l ∈ˢ narL S) : tagged 1 pt l ∈ˢ unionSet 2 uIs (narC S) :=
  mem_narIdx.mpr (Or.inr ⟨l, hl, rfl⟩)

/-! ### The three ∈-depth facts the instance owes

One line each, straight off `TagDepth`: the constructor's fields are
subterms of the constructed value, so the corresponding tagged indices
are predecessors. -/

theorem list_pred_node (hS : NarOk S) (hw : S.w ≠ 0) {l : V} (hl : l ∈ˢ narL S) :
    tagged 1 pt l ∈ˢ tcPred (unionSet 2 uIs (narC S)) (tagged 0 pt (S.injT 0 [l])) := by
  refine mem_tcPred.mpr ⟨list_mem_narIdx hl, ?_⟩
  rw [tagVal_tagged, tagVal_tagged]
  exact hS.depthT.depth hw 0 [l] l List.mem_cons_self

theorem tree_pred_cons (hS : NarOk S) (hw : S.w ≠ 0) {h t : V} (hh : h ∈ˢ narT S) :
    tagged 0 pt h ∈ˢ tcPred (unionSet 2 uIs (narC S)) (tagged 1 pt (S.injL 1 [h, t])) := by
  refine mem_tcPred.mpr ⟨tree_mem_narIdx hh, ?_⟩
  rw [tagVal_tagged, tagVal_tagged]
  exact hS.depthL.depth hw 1 [h, t] h List.mem_cons_self

theorem list_pred_cons (hS : NarOk S) (hw : S.w ≠ 0) {h t : V} (ht : t ∈ˢ narL S) :
    tagged 1 pt t ∈ˢ tcPred (unionSet 2 uIs (narC S)) (tagged 1 pt (S.injL 1 [h, t])) := by
  refine mem_tcPred.mpr ⟨list_mem_narIdx ht, ?_⟩
  rw [tagVal_tagged, tagVal_tagged]
  exact hS.depthL.depth hw 1 [h, t] t (List.mem_cons_of_mem h List.mem_cons_self)

/-! ### The kit -/

section Kit

variable (hS : NarOk S) (hw : S.w ≠ 0)
  (hM₀ : ∀ x, x ∈ˢ narT S → M₀ x ∈ˢ (univ ℓ : V))
  (hM₁ : ∀ l, l ∈ˢ narL S → M₁ l ∈ˢ (univ ℓ : V))
  (hmNode : ∀ l ih, l ∈ˢ narL S → ih ∈ˢ M₁ l → mNode l ih ∈ˢ M₀ (S.injT 0 [l]))
  (hmNil : mNil ∈ˢ M₁ (S.injL 0 []))
  (hmCons : ∀ h t ih₁ ih₂, h ∈ˢ narT S → t ∈ˢ narL S → ih₁ ∈ˢ M₀ h → ih₂ ∈ˢ M₁ t →
    mCons h t ih₁ ih₂ ∈ˢ M₁ (S.injL 1 [h, t]))

include hM₀ hM₁ in
theorem narB_mem_univ : ∀ u, u ∈ˢ unionSet 2 uIs (narC S) → blkB M₀ M₁ u ∈ˢ (univ ℓ : V) := by
  intro u hu
  rcases mem_narIdx.mp hu with ⟨x, hx, rfl⟩ | ⟨l, hl, rfl⟩
  · rw [blkB_tree]; exact hM₀ x hx
  · rw [blkB_list]; exact hM₁ l hl

include hM₀ hM₁ in
theorem narGraph_mem_B {u v : V} (hu : u ∈ˢ unionSet 2 uIs (narC S))
    (hv : v ∈ˢ app (recGraph ℓ (unionSet 2 uIs (narC S)) (tcPred (unionSet 2 uIs (narC S)))
      (blkB M₀ M₁) (blkSt S mNode mNil mCons)) u) : v ∈ˢ blkB M₀ M₁ u := by
  rw [app_recGraph_eq (narB_mem_univ hM₀ hM₁) (fun u _ => tcPred_subset _ u) hu] at hv
  exact (mem_recGraphFibre.mp hv).1

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- **The step is typed** — from the minors' typing and the three
∈-depth facts alone. -/
theorem narSt_mem : ∀ u, u ∈ˢ unionSet 2 uIs (narC S) → ∀ g,
    g ∈ˢ piSet (tcPred (unionSet 2 uIs (narC S)) u)
      (fun j => app (recGraph ℓ (unionSet 2 uIs (narC S)) (tcPred (unionSet 2 uIs (narC S)))
        (blkB M₀ M₁) (blkSt S mNode mNil mCons)) j) →
    blkSt S mNode mNil mCons u g ∈ˢ blkB M₀ M₁ u := by
  intro u hu g hg
  have hval : ∀ v, v ∈ˢ tcPred (unionSet 2 uIs (narC S)) u → app g v ∈ˢ blkB M₀ M₁ v := fun v hv =>
    narGraph_mem_B hM₀ hM₁ (tcPred_subset _ u v hv) (app_mem_of_mem_piSet hg hv)
  rcases mem_narIdx.mp hu with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
  · obtain ⟨l, hl, rfl⟩ := (mem_narT hS).mp hx
    rw [blkSt_node hS.ok hw, blkB_tree]
    have h := hval (tagged 1 pt l) (list_pred_node hS hw hl)
    rw [blkB_list] at h
    exact hmNode l _ hl h
  · rcases (mem_narL hS).mp hy with rfl | ⟨h, hh, t, ht, rfl⟩
    · rw [blkSt_nil, blkB_list]; exact hmNil
    · rw [blkSt_cons hS.ok hw, blkB_list]
      have h₁ := hval (tagged 0 pt h) (tree_pred_cons hS hw hh)
      have h₂ := hval (tagged 1 pt t) (list_pred_cons hS hw ht)
      rw [blkB_tree] at h₁
      rw [blkB_list] at h₂
      exact hmCons h t _ _ hh ht h₁ h₂

/-- **The block's recursion kit**: two ordinary carriers, the motives,
the step.  No `PredsFrom`, no accessibility obligation, no tuple. -/
noncomputable def narKit : WfRecKit ℓ 2 uIs (narC S) :=
  ⟨blkB M₀ M₁, blkSt S mNode mNil mCons, narB_mem_univ hM₀ hM₁,
    narSt_mem hS hw hM₀ hM₁ hmNode hmNil hmCons⟩

local notation "K*" => narKit hS hw hM₀ hM₁ hmNode hmNil hmCons

@[simp] theorem narKit_B : (K*).B = blkB M₀ M₁ := rfl
@[simp] theorem narKit_st : (K*).st = blkSt S mNode mNil mCons := rfl

theorem narKit_recAt (c : Nat) (i x : V) :
    (K*).recAt c i x
      = recSel (recGraph ℓ (unionSet 2 uIs (narC S)) (tcPred (unionSet 2 uIs (narC S)))
          (blkB M₀ M₁) (blkSt S mNode mNil mCons)) (tagged c i x) := rfl

/-- `Tree.rec`. -/
noncomputable def narRecT (x : V) : V := (K*).recAt 0 pt x

/-- `Tree.rec_1` — the recursor of the container's reading at the pin,
the one official emits for the aux key `List Tree`. -/
noncomputable def narRecL (l : V) : V := (K*).recAt 1 pt l

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- **Typing**: `Tree.rec … x ∈ motive x`. -/
theorem narRecT_mem {x : V} (hx : x ∈ˢ narT S) :
    narRecT hS hw hM₀ hM₁ hmNode hmNil hmCons x ∈ˢ M₀ x := by
  have h := (K*).rec_mem_B (show (0 : Nat) < 2 by omega)
    (show (pt : V) ∈ˢ uIs 0 from pt_mem_unitSet) (show x ∈ˢ app (narC S 0) pt from hx)
  rw [narKit_B, blkB_tree] at h
  exact h

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- **Typing**: `Tree.rec_1 … l ∈ motive_1 l`. -/
theorem narRecL_mem {l : V} (hl : l ∈ˢ narL S) :
    narRecL hS hw hM₀ hM₁ hmNode hmNil hmCons l ∈ˢ M₁ l := by
  have h := (K*).rec_mem_B (show (1 : Nat) < 2 by omega)
    (show (pt : V) ∈ˢ uIs 1 from pt_mem_unitSet) (show l ∈ˢ app (narC S 1) pt from hl)
  rw [narKit_B, blkB_list] at h
  exact h

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- The recursion equation, in the engine's form. -/
theorem narRec_eq {c : Nat} (hc : c < 2) {x : V} (hx : x ∈ˢ app (narC S c) pt) :
    (K*).recAt c pt x
      = blkSt S mNode mNil mCons (tagged c pt x)
          (graph
            (fun j => recSel (recGraph ℓ (unionSet 2 uIs (narC S))
              (tcPred (unionSet 2 uIs (narC S))) (blkB M₀ M₁) (blkSt S mNode mNil mCons)) j)
            (tcPred (unionSet 2 uIs (narC S)) (tagged c pt x))) :=
  (K*).rec_eq hc (show (pt : V) ∈ˢ uIs c from pt_mem_unitSet) hx

/-! ### The three ι rules -/

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- ι 1: `Tree.rec … (node l) = mNode l (Tree.rec_1 … l)`. -/
theorem narRecT_node {l : V} (hl : l ∈ˢ narL S) :
    narRecT hS hw hM₀ hM₁ hmNode hmNil hmCons (S.injT 0 [l])
      = mNode l (narRecL hS hw hM₀ hM₁ hmNode hmNil hmCons l) := by
  show (K*).recAt 0 pt (S.injT 0 [l]) = mNode l ((K*).recAt 1 pt l)
  rw [narRec_eq hS hw hM₀ hM₁ hmNode hmNil hmCons (show (0 : Nat) < 2 by omega)
      (show S.injT 0 [l] ∈ˢ app (narC S 0) pt from node_mem_narT hS hl),
    blkSt_node hS.ok hw, app_graph (list_pred_node hS hw hl), narKit_recAt]

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- ι 2: `Tree.rec_1 … nil = mNil`. -/
theorem narRecL_nil : narRecL hS hw hM₀ hM₁ hmNode hmNil hmCons (S.injL 0 []) = mNil := by
  show (K*).recAt 1 pt (S.injL 0 []) = mNil
  rw [narRec_eq hS hw hM₀ hM₁ hmNode hmNil hmCons (show (1 : Nat) < 2 by omega)
      (show S.injL 0 [] ∈ˢ app (narC S 1) pt from nil_mem_narL hS),
    blkSt_nil]

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- ι 3: `Tree.rec_1 … (cons h t) = mCons h t (Tree.rec … h) (Tree.rec_1 … t)` —
the rule that CROSSES the two classes. -/
theorem narRecL_cons {h t : V} (hh : h ∈ˢ narT S) (ht : t ∈ˢ narL S) :
    narRecL hS hw hM₀ hM₁ hmNode hmNil hmCons (S.injL 1 [h, t])
      = mCons h t (narRecT hS hw hM₀ hM₁ hmNode hmNil hmCons h)
          (narRecL hS hw hM₀ hM₁ hmNode hmNil hmCons t) := by
  show (K*).recAt 1 pt (S.injL 1 [h, t])
    = mCons h t ((K*).recAt 0 pt h) ((K*).recAt 1 pt t)
  rw [narRec_eq hS hw hM₀ hM₁ hmNode hmNil hmCons (show (1 : Nat) < 2 by omega)
      (show S.injL 1 [h, t] ∈ˢ app (narC S 1) pt from cons_mem_narL hS hh ht),
    blkSt_cons hS.ok hw, app_graph (tree_pred_cons hS hw hh),
    app_graph (list_pred_cons hS hw ht), narKit_recAt, narKit_recAt]

end Kit

end Rec

/-! ## Non-vacuity: the standard encoding satisfies the depth clause

F0 already exhibits a model of `ListClause`/`TreeTags` (`stdInj`, the
tagged `kpair` tower).  The only new hypothesis F5 adds is the
encoding depth, and the same encoding satisfies it — so every theorem
of this file has a model at every level. -/

theorem mem_tc_kTuple : ∀ (fs : List V) {a : V}, a ∈ fs → a ∈ˢ tc (kTuple fs)
  | [], _, h => absurd h (List.not_mem_nil)
  | b :: bs, a, h => by
    show a ∈ˢ tc (kpair b (kTuple bs))
    rcases List.mem_cons.mp h with rfl | h'
    · exact mem_tc_kpair_left _ _
    · exact tc_trans (mem_tc_kTuple bs h') (mem_tc_kpair_right _ _)

/-- The standard tagged tower is ∈-deep in its fields. -/
theorem tagDepth_stdInj (w : Nat) : TagDepth w (stdInj (V := V) w) := by
  refine ⟨fun hw j fs a ha => ?_⟩
  unfold stdInj
  rw [if_neg hw]
  exact tc_trans (mem_tc_kTuple fs ha) (mem_tc_kpair_right _ _)

/-- **F5's hypothesis is satisfiable**: the standard `List` and the
standard member tags satisfy the env clause, the tag laws AND the
encoding depth. -/
theorem narOk_std (w : Nat) :
    NarOk (V := V) ⟨w, stdLIST w, stdΨL w, stdInj w, stdInj w⟩ :=
  ⟨treeListOk_std w, tagDepth_stdInj w, tagDepth_stdInj w⟩

end ConLeche.SetTheory
