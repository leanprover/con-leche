module

public import ConLeche.SetModel.EnvClauseTreeList
import ConLeche.SetModel.TupleContainer
@[expose] public section

/-!
# `P4 ::= mk (Rose P4)` through a NESTED container's wide table (falsifier F2)

The third falsifier of the *uniform* nested route
(`DESIGN-theory.md` §6.1 F2) — the **seeded-group** case: the pin's
container is ITSELF nested, so the group's segment is the container's
own WIDE table, seeded from its clause at the pin's value.

`nested_p04` is `P4C α ::= append (Array (P4C α))` with
`P4 ::= mk (P4C P4)`.  The smallest shape that still exercises
"the instance's segment is the container's WIDE table, seeded from its
clause" replaces `Array` by `List` and gives the container a real
parameter occurrence (`P4C`'s `α` is a phantom — it occurs only in the
recursive slot, so `P4C α` would not exercise the pin at all):

    inductive Rose (α : Type) where | node : α → List (Rose α) → Rose α

`Rose`'s own recorded table is WIDE — `N_Rose = 2`: `Rose`-at-`α` and
`Rose`'s own copy of `List` at `Rose α`.  The block `P4 ::= mk (Rose P4)`
is then a plain **three**-component block:

| c | component | group |
|---|---|---|
| 0 | `P4` | the member |
| 1 | `Rose P4` | `g₁` = `Rose` at the pin `P4`, component 0 of `Rose`'s table |
| 2 | `List (Rose P4)` | `g₁`, component 1 of `Rose`'s table |

There is exactly ONE group, of rank `0`: its pin is the member.  The
whole segment `[1, 1 + N_Rose)` is identified with `Rose`'s wide table
at `α := ⟦P4⟧` in ONE `lfpTuple_seg_congr` step (`car_seg_eq`), and
the seeding is visible in it: component `1`'s fibre reads the pin's
value — `car 0`, OUTSIDE the segment — for `Rose.node`'s label field,
while component `2`'s fibre reads only components INSIDE the segment.

**Pass criterion met**: no narrow clause of the container is used or
needed anywhere.  `RoseClause` is `DESIGN-theory.md` §1.2's record at
`N = 2`; nothing of the form "`⟦Rose α⟧` is a least fixed point in its
own parameter" appears, and the identification, the constructor typing
and the crossing ι rules all read the wide table.  The two places
where the clause of §1.2 as literally written is INSUFFICIENT are
marked `-- F2 FINDING:` and collected in the last section; both are
about what an INSTANCE component of a container's table must carry,
and the first is F1's finding seen again.

The last section discharges `RoseClause` at the standard reading of
`Rose` (`stdRoseClause`, `p4Ok_std`), at F0's own tags — in
particular the self-referential `instLeaf` of FINDING (2) has a model.

Everything here is over the bare `SetTheory` interface; no syntax.
`ListClause`, `consArm`, `uIs` and `TreeTags` are F0's
(`ConLeche/SetModel/EnvClauseTreeList.lean`), reused verbatim; the
file's shape follows F1 (`ConLeche/SetModel/EnvClauseP3.lean`).
-/

namespace ConLeche.SetTheory

open Tower (natFibre natFibre_vnat)

universe u

variable {V : Type u} [SetTheory V]

namespace P4Block

/-! ## `Rose`'s env clause — WIDE, at `N_Rose = 2`

`DESIGN-theory.md` §1.2 at a one-member block with one type parameter,
no indices, and ONE instance component of its own:

    Rose α ::= node (label : α) (children : List (Rose α))

Component `0` is `Rose` itself — `node`'s first field is an ordinary
field at the PARAMETER, its second a slot at component `1`; component
`1` is `Rose`'s own copy of `List` at `Rose α`, whose heads are a slot
at component `0` (**this** is what makes the container nested, and
what the seeding must transport). -/
structure RoseClause (w : Nat) (ROSE : V → V) (ΨR : V → (Nat → V) → Nat → V)
    (LIST : V → V) (injR : Nat → List V → V) (injL : Nat → List V → V) : Prop where
  /-- `leaf`, at the MEMBER's component. -/
  leaf : ∀ α, α ∈ˢ (univ w : V) → ROSE α = lfpTuple w 2 uIs (ΨR α) 0
  /-- `functor`, monotonicity, at width `2`. -/
  mono : ∀ α, α ∈ˢ (univ w : V) → MonoTuple w 2 uIs (ΨR α)
  /-- `functor`, space preservation. -/
  maps : ∀ α, α ∈ˢ (univ w : V) → MapsTuple w 2 uIs (ΨR α)
  /-- `functor`, the closed tuple. -/
  closed : ∀ α, α ∈ˢ (univ w : V) → ∃ L, IsClosedTuple w 2 uIs (ΨR α) L
  /-- `fibre` at component `0`: `Rose.node`'s label is an ordinary
  field at the parameter, its children a slot at component `1`. -/
  fibre0 : ∀ α, α ∈ˢ (univ w : V) → ∀ Y, InTupleSpace w 2 uIs Y → ∀ t, t ∈ˢ (unitSet : V) →
    ∀ x, x ∈ˢ app (ΨR α Y 0) t ↔
      ∃ a, a ∈ˢ α ∧ ∃ l, l ∈ˢ app (Y 1) pt ∧ x = injR 0 [a, l]
  /-- `fibre` at component `1`, `Rose`'s own copy of `List` at
  `Rose α`: heads at component `0`, tails at component `1` — the
  parameter `α` does NOT occur.

  F2 FINDING (1): the injections here are `injL`, the INNER
  container's member-local tags; §1.2's `ctor` clause is "members
  only", so an instance component's tags are tied to nothing and the ι
  rule the checker emits for this component (it fires on `List.cons`)
  cannot be stated.  Same finding as F1. -/
  fibre1 : ∀ α, α ∈ˢ (univ w : V) → ∀ Y, InTupleSpace w 2 uIs Y → ∀ t, t ∈ˢ (unitSet : V) →
    ∀ x, x ∈ˢ app (ΨR α Y 1) t ↔
      (x = injL 0 [] ∨ ∃ h, h ∈ˢ app (Y 0) pt ∧ ∃ t', t' ∈ˢ app (Y 1) pt ∧ x = injL 1 [h, t'])
  /-- The instance component's READING.

  F2 FINDING (2): §1.2 records `leaf` for members only, and the pins
  of an instance component's key may mention the container's OWN
  members — here component `1`'s key is `List (Rose α)`, so the
  recorded reading is `⟦List⟧` at `⟦Rose α⟧ = app (ROSE α) pt`, a
  frame in which the container's own member carrier appears.  §2.4's
  `⟦Ds⟧^ord` must therefore be defined RECURSIVELY over the block's
  own table, not just over the block's parameters — which is more than
  §1.2's members-only `leaf` says.  (In F1 the same clause was
  `LIST α`, and the recursion was invisible.) -/
  instLeaf : ∀ α, α ∈ˢ (univ w : V) → lfpTuple w 2 uIs (ΨR α) 1 = LIST (app (ROSE α) pt)
  /-- `mkZero` at the member's tags. -/
  mkZero : w = 0 → ∀ j fs, injR j fs = (pt : V)
  /-- `mkInj` at the member's tags. -/
  mkInj : w ≠ 0 → ∀ j j' fs fs', injR j fs = injR j' fs' → j = j' ∧ fs = fs'

namespace RoseClause

variable {w : Nat} {ROSE LIST : V → V} {ΨR : V → (Nat → V) → Nat → V}
  {injR injL : Nat → List V → V}

/-- Formation of `Rose.node`'s value, derived from `maps` + `fibre0`
at a parameter and a tuple chosen to hold exactly the wanted fields
(F0's recipe, `F0-REPORT.md` (F0-1)). -/
theorem node_mem_univ (hC : RoseClause w ROSE ΨR LIST injR injL) (hw : w ≠ 0) {a l : V}
    (ha : a ∈ˢ (univ w : V)) (hl : l ∈ˢ (univ w : V)) : injR 0 [a, l] ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  have hY : InTupleSpace w 2 uIs (fun _ => graph (fun _ => sing l) unitSet) :=
    fun _ _ => graph_mem_famSpace fun _ _ => hU.sing_mem hl hl
  refine hU.transitive
    (famSpace_app (hC.maps _ (hU.sing_mem ha ha) _ hY 0 (by omega)) pt_mem_unitSet) ?_
  refine (hC.fibre0 _ (hU.sing_mem ha ha) _ hY pt pt_mem_unitSet _).mpr
    ⟨a, mem_sing.mpr rfl, l, ?_, rfl⟩
  rw [app_graph pt_mem_unitSet]
  exact mem_sing.mpr rfl

end RoseClause

/-! ## The block's datum -/

/-- The data F2 reasons about.  ONE level `w`. -/
structure P4Sig (V : Type u) [SetTheory V] where
  /-- The value level. -/
  w : Nat
  /-- `⟦Rose α⟧`, as a family. -/
  ROSE : V → V
  /-- `Rose`'s own WIDE operator at a parameter, two components. -/
  ΨR : V → (Nat → V) → Nat → V
  /-- `⟦List α⟧`, as a family. -/
  LIST : V → V
  /-- `List`'s own operator at a parameter, one component. -/
  ΨL : V → (Nat → V) → Nat → V
  /-- `Rose`'s member-local tags. -/
  injR : Nat → List V → V
  /-- `List`'s member-local tags, shared with `Rose`'s table component
  `1`. -/
  injL : Nat → List V → V
  /-- `P4`'s tags. -/
  injP : Nat → List V → V

/-- The hypotheses: the containers' env clauses and the member's tag
laws.  `ListClause` is needed only for the FORMATION of the copy's
values at `w ≠ 0` (`nil_mem_univ`/`cons_mem_univ`); the identification
never reads it. -/
structure P4Ok (S : P4Sig V) : Prop where
  /-- `Rose`'s wide env clause, `DESIGN-theory.md` §1.2 at `N = 2`. -/
  rose : RoseClause S.w S.ROSE S.ΨR S.LIST S.injR S.injL
  /-- `List`'s env clause, F0's, at `N = 1`. -/
  list : ListClause S.w S.LIST S.ΨL S.injL
  /-- The member's own `mkZero`/`mkInj`/formation. -/
  mem : TreeTags S.w S.injP

variable {S : P4Sig V}

/-! ## The three-component operator -/

/-- `Rose.node`'s arm over a label set `A` and a children set `B`:
`{ node a l | a ∈ A, l ∈ B }`.  It serves both the COPY's fibre and,
at a parameter, the container's own operator (the non-vacuity section
below). -/
noncomputable def nodeArm (inj : Nat → List V → V) (A B : V) : V :=
  image (fun q => inj 0 [sfst q, ssnd q]) (sigmaPairs A fun _ => B)

theorem mem_nodeArm {inj : Nat → List V → V} {A B x : V} :
    x ∈ˢ nodeArm inj A B ↔ ∃ a, a ∈ˢ A ∧ ∃ l, l ∈ˢ B ∧ x = inj 0 [a, l] := by
  unfold nodeArm
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
    obtain ⟨a, ha, l, hl, rfl⟩ := mem_sigmaPairs.mp hq
    rw [sfst_kpair, ssnd_kpair]
    exact ⟨a, ha, l, hl, rfl⟩
  · rintro ⟨a, ha, l, hl, rfl⟩
    refine mem_image.mpr ⟨kpair a l, mem_sigmaPairs.mpr ⟨a, ha, l, hl, rfl⟩, ?_⟩
    rw [sfst_kpair, ssnd_kpair]

/-- The `node` arm's formation, above `Prop`. -/
theorem nodeArm_mem_univ {w : Nat} (hw : w ≠ 0) {inj : Nat → List V → V} {A B : V}
    (hA : A ∈ˢ (univ w : V)) (hB : B ∈ˢ (univ w : V))
    (hnode : ∀ a l, a ∈ˢ (univ w : V) → l ∈ˢ (univ w : V) → inj 0 [a, l] ∈ˢ (univ w : V)) :
    nodeArm inj A B ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  refine hU.image_mem (hU.sigmaPairs_mem hA fun _ _ => hB) fun q hq => ?_
  obtain ⟨a, ha, l, hl, rfl⟩ := mem_sigmaPairs.mp hq
  rw [sfst_kpair, ssnd_kpair]
  exact hnode a l (hU.transitive hA ha) (hU.transitive hB hl)

/-- The three components' fibres at an argument tuple: `P4.mk`'s field
is a slot at `1`; `Rose.node`'s label is a slot at `0` (the pin is the
MEMBER) and its children a slot at `2`; the copy of `List` has heads
at `1` and tails at `2`. -/
noncomputable def blkFib (S : P4Sig V) (X : Nat → V) : Nat → V
  | 0 => image (fun r => S.injP 0 [r]) (app (X 1) pt)
  | 1 => nodeArm S.injR (app (X 0) pt) (app (X 2) pt)
  | _ => consArm S.injL (app (X 1) pt) (app (X 2) pt)

/-- **The block's operator**, a plain three-component block operator. -/
noncomputable def blkΨ (S : P4Sig V) (X : Nat → V) (c : Nat) : V :=
  graph (fun _ => blkFib S X c) unitSet

theorem app_blkΨ (S : P4Sig V) (X : Nat → V) (c : Nat) :
    app (blkΨ S X c) pt = blkFib S X c := app_graph pt_mem_unitSet

theorem blkFib_zero (S : P4Sig V) (X : Nat → V) :
    blkFib S X 0 = image (fun r => S.injP 0 [r]) (app (X 1) pt) := rfl

theorem blkFib_one (S : P4Sig V) (X : Nat → V) :
    blkFib S X 1 = nodeArm S.injR (app (X 0) pt) (app (X 2) pt) := rfl

theorem blkFib_two (S : P4Sig V) (X : Nat → V) :
    blkFib S X 2 = consArm S.injL (app (X 1) pt) (app (X 2) pt) := rfl

theorem mem_blkFib_zero {X : Nat → V} {x : V} :
    x ∈ˢ blkFib S X 0 ↔ ∃ r, r ∈ˢ app (X 1) pt ∧ x = S.injP 0 [r] := mem_image

theorem mem_blkFib_one {X : Nat → V} {x : V} :
    x ∈ˢ blkFib S X 1 ↔
      ∃ a, a ∈ˢ app (X 0) pt ∧ ∃ l, l ∈ˢ app (X 2) pt ∧ x = S.injR 0 [a, l] := mem_nodeArm

theorem mem_blkFib_two {X : Nat → V} {x : V} :
    x ∈ˢ blkFib S X 2 ↔
      x = S.injL 0 [] ∨
        ∃ h t, h ∈ˢ app (X 1) pt ∧ t ∈ˢ app (X 2) pt ∧ x = S.injL 1 [h, t] := mem_consArm

/-! ## (a) The functor clauses -/

theorem blkΨ_mono (S : P4Sig V) : MonoTuple S.w 3 uIs (blkΨ S) := by
  intro X Y hX hY hle c hc i hi x hx
  obtain rfl := mem_unitSet_iff.mp hi
  rw [app_blkΨ] at hx ⊢
  match c, hc with
  | 0, _ =>
    obtain ⟨r, hr, rfl⟩ := mem_blkFib_zero.mp hx
    exact mem_blkFib_zero.mpr ⟨r, hle 1 (by omega) pt pt_mem_unitSet r hr, rfl⟩
  | 1, _ =>
    obtain ⟨a, ha, l, hl, rfl⟩ := mem_blkFib_one.mp hx
    exact mem_blkFib_one.mpr ⟨a, hle 0 (by omega) pt pt_mem_unitSet a ha, l,
      hle 2 (by omega) pt pt_mem_unitSet l hl, rfl⟩
  | 2, _ =>
    rcases mem_blkFib_two.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · exact mem_blkFib_two.mpr (Or.inl rfl)
    · exact mem_blkFib_two.mpr (Or.inr ⟨h, t, hle 1 (by omega) pt pt_mem_unitSet h hh,
        hle 2 (by omega) pt pt_mem_unitSet t ht, rfl⟩)

theorem blkFib_mem (hS : P4Ok S) {X : Nat → V} (hX : InTupleSpace S.w 3 uIs X) (c : Nat)
    (hc : c < 3) : blkFib S X c ∈ˢ (univ S.w : V) := by
  by_cases hw : S.w = 0
  · rw [hw, univ_zero]
    refine mem_univZero.mpr fun x hx => ?_
    match c, hc with
    | 0, _ =>
      obtain ⟨r, -, rfl⟩ := mem_blkFib_zero.mp hx
      rw [hS.mem.mkZero hw 0 [r]]; exact pt_mem_unitSet
    | 1, _ =>
      obtain ⟨a, -, l, -, rfl⟩ := mem_blkFib_one.mp hx
      rw [hS.rose.mkZero hw 0 [a, l]]; exact pt_mem_unitSet
    | 2, _ =>
      rcases mem_blkFib_two.mp hx with rfl | ⟨h, t, -, -, rfl⟩
      · rw [hS.list.mkZero hw 0 []]; exact pt_mem_unitSet
      · rw [hS.list.mkZero hw 1 [h, t]]; exact pt_mem_unitSet
  · have hU := univ_isTGUniverse (V := V) hw
    have hap : ∀ m, m < 3 → app (X m) pt ∈ˢ (univ S.w : V) := fun m hm =>
      famSpace_app (hX m hm) pt_mem_unitSet
    match c, hc with
    | 0, _ =>
      rw [blkFib_zero]
      exact hU.image_mem (hap 1 (by omega)) fun r hr =>
        hS.mem.memU hw r (hU.transitive (hap 1 (by omega)) hr)
    | 1, _ =>
      rw [blkFib_one]
      exact nodeArm_mem_univ hw (hap 0 (by omega)) (hap 2 (by omega))
        fun _ _ ha hl => hS.rose.node_mem_univ hw ha hl
    | 2, _ =>
      rw [blkFib_two]
      exact consArm_mem_univ hw (hap 1 (by omega)) (hap 2 (by omega))
        (hS.list.nil_mem_univ hw) fun _ _ hh ht => hS.list.cons_mem_univ hw hh ht

theorem blkΨ_maps (hS : P4Ok S) : MapsTuple S.w 3 uIs (blkΨ S) := fun _ hX c hc =>
  graph_mem_famSpace fun _ _ => blkFib_mem hS hX c hc

/-! ## (b) (W): the closed tuple

Four constructors over three components; shapes `0 = P4.mk`,
`1 = Rose.node`, `2 = List.nil`, `3 = List.cons`, globally
distinguishing (`tupleContainer_closed_exists` reads `B`/`tgtM` off
the shape alone). -/

/-- The shapes, per component. -/
noncomputable def shp : Nat → V → V
  | 0, _ => sing (vnat 0)
  | 1, _ => sing (vnat 1)
  | _, _ => upair (vnat 2) (vnat 3)

/-- The positions of a shape, by tag. -/
noncomputable def posN : Nat → V
  | 0 => sing (vnat 0)
  | 1 => upair (vnat 0) (vnat 1)
  | 3 => upair (vnat 0) (vnat 1)
  | _ => empty

/-- The positions of a shape. -/
noncomputable def posns (a : V) : V := natFibre posN a

theorem posns_vnat (j : Nat) : posns (vnat j : V) = posN j := natFibre_vnat _ j

open Classical in
/-- The target component of a slot.  `Rose.node`'s label targets the
MEMBER (the pin is `P4`), its children the group's second component;
`List.cons`'s head targets the group's first component. -/
noncomputable def tgtC (a p : V) : Nat :=
  if a = (vnat 0 : V) then 1
  else if a = (vnat 1 : V) then (if p = (vnat 0 : V) then 0 else 2)
  else (if p = (vnat 0 : V) then 1 else 2)

open Classical in
/-- The builder. -/
noncomputable def mkC (S : P4Sig V) (_m : Nat) (a g : V) : V :=
  if a = (vnat 0 : V) then S.injP 0 [app g (vnat 0)]
  else if a = (vnat 1 : V) then S.injR 0 [app g (vnat 0), app g (vnat 1)]
  else if a = (vnat 2 : V) then S.injL 0 []
  else S.injL 1 [app g (vnat 0), app g (vnat 1)]

open Classical in
/-- **(W)**: the block's operator has a closed tuple. -/
theorem blkΨ_closed (hS : P4Ok S) : ∃ L, IsClosedTuple S.w 3 uIs (blkΨ S) L := by
  by_cases hw : S.w = 0
  · rw [hw]
    exact closedTuple_zero (hw ▸ blkΨ_maps hS)
  have hU := univ_isTGUniverse (V := V) hw
  have hv : ∀ j : Nat, (vnat j : V) ∈ˢ (univ S.w : V) := fun j => vnat_mem_univ_pos hw j
  refine tupleContainer_closed_exists hw (Is := uIs) (blkΨ S) shp posns tgtC (fun _ _ => pt)
    (mkC S) ?hA ?hB ?htgt ?hmkU ?helim
  case hA =>
    intro m hm i hi
    match m, hm with
    | 0, _ => exact hU.sing_mem (hv 0) (hv 0)
    | 1, _ => exact hU.sing_mem (hv 1) (hv 1)
    | 2, _ => exact hU.upair_mem (hv 2) (hv 2) (hv 3)
  case hB =>
    intro m hm i a hi ha
    have hcases : ∃ j : Nat, a = (vnat j : V) ∧ j < 4 := by
      match m, hm with
      | 0, _ => exact ⟨0, mem_sing.mp ha, by omega⟩
      | 1, _ => exact ⟨1, mem_sing.mp ha, by omega⟩
      | 2, _ => rcases mem_upair.mp ha with h | h
                · exact ⟨2, h, by omega⟩
                · exact ⟨3, h, by omega⟩
    obtain ⟨j, rfl, hj⟩ := hcases
    rw [posns_vnat]
    match j, hj with
    | 0, _ => exact hU.sing_mem (hv 0) (hv 0)
    | 1, _ => exact hU.upair_mem (hv 0) (hv 0) (hv 1)
    | 2, _ => exact hU.empty_mem (hv 0)
    | 3, _ => exact hU.upair_mem (hv 0) (hv 0) (hv 1)
  case htgt =>
    intro m hm i a p hi ha hp
    refine ⟨?_, pt_mem_unitSet⟩
    unfold tgtC
    repeat' split
    all_goals omega
  case hmkU =>
    intro m hm i a g hi ha hg
    unfold mkC
    split
    · exact hS.mem.memU hw _ (app_mem_univ hw hg _)
    · split
      · exact hS.rose.node_mem_univ hw (app_mem_univ hw hg _) (app_mem_univ hw hg _)
      · split
        · exact hS.list.nil_mem_univ hw
        · exact hS.list.cons_mem_univ hw (app_mem_univ hw hg _) (app_mem_univ hw hg _)
  case helim =>
    intro X hX m hm i hi x hx
    obtain rfl := mem_unitSet_iff.mp hi
    rw [app_blkΨ] at hx
    match m, hm with
    | 0, _ =>
      obtain ⟨r, hr, rfl⟩ := mem_blkFib_zero.mp hx
      refine ⟨vnat 0, mem_sing.mpr rfl, graph (fun _ => r) (sing (vnat 0)), ?_, ?_⟩
      · rw [posns_vnat]
        refine graph_mem_piSet fun p hp => ?_
        obtain rfl := mem_sing.mp hp
        show r ∈ˢ app (X (tgtC (vnat 0) (vnat 0))) pt
        rw [show tgtC (vnat 0 : V) (vnat 0) = 1 from by unfold tgtC; rw [if_pos rfl]]
        exact hr
      · show _ = mkC S 0 (vnat 0) _
        unfold mkC
        rw [if_pos rfl, app_graph (mem_sing.mpr rfl)]
    | 1, _ =>
      obtain ⟨a, ha, l, hl, rfl⟩ := mem_blkFib_one.mp hx
      refine ⟨vnat 1, mem_sing.mpr rfl,
        graph (fun p => if p = (vnat 0 : V) then a else l) (upair (vnat 0) (vnat 1)), ?_, ?_⟩
      · rw [posns_vnat]
        refine graph_mem_piSet fun p hp => ?_
        rcases mem_upair.mp hp with rfl | rfl
        · rw [if_pos rfl]
          show a ∈ˢ app (X (tgtC (vnat 1) (vnat 0))) pt
          rw [show tgtC (vnat 1 : V) (vnat 0) = 0 from by
            unfold tgtC; rw [if_neg (vnat_ne (by omega)), if_pos rfl, if_pos rfl]]
          exact ha
        · rw [if_neg (vnat_ne (by omega))]
          show l ∈ˢ app (X (tgtC (vnat 1) (vnat 1))) pt
          rw [show tgtC (vnat 1 : V) (vnat 1) = 2 from by
            unfold tgtC
            rw [if_neg (vnat_ne (by omega)), if_pos rfl, if_neg (vnat_ne (by omega))]]
          exact hl
      · show _ = mkC S 1 (vnat 1) _
        unfold mkC
        rw [if_neg (vnat_ne (by omega)), if_pos rfl,
          app_graph (mem_upair.mpr (Or.inl rfl)), app_graph (mem_upair.mpr (Or.inr rfl)),
          if_pos rfl, if_neg (vnat_ne (by omega))]
    | 2, _ =>
      rcases mem_blkFib_two.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
      · refine ⟨vnat 2, mem_upair.mpr (Or.inl rfl), graph (fun _ => pt) empty, ?_, ?_⟩
        · rw [posns_vnat]
          exact graph_mem_piSet fun p hp => absurd hp (not_mem_empty p)
        · show _ = mkC S 2 (vnat 2) _
          unfold mkC
          rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)), if_pos rfl]
      · refine ⟨vnat 3, mem_upair.mpr (Or.inr rfl),
          graph (fun p => if p = (vnat 0 : V) then h else t) (upair (vnat 0) (vnat 1)), ?_, ?_⟩
        · rw [posns_vnat]
          refine graph_mem_piSet fun p hp => ?_
          rcases mem_upair.mp hp with rfl | rfl
          · rw [if_pos rfl]
            show h ∈ˢ app (X (tgtC (vnat 3) (vnat 0))) pt
            rw [show tgtC (vnat 3 : V) (vnat 0) = 1 from by
              unfold tgtC
              rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)), if_pos rfl]]
            exact hh
          · rw [if_neg (vnat_ne (by omega))]
            show t ∈ˢ app (X (tgtC (vnat 3) (vnat 1))) pt
            rw [show tgtC (vnat 3 : V) (vnat 1) = 2 from by
              unfold tgtC
              rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
                if_neg (vnat_ne (by omega))]]
            exact ht
        · show _ = mkC S 2 (vnat 3) _
          unfold mkC
          rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
            if_neg (vnat_ne (by omega)),
            app_graph (mem_upair.mpr (Or.inl rfl)), app_graph (mem_upair.mpr (Or.inr rfl)),
            if_pos rfl, if_neg (vnat_ne (by omega))]

/-! ## The carrier -/

/-- The block's carrier tuple, three components. -/
noncomputable def car (S : P4Sig V) : Nat → V := lfpTuple S.w 3 uIs (blkΨ S)

/-- `⟦P4⟧` — and the group's PIN value. -/
noncomputable def carP (S : P4Sig V) : V := app (car S 0) pt

/-- The `Rose P4` component. -/
noncomputable def carR (S : P4Sig V) : V := app (car S 1) pt

/-- The `List (Rose P4)` component. -/
noncomputable def carL (S : P4Sig V) : V := app (car S 2) pt

theorem car_mem (S : P4Sig V) : InTupleSpace S.w 3 uIs (car S) := lfpTuple_mem _ _ _ _

/-- The pin's value lies in `Rose`'s `Sat` domain — `famSpace_app` at
the SAME level, the seed of the group's table. -/
theorem carP_mem_univ (S : P4Sig V) : carP S ∈ˢ (univ S.w : V) :=
  famSpace_app (car_mem S 0 (by omega)) pt_mem_unitSet

/-! ## (c) THE IDENTIFICATION: the whole segment is the container's WIDE table

One group, rank `0`, the segment `[1, 1 + N_Rose)` — ONE
`lfpTuple_seg_congr` at `s = 2`.  The SEEDING is entry `0` of the
agreement below: the section operator reads the pin's value `car 0`,
outside the segment, exactly where `RoseClause.fibre0` reads its
parameter `α`. -/

/-- The segment `[1, 3)`'s section operator agrees, on the whole
two-tuple space, with `Rose`'s own WIDE operator at the parameter
`⟦P4⟧`. -/
theorem segSec_eq_ΨR (hS : P4Ok S) {Y : Nat → V}
    (hY : InTupleSpace S.w 2 (fun i => uIs (1 + i)) Y) (i : Nat) (hi : i < 2) :
    blkΨ S (segJoin 1 2 (car S) Y) (1 + i) = S.ΨR (carP S) Y i := by
  have hY' : InTupleSpace S.w 2 uIs Y := hY
  have hZ : InTupleSpace S.w 3 uIs (segJoin 1 2 (car S) Y) :=
    inTupleSpace_segJoin (car_mem S) hY'
  have h0 : segJoin 1 2 (car S) Y 0 = car S 0 := segJoin_lt _ _ (by omega)
  have h1 : segJoin 1 2 (car S) Y 1 = Y 0 := segJoin_add (q := 0) _ _ (by omega)
  have h2 : segJoin 1 2 (car S) Y 2 = Y 1 := segJoin_add (q := 1) _ _ (by omega)
  match i, hi with
  | 0, _ =>
    refine famSpace_ext (blkΨ_maps hS _ hZ 1 (by omega))
      (hS.rose.maps (carP S) (carP_mem_univ S) Y hY' 0 (by omega)) ?_
    intro t ht
    obtain rfl := mem_unitSet_iff.mp ht
    apply SetTheory.ext
    intro x
    rw [app_blkΨ, mem_blkFib_one, h0, h2,
      hS.rose.fibre0 (carP S) (carP_mem_univ S) Y hY' pt pt_mem_unitSet x]
    exact Iff.rfl
  | 1, _ =>
    refine famSpace_ext (blkΨ_maps hS _ hZ 2 (by omega))
      (hS.rose.maps (carP S) (carP_mem_univ S) Y hY' 1 (by omega)) ?_
    intro t ht
    obtain rfl := mem_unitSet_iff.mp ht
    apply SetTheory.ext
    intro x
    rw [app_blkΨ, mem_blkFib_two, h1, h2,
      hS.rose.fibre1 (carP S) (carP_mem_univ S) Y hY' pt pt_mem_unitSet x]
    constructor
    · rintro (rfl | ⟨h, t, hh, ht, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨h, hh, t, ht, rfl⟩
    · rintro (rfl | ⟨h, hh, t, ht, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨h, t, hh, ht, rfl⟩

/-- **THE IDENTIFICATION, at the whole segment**: the group's two
components ARE `Rose`'s wide table at the pin's value, in one step.
No narrow clause of `Rose` is used — only its recorded wide table. -/
theorem car_seg_eq (hS : P4Ok S) {q : Nat} (hq : q < 2) :
    car S (1 + q) = lfpTuple S.w 2 uIs (S.ΨR (carP S)) q :=
  lfpTuple_seg_congr (blkΨ_closed hS) (blkΨ_mono S) (by omega) (fun _ _ => rfl)
    (fun Y hY i hi => segSec_eq_ΨR hS hY i hi) hq

/-- **`car 1 = ⟦Rose⟧ ⟦P4⟧`** — the member component of the group, by
the container's `leaf`.  This is the domain of `P4.mk`. -/
theorem car_one_eq (hS : P4Ok S) : car S 1 = S.ROSE (carP S) := by
  have h := car_seg_eq hS (q := 0) (by omega)
  rw [show (1 : Nat) + 0 = 1 from rfl] at h
  rw [h, ← hS.rose.leaf (carP S) (carP_mem_univ S)]

/-- **`car 2 = ⟦List⟧ ⟦Rose P4⟧`** — the INSTANCE component of the
group, by `RoseClause.instLeaf`, at a pin that mentions the
container's own member carrier (F2 FINDING (2)). -/
theorem car_two_eq (hS : P4Ok S) : car S 2 = S.LIST (app (S.ROSE (carP S)) pt) := by
  have h := car_seg_eq hS (q := 1) (by omega)
  rw [show (1 : Nat) + 1 = 2 from rfl] at h
  rw [h, hS.rose.instLeaf (carP S) (carP_mem_univ S)]

/-! ## (d) The fixed-point equations and the constructors' typing -/

theorem app_car_eq (hS : P4Ok S) {c : Nat} (hc : c < 3) :
    app (car S c) pt = blkFib S (car S) c := by
  rw [← app_blkΨ]
  exact (app_lfpTuple_eq (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS) hc
    (show (pt : V) ∈ˢ uIs c from pt_mem_unitSet)).symm

theorem carP_eq (hS : P4Ok S) : carP S = blkFib S (car S) 0 := app_car_eq hS (by omega)

theorem carR_eq (hS : P4Ok S) : carR S = blkFib S (car S) 1 := app_car_eq hS (by omega)

theorem carL_eq (hS : P4Ok S) : carL S = blkFib S (car S) 2 := app_car_eq hS (by omega)

theorem mem_carP (hS : P4Ok S) {x : V} :
    x ∈ˢ carP S ↔ ∃ r, r ∈ˢ carR S ∧ x = S.injP 0 [r] := by
  constructor
  · intro hx; rw [carP_eq hS] at hx; exact mem_blkFib_zero.mp hx
  · intro hx; rw [carP_eq hS]; exact mem_blkFib_zero.mpr hx

theorem mem_carR (hS : P4Ok S) {x : V} :
    x ∈ˢ carR S ↔ ∃ a, a ∈ˢ carP S ∧ ∃ l, l ∈ˢ carL S ∧ x = S.injR 0 [a, l] := by
  constructor
  · intro hx; rw [carR_eq hS] at hx; exact mem_blkFib_one.mp hx
  · intro hx; rw [carR_eq hS]; exact mem_blkFib_one.mpr hx

theorem mem_carL (hS : P4Ok S) {x : V} :
    x ∈ˢ carL S ↔
      x = S.injL 0 [] ∨ ∃ h t, h ∈ˢ carR S ∧ t ∈ˢ carL S ∧ x = S.injL 1 [h, t] := by
  constructor
  · intro hx; rw [carL_eq hS] at hx; exact mem_blkFib_two.mp hx
  · intro hx; rw [carL_eq hS]; exact mem_blkFib_two.mpr hx

/-- **`P4.mk`'s typing, with its domain read ORDINARILY.**  `r` is a
value of `⟦Rose⟧ ⟦P4⟧` — the reading the checker produces for
`P4.mk : Rose P4 → P4` — and `mk r` is a value of the member. -/
theorem mk_mem_carP (hS : P4Ok S) {r : V} (hr : r ∈ˢ app (S.ROSE (carP S)) pt) :
    S.injP 0 [r] ∈ˢ carP S :=
  (mem_carP hS).mpr ⟨r, by unfold carR; rw [car_one_eq hS]; exact hr, rfl⟩

/-- `Rose.node`'s value, read ordinarily at the pin `P4`: its label is
a value of the MEMBER and its children a value of the group's instance
component. -/
theorem node_mem_carR (hS : P4Ok S) {a l : V} (ha : a ∈ˢ carP S) (hl : l ∈ˢ carL S) :
    S.injR 0 [a, l] ∈ˢ carR S := (mem_carR hS).mpr ⟨a, ha, l, hl, rfl⟩

/-- `List.cons`'s value at the pin `Rose P4`, read ordinarily. -/
theorem cons_mem_carL (hS : P4Ok S) {h t : V} (hh : h ∈ˢ carR S) (ht : t ∈ˢ carL S) :
    S.injL 1 [h, t] ∈ˢ carL S := (mem_carL hS).mpr (Or.inr ⟨h, t, hh, ht, rfl⟩)

/-! ## (e) The recursor: `UnionRecKit` at THREE components

The crossing rules are `Rose.node`'s — label to the MEMBER, children
to the group's instance component — and `List.cons`'s at the pin
`Rose P4` (head to the group's member component). -/

section Rec

/-- The motives and the minors, bundled. -/
structure RecData (V : Type u) [SetTheory V] where
  /-- The three motives, by component. -/
  M : Nat → V → V
  /-- `P4.mk`'s minor. -/
  mkP : V → V → V
  /-- `Rose.node`'s minor. -/
  node : V → V → V → V → V
  /-- `List.nil`'s minor at the pin `Rose P4`. -/
  nil : V
  /-- `List.cons`'s minor at the pin `Rose P4`. -/
  cons : V → V → V → V → V

variable {ℓ : Nat} {R : RecData V}

/-- The minors' typing hypotheses. -/
structure RecOk (S : P4Sig V) (ℓ : Nat) (R : RecData V) : Prop where
  /-- The motives take values in `univ ℓ`. -/
  motive : ∀ c, c < 3 → ∀ x, x ∈ˢ app (car S c) pt → R.M c x ∈ˢ (univ ℓ : V)
  /-- `P4.mk`. -/
  mkP : ∀ r ih, r ∈ˢ carR S → ih ∈ˢ R.M 1 r → R.mkP r ih ∈ˢ R.M 0 (S.injP 0 [r])
  /-- `Rose.node`. -/
  node : ∀ a l ih₁ ih₂, a ∈ˢ carP S → l ∈ˢ carL S → ih₁ ∈ˢ R.M 0 a → ih₂ ∈ˢ R.M 2 l →
    R.node a l ih₁ ih₂ ∈ˢ R.M 1 (S.injR 0 [a, l])
  /-- `List.nil`. -/
  nil : R.nil ∈ˢ R.M 2 (S.injL 0 [])
  /-- `List.cons`. -/
  cons : ∀ h t ih₁ ih₂, h ∈ˢ carR S → t ∈ˢ carL S → ih₁ ∈ˢ R.M 1 h → ih₂ ∈ˢ R.M 2 t →
    R.cons h t ih₁ ih₂ ∈ˢ R.M 2 (S.injL 1 [h, t])

/-- The index set of the recursion. -/
noncomputable def blkIdx (S : P4Sig V) : V := unionSet 3 uIs (car S)

theorem tagged_mem_blkIdx {c : Nat} (hc : c < 3) {x : V} (hx : x ∈ˢ app (car S c) pt) :
    tagged c pt x ∈ˢ blkIdx S := tagged_mem_unionSet hc pt_mem_unitSet hx

theorem mem_blkIdx {u : V} :
    u ∈ˢ blkIdx S ↔ ∃ c, c < 3 ∧ ∃ x, x ∈ˢ app (car S c) pt ∧ u = tagged c pt x := by
  unfold blkIdx
  rw [mem_unionSet]
  constructor
  · rintro ⟨c, hc, i, hi, x, hx, rfl⟩
    obtain rfl := mem_unitSet_iff.mp hi
    exact ⟨c, hc, x, hx, rfl⟩
  · rintro ⟨c, hc, x, hx, rfl⟩
    exact ⟨c, hc, pt, pt_mem_unitSet, x, hx, rfl⟩

/-- The predecessor relation, read off the four constructors. -/
def BlkRel (S : P4Sig V) (u v : V) : Prop :=
  (∃ r, u = tagged 0 pt (S.injP 0 [r]) ∧ v = tagged 1 pt r) ∨
  (∃ a l, u = tagged 1 pt (S.injR 0 [a, l]) ∧ (v = tagged 0 pt a ∨ v = tagged 2 pt l)) ∨
  (∃ h t, u = tagged 2 pt (S.injL 1 [h, t]) ∧ (v = tagged 1 pt h ∨ v = tagged 2 pt t))

/-- The predecessor sets. -/
noncomputable def blkPred (S : P4Sig V) (u : V) : V := relPred (blkIdx S) (BlkRel S) u

theorem blkPred_subset (S : P4Sig V) (u : V) : blkPred S u ⊆ˢ blkIdx S := relPred_subset _ _ u

theorem mem_blkPred {u v : V} : v ∈ˢ blkPred S u ↔ v ∈ˢ blkIdx S ∧ BlkRel S u v := mem_relPred

section Decompose

variable (hS : P4Ok S) (hw : S.w ≠ 0)

include hS hw

theorem mem_blkPred_mkP {r v : V} :
    v ∈ˢ blkPred S (tagged 0 pt (S.injP 0 [r])) ↔ v ∈ˢ blkIdx S ∧ v = tagged 1 pt r := by
  rw [mem_blkPred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inl ⟨r, rfl, h⟩⟩
  rcases h with ⟨r', h₁, h₂⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
  · rw [h₂, hS.mem.mkInj hw r r' (tagged_inj h₁).2.2]
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)

theorem mem_blkPred_node {a l v : V} :
    v ∈ˢ blkPred S (tagged 1 pt (S.injR 0 [a, l])) ↔
      v ∈ˢ blkIdx S ∧ (v = tagged 0 pt a ∨ v = tagged 2 pt l) := by
  rw [mem_blkPred]
  refine and_congr_right fun _ => ⟨fun hv => ?_, fun hv => Or.inr (Or.inl ⟨a, l, rfl, hv⟩)⟩
  rcases hv with ⟨_, h₁, -⟩ | ⟨a', l', h₁, h₂⟩ | ⟨_, _, h₁, -⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · obtain ⟨-, he⟩ := hS.rose.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
    obtain ⟨rfl, he'⟩ := List.cons.inj he
    obtain ⟨rfl, -⟩ := List.cons.inj he'
    exact h₂
  · exact absurd (tagged_inj h₁).1 (by omega)

theorem not_mem_blkPred_nil {v : V} : ¬ v ∈ˢ blkPred S (tagged 2 pt (S.injL 0 [])) := by
  intro h
  rcases (mem_blkPred.mp h).2 with ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2).1 (by omega)

theorem mem_blkPred_cons {h t v : V} :
    v ∈ˢ blkPred S (tagged 2 pt (S.injL 1 [h, t])) ↔
      v ∈ˢ blkIdx S ∧ (v = tagged 1 pt h ∨ v = tagged 2 pt t) := by
  rw [mem_blkPred]
  refine and_congr_right fun _ => ⟨fun hv => ?_, fun hv => Or.inr (Or.inr ⟨h, t, rfl, hv⟩)⟩
  rcases hv with ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨h', t', h₁, h₂⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)
  · obtain ⟨-, he⟩ := hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
    obtain ⟨rfl, he'⟩ := List.cons.inj he
    obtain ⟨rfl, -⟩ := List.cons.inj he'
    exact h₂

/-- **The predecessors come from the argument tuple.** -/
theorem blkPred_predsFrom : PredsFrom S.w 3 uIs (blkΨ S) (blkPred S) := by
  intro X hX hXle c hc i hi x hx v hv
  obtain rfl := mem_unitSet_iff.mp hi
  obtain ⟨-, hrel⟩ := mem_relPred.mp hv
  rw [app_blkΨ] at hx
  match c, hc with
  | 0, _ =>
    obtain ⟨r, hr, rfl⟩ := mem_blkFib_zero.mp hx
    rcases hrel with ⟨r', h₁, rfl⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
    · obtain rfl := hS.mem.mkInj hw r r' (tagged_inj h₁).2.2
      exact tagged_mem_unionSet (by omega) pt_mem_unitSet hr
    · exact absurd (tagged_inj h₁).1 (by omega)
    · exact absurd (tagged_inj h₁).1 (by omega)
  | 1, _ =>
    obtain ⟨a, ha, l, hl, rfl⟩ := mem_blkFib_one.mp hx
    rcases hrel with ⟨_, h₁, -⟩ | ⟨a', l', h₁, h₂⟩ | ⟨_, _, h₁, -⟩
    · exact absurd (tagged_inj h₁).1 (by omega)
    · obtain ⟨-, he⟩ := hS.rose.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
      obtain ⟨rfl, he'⟩ := List.cons.inj he
      obtain ⟨rfl, -⟩ := List.cons.inj he'
      rcases h₂ with rfl | rfl
      · exact tagged_mem_unionSet (by omega) pt_mem_unitSet ha
      · exact tagged_mem_unionSet (by omega) pt_mem_unitSet hl
    · exact absurd (tagged_inj h₁).1 (by omega)
  | 2, _ =>
    rcases mem_blkFib_two.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · rcases hrel with ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
      · exact absurd (tagged_inj h₁).1 (by omega)
      · exact absurd (tagged_inj h₁).1 (by omega)
      · exact absurd (hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2).1 (by omega)
    · rcases hrel with ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨h', t', h₁, h₂⟩
      · exact absurd (tagged_inj h₁).1 (by omega)
      · exact absurd (tagged_inj h₁).1 (by omega)
      · obtain ⟨-, he⟩ := hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
        obtain ⟨rfl, he'⟩ := List.cons.inj he
        obtain ⟨rfl, -⟩ := List.cons.inj he'
        rcases h₂ with rfl | rfl
        · exact tagged_mem_unionSet (by omega) pt_mem_unitSet hh
        · exact tagged_mem_unionSet (by omega) pt_mem_unitSet ht

end Decompose

/-! ### The bound and the step -/

/-- The bound: the motive of the value's component, at the value. -/
noncomputable def blkB (M : Nat → V → V) (u : V) : V :=
  natFibre (fun c => M c (ssnd (ssnd u))) (sfst u)

theorem blkB_at (M : Nat → V → V) (c : Nat) (x : V) : blkB M (tagged c pt x) = M c x := by
  unfold blkB tagged
  rw [sfst_kpair, ssnd_kpair, ssnd_kpair, natFibre_vnat]

open Classical in
/-- The step: the minors at the predecessors' recursive values. -/
noncomputable def blkSt (S : P4Sig V) (R : RecData V) (u g : V) : V :=
  if h : ∃ r, u = tagged 0 pt (S.injP 0 [r]) then
    R.mkP h.choose (app g (tagged 1 pt h.choose))
  else if h : ∃ q : V × V, u = tagged 1 pt (S.injR 0 [q.1, q.2]) then
    R.node h.choose.1 h.choose.2 (app g (tagged 0 pt h.choose.1))
      (app g (tagged 2 pt h.choose.2))
  else if u = tagged 2 pt (S.injL 0 []) then R.nil
  else if h : ∃ q : V × V, u = tagged 2 pt (S.injL 1 [q.1, q.2]) then
    R.cons h.choose.1 h.choose.2 (app g (tagged 1 pt h.choose.1))
      (app g (tagged 2 pt h.choose.2))
  else empty

section StEq

variable (hS : P4Ok S) (hw : S.w ≠ 0)

include hS hw

theorem blkSt_mkP (r g : V) :
    blkSt S R (tagged 0 pt (S.injP 0 [r])) g = R.mkP r (app g (tagged 1 pt r)) := by
  unfold blkSt
  rw [dif_pos ⟨r, rfl⟩]
  have h := Exists.choose_spec
    (⟨r, rfl⟩ : ∃ y, (tagged 0 pt (S.injP 0 [r]) : V) = tagged 0 pt (S.injP 0 [y]))
  rw [← hS.mem.mkInj hw _ _ (tagged_inj h).2.2]

theorem blkSt_node (a l g : V) :
    blkSt S R (tagged 1 pt (S.injR 0 [a, l])) g
      = R.node a l (app g (tagged 0 pt a)) (app g (tagged 2 pt l)) := by
  unfold blkSt
  rw [dif_neg (fun ⟨_, h⟩ => by exact absurd (tagged_inj h).1 (by omega)),
    dif_pos ⟨(a, l), rfl⟩]
  have hs := Exists.choose_spec
    (⟨(a, l), rfl⟩ :
      ∃ q : V × V, (tagged 1 pt (S.injR 0 [a, l]) : V) = tagged 1 pt (S.injR 0 [q.1, q.2]))
  obtain ⟨-, he⟩ := hS.rose.mkInj hw _ _ _ _ (tagged_inj hs).2.2
  obtain ⟨h₁, he'⟩ := List.cons.inj he
  obtain ⟨h₂, -⟩ := List.cons.inj he'
  rw [← h₁, ← h₂]

omit hS hw in
theorem blkSt_nil (g : V) : blkSt S R (tagged 2 pt (S.injL 0 [])) g = R.nil := by
  unfold blkSt
  rw [dif_neg (fun ⟨_, h⟩ => by exact absurd (tagged_inj h).1 (by omega)),
    dif_neg (fun ⟨_, h⟩ => by exact absurd (tagged_inj h).1 (by omega)), if_pos rfl]

theorem blkSt_cons (h t g : V) :
    blkSt S R (tagged 2 pt (S.injL 1 [h, t])) g
      = R.cons h t (app g (tagged 1 pt h)) (app g (tagged 2 pt t)) := by
  unfold blkSt
  rw [dif_neg (fun ⟨_, h'⟩ => by exact absurd (tagged_inj h').1 (by omega)),
    dif_neg (fun ⟨_, h'⟩ => by exact absurd (tagged_inj h').1 (by omega)),
    if_neg (fun h' => absurd (hS.list.mkInj hw _ _ _ _ (tagged_inj h').2.2).1 (by omega)),
    dif_pos ⟨(h, t), rfl⟩]
  have hs := Exists.choose_spec
    (⟨(h, t), rfl⟩ :
      ∃ q : V × V, (tagged 2 pt (S.injL 1 [h, t]) : V) = tagged 2 pt (S.injL 1 [q.1, q.2]))
  obtain ⟨-, he⟩ := hS.list.mkInj hw _ _ _ _ (tagged_inj hs).2.2
  obtain ⟨h₁, he'⟩ := List.cons.inj he
  obtain ⟨h₂, -⟩ := List.cons.inj he'
  rw [← h₁, ← h₂]

end StEq

/-! ### The kit -/

section Kit

variable (hS : P4Ok S) (hw : S.w ≠ 0) (hR : RecOk S ℓ R)

include hR in
theorem blkB_mem_univ : ∀ u, u ∈ˢ blkIdx S → blkB R.M u ∈ˢ (univ ℓ : V) := by
  intro u hu
  obtain ⟨c, hc, x, hx, rfl⟩ := mem_blkIdx.mp hu
  rw [blkB_at]
  exact hR.motive c hc x hx

include hR in
theorem blkGraph_mem_B {u v : V} (hu : u ∈ˢ blkIdx S)
    (hv : v ∈ˢ app (recGraph ℓ (blkIdx S) (blkPred S) (blkB R.M) (blkSt S R)) u) :
    v ∈ˢ blkB R.M u := by
  rw [app_recGraph_eq (blkB_mem_univ hR) (fun u _ => blkPred_subset S u) hu] at hv
  exact (mem_recGraphFibre.mp hv).1

include hS hw hR in
/-- **The step is typed** — from the minors' typing alone. -/
theorem blkSt_mem : ∀ u, u ∈ˢ blkIdx S → ∀ g,
    g ∈ˢ piSet (blkPred S u)
      (fun j => app (recGraph ℓ (blkIdx S) (blkPred S) (blkB R.M) (blkSt S R)) j) →
    blkSt S R u g ∈ˢ blkB R.M u := by
  intro u hu g hg
  have hval : ∀ v, v ∈ˢ blkPred S u → app g v ∈ˢ blkB R.M v := fun v hv =>
    blkGraph_mem_B hR (blkPred_subset S u v hv) (app_mem_of_mem_piSet hg hv)
  obtain ⟨c, hc, x, hx, rfl⟩ := mem_blkIdx.mp hu
  match c, hc with
  | 0, _ =>
    obtain ⟨r, hr, rfl⟩ := (mem_carP hS).mp hx
    rw [blkSt_mkP hS hw, blkB_at]
    have h := hval (tagged 1 pt r)
      ((mem_blkPred_mkP hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hr, rfl⟩)
    rw [blkB_at] at h
    exact hR.mkP r _ hr h
  | 1, _ =>
    obtain ⟨a, ha, l, hl, rfl⟩ := (mem_carR hS).mp hx
    rw [blkSt_node hS hw, blkB_at]
    have h₁ := hval (tagged 0 pt a)
      ((mem_blkPred_node hS hw).mpr ⟨tagged_mem_blkIdx (by omega) ha, Or.inl rfl⟩)
    have h₂ := hval (tagged 2 pt l)
      ((mem_blkPred_node hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hl, Or.inr rfl⟩)
    rw [blkB_at] at h₁ h₂
    exact hR.node a l _ _ ha hl h₁ h₂
  | 2, _ =>
    rcases (mem_carL hS).mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · rw [blkSt_nil, blkB_at]; exact hR.nil
    · rw [blkSt_cons hS hw, blkB_at]
      have h₁ := hval (tagged 1 pt h)
        ((mem_blkPred_cons hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hh, Or.inl rfl⟩)
      have h₂ := hval (tagged 2 pt t)
        ((mem_blkPred_cons hS hw).mpr ⟨tagged_mem_blkIdx (by omega) ht, Or.inr rfl⟩)
      rw [blkB_at] at h₁ h₂
      exact hR.cons h t _ _ hh ht h₁ h₂

/-- **The block's recursion kit** at `N = 3` components. -/
noncomputable def blkKit : UnionRecKit ℓ S.w 3 uIs (blkΨ S) :=
  ⟨blkPred S, blkB R.M, blkSt S R, blkPred_predsFrom hS hw, blkB_mem_univ hR,
    blkSt_mem hS hw hR⟩

local notation "K*" => blkKit hS hw hR

@[simp] theorem blkKit_pred : (K*).pred = blkPred S := rfl
@[simp] theorem blkKit_B : (K*).B = blkB R.M := rfl
@[simp] theorem blkKit_st : (K*).st = blkSt S R := rfl

theorem blkKit_recAt (c : Nat) (i x : V) :
    (K*).recAt c i x
      = recSel (recGraph ℓ (blkIdx S) (blkPred S) (blkB R.M) (blkSt S R)) (tagged c i x) := rfl

/-- The recursor at a component: `P4.rec` at `0`, `P4.rec_1`/`P4.rec_2`
at `1`/`2`. -/
noncomputable def recAt (c : Nat) (x : V) : V := (blkKit hS hw hR).recAt c pt x

include hS hw hR in
/-- **Typing**: the recursor's value is in the component's motive. -/
theorem recAt_mem {c : Nat} (hc : c < 3) {x : V} (hx : x ∈ˢ app (car S c) pt) :
    recAt hS hw hR c x ∈ˢ R.M c x := by
  have h := (K*).rec_mem_B (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS) hc
    (show (pt : V) ∈ˢ uIs c from pt_mem_unitSet) hx
  rw [blkKit_B, blkB_at] at h
  exact h

include hS hw hR in
theorem blkRec_eq {c : Nat} (hc : c < 3) {x : V} (hx : x ∈ˢ app (car S c) pt) :
    (K*).recAt c pt x
      = blkSt S R (tagged c pt x)
          (graph (fun j => recSel (recGraph ℓ (blkIdx S) (blkPred S) (blkB R.M) (blkSt S R)) j)
            (blkPred S (tagged c pt x))) :=
  (K*).rec_eq (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS) hc
    (show (pt : V) ∈ˢ uIs c from pt_mem_unitSet) hx

/-! ### The ι rules -/

include hS hw hR in
/-- ι 1 — `P4.rec … (P4.mk r) = mkP r (P4.rec_1 … r)`. -/
theorem rec_mkP {r : V} (hr : r ∈ˢ carR S) :
    recAt hS hw hR 0 (S.injP 0 [r]) = R.mkP r (recAt hS hw hR 1 r) := by
  show (K*).recAt 0 pt (S.injP 0 [r]) = R.mkP r ((K*).recAt 1 pt r)
  rw [blkRec_eq hS hw hR (show (0:Nat) < 3 by omega) ((mem_carP hS).mpr ⟨r, hr, rfl⟩),
    blkSt_mkP hS hw,
    app_graph ((mem_blkPred_mkP hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hr, rfl⟩),
    blkKit_recAt]

include hS hw hR in
/-- ι 2 — `P4.rec_1 … (Rose.node a l) = node a l (P4.rec … a) (P4.rec_2 … l)`:
**the crossing rule of the seeded group** — the label's minor
recurses at the MEMBER (the pin), the children's at the group's
instance component. -/
theorem rec_node {a l : V} (ha : a ∈ˢ carP S) (hl : l ∈ˢ carL S) :
    recAt hS hw hR 1 (S.injR 0 [a, l])
      = R.node a l (recAt hS hw hR 0 a) (recAt hS hw hR 2 l) := by
  show (K*).recAt 1 pt (S.injR 0 [a, l])
    = R.node a l ((K*).recAt 0 pt a) ((K*).recAt 2 pt l)
  rw [blkRec_eq hS hw hR (show (1:Nat) < 3 by omega)
      ((mem_carR hS).mpr ⟨a, ha, l, hl, rfl⟩),
    blkSt_node hS hw,
    app_graph ((mem_blkPred_node hS hw).mpr ⟨tagged_mem_blkIdx (by omega) ha, Or.inl rfl⟩),
    app_graph ((mem_blkPred_node hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hl, Or.inr rfl⟩),
    blkKit_recAt, blkKit_recAt]

include hS hw hR in
/-- ι 3 — `P4.rec_2 … nil = nil`. -/
theorem rec_nil : recAt hS hw hR 2 (S.injL 0 []) = R.nil := by
  show (K*).recAt 2 pt (S.injL 0 []) = R.nil
  rw [blkRec_eq hS hw hR (show (2:Nat) < 3 by omega) ((mem_carL hS).mpr (Or.inl rfl)),
    blkSt_nil]

include hS hw hR in
/-- ι 4 — `P4.rec_2 … (List.cons h t) = cons h t (P4.rec_1 … h) (P4.rec_2 … t)`:
`List.cons` at the pin `Rose P4`, the inner container's rule, whose
head crosses to the group's member component. -/
theorem rec_cons {h t : V} (hh : h ∈ˢ carR S) (ht : t ∈ˢ carL S) :
    recAt hS hw hR 2 (S.injL 1 [h, t])
      = R.cons h t (recAt hS hw hR 1 h) (recAt hS hw hR 2 t) := by
  show (K*).recAt 2 pt (S.injL 1 [h, t])
    = R.cons h t ((K*).recAt 1 pt h) ((K*).recAt 2 pt t)
  rw [blkRec_eq hS hw hR (show (2:Nat) < 3 by omega)
      ((mem_carL hS).mpr (Or.inr ⟨h, t, hh, ht, rfl⟩)),
    blkSt_cons hS hw,
    app_graph ((mem_blkPred_cons hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hh, Or.inl rfl⟩),
    app_graph ((mem_blkPred_cons hS hw).mpr ⟨tagged_mem_blkIdx (by omega) ht, Or.inr rfl⟩),
    blkKit_recAt, blkKit_recAt]

end Kit

end Rec

/-! ## What the clause must record (the F2 record)

**PASS.**  The seeded group needs the container's WIDE table and
nothing narrow: `car_seg_eq` identifies the whole segment `[1, 3)`
with `lfpTuple w 2 uIs (ΨR ⟦P4⟧)` in one `lfpTuple_seg_congr`, with
`RoseClause`'s `functor`/`fibre0`/`fibre1` as the only container
input; `car_one_eq`/`car_two_eq` then read it off `leaf`/`instLeaf`.
No form of "`⟦Rose α⟧` as a least fixed point in `α`" occurs, and no
clamp, `composeΦ`, `pinsCar` or class accessibility.

Two clauses beyond the letter of §1.2 were needed, both about an
INSTANCE component of the container's own table:

1. **(F2-1) = (F1-1): its injections must be recorded.**  §1.2's
   `ctor` clause is members-only, so component `2`'s tags — `List`'s
   — are tied to nothing, and `rec_cons` (the ι rule of the recursor
   official emits for that component) cannot be stated.  Here the tie
   is `RoseClause`'s `injL` argument, shared with `ListClause`.

2. **(F2-2) its recorded READING is at pins that mention the
   container's OWN carriers.**  Component `1` of `Rose`'s table has
   the key `List (Rose α)`, so the recorded reading is
   `LIST (app (ROSE α) pt)` — `⟦Ds⟧^ord` of §2.4 is a recursion over
   the container's own table, not a substitution of the container's
   parameters alone.  `BlockModelAt` must record per instance
   component the key AND the frame in which its pins are read; F1's
   `instLeaf` (`LIST α`) is the degenerate case that hides this.

3. **(F2-3, a confirmation) the seeding costs nothing.**  The pin's
   value enters the segment's section only through
   `segJoin_lt`/`segJoin_out` — the components outside the segment are
   held at the carrier — and `RoseClause.fibre0` consumes it as its
   parameter `α`.  The only fact needed of the pin is
   `carP_mem_univ` (`famSpace_app`, three lines): a group whose pin is
   the member needs NO identification of its own, which is why it has
   rank `0`. -/

/-! ## Non-vacuity: `RoseClause` has a model

`RoseClause` carries the two fields §1.2 does not (`fibre1` at the
inner container's tags, and the self-referential `instLeaf`), so it
must be shown satisfiable — otherwise F2's identification would be
vacuous and its finding empty.  This section builds the standard
reading of `Rose α ::= node α (List (Rose α))` with F0's own
`stdInj`/`stdΨL`/`stdLIST` for the inner container, so that
`stdListClause` applies verbatim and both clauses hold at the SAME
tags. -/

section StdRose

/-- `Rose`'s own WIDE operator at a parameter: component `0` is the
`node` arm with the labels in the PARAMETER and the children at
component `1`; component `1` is the `nil`/`cons` arm whose heads are
at component `0` — the nesting inside the container. -/
noncomputable def stdΨR (w : Nat) (α : V) (Y : Nat → V) : Nat → V
  | 0 => graph (fun _ => nodeArm (stdInj w) α (app (Y 1) pt)) unitSet
  | _ => graph (fun _ => consArm (stdInj w) (app (Y 0) pt) (app (Y 1) pt)) unitSet

theorem app_stdΨR_zero (w : Nat) (α : V) (Y : Nat → V) :
    app (stdΨR w α Y 0) pt = nodeArm (stdInj w) α (app (Y 1) pt) := app_graph pt_mem_unitSet

theorem app_stdΨR_one (w : Nat) (α : V) (Y : Nat → V) :
    app (stdΨR w α Y 1) pt = consArm (stdInj w) (app (Y 0) pt) (app (Y 1) pt) :=
  app_graph pt_mem_unitSet

/-- `⟦Rose α⟧`, the member's component of the wide table. -/
noncomputable def stdROSE (w : Nat) (α : V) : V := lfpTuple w 2 uIs (stdΨR w α) 0

theorem stdΨR_mono (w : Nat) (α : V) : MonoTuple w 2 uIs (stdΨR w α) := by
  intro X Y hX hY hle c hc i hi x hx
  obtain rfl := mem_unitSet_iff.mp hi
  match c, hc with
  | 0, _ =>
    rw [app_stdΨR_zero] at hx ⊢
    obtain ⟨a, ha, l, hl, rfl⟩ := mem_nodeArm.mp hx
    exact mem_nodeArm.mpr ⟨a, ha, l, hle 1 (by omega) pt pt_mem_unitSet l hl, rfl⟩
  | 1, _ =>
    rw [app_stdΨR_one] at hx ⊢
    rcases mem_consArm.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · exact mem_consArm.mpr (Or.inl rfl)
    · exact mem_consArm.mpr (Or.inr ⟨h, t, hle 0 (by omega) pt pt_mem_unitSet h hh,
        hle 1 (by omega) pt pt_mem_unitSet t ht, rfl⟩)

theorem stdInj_two_mem_univ {w : Nat} (hw : w ≠ 0) (j : Nat) {a b : V}
    (ha : a ∈ˢ (univ w : V)) (hb : b ∈ˢ (univ w : V)) : stdInj w j [a, b] ∈ˢ (univ w : V) := by
  refine stdInj_mem_univ hw ?_
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact hb
    · exact absurd hx List.not_mem_nil

theorem stdΨR_maps {w : Nat} {α : V} (hα : α ∈ˢ (univ w : V)) : MapsTuple w 2 uIs (stdΨR w α) := by
  intro Y hY c hc
  have hY0 : app (Y 0) pt ∈ˢ (univ w : V) := famSpace_app (hY 0 (by omega)) pt_mem_unitSet
  have hY1 : app (Y 1) pt ∈ˢ (univ w : V) := famSpace_app (hY 1 (by omega)) pt_mem_unitSet
  by_cases hw : w = 0
  · subst hw
    match c, hc with
    | 0, _ =>
      refine graph_mem_famSpace fun i hi => ?_
      rw [univ_zero]
      refine mem_univZero.mpr fun x hx => ?_
      obtain ⟨a, -, l, -, rfl⟩ := mem_nodeArm.mp hx
      rw [stdInj_zero]; exact pt_mem_unitSet
    | 1, _ =>
      refine graph_mem_famSpace fun i hi => ?_
      rw [univ_zero]
      refine mem_univZero.mpr fun x hx => ?_
      rcases mem_consArm.mp hx with rfl | ⟨h, t, -, -, rfl⟩
      · rw [stdInj_zero]; exact pt_mem_unitSet
      · rw [stdInj_zero]; exact pt_mem_unitSet
  · match c, hc with
    | 0, _ =>
      exact graph_mem_famSpace fun _ _ =>
        nodeArm_mem_univ hw hα hY1 fun _ _ ha hl => stdInj_two_mem_univ hw 0 ha hl
    | 1, _ =>
      exact graph_mem_famSpace fun _ _ =>
        consArm_mem_univ hw hY0 hY1 (stdInj_mem_univ hw (by simp))
          fun _ _ hh ht => stdInj_two_mem_univ hw 1 hh ht

/-! ### (W) for `Rose`'s wide table

Shapes `⟨0, a⟩ = node` at the label `a` (a HOLE-FREE entry, so it
lives in the SHAPE), `⟨1, pt⟩ = nil`, `⟨2, pt⟩ = cons` — `cons`'s head
is a SLOT here (it targets component `0`), not shape data. -/

/-- The shapes, per component. -/
noncomputable def rShapes (α : V) : Nat → V → V
  | 0, _ => image (fun a => kpair (vnat 0) a) α
  | _, _ => upair (kpair (vnat 1) pt) (kpair (vnat 2) pt)

/-- The positions of a shape. -/
noncomputable def rPos (a : V) : V :=
  natFibre (fun j => if j = 0 then sing (vnat 0) else if j = 1 then empty
    else upair (vnat 0) (vnat 1)) (sfst a)

theorem rPos_node (a : V) : rPos (kpair (vnat 0) a) = sing (vnat 0) := by
  unfold rPos; rw [sfst_kpair, natFibre_vnat, if_pos rfl]

theorem rPos_nil : rPos (kpair (vnat 1) pt : V) = empty := by
  unfold rPos; rw [sfst_kpair, natFibre_vnat, if_neg (by omega), if_pos rfl]

theorem rPos_cons : rPos (kpair (vnat 2) pt : V) = upair (vnat 0) (vnat 1) := by
  unfold rPos; rw [sfst_kpair, natFibre_vnat, if_neg (by omega), if_neg (by omega)]

open Classical in
/-- The target of a slot: `node`'s child and `cons`'s tail go to
component `1`, `cons`'s head to component `0`. -/
noncomputable def rTgt (a p : V) : Nat :=
  if sfst a = (vnat 2 : V) then (if p = (vnat 0 : V) then 0 else 1) else 1

theorem rTgt_node (a p : V) : rTgt (kpair (vnat 0) a) p = 1 := by
  unfold rTgt; rw [sfst_kpair, if_neg (vnat_ne (by omega))]

theorem rTgt_cons_head : rTgt (kpair (vnat 2) pt : V) (vnat 0) = 0 := by
  unfold rTgt; rw [sfst_kpair, if_pos rfl, if_pos rfl]

theorem rTgt_cons_tail : rTgt (kpair (vnat 2) pt : V) (vnat 1) = 1 := by
  unfold rTgt; rw [sfst_kpair, if_pos rfl, if_neg (vnat_ne (by omega))]

/-- The builder: `node`'s label comes from the SHAPE. -/
noncomputable def rMk (w : Nat) (_m : Nat) (a g : V) : V :=
  natFibre (fun j => if j = 0 then stdInj w 0 [ssnd a, app g (vnat 0)]
    else if j = 1 then stdInj w 0 []
    else stdInj w 1 [app g (vnat 0), app g (vnat 1)]) (sfst a)

theorem rMk_node (w m : Nat) (a g : V) :
    rMk w m (kpair (vnat 0) a) g = stdInj (V := V) w 0 [a, app g (vnat 0)] := by
  unfold rMk; rw [sfst_kpair, natFibre_vnat, if_pos rfl, ssnd_kpair]

theorem rMk_nil (w m : Nat) (g : V) : rMk w m (kpair (vnat 1) pt) g = stdInj (V := V) w 0 [] := by
  unfold rMk; rw [sfst_kpair, natFibre_vnat, if_neg (by omega), if_pos rfl]

theorem rMk_cons (w m : Nat) (g : V) :
    rMk w m (kpair (vnat 2) pt) g = stdInj (V := V) w 1 [app g (vnat 0), app g (vnat 1)] := by
  unfold rMk; rw [sfst_kpair, natFibre_vnat, if_neg (by omega), if_neg (by omega)]

open Classical in
theorem stdΨR_closed {w : Nat} {α : V} (hα : α ∈ˢ (univ w : V)) :
    ∃ L, IsClosedTuple w 2 uIs (stdΨR w α) L := by
  by_cases hw : w = 0
  · rw [hw]; exact closedTuple_zero (hw ▸ stdΨR_maps hα)
  have hU := univ_isTGUniverse (V := V) hw
  have hv : ∀ j : Nat, (vnat j : V) ∈ˢ (univ w : V) := fun j => vnat_mem_univ_pos hw j
  have hsh : ∀ j : Nat, ∀ x, x ∈ˢ (univ w : V) → (kpair (vnat j) x : V) ∈ˢ (univ w : V) :=
    fun j x hx => hU.kpair_mem hx (hv j) hx
  refine tupleContainer_closed_exists hw (Is := uIs) (stdΨR w α) (rShapes α) rPos rTgt
    (fun _ _ => pt) (rMk w) ?hA ?hB ?htgt ?hmkU ?helim
  case hA =>
    intro m hm i hi
    match m, hm with
    | 0, _ =>
      show image _ α ∈ˢ (univ w : V)
      exact hU.image_mem hα fun a ha => hsh 0 a (hU.transitive hα ha)
    | 1, _ =>
      show upair _ _ ∈ˢ (univ w : V)
      exact hU.upair_mem (hsh 1 pt (pt_mem_univ hw)) (hsh 1 pt (pt_mem_univ hw))
        (hsh 2 pt (pt_mem_univ hw))
  case hB =>
    intro m hm i a hi ha
    match m, hm with
    | 0, _ =>
      obtain ⟨b, -, rfl⟩ := mem_image.mp (show a ∈ˢ image _ α from ha)
      rw [rPos_node]; exact hU.sing_mem (hv 0) (hv 0)
    | 1, _ =>
      rcases mem_upair.mp (show a ∈ˢ upair _ _ from ha) with rfl | rfl
      · rw [rPos_nil]; exact hU.empty_mem (hv 0)
      · rw [rPos_cons]; exact hU.upair_mem (hv 0) (hv 0) (hv 1)
  case htgt =>
    intro m hm i a p hi ha hp
    refine ⟨?_, pt_mem_unitSet⟩
    unfold rTgt
    repeat' split
    all_goals omega
  case hmkU =>
    intro m hm i a g hi ha hg
    match m, hm with
    | 0, _ =>
      obtain ⟨b, hb, rfl⟩ := mem_image.mp (show a ∈ˢ image _ α from ha)
      rw [rMk_node]
      exact stdInj_two_mem_univ hw 0 (hU.transitive hα hb) (app_mem_univ hw hg _)
    | 1, _ =>
      rcases mem_upair.mp (show a ∈ˢ upair _ _ from ha) with rfl | rfl
      · rw [rMk_nil]; exact stdInj_mem_univ hw (by simp)
      · rw [rMk_cons]
        exact stdInj_two_mem_univ hw 1 (app_mem_univ hw hg _) (app_mem_univ hw hg _)
  case helim =>
    intro X hX m hm i hi x hx
    obtain rfl := mem_unitSet_iff.mp hi
    match m, hm with
    | 0, _ =>
      rw [app_stdΨR_zero] at hx
      obtain ⟨a, ha, l, hl, rfl⟩ := mem_nodeArm.mp hx
      refine ⟨kpair (vnat 0) a, mem_image.mpr ⟨a, ha, rfl⟩,
        graph (fun _ => l) (sing (vnat 0)), ?_, ?_⟩
      · rw [rPos_node]
        refine graph_mem_piSet fun p hp => ?_
        rw [rTgt_node]
        exact hl
      · rw [rMk_node, app_graph (mem_sing.mpr rfl)]
    | 1, _ =>
      rw [app_stdΨR_one] at hx
      rcases mem_consArm.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
      · refine ⟨kpair (vnat 1) pt, mem_upair.mpr (Or.inl rfl), graph (fun _ => pt) empty, ?_, ?_⟩
        · rw [rPos_nil]
          exact graph_mem_piSet fun p hp => absurd hp (not_mem_empty p)
        · rw [rMk_nil]
      · refine ⟨kpair (vnat 2) pt, mem_upair.mpr (Or.inr rfl),
          graph (fun p => if p = (vnat 0 : V) then h else t) (upair (vnat 0) (vnat 1)), ?_, ?_⟩
        · rw [rPos_cons]
          refine graph_mem_piSet fun p hp => ?_
          rcases mem_upair.mp hp with rfl | rfl
          · rw [if_pos rfl, rTgt_cons_head]; exact hh
          · rw [if_neg (vnat_ne (by omega)), rTgt_cons_tail]; exact ht
        · rw [rMk_cons, app_graph (mem_upair.mpr (Or.inl rfl)),
            app_graph (mem_upair.mpr (Or.inr rfl)), if_pos rfl, if_neg (vnat_ne (by omega))]

/-- The instance component of `Rose`'s table IS `⟦List⟧` at the
container's OWN member carrier — the self-referential `instLeaf`
(F2 FINDING (2)), proved by the same segment Bekić the identification
uses, at `Rose`'s own block. -/
theorem stdΨR_instLeaf {w : Nat} {α : V} (hα : α ∈ˢ (univ w : V)) :
    lfpTuple w 2 uIs (stdΨR w α) 1 = stdLIST w (app (stdROSE w α) pt) := by
  have h : lfpTuple w 2 uIs (stdΨR w α) (1 + 0)
      = lfpTuple w 1 uIs (stdΨL w (app (stdROSE w α) pt)) 0 :=
    lfpTuple_seg_congr (stdΨR_closed hα) (stdΨR_mono w α) (by omega) (fun _ _ => rfl)
      (fun Y hY i hi => by
        obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
        show stdΨR w α (segJoin 1 1 (lfpTuple w 2 uIs (stdΨR w α)) Y) 1
          = stdΨL w (app (stdROSE w α) pt) Y 0
        unfold stdΨR stdΨL
        rw [segJoin_add (q := 0) _ _ (show (0:Nat) < 1 by omega),
          segJoin_lt _ _ (show (0:Nat) < 1 by omega)]
        rfl)
      Nat.zero_lt_one
  exact h

/-- **`RoseClause` is not an empty hypothesis**: the standard reading
of `Rose α ::= node α (List (Rose α))` satisfies it at every level,
with F0's standard `List` as its instance component and the SAME
tags. -/
theorem stdRoseClause (w : Nat) :
    RoseClause w (stdROSE (V := V) w) (stdΨR w) (stdLIST w) (stdInj w) (stdInj w) where
  leaf := fun _ _ => rfl
  mono := fun α _ => stdΨR_mono w α
  maps := fun _ hα => stdΨR_maps hα
  closed := fun _ hα => stdΨR_closed hα
  fibre0 := fun α hα Y hY t ht x => by
    obtain rfl := mem_unitSet_iff.mp ht
    rw [app_stdΨR_zero]
    exact mem_nodeArm
  fibre1 := fun α hα Y hY t ht x => by
    obtain rfl := mem_unitSet_iff.mp ht
    rw [app_stdΨR_one, mem_consArm]
    exact ⟨fun hx => by
        rcases hx with rfl | ⟨h, t', hh, ht', rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h, hh, t', ht', rfl⟩,
      fun hx => by
        rcases hx with rfl | ⟨h, hh, t', ht', rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h, t', hh, ht', rfl⟩⟩
  instLeaf := fun _ hα => stdΨR_instLeaf hα
  mkZero := fun hw j fs => by unfold stdInj; rw [if_pos hw]
  mkInj := fun hw j j' fs fs' h => stdInj_inj hw j j' fs fs' h

/-- The whole hypothesis of F2 is satisfiable. -/
theorem p4Ok_std (w : Nat) :
    P4Ok (V := V) ⟨w, stdROSE w, stdΨR w, stdLIST w, stdΨL w, stdInj w, stdInj w, stdInj w⟩ :=
  ⟨stdRoseClause w, stdListClause w, treeTags_stdInj w⟩

end StdRose

end P4Block

end ConLeche.SetTheory
