module

public import ConLeche.SetModel.EnvClauseTreeList
import ConLeche.SetModel.TupleContainer
@[expose] public section

/-!
# `P3 ::= mk (Array (List P3))` — the RANK INDUCTION (falsifier F1)

The second falsifier of the *uniform* nested route
(`DESIGN-theory.md` §6.1 F1, §2.1 step 5, §2.4, §5's `P3` row).  The
block

    inductive P3 where | mk : Array (List P3) → P3

is modelled as a plain **four**-component block, the components in the
check's order (`SURVEY-official.md` §2.4 prints official's four
motives):

| c | component | group |
|---|---|---|
| 0 | `P3` | the member |
| 1 | `Array (List P3)` | `g₁` = `Array` at the pin `List P3`, component 0 of `Array`'s table |
| 2 | `List (List P3)` | `g₁`, component 1 of `Array`'s table |
| 3 | `List P3` | `g₂` = `List` at the pin `P3` |

`Array α ::= mk (toList : List α)`'s ONE field is an *ordinary* field
whose type is itself a container instance, so `Array`'s OWN recorded
clause is **wide**: `N_Array = 2`, and the group `g₁` opened by the key
`Array (List P3)` occupies the two contiguous components `1, 2`
(`DESIGN-theory.md` §2.1 step 2: a group's components are the
container's own stored table substituted at the pins).  `g₂`, opened
by the key `List P3` while descending into `g₁`'s copy of `List.cons`,
is one component.

**The ranks** (§2.1 step 5): `g₂`'s pin is the member, so `g₂` has rank
`0`; `g₁`'s pin `List P3` is `g₂`'s atom, so `g₁` has rank `1`.  The
identifications are proved IN RANK ORDER and this file exhibits the
induction step:

* rank 0 — `car 3 = ⟦List⟧ ⟦P3⟧`, Bekić at the segment `[3, 4)` of
  width `1` (exactly F0);
* rank 1 — `(car 1, car 2) = Array's WIDE table at α := car 3`, ONE
  `lfpTuple_seg_congr` at the segment `[1, 3)` of width `s = 2`, using
  `ArrayClause` at `α := carL` and, *for the statement*, the rank-0
  identification: `car 1 = ⟦Array⟧ ⟦List P3⟧ = ⟦Array⟧ (⟦List⟧ ⟦P3⟧)`.

The pass criterion is met: the rank-1 identification uses only `g₂`'s
identification, `Array`'s wide clause and segment Bekić/congruence —
no clamp (`meetT`), no `composeΦ`, no `pinsCar`, no class
accessibility (`unionAcc_of_classAcc`, `unionRecC`), and ONE level
`w`.  Mechanically: those names occur in this file only inside
comments.

**F1 FINDING** (`-- F1 FINDING:` at `ArrayClause.fibre1`): the clause
of §1.2 records `ctor` — the tie between an injection and a real
constructor's reading — for the block's MEMBERS only.  An instance
component of the container's own table (`List`-at-α inside `Array`'s
table, component `2` here) then has injections tied to nothing, and
the ι rule official emits for it (`P3.rec_2`, firing on `List.cons` at
`List P3`) cannot be stated.  The clause must record, per instance
component, the inner container's tags; here that is the `injL`
argument of `ArrayClause`, shared with `ListClause`.  See the module
`## What the clause must record` section at the end.

Everything here is over the bare `SetTheory` interface; no syntax.
The container clause `ListClause`, the `nil`/`cons` arm `consArm`, the
index sets `uIs` and the member-tag record `TreeTags` (a member with
one constructor of one field — `P3.mk`'s shape as much as
`Tree.node`'s) are F0's, reused verbatim from
`ConLeche/SetModel/EnvClauseTreeList.lean`.
-/

namespace ConLeche.SetTheory

open Tower (natFibre natFibre_vnat)

universe u

variable {V : Type u} [SetTheory V]

namespace P3Block

/-! ## `Array`'s env clause — WIDE, at `N_Array = 2`

`DESIGN-theory.md` §1.2 at a one-member block with one type parameter,
no indices, and ONE instance component:

    Array α ::= mk (toList : List α)

Component `0` is `Array` itself, component `1` is `Array`'s own
abstract copy of `List` at `α`; `Array.mk`'s single field is a plain
slot at component `1`.  The clause is stated at every parameter in the
`Sat` domain `univ w` and at every tuple of the two-component space. -/
structure ArrayClause (w : Nat) (ARR : V → V) (ΨA : V → (Nat → V) → Nat → V)
    (LIST : V → V) (injA : Nat → List V → V) (injL : Nat → List V → V) : Prop where
  /-- `leaf`: the stored reading of the MEMBER is component `0` of the
  wide least tuple. -/
  leaf : ∀ α, α ∈ˢ (univ w : V) → ARR α = lfpTuple w 2 uIs (ΨA α) 0
  /-- `functor`, monotonicity, at width `2`. -/
  mono : ∀ α, α ∈ˢ (univ w : V) → MonoTuple w 2 uIs (ΨA α)
  /-- `functor`, space preservation. -/
  maps : ∀ α, α ∈ˢ (univ w : V) → MapsTuple w 2 uIs (ΨA α)
  /-- `functor`, the closed tuple. -/
  closed : ∀ α, α ∈ˢ (univ w : V) → ∃ L, IsClosedTuple w 2 uIs (ΨA α) L
  /-- `fibre` at component `0`: `Array.mk`'s field is a slot at
  component `1` — the ordinary field whose type is an instance. -/
  fibre0 : ∀ α, α ∈ˢ (univ w : V) → ∀ Y, InTupleSpace w 2 uIs Y → ∀ t, t ∈ˢ (unitSet : V) →
    ∀ x, x ∈ˢ app (ΨA α Y 0) t ↔ ∃ l, l ∈ˢ app (Y 1) pt ∧ x = injA 0 [l]
  /-- `fibre` at component `1`, the copy of `List` at `α`: heads in the
  PARAMETER (an ordinary field), tails at component `1`.

  F1 FINDING: the injections here are `injL`, the INNER container's
  own member-local tags — §1.2's `ctor` clause is "members only", so
  the clause as written leaves an instance component's injections tied
  to nothing and `P3.rec_2`'s ι rule (which fires on `List.cons`)
  cannot be stated.  `BlockModelAt` must record, per instance
  component, the inner container's constructor readings. -/
  fibre1 : ∀ α, α ∈ˢ (univ w : V) → ∀ Y, InTupleSpace w 2 uIs Y → ∀ t, t ∈ˢ (unitSet : V) →
    ∀ x, x ∈ˢ app (ΨA α Y 1) t ↔
      (x = injL 0 [] ∨ ∃ h, h ∈ˢ α ∧ ∃ t', t' ∈ˢ app (Y 1) pt ∧ x = injL 1 [h, t'])
  /-- The same FINDING at the level of readings: component `1` of the
  table IS the inner container's recorded reading at the (substituted)
  pin.  This is what `Array`'s own install proved — F0's theorem at
  `Array`'s block — and it is what makes §2.4's claim at an instance
  component of a group EXPRESSIBLE in ordinary-reading form.  Its only
  consumer here is `car_two_eq`. -/
  instLeaf : ∀ α, α ∈ˢ (univ w : V) → lfpTuple w 2 uIs (ΨA α) 1 = LIST α
  /-- `mkZero` at the member's tags. -/
  mkZero : w = 0 → ∀ j fs, injA j fs = (pt : V)
  /-- `mkInj` at the member's tags. -/
  mkInj : w ≠ 0 → ∀ j j' fs fs', injA j fs = injA j' fs' → j = j' ∧ fs = fs'

namespace ArrayClause

variable {w : Nat} {ARR LIST : V → V} {ΨA : V → (Nat → V) → Nat → V}
  {injA injL : Nat → List V → V}

/-- Formation of `Array.mk`'s value, derived from `maps` + `fibre0` at
a tuple chosen to hold exactly the wanted field (F0's recipe, the
`inj_mem_univ` derivation of `F0-REPORT.md` (F0-1)). -/
theorem mk_mem_univ (hC : ArrayClause w ARR ΨA LIST injA injL) (hw : w ≠ 0) {l : V}
    (hl : l ∈ˢ (univ w : V)) : injA 0 [l] ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  have hY : InTupleSpace w 2 uIs (fun _ => graph (fun _ => sing l) unitSet) :=
    fun _ _ => graph_mem_famSpace fun _ _ => hU.sing_mem hl hl
  refine hU.transitive (famSpace_app (hC.maps _ (unitSet_mem_univ (V := V) w) _ hY 0 (by omega))
    pt_mem_unitSet) ?_
  refine (hC.fibre0 _ (unitSet_mem_univ (V := V) w) _ hY pt pt_mem_unitSet _).mpr ⟨l, ?_, rfl⟩
  rw [app_graph pt_mem_unitSet]
  exact mem_sing.mpr rfl

end ArrayClause

/-! ## The block's datum -/

/-- The data F1 reasons about: the two containers' recorded readings,
operators and tags, and the member's tags.  ONE level `w`: the sort
gate makes every container's sort the block's
(`DESIGN-theory.md` §2.5). -/
structure P3Sig (V : Type u) [SetTheory V] where
  /-- The value level. -/
  w : Nat
  /-- `⟦Array α⟧`, as a family. -/
  ARR : V → V
  /-- `Array`'s own WIDE operator at a parameter, two components. -/
  ΨA : V → (Nat → V) → Nat → V
  /-- `⟦List α⟧`, as a family. -/
  LIST : V → V
  /-- `List`'s own operator at a parameter, one component. -/
  ΨL : V → (Nat → V) → Nat → V
  /-- `Array`'s member-local tags. -/
  injA : Nat → List V → V
  /-- `List`'s member-local tags — shared by BOTH copies of `List`
  (components `2` and `3`) and by `Array`'s table component `1`. -/
  injL : Nat → List V → V
  /-- `P3`'s tags. -/
  injP : Nat → List V → V

/-- The hypotheses: the two containers' env clauses and the member's
tag laws.  Nothing else. -/
structure P3Ok (S : P3Sig V) : Prop where
  /-- `Array`'s wide env clause, `DESIGN-theory.md` §1.2 at `N = 2`. -/
  arr : ArrayClause S.w S.ARR S.ΨA S.LIST S.injA S.injL
  /-- `List`'s env clause, F0's, at `N = 1`. -/
  list : ListClause S.w S.LIST S.ΨL S.injL
  /-- The member's own `mkZero`/`mkInj`/formation (F0's record: a
  member with one constructor of one field). -/
  mem : TreeTags S.w S.injP

variable {S : P3Sig V}

/-! ## The four-component operator -/

/-- The four components' fibres at an argument tuple:
`P3.mk`'s field is a slot at `1`; `Array.mk`'s at `2`; the copy of
`List` at `List P3` has heads at `3` and tails at `2`; the copy of
`List` at `P3` has heads at `0` and tails at `3`. -/
noncomputable def blkFib (S : P3Sig V) (X : Nat → V) : Nat → V
  | 0 => image (fun a => S.injP 0 [a]) (app (X 1) pt)
  | 1 => image (fun l => S.injA 0 [l]) (app (X 2) pt)
  | 2 => consArm S.injL (app (X 3) pt) (app (X 2) pt)
  | _ => consArm S.injL (app (X 0) pt) (app (X 3) pt)

/-- **The block's operator**, a plain four-component block operator. -/
noncomputable def blkΨ (S : P3Sig V) (X : Nat → V) (c : Nat) : V :=
  graph (fun _ => blkFib S X c) unitSet

theorem app_blkΨ (S : P3Sig V) (X : Nat → V) (c : Nat) :
    app (blkΨ S X c) pt = blkFib S X c := app_graph pt_mem_unitSet

theorem blkFib_zero (S : P3Sig V) (X : Nat → V) :
    blkFib S X 0 = image (fun a => S.injP 0 [a]) (app (X 1) pt) := rfl

theorem blkFib_one (S : P3Sig V) (X : Nat → V) :
    blkFib S X 1 = image (fun l => S.injA 0 [l]) (app (X 2) pt) := rfl

theorem blkFib_two (S : P3Sig V) (X : Nat → V) :
    blkFib S X 2 = consArm S.injL (app (X 3) pt) (app (X 2) pt) := rfl

theorem blkFib_three (S : P3Sig V) (X : Nat → V) :
    blkFib S X 3 = consArm S.injL (app (X 0) pt) (app (X 3) pt) := rfl

theorem mem_blkFib_zero {X : Nat → V} {x : V} :
    x ∈ˢ blkFib S X 0 ↔ ∃ a, a ∈ˢ app (X 1) pt ∧ x = S.injP 0 [a] := mem_image

theorem mem_blkFib_one {X : Nat → V} {x : V} :
    x ∈ˢ blkFib S X 1 ↔ ∃ l, l ∈ˢ app (X 2) pt ∧ x = S.injA 0 [l] := mem_image

theorem mem_blkFib_two {X : Nat → V} {x : V} :
    x ∈ˢ blkFib S X 2 ↔
      x = S.injL 0 [] ∨
        ∃ h t, h ∈ˢ app (X 3) pt ∧ t ∈ˢ app (X 2) pt ∧ x = S.injL 1 [h, t] := mem_consArm

theorem mem_blkFib_three {X : Nat → V} {x : V} :
    x ∈ˢ blkFib S X 3 ↔
      x = S.injL 0 [] ∨
        ∃ h t, h ∈ˢ app (X 0) pt ∧ t ∈ˢ app (X 3) pt ∧ x = S.injL 1 [h, t] := mem_consArm

/-! ## (a) The functor clauses -/

theorem blkΨ_mono (S : P3Sig V) : MonoTuple S.w 4 uIs (blkΨ S) := by
  intro X Y hX hY hle c hc i hi x hx
  obtain rfl := mem_unitSet_iff.mp hi
  rw [app_blkΨ] at hx ⊢
  match c, hc with
  | 0, _ =>
    obtain ⟨a, ha, rfl⟩ := mem_blkFib_zero.mp hx
    exact mem_blkFib_zero.mpr ⟨a, hle 1 (by omega) pt pt_mem_unitSet a ha, rfl⟩
  | 1, _ =>
    obtain ⟨l, hl, rfl⟩ := mem_blkFib_one.mp hx
    exact mem_blkFib_one.mpr ⟨l, hle 2 (by omega) pt pt_mem_unitSet l hl, rfl⟩
  | 2, _ =>
    rcases mem_blkFib_two.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · exact mem_blkFib_two.mpr (Or.inl rfl)
    · exact mem_blkFib_two.mpr (Or.inr ⟨h, t, hle 3 (by omega) pt pt_mem_unitSet h hh,
        hle 2 (by omega) pt pt_mem_unitSet t ht, rfl⟩)
  | 3, _ =>
    rcases mem_blkFib_three.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · exact mem_blkFib_three.mpr (Or.inl rfl)
    · exact mem_blkFib_three.mpr (Or.inr ⟨h, t, hle 0 (by omega) pt pt_mem_unitSet h hh,
        hle 3 (by omega) pt pt_mem_unitSet t ht, rfl⟩)

theorem blkFib_mem (hS : P3Ok S) {X : Nat → V} (hX : InTupleSpace S.w 4 uIs X) (c : Nat)
    (hc : c < 4) : blkFib S X c ∈ˢ (univ S.w : V) := by
  by_cases hw : S.w = 0
  · rw [hw, univ_zero]
    refine mem_univZero.mpr fun x hx => ?_
    match c, hc with
    | 0, _ =>
      obtain ⟨a, -, rfl⟩ := mem_blkFib_zero.mp hx
      rw [hS.mem.mkZero hw 0 [a]]; exact pt_mem_unitSet
    | 1, _ =>
      obtain ⟨l, -, rfl⟩ := mem_blkFib_one.mp hx
      rw [hS.arr.mkZero hw 0 [l]]; exact pt_mem_unitSet
    | 2, _ =>
      rcases mem_blkFib_two.mp hx with rfl | ⟨h, t, -, -, rfl⟩
      · rw [hS.list.mkZero hw 0 []]; exact pt_mem_unitSet
      · rw [hS.list.mkZero hw 1 [h, t]]; exact pt_mem_unitSet
    | 3, _ =>
      rcases mem_blkFib_three.mp hx with rfl | ⟨h, t, -, -, rfl⟩
      · rw [hS.list.mkZero hw 0 []]; exact pt_mem_unitSet
      · rw [hS.list.mkZero hw 1 [h, t]]; exact pt_mem_unitSet
  · have hU := univ_isTGUniverse (V := V) hw
    have hap : ∀ m, m < 4 → app (X m) pt ∈ˢ (univ S.w : V) := fun m hm =>
      famSpace_app (hX m hm) pt_mem_unitSet
    match c, hc with
    | 0, _ =>
      rw [blkFib_zero]
      exact hU.image_mem (hap 1 (by omega)) fun a ha =>
        hS.mem.memU hw a (hU.transitive (hap 1 (by omega)) ha)
    | 1, _ =>
      rw [blkFib_one]
      exact hU.image_mem (hap 2 (by omega)) fun l hl =>
        hS.arr.mk_mem_univ hw (hU.transitive (hap 2 (by omega)) hl)
    | 2, _ =>
      rw [blkFib_two]
      exact consArm_mem_univ hw (hap 3 (by omega)) (hap 2 (by omega))
        (hS.list.nil_mem_univ hw) fun _ _ hh ht => hS.list.cons_mem_univ hw hh ht
    | 3, _ =>
      rw [blkFib_three]
      exact consArm_mem_univ hw (hap 0 (by omega)) (hap 3 (by omega))
        (hS.list.nil_mem_univ hw) fun _ _ hh ht => hS.list.cons_mem_univ hw hh ht

theorem blkΨ_maps (hS : P3Ok S) : MapsTuple S.w 4 uIs (blkΨ S) := fun _ hX c hc =>
  graph_mem_famSpace fun _ _ => blkFib_mem hS hX c hc

/-! ## (b) (W): the closed tuple

Six constructors over four components; the shapes must be GLOBALLY
distinguishing, because `tupleContainer_closed_exists`'s `B`/`tgtM`
read the shape ALONE (`F0-REPORT.md`, "what was hard" (2)) — and here
that bites: `List.cons` occurs at components `2` and `3` with
DIFFERENT targets (`3, 2` against `0, 3`), so the two copies of the
same container constructor need different shapes.  Tags:
`0 = P3.mk`, `1 = Array.mk`, `2 = nil@2`, `3 = cons@2`, `4 = nil@3`,
`5 = cons@3`. -/

/-- The shapes, per component. -/
noncomputable def shp : Nat → V → V
  | 0, _ => sing (vnat 0)
  | 1, _ => sing (vnat 1)
  | 2, _ => upair (vnat 2) (vnat 3)
  | _, _ => upair (vnat 4) (vnat 5)

/-- The positions of a shape, by tag. -/
noncomputable def posN : Nat → V
  | 0 => sing (vnat 0)
  | 1 => sing (vnat 0)
  | 3 => upair (vnat 0) (vnat 1)
  | 5 => upair (vnat 0) (vnat 1)
  | _ => empty

/-- The positions of a shape. -/
noncomputable def posns (a : V) : V := natFibre posN a

theorem posns_vnat (j : Nat) : posns (vnat j : V) = posN j := natFibre_vnat _ j

open Classical in
/-- The target component of a slot, read off the shape and the
position. -/
noncomputable def tgtC (a p : V) : Nat :=
  if a = (vnat 0 : V) then 1
  else if a = (vnat 1 : V) then 2
  else if a = (vnat 3 : V) then (if p = (vnat 0 : V) then 3 else 2)
  else (if p = (vnat 0 : V) then 0 else 3)

open Classical in
/-- The builder. -/
noncomputable def mkC (S : P3Sig V) (_m : Nat) (a g : V) : V :=
  if a = (vnat 0 : V) then S.injP 0 [app g (vnat 0)]
  else if a = (vnat 1 : V) then S.injA 0 [app g (vnat 0)]
  else if a = (vnat 2 : V) then S.injL 0 []
  else if a = (vnat 4 : V) then S.injL 0 []
  else S.injL 1 [app g (vnat 0), app g (vnat 1)]

open Classical in
/-- **(W)**: the block's operator has a closed tuple. -/
theorem blkΨ_closed (hS : P3Ok S) : ∃ L, IsClosedTuple S.w 4 uIs (blkΨ S) L := by
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
    | 3, _ => exact hU.upair_mem (hv 4) (hv 4) (hv 5)
  case hB =>
    intro m hm i a hi ha
    have hcases : ∃ j : Nat, a = (vnat j : V) ∧ j < 6 := by
      match m, hm with
      | 0, _ => exact ⟨0, mem_sing.mp ha, by omega⟩
      | 1, _ => exact ⟨1, mem_sing.mp ha, by omega⟩
      | 2, _ => rcases mem_upair.mp ha with h | h
                · exact ⟨2, h, by omega⟩
                · exact ⟨3, h, by omega⟩
      | 3, _ => rcases mem_upair.mp ha with h | h
                · exact ⟨4, h, by omega⟩
                · exact ⟨5, h, by omega⟩
    obtain ⟨j, rfl, hj⟩ := hcases
    rw [posns_vnat]
    match j, hj with
    | 0, _ => exact hU.sing_mem (hv 0) (hv 0)
    | 1, _ => exact hU.sing_mem (hv 0) (hv 0)
    | 2, _ => exact hU.empty_mem (hv 0)
    | 3, _ => exact hU.upair_mem (hv 0) (hv 0) (hv 1)
    | 4, _ => exact hU.empty_mem (hv 0)
    | 5, _ => exact hU.upair_mem (hv 0) (hv 0) (hv 1)
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
      · exact hS.arr.mk_mem_univ hw (app_mem_univ hw hg _)
      · split
        · exact hS.list.nil_mem_univ hw
        · split
          · exact hS.list.nil_mem_univ hw
          · exact hS.list.cons_mem_univ hw (app_mem_univ hw hg _) (app_mem_univ hw hg _)
  case helim =>
    intro X hX m hm i hi x hx
    obtain rfl := mem_unitSet_iff.mp hi
    rw [app_blkΨ] at hx
    match m, hm with
    | 0, _ =>
      obtain ⟨a, ha, rfl⟩ := mem_blkFib_zero.mp hx
      refine ⟨vnat 0, mem_sing.mpr rfl, graph (fun _ => a) (sing (vnat 0)), ?_, ?_⟩
      · rw [posns_vnat]
        refine graph_mem_piSet fun p hp => ?_
        obtain rfl := mem_sing.mp hp
        show a ∈ˢ app (X (tgtC (vnat 0) (vnat 0))) pt
        rw [show tgtC (vnat 0 : V) (vnat 0) = 1 from by unfold tgtC; rw [if_pos rfl]]
        exact ha
      · show _ = mkC S 0 (vnat 0) _
        unfold mkC
        rw [if_pos rfl, app_graph (mem_sing.mpr rfl)]
    | 1, _ =>
      obtain ⟨l, hl, rfl⟩ := mem_blkFib_one.mp hx
      refine ⟨vnat 1, mem_sing.mpr rfl, graph (fun _ => l) (sing (vnat 0)), ?_, ?_⟩
      · rw [posns_vnat]
        refine graph_mem_piSet fun p hp => ?_
        obtain rfl := mem_sing.mp hp
        show l ∈ˢ app (X (tgtC (vnat 1) (vnat 0))) pt
        rw [show tgtC (vnat 1 : V) (vnat 0) = 2 from by
          unfold tgtC; rw [if_neg (vnat_ne (by omega)), if_pos rfl]]
        exact hl
      · show _ = mkC S 1 (vnat 1) _
        unfold mkC
        rw [if_neg (vnat_ne (by omega)), if_pos rfl, app_graph (mem_sing.mpr rfl)]
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
            rw [show tgtC (vnat 3 : V) (vnat 0) = 3 from by
              unfold tgtC
              rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)), if_pos rfl,
                if_pos rfl]]
            exact hh
          · rw [if_neg (vnat_ne (by omega))]
            show t ∈ˢ app (X (tgtC (vnat 3) (vnat 1))) pt
            rw [show tgtC (vnat 3 : V) (vnat 1) = 2 from by
              unfold tgtC
              rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)), if_pos rfl,
                if_neg (vnat_ne (by omega))]]
            exact ht
        · show _ = mkC S 2 (vnat 3) _
          unfold mkC
          rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
            if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
            app_graph (mem_upair.mpr (Or.inl rfl)), app_graph (mem_upair.mpr (Or.inr rfl)),
            if_pos rfl, if_neg (vnat_ne (by omega))]
    | 3, _ =>
      rcases mem_blkFib_three.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
      · refine ⟨vnat 4, mem_upair.mpr (Or.inl rfl), graph (fun _ => pt) empty, ?_, ?_⟩
        · rw [posns_vnat]
          exact graph_mem_piSet fun p hp => absurd hp (not_mem_empty p)
        · show _ = mkC S 3 (vnat 4) _
          unfold mkC
          rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
            if_neg (vnat_ne (by omega)), if_pos rfl]
      · refine ⟨vnat 5, mem_upair.mpr (Or.inr rfl),
          graph (fun p => if p = (vnat 0 : V) then h else t) (upair (vnat 0) (vnat 1)), ?_, ?_⟩
        · rw [posns_vnat]
          refine graph_mem_piSet fun p hp => ?_
          rcases mem_upair.mp hp with rfl | rfl
          · rw [if_pos rfl]
            show h ∈ˢ app (X (tgtC (vnat 5) (vnat 0))) pt
            rw [show tgtC (vnat 5 : V) (vnat 0) = 0 from by
              unfold tgtC
              rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
                if_neg (vnat_ne (by omega)), if_pos rfl]]
            exact hh
          · rw [if_neg (vnat_ne (by omega))]
            show t ∈ˢ app (X (tgtC (vnat 5) (vnat 1))) pt
            rw [show tgtC (vnat 5 : V) (vnat 1) = 3 from by
              unfold tgtC
              rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
                if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega))]]
            exact ht
        · show _ = mkC S 3 (vnat 5) _
          unfold mkC
          rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
            if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega)),
            app_graph (mem_upair.mpr (Or.inl rfl)), app_graph (mem_upair.mpr (Or.inr rfl)),
            if_pos rfl, if_neg (vnat_ne (by omega))]

/-! ## The carrier -/

/-- The block's carrier tuple, four components. -/
noncomputable def car (S : P3Sig V) : Nat → V := lfpTuple S.w 4 uIs (blkΨ S)

/-- `⟦P3⟧`. -/
noncomputable def carP (S : P3Sig V) : V := app (car S 0) pt

/-- The `Array (List P3)` component. -/
noncomputable def carA (S : P3Sig V) : V := app (car S 1) pt

/-- The `List (List P3)` component. -/
noncomputable def carLL (S : P3Sig V) : V := app (car S 2) pt

/-- The `List P3` component. -/
noncomputable def carL (S : P3Sig V) : V := app (car S 3) pt

theorem car_mem (S : P3Sig V) : InTupleSpace S.w 4 uIs (car S) := lfpTuple_mem _ _ _ _

theorem carP_mem_univ (S : P3Sig V) : carP S ∈ˢ (univ S.w : V) :=
  famSpace_app (car_mem S 0 (by omega)) pt_mem_unitSet

/-- The rank-1 group's pin value lies in `Array`'s `Sat` domain — by
`famSpace_app` at the SAME level, with no appeal to the rank-0
identification.  (The rank induction enters the STATEMENT of the
rank-1 claim, not its proof; see the module's last section.) -/
theorem carL_mem_univ (S : P3Sig V) : carL S ∈ˢ (univ S.w : V) :=
  famSpace_app (car_mem S 3 (by omega)) pt_mem_unitSet

/-! ## (c) THE IDENTIFICATIONS, IN RANK ORDER

Rank `0` first (`g₂ = List` at the pin `P3`, component `3`), then rank
`1` (`g₁ = Array` at the pin `List P3`, the SEGMENT `[1, 3)` of width
`2`). -/

/-- The segment `[3, 4)`'s section operator agrees with `List`'s own
operator at the parameter `⟦P3⟧`, on the whole one-tuple space. -/
theorem segSec_eq_ΨL (hS : P3Ok S) {Y : Nat → V}
    (hY : InTupleSpace S.w 1 (fun i => uIs (3 + i)) Y) :
    blkΨ S (segJoin 3 1 (car S) Y) 3 = S.ΨL (carP S) Y 0 := by
  have hY' : InTupleSpace S.w 1 uIs Y := hY
  have hZ : InTupleSpace S.w 4 uIs (segJoin 3 1 (car S) Y) :=
    inTupleSpace_segJoin (car S |> fun Z => car_mem S) hY'
  refine famSpace_ext (blkΨ_maps hS _ hZ 3 (by omega))
    (hS.list.maps (carP S) (carP_mem_univ S) Y hY' 0 Nat.one_pos) ?_
  intro i hi
  obtain rfl := mem_unitSet_iff.mp hi
  apply SetTheory.ext
  intro x
  rw [app_blkΨ, blkFib_three, segJoin_lt _ _ (show (0:Nat) < 3 by omega),
    segJoin_add (q := 0) _ _ (show (0:Nat) < 1 by omega), mem_consArm,
    hS.list.fibre (carP S) (carP_mem_univ S) Y hY' pt pt_mem_unitSet x]
  constructor
  · rintro (rfl | ⟨h, t, hh, ht, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨h, hh, t, ht, rfl⟩
  · rintro (rfl | ⟨h, hh, t, ht, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨h, t, hh, ht, rfl⟩

/-- **THE RANK-0 IDENTIFICATION**: `car 3 = ⟦List⟧ ⟦P3⟧`, exactly F0. -/
theorem car_three_eq (hS : P3Ok S) : car S 3 = S.LIST (carP S) := by
  have h : car S (3 + 0) = lfpTuple S.w 1 uIs (S.ΨL (carP S)) 0 :=
    lfpTuple_seg_congr (blkΨ_closed hS) (blkΨ_mono S) (by omega) (fun _ _ => rfl)
      (fun Y hY i hi => by
        obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
        exact segSec_eq_ΨL hS hY)
      Nat.zero_lt_one
  rw [hS.list.leaf (carP S) (carP_mem_univ S)]
  exact h

/-- The segment `[1, 3)`'s section operator agrees, on the whole
TWO-tuple space, with `Array`'s own WIDE operator at the parameter
`carL` — the pin's value.  Component `1` is `Array.mk`'s fibre with
its slot at the segment's second component; component `2` is the copy
of `List` whose heads come from OUTSIDE the segment (`car 3`, the
rank-0 group's component) and whose tails stay inside. -/
theorem segSec_eq_ΨA (hS : P3Ok S) {Y : Nat → V}
    (hY : InTupleSpace S.w 2 (fun i => uIs (1 + i)) Y) (i : Nat) (hi : i < 2) :
    blkΨ S (segJoin 1 2 (car S) Y) (1 + i) = S.ΨA (carL S) Y i := by
  have hY' : InTupleSpace S.w 2 uIs Y := hY
  have hZ : InTupleSpace S.w 4 uIs (segJoin 1 2 (car S) Y) :=
    inTupleSpace_segJoin (car_mem S) hY'
  have h1 : segJoin 1 2 (car S) Y 2 = Y 1 := segJoin_add (q := 1) _ _ (by omega)
  have h3 : segJoin 1 2 (car S) Y 3 = car S 3 :=
    segJoin_out _ _ (by omega)
  match i, hi with
  | 0, _ =>
    refine famSpace_ext (blkΨ_maps hS _ hZ 1 (by omega))
      (hS.arr.maps (carL S) (carL_mem_univ S) Y hY' 0 (by omega)) ?_
    intro t ht
    obtain rfl := mem_unitSet_iff.mp ht
    apply SetTheory.ext
    intro x
    rw [app_blkΨ, blkFib_one, h1,
      hS.arr.fibre0 (carL S) (carL_mem_univ S) Y hY' pt pt_mem_unitSet x]
    exact mem_image
  | 1, _ =>
    refine famSpace_ext (blkΨ_maps hS _ hZ 2 (by omega))
      (hS.arr.maps (carL S) (carL_mem_univ S) Y hY' 1 (by omega)) ?_
    intro t ht
    obtain rfl := mem_unitSet_iff.mp ht
    apply SetTheory.ext
    intro x
    rw [app_blkΨ, blkFib_two, h1, h3, mem_consArm,
      hS.arr.fibre1 (carL S) (carL_mem_univ S) Y hY' pt pt_mem_unitSet x]
    constructor
    · rintro (rfl | ⟨h, t, hh, ht, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨h, hh, t, ht, rfl⟩
    · rintro (rfl | ⟨h, hh, t, ht, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨h, t, hh, ht, rfl⟩

/-- **THE RANK-1 IDENTIFICATION, at the whole segment.**  The two
components of the group `g₁` ARE `Array`'s wide table at the pin's
value — ONE `lfpTuple_seg_congr` at `s = 2`.  This is the induction
step §2.4 claims, and its ingredients are exactly: `Array`'s wide env
clause and segment Bekić.  (The rank-0 identification enters the
COROLLARIES below, which state the claim in ordinary-reading form.) -/
theorem car_seg_eq (hS : P3Ok S) {q : Nat} (hq : q < 2) :
    car S (1 + q) = lfpTuple S.w 2 uIs (S.ΨA (carL S)) q :=
  lfpTuple_seg_congr (blkΨ_closed hS) (blkΨ_mono S) (by omega) (fun _ _ => rfl)
    (fun Y hY i hi => segSec_eq_ΨA hS hY i hi) hq

/-- **`car 1 = ⟦Array⟧ (⟦List⟧ ⟦P3⟧)`** — the rank-1 claim in
ordinary-reading form: the pin `List P3` is read through the rank-0
identification.  This is the domain of `P3.mk`. -/
theorem car_one_eq (hS : P3Ok S) : car S 1 = S.ARR (app (S.LIST (carP S)) pt) := by
  have h := car_seg_eq hS (q := 0) (by omega)
  rw [show (1 : Nat) + 0 = 1 from rfl] at h
  rw [h, ← hS.arr.leaf (carL S) (carL_mem_univ S)]
  unfold carL
  rw [car_three_eq hS]

/-- **`car 2 = ⟦List⟧ (⟦List⟧ ⟦P3⟧)`** — the rank-1 claim at the
group's INSTANCE component, through `ArrayClause.instLeaf` (the second
half of the F1 finding: without a recorded reading for an instance
component of the container's table, this statement cannot even be
made). -/
theorem car_two_eq (hS : P3Ok S) : car S 2 = S.LIST (app (S.LIST (carP S)) pt) := by
  have h := car_seg_eq hS (q := 1) (by omega)
  rw [show (1 : Nat) + 1 = 2 from rfl] at h
  rw [h, hS.arr.instLeaf (carL S) (carL_mem_univ S)]
  unfold carL
  rw [car_three_eq hS]

/-! ## (d) The fixed-point equations and the constructors' typing -/

theorem app_car_eq (hS : P3Ok S) {c : Nat} (hc : c < 4) :
    app (car S c) pt = blkFib S (car S) c := by
  rw [← app_blkΨ]
  exact (app_lfpTuple_eq (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS) hc
    (show (pt : V) ∈ˢ uIs c from pt_mem_unitSet)).symm

theorem carP_eq (hS : P3Ok S) : carP S = blkFib S (car S) 0 := app_car_eq hS (by omega)

theorem carA_eq (hS : P3Ok S) : carA S = blkFib S (car S) 1 := app_car_eq hS (by omega)

theorem carLL_eq (hS : P3Ok S) : carLL S = blkFib S (car S) 2 := app_car_eq hS (by omega)

theorem carL_eq (hS : P3Ok S) : carL S = blkFib S (car S) 3 := app_car_eq hS (by omega)

theorem mem_carP (hS : P3Ok S) {x : V} :
    x ∈ˢ carP S ↔ ∃ a, a ∈ˢ carA S ∧ x = S.injP 0 [a] := by
  constructor
  · intro hx; rw [carP_eq hS] at hx; exact mem_blkFib_zero.mp hx
  · intro hx; rw [carP_eq hS]; exact mem_blkFib_zero.mpr hx

theorem mem_carA (hS : P3Ok S) {x : V} :
    x ∈ˢ carA S ↔ ∃ l, l ∈ˢ carLL S ∧ x = S.injA 0 [l] := by
  constructor
  · intro hx; rw [carA_eq hS] at hx; exact mem_blkFib_one.mp hx
  · intro hx; rw [carA_eq hS]; exact mem_blkFib_one.mpr hx

theorem mem_carLL (hS : P3Ok S) {x : V} :
    x ∈ˢ carLL S ↔
      x = S.injL 0 [] ∨ ∃ h t, h ∈ˢ carL S ∧ t ∈ˢ carLL S ∧ x = S.injL 1 [h, t] := by
  constructor
  · intro hx; rw [carLL_eq hS] at hx; exact mem_blkFib_two.mp hx
  · intro hx; rw [carLL_eq hS]; exact mem_blkFib_two.mpr hx

theorem mem_carL (hS : P3Ok S) {x : V} :
    x ∈ˢ carL S ↔
      x = S.injL 0 [] ∨ ∃ h t, h ∈ˢ carP S ∧ t ∈ˢ carL S ∧ x = S.injL 1 [h, t] := by
  constructor
  · intro hx; rw [carL_eq hS] at hx; exact mem_blkFib_three.mp hx
  · intro hx; rw [carL_eq hS]; exact mem_blkFib_three.mpr hx

/-- **`P3.mk`'s typing, with its domain read ORDINARILY.**  `r` is a
value of `⟦Array⟧ (⟦List⟧ ⟦P3⟧)` — the reading the checker produces
for `P3.mk : Array (List P3) → P3` — and `mk r` is a value of the
member.  Both identifications are consumed, in rank order. -/
theorem mk_mem_carP (hS : P3Ok S) {r : V}
    (hr : r ∈ˢ app (S.ARR (app (S.LIST (carP S)) pt)) pt) : S.injP 0 [r] ∈ˢ carP S :=
  (mem_carP hS).mpr ⟨r, by unfold carA; rw [car_one_eq hS]; exact hr, rfl⟩

/-- `Array.mk`'s value, read ordinarily at the pin `List P3`, is a
value of the group's component `1`. -/
theorem arrMk_mem_carA (hS : P3Ok S) {l : V} (hl : l ∈ˢ carLL S) : S.injA 0 [l] ∈ˢ carA S :=
  (mem_carA hS).mpr ⟨l, hl, rfl⟩

/-- `List.cons`'s value at the pin `List P3` (component `2`). -/
theorem cons_mem_carLL (hS : P3Ok S) {h t : V} (hh : h ∈ˢ carL S) (ht : t ∈ˢ carLL S) :
    S.injL 1 [h, t] ∈ˢ carLL S := (mem_carLL hS).mpr (Or.inr ⟨h, t, hh, ht, rfl⟩)

/-- `List.cons`'s value at the pin `P3` (component `3`). -/
theorem cons_mem_carL (hS : P3Ok S) {h t : V} (hh : h ∈ˢ carP S) (ht : t ∈ˢ carL S) :
    S.injL 1 [h, t] ∈ˢ carL S := (mem_carL hS).mpr (Or.inr ⟨h, t, hh, ht, rfl⟩)

/-! ## (e) The recursor: `UnionRecKit` at FOUR components

Official emits `P3.rec` and `P3.rec_1..3`, one per component
(`SURVEY-official.md` §2.4); the model's recursor is `unionRec` over
the four components, with the six constructors' rules.  All four
recursion classes are components of the tuple lfp, so `unionAcc_all`
reaches them and `unionAcc_of_classAcc` is not needed.

The section runs above `Prop` (`S.w ≠ 0`): the constructor
decomposition of a value must be unique, which is `mkInj`'s guard. -/

section Rec

/-- The motives and the minors, bundled. -/
structure RecData (V : Type u) [SetTheory V] where
  /-- The four motives, by component. -/
  M : Nat → V → V
  /-- `P3.mk`'s minor. -/
  mkP : V → V → V
  /-- `Array.mk`'s minor. -/
  mkA : V → V → V
  /-- `List.nil`'s minor at the pin `List P3`. -/
  nilLL : V
  /-- `List.cons`'s minor at the pin `List P3`. -/
  consLL : V → V → V → V → V
  /-- `List.nil`'s minor at the pin `P3`. -/
  nilL : V
  /-- `List.cons`'s minor at the pin `P3`. -/
  consL : V → V → V → V → V

variable {ℓ : Nat} {R : RecData V}

/-- The minors' typing hypotheses. -/
structure RecOk (S : P3Sig V) (ℓ : Nat) (R : RecData V) : Prop where
  /-- The motives take values in `univ ℓ`. -/
  motive : ∀ c, c < 4 → ∀ x, x ∈ˢ app (car S c) pt → R.M c x ∈ˢ (univ ℓ : V)
  /-- `P3.mk`. -/
  mkP : ∀ a ih, a ∈ˢ carA S → ih ∈ˢ R.M 1 a → R.mkP a ih ∈ˢ R.M 0 (S.injP 0 [a])
  /-- `Array.mk`. -/
  mkA : ∀ l ih, l ∈ˢ carLL S → ih ∈ˢ R.M 2 l → R.mkA l ih ∈ˢ R.M 1 (S.injA 0 [l])
  /-- `List.nil` at `List P3`. -/
  nilLL : R.nilLL ∈ˢ R.M 2 (S.injL 0 [])
  /-- `List.cons` at `List P3`. -/
  consLL : ∀ h t ih₁ ih₂, h ∈ˢ carL S → t ∈ˢ carLL S → ih₁ ∈ˢ R.M 3 h → ih₂ ∈ˢ R.M 2 t →
    R.consLL h t ih₁ ih₂ ∈ˢ R.M 2 (S.injL 1 [h, t])
  /-- `List.nil` at `P3`. -/
  nilL : R.nilL ∈ˢ R.M 3 (S.injL 0 [])
  /-- `List.cons` at `P3`. -/
  consL : ∀ h t ih₁ ih₂, h ∈ˢ carP S → t ∈ˢ carL S → ih₁ ∈ˢ R.M 0 h → ih₂ ∈ˢ R.M 3 t →
    R.consL h t ih₁ ih₂ ∈ˢ R.M 3 (S.injL 1 [h, t])

/-- The index set of the recursion: the disjoint union of the four
components' values. -/
noncomputable def blkIdx (S : P3Sig V) : V := unionSet 4 uIs (car S)

theorem tagged_mem_blkIdx {c : Nat} (hc : c < 4) {x : V} (hx : x ∈ˢ app (car S c) pt) :
    tagged c pt x ∈ˢ blkIdx S := tagged_mem_unionSet hc pt_mem_unitSet hx

theorem mem_blkIdx {u : V} :
    u ∈ˢ blkIdx S ↔ ∃ c, c < 4 ∧ ∃ x, x ∈ˢ app (car S c) pt ∧ u = tagged c pt x := by
  unfold blkIdx
  rw [mem_unionSet]
  constructor
  · rintro ⟨c, hc, i, hi, x, hx, rfl⟩
    obtain rfl := mem_unitSet_iff.mp hi
    exact ⟨c, hc, x, hx, rfl⟩
  · rintro ⟨c, hc, x, hx, rfl⟩
    exact ⟨c, hc, pt, pt_mem_unitSet, x, hx, rfl⟩

/-- The predecessor relation, read off the six constructors. -/
def BlkRel (S : P3Sig V) (u v : V) : Prop :=
  (∃ a, u = tagged 0 pt (S.injP 0 [a]) ∧ v = tagged 1 pt a) ∨
  (∃ l, u = tagged 1 pt (S.injA 0 [l]) ∧ v = tagged 2 pt l) ∨
  (∃ h t, u = tagged 2 pt (S.injL 1 [h, t]) ∧ (v = tagged 3 pt h ∨ v = tagged 2 pt t)) ∨
  (∃ h t, u = tagged 3 pt (S.injL 1 [h, t]) ∧ (v = tagged 0 pt h ∨ v = tagged 3 pt t))

/-- The predecessor sets. -/
noncomputable def blkPred (S : P3Sig V) (u : V) : V := relPred (blkIdx S) (BlkRel S) u

theorem blkPred_subset (S : P3Sig V) (u : V) : blkPred S u ⊆ˢ blkIdx S := relPred_subset _ _ u

theorem mem_blkPred {u v : V} : v ∈ˢ blkPred S u ↔ v ∈ˢ blkIdx S ∧ BlkRel S u v := mem_relPred

section Decompose

variable (hS : P3Ok S) (hw : S.w ≠ 0)

include hS hw

theorem mem_blkPred_mkP {a v : V} :
    v ∈ˢ blkPred S (tagged 0 pt (S.injP 0 [a])) ↔ v ∈ˢ blkIdx S ∧ v = tagged 1 pt a := by
  rw [mem_blkPred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inl ⟨a, rfl, h⟩⟩
  rcases h with ⟨a', h₁, h₂⟩ | ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
  · rw [h₂, hS.mem.mkInj hw a a' (tagged_inj h₁).2.2]
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)

theorem mem_blkPred_mkA {l v : V} :
    v ∈ˢ blkPred S (tagged 1 pt (S.injA 0 [l])) ↔ v ∈ˢ blkIdx S ∧ v = tagged 2 pt l := by
  rw [mem_blkPred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inr (Or.inl ⟨l, rfl, h⟩)⟩
  rcases h with ⟨_, h₁, -⟩ | ⟨l', h₁, h₂⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · obtain ⟨-, he⟩ := hS.arr.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
    obtain ⟨rfl, -⟩ := List.cons.inj he
    exact h₂
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)

theorem not_mem_blkPred_nilLL {v : V} : ¬ v ∈ˢ blkPred S (tagged 2 pt (S.injL 0 [])) := by
  intro h
  rcases (mem_blkPred.mp h).2 with ⟨_, h₁, -⟩ | ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)

theorem not_mem_blkPred_nilL {v : V} : ¬ v ∈ˢ blkPred S (tagged 3 pt (S.injL 0 [])) := by
  intro h
  rcases (mem_blkPred.mp h).2 with ⟨_, h₁, -⟩ | ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2).1 (by omega)

theorem mem_blkPred_consLL {h t v : V} :
    v ∈ˢ blkPred S (tagged 2 pt (S.injL 1 [h, t])) ↔
      v ∈ˢ blkIdx S ∧ (v = tagged 3 pt h ∨ v = tagged 2 pt t) := by
  rw [mem_blkPred]
  refine and_congr_right fun _ =>
    ⟨fun hv => ?_, fun hv => Or.inr (Or.inr (Or.inl ⟨h, t, rfl, hv⟩))⟩
  rcases hv with ⟨_, h₁, -⟩ | ⟨_, h₁, -⟩ | ⟨h', t', h₁, h₂⟩ | ⟨_, _, h₁, -⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)
  · obtain ⟨-, he⟩ := hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
    obtain ⟨rfl, he'⟩ := List.cons.inj he
    obtain ⟨rfl, -⟩ := List.cons.inj he'
    exact h₂
  · exact absurd (tagged_inj h₁).1 (by omega)

theorem mem_blkPred_consL {h t v : V} :
    v ∈ˢ blkPred S (tagged 3 pt (S.injL 1 [h, t])) ↔
      v ∈ˢ blkIdx S ∧ (v = tagged 0 pt h ∨ v = tagged 3 pt t) := by
  rw [mem_blkPred]
  refine and_congr_right fun _ =>
    ⟨fun hv => ?_, fun hv => Or.inr (Or.inr (Or.inr ⟨h, t, rfl, hv⟩))⟩
  rcases hv with ⟨_, h₁, -⟩ | ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨h', t', h₁, h₂⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (tagged_inj h₁).1 (by omega)
  · obtain ⟨-, he⟩ := hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
    obtain ⟨rfl, he'⟩ := List.cons.inj he
    obtain ⟨rfl, -⟩ := List.cons.inj he'
    exact h₂

/-- **The predecessors come from the argument tuple.** -/
theorem blkPred_predsFrom : PredsFrom S.w 4 uIs (blkΨ S) (blkPred S) := by
  intro X hX hXle c hc i hi x hx v hv
  obtain rfl := mem_unitSet_iff.mp hi
  obtain ⟨-, hrel⟩ := mem_relPred.mp hv
  rw [app_blkΨ] at hx
  match c, hc with
  | 0, _ =>
    obtain ⟨a, ha, rfl⟩ := mem_blkFib_zero.mp hx
    rcases hrel with ⟨a', h₁, rfl⟩ | ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
    · obtain rfl := hS.mem.mkInj hw a a' (tagged_inj h₁).2.2
      exact tagged_mem_unionSet (by omega) pt_mem_unitSet ha
    · exact absurd (tagged_inj h₁).1 (by omega)
    · exact absurd (tagged_inj h₁).1 (by omega)
    · exact absurd (tagged_inj h₁).1 (by omega)
  | 1, _ =>
    obtain ⟨l, hl, rfl⟩ := mem_blkFib_one.mp hx
    rcases hrel with ⟨_, h₁, -⟩ | ⟨l', h₁, rfl⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
    · exact absurd (tagged_inj h₁).1 (by omega)
    · obtain ⟨-, he⟩ := hS.arr.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
      obtain ⟨rfl, -⟩ := List.cons.inj he
      exact tagged_mem_unionSet (by omega) pt_mem_unitSet hl
    · exact absurd (tagged_inj h₁).1 (by omega)
    · exact absurd (tagged_inj h₁).1 (by omega)
  | 2, _ =>
    rcases mem_blkFib_two.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · rcases hrel with ⟨_, h₁, -⟩ | ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
      · exact absurd (tagged_inj h₁).1 (by omega)
      · exact absurd (tagged_inj h₁).1 (by omega)
      · exact absurd (hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2).1 (by omega)
      · exact absurd (tagged_inj h₁).1 (by omega)
    · rcases hrel with ⟨_, h₁, -⟩ | ⟨_, h₁, -⟩ | ⟨h', t', h₁, h₂⟩ | ⟨_, _, h₁, -⟩
      · exact absurd (tagged_inj h₁).1 (by omega)
      · exact absurd (tagged_inj h₁).1 (by omega)
      · obtain ⟨-, he⟩ := hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
        obtain ⟨rfl, he'⟩ := List.cons.inj he
        obtain ⟨rfl, -⟩ := List.cons.inj he'
        rcases h₂ with rfl | rfl
        · exact tagged_mem_unionSet (by omega) pt_mem_unitSet hh
        · exact tagged_mem_unionSet (by omega) pt_mem_unitSet ht
      · exact absurd (tagged_inj h₁).1 (by omega)
  | 3, _ =>
    rcases mem_blkFib_three.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · rcases hrel with ⟨_, h₁, -⟩ | ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨_, _, h₁, -⟩
      · exact absurd (tagged_inj h₁).1 (by omega)
      · exact absurd (tagged_inj h₁).1 (by omega)
      · exact absurd (tagged_inj h₁).1 (by omega)
      · exact absurd (hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2).1 (by omega)
    · rcases hrel with ⟨_, h₁, -⟩ | ⟨_, h₁, -⟩ | ⟨_, _, h₁, -⟩ | ⟨h', t', h₁, h₂⟩
      · exact absurd (tagged_inj h₁).1 (by omega)
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
noncomputable def blkSt (S : P3Sig V) (R : RecData V) (u g : V) : V :=
  if h : ∃ a, u = tagged 0 pt (S.injP 0 [a]) then
    R.mkP h.choose (app g (tagged 1 pt h.choose))
  else if h : ∃ l, u = tagged 1 pt (S.injA 0 [l]) then
    R.mkA h.choose (app g (tagged 2 pt h.choose))
  else if u = tagged 2 pt (S.injL 0 []) then R.nilLL
  else if h : ∃ q : V × V, u = tagged 2 pt (S.injL 1 [q.1, q.2]) then
    R.consLL h.choose.1 h.choose.2 (app g (tagged 3 pt h.choose.1))
      (app g (tagged 2 pt h.choose.2))
  else if u = tagged 3 pt (S.injL 0 []) then R.nilL
  else if h : ∃ q : V × V, u = tagged 3 pt (S.injL 1 [q.1, q.2]) then
    R.consL h.choose.1 h.choose.2 (app g (tagged 0 pt h.choose.1))
      (app g (tagged 3 pt h.choose.2))
  else empty

section StEq

variable (hS : P3Ok S) (hw : S.w ≠ 0)

include hS hw

theorem blkSt_mkP (a g : V) :
    blkSt S R (tagged 0 pt (S.injP 0 [a])) g = R.mkP a (app g (tagged 1 pt a)) := by
  unfold blkSt
  rw [dif_pos ⟨a, rfl⟩]
  have h := Exists.choose_spec
    (⟨a, rfl⟩ : ∃ y, (tagged 0 pt (S.injP 0 [a]) : V) = tagged 0 pt (S.injP 0 [y]))
  rw [← hS.mem.mkInj hw _ _ (tagged_inj h).2.2]

theorem blkSt_mkA (l g : V) :
    blkSt S R (tagged 1 pt (S.injA 0 [l])) g = R.mkA l (app g (tagged 2 pt l)) := by
  unfold blkSt
  rw [dif_neg (fun ⟨_, h⟩ => Nat.one_ne_zero (tagged_inj h).1), dif_pos ⟨l, rfl⟩]
  have h := Exists.choose_spec
    (⟨l, rfl⟩ : ∃ y, (tagged 1 pt (S.injA 0 [l]) : V) = tagged 1 pt (S.injA 0 [y]))
  obtain ⟨-, he⟩ := hS.arr.mkInj hw _ _ _ _ (tagged_inj h).2.2
  obtain ⟨he', -⟩ := List.cons.inj he
  rw [← he']

omit hS hw in
theorem blkSt_nilLL (g : V) : blkSt S R (tagged 2 pt (S.injL 0 [])) g = R.nilLL := by
  unfold blkSt
  rw [dif_neg (fun ⟨_, h⟩ => by exact absurd (tagged_inj h).1 (by omega)),
    dif_neg (fun ⟨_, h⟩ => by exact absurd (tagged_inj h).1 (by omega)), if_pos rfl]

theorem blkSt_consLL (h t g : V) :
    blkSt S R (tagged 2 pt (S.injL 1 [h, t])) g
      = R.consLL h t (app g (tagged 3 pt h)) (app g (tagged 2 pt t)) := by
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

omit hS hw in
theorem blkSt_nilL (g : V) : blkSt S R (tagged 3 pt (S.injL 0 [])) g = R.nilL := by
  unfold blkSt
  rw [dif_neg (fun ⟨_, h⟩ => by exact absurd (tagged_inj h).1 (by omega)),
    dif_neg (fun ⟨_, h⟩ => by exact absurd (tagged_inj h).1 (by omega)),
    if_neg (fun h => by exact absurd (tagged_inj h).1 (by omega)),
    dif_neg (fun ⟨_, h⟩ => by exact absurd (tagged_inj h).1 (by omega)), if_pos rfl]

theorem blkSt_consL (h t g : V) :
    blkSt S R (tagged 3 pt (S.injL 1 [h, t])) g
      = R.consL h t (app g (tagged 0 pt h)) (app g (tagged 3 pt t)) := by
  unfold blkSt
  rw [dif_neg (fun ⟨_, h'⟩ => by exact absurd (tagged_inj h').1 (by omega)),
    dif_neg (fun ⟨_, h'⟩ => by exact absurd (tagged_inj h').1 (by omega)),
    if_neg (fun h' => by exact absurd (tagged_inj h').1 (by omega)),
    dif_neg (fun ⟨_, h'⟩ => by exact absurd (tagged_inj h').1 (by omega)),
    if_neg (fun h' => absurd (hS.list.mkInj hw _ _ _ _ (tagged_inj h').2.2).1 (by omega)),
    dif_pos ⟨(h, t), rfl⟩]
  have hs := Exists.choose_spec
    (⟨(h, t), rfl⟩ :
      ∃ q : V × V, (tagged 3 pt (S.injL 1 [h, t]) : V) = tagged 3 pt (S.injL 1 [q.1, q.2]))
  obtain ⟨-, he⟩ := hS.list.mkInj hw _ _ _ _ (tagged_inj hs).2.2
  obtain ⟨h₁, he'⟩ := List.cons.inj he
  obtain ⟨h₂, -⟩ := List.cons.inj he'
  rw [← h₁, ← h₂]

end StEq

/-! ### The kit -/

section Kit

variable (hS : P3Ok S) (hw : S.w ≠ 0) (hR : RecOk S ℓ R)

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
    obtain ⟨a, ha, rfl⟩ := (mem_carP hS).mp hx
    rw [blkSt_mkP hS hw, blkB_at]
    have h := hval (tagged 1 pt a)
      ((mem_blkPred_mkP hS hw).mpr ⟨tagged_mem_blkIdx (by omega) ha, rfl⟩)
    rw [blkB_at] at h
    exact hR.mkP a _ ha h
  | 1, _ =>
    obtain ⟨l, hl, rfl⟩ := (mem_carA hS).mp hx
    rw [blkSt_mkA hS hw, blkB_at]
    have h := hval (tagged 2 pt l)
      ((mem_blkPred_mkA hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hl, rfl⟩)
    rw [blkB_at] at h
    exact hR.mkA l _ hl h
  | 2, _ =>
    rcases (mem_carLL hS).mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · rw [blkSt_nilLL, blkB_at]; exact hR.nilLL
    · rw [blkSt_consLL hS hw, blkB_at]
      have h₁ := hval (tagged 3 pt h)
        ((mem_blkPred_consLL hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hh, Or.inl rfl⟩)
      have h₂ := hval (tagged 2 pt t)
        ((mem_blkPred_consLL hS hw).mpr ⟨tagged_mem_blkIdx (by omega) ht, Or.inr rfl⟩)
      rw [blkB_at] at h₁ h₂
      exact hR.consLL h t _ _ hh ht h₁ h₂
  | 3, _ =>
    rcases (mem_carL hS).mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · rw [blkSt_nilL, blkB_at]; exact hR.nilL
    · rw [blkSt_consL hS hw, blkB_at]
      have h₁ := hval (tagged 0 pt h)
        ((mem_blkPred_consL hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hh, Or.inl rfl⟩)
      have h₂ := hval (tagged 3 pt t)
        ((mem_blkPred_consL hS hw).mpr ⟨tagged_mem_blkIdx (by omega) ht, Or.inr rfl⟩)
      rw [blkB_at] at h₁ h₂
      exact hR.consL h t _ _ hh ht h₁ h₂

/-- **The block's recursion kit** at `N = 4` components. -/
noncomputable def blkKit : UnionRecKit ℓ S.w 4 uIs (blkΨ S) :=
  ⟨blkPred S, blkB R.M, blkSt S R, blkPred_predsFrom hS hw, blkB_mem_univ hR,
    blkSt_mem hS hw hR⟩

local notation "K*" => blkKit hS hw hR

@[simp] theorem blkKit_pred : (K*).pred = blkPred S := rfl
@[simp] theorem blkKit_B : (K*).B = blkB R.M := rfl
@[simp] theorem blkKit_st : (K*).st = blkSt S R := rfl

theorem blkKit_recAt (c : Nat) (i x : V) :
    (K*).recAt c i x
      = recSel (recGraph ℓ (blkIdx S) (blkPred S) (blkB R.M) (blkSt S R)) (tagged c i x) := rfl

/-- The recursor at a component: `P3.rec` at `0`, `P3.rec_1..3` at
`1, 2, 3` — official's four motives. -/
noncomputable def recAt (c : Nat) (x : V) : V := (blkKit hS hw hR).recAt c pt x

include hS hw hR in
/-- **Typing**: the recursor's value is in the component's motive. -/
theorem recAt_mem {c : Nat} (hc : c < 4) {x : V} (hx : x ∈ˢ app (car S c) pt) :
    recAt hS hw hR c x ∈ˢ R.M c x := by
  have h := (K*).rec_mem_B (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS) hc
    (show (pt : V) ∈ˢ uIs c from pt_mem_unitSet) hx
  rw [blkKit_B, blkB_at] at h
  exact h

include hS hw hR in
theorem blkRec_eq {c : Nat} (hc : c < 4) {x : V} (hx : x ∈ˢ app (car S c) pt) :
    (K*).recAt c pt x
      = blkSt S R (tagged c pt x)
          (graph (fun j => recSel (recGraph ℓ (blkIdx S) (blkPred S) (blkB R.M) (blkSt S R)) j)
            (blkPred S (tagged c pt x))) :=
  (K*).rec_eq (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS) hc
    (show (pt : V) ∈ˢ uIs c from pt_mem_unitSet) hx

/-! ### The ι rules, one per constructor

The four crossing rules official prints for `P3` (`DESIGN-theory.md`
§5's `P3` row) are `rec_mk` (`P3.mk`, to component `1`), `rec_mkA`
(`Array.mk`'s ordinary field, to component `2`), `rec_consLL`
(`List.cons` at `List P3`: head to `3`, tail to `2`) and `rec_consL`
(`List.cons` at `P3`: head to `0`, tail to `3`). -/

include hS hw hR in
/-- ι 1 — `P3.rec … (P3.mk a) = mkP a (P3.rec_1 … a)`. -/
theorem rec_mkP {a : V} (ha : a ∈ˢ carA S) :
    recAt hS hw hR 0 (S.injP 0 [a]) = R.mkP a (recAt hS hw hR 1 a) := by
  show (K*).recAt 0 pt (S.injP 0 [a]) = R.mkP a ((K*).recAt 1 pt a)
  rw [blkRec_eq hS hw hR (show (0:Nat) < 4 by omega) ((mem_carP hS).mpr ⟨a, ha, rfl⟩),
    blkSt_mkP hS hw,
    app_graph ((mem_blkPred_mkP hS hw).mpr ⟨tagged_mem_blkIdx (by omega) ha, rfl⟩),
    blkKit_recAt]

include hS hw hR in
/-- ι 2 — `P3.rec_1 … (Array.mk l) = mkA l (P3.rec_2 … l)`: the
ORDINARY field of `Array` that became an instance component. -/
theorem rec_mkA {l : V} (hl : l ∈ˢ carLL S) :
    recAt hS hw hR 1 (S.injA 0 [l]) = R.mkA l (recAt hS hw hR 2 l) := by
  show (K*).recAt 1 pt (S.injA 0 [l]) = R.mkA l ((K*).recAt 2 pt l)
  rw [blkRec_eq hS hw hR (show (1:Nat) < 4 by omega) ((mem_carA hS).mpr ⟨l, hl, rfl⟩),
    blkSt_mkA hS hw,
    app_graph ((mem_blkPred_mkA hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hl, rfl⟩),
    blkKit_recAt]

include hS hw hR in
/-- ι 3 — `P3.rec_2 … nil = nilLL`. -/
theorem rec_nilLL : recAt hS hw hR 2 (S.injL 0 []) = R.nilLL := by
  show (K*).recAt 2 pt (S.injL 0 []) = R.nilLL
  rw [blkRec_eq hS hw hR (show (2:Nat) < 4 by omega) ((mem_carLL hS).mpr (Or.inl rfl)),
    blkSt_nilLL]

include hS hw hR in
/-- ι 4 — `P3.rec_2 … (List.cons h t) = consLL h t (P3.rec_3 … h) (P3.rec_2 … t)`:
`List.cons` AT THE PIN `List P3`, the rule whose head crosses to the
rank-0 group's component. -/
theorem rec_consLL {h t : V} (hh : h ∈ˢ carL S) (ht : t ∈ˢ carLL S) :
    recAt hS hw hR 2 (S.injL 1 [h, t])
      = R.consLL h t (recAt hS hw hR 3 h) (recAt hS hw hR 2 t) := by
  show (K*).recAt 2 pt (S.injL 1 [h, t])
    = R.consLL h t ((K*).recAt 3 pt h) ((K*).recAt 2 pt t)
  rw [blkRec_eq hS hw hR (show (2:Nat) < 4 by omega)
      ((mem_carLL hS).mpr (Or.inr ⟨h, t, hh, ht, rfl⟩)),
    blkSt_consLL hS hw,
    app_graph ((mem_blkPred_consLL hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hh, Or.inl rfl⟩),
    app_graph ((mem_blkPred_consLL hS hw).mpr ⟨tagged_mem_blkIdx (by omega) ht, Or.inr rfl⟩),
    blkKit_recAt, blkKit_recAt]

include hS hw hR in
/-- ι 5 — `P3.rec_3 … nil = nilL`. -/
theorem rec_nilL : recAt hS hw hR 3 (S.injL 0 []) = R.nilL := by
  show (K*).recAt 3 pt (S.injL 0 []) = R.nilL
  rw [blkRec_eq hS hw hR (show (3:Nat) < 4 by omega) ((mem_carL hS).mpr (Or.inl rfl)),
    blkSt_nilL]

include hS hw hR in
/-- ι 6 — `P3.rec_3 … (List.cons h t) = consL h t (P3.rec … h) (P3.rec_3 … t)`:
`List.cons` AT THE PIN `P3`, the rule whose head crosses to the
member. -/
theorem rec_consL {h t : V} (hh : h ∈ˢ carP S) (ht : t ∈ˢ carL S) :
    recAt hS hw hR 3 (S.injL 1 [h, t])
      = R.consL h t (recAt hS hw hR 0 h) (recAt hS hw hR 3 t) := by
  show (K*).recAt 3 pt (S.injL 1 [h, t])
    = R.consL h t ((K*).recAt 0 pt h) ((K*).recAt 3 pt t)
  rw [blkRec_eq hS hw hR (show (3:Nat) < 4 by omega)
      ((mem_carL hS).mpr (Or.inr ⟨h, t, hh, ht, rfl⟩)),
    blkSt_consL hS hw,
    app_graph ((mem_blkPred_consL hS hw).mpr ⟨tagged_mem_blkIdx (by omega) hh, Or.inl rfl⟩),
    app_graph ((mem_blkPred_consL hS hw).mpr ⟨tagged_mem_blkIdx (by omega) ht, Or.inr rfl⟩),
    blkKit_recAt, blkKit_recAt]

end Kit

end Rec

/-! ## What the clause must record (the F1 record)

1. **(F1-1) An instance component's injections must be recorded.**
   §1.2's `ctor` clause is "members only", so the tags of a component
   that is the container's own copy of an inner container are tied to
   nothing.  Component `2` here (`List (List P3)`, `Array`'s table
   component `1` at the pin) carries `List`'s tags, and official's
   `P3.rec_2` fires on `List.cons`; without the tie, `rec_consLL`
   cannot be stated.  In this file the tie is the shared `injL`
   argument of `ArrayClause` and `ListClause`.  `BlockModelAt` must
   record, per instance component `c` with key `(C', Ds')`,
   `inj ψ c j fs = ⟦C'.ctor_j⟧ ⟦Ds'⟧^ord fs`.

2. **(F1-2) An instance component's READING must be recorded** if
   §2.4's claim is to be stated at `c ≠ 0` of a group.  That is
   `ArrayClause.instLeaf`; it is what `Array`'s own install proved
   (F0's theorem at `Array`'s block).  Only `car_two_eq` consumes it —
   the load-bearing half of the finding is (F1-1).

3. **(F1-3) The rank order is needed for the STATEMENT, not for the
   proof of the step.**  `car_seg_eq` — the rank-1 identification —
   uses only `carL_mem_univ` (`famSpace_app`, three lines) to put the
   pin's value in `Array`'s `Sat` domain; the rank-0 identification
   enters only when the claim is *expressed* in ordinary-reading form
   (`car_one_eq`, `car_two_eq`).  With INDEXED pins the `hIs` premise
   of `lfpTuple_seg_congr` would consume the lower-rank claim as well;
   unindexed, it is `rfl`.

4. **(F1-4) The shapes for (W) must distinguish the same container
   constructor at different components.**  `List.cons` occurs at
   components `2` and `3` with different targets, and
   `tupleContainer_closed_exists` reads `B`/`tgtM` off the shape
   alone: a per-container shape set is not enough, the generator must
   tag shapes by (component, constructor).  This sharpens
   `F0-REPORT.md`'s point (2) — there the collision could not yet
   arise. -/

end P3Block

end ConLeche.SetTheory
