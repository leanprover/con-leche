module

public import ConLeche.SetModel.WfRec
public import ConLeche.SetModel.Iter
import ConLeche.SetModel.TupleContainer
@[expose] public section

/-!
# `Tree ::= node (List Tree)` NARROW, with ∈-recursion (falsifier F5)

The maintainer's formulation of nested inductives (2026-09-21),
falsified at the set level on the same block the WIDE falsifiers took
(F0–F4, retired at DESIGN 2026-09-21's flip: this file carries their
clause, minors, transient bound and standard model itself, D-e):

* **(ii) the block's meaning is the NARROW least fixed point**

      ⟦Tree⟧ = T* = lfp (X ↦ { node l | l ∈ ⟦List⟧ X })

  where the container's carrier at the hole is read ORDINARILY through
  its recorded env clause (`ListClause` below).  The wide tuple — the
  block plus a COPY of the container, official's auxiliary block — is
  **not recorded and not identified with anything**: there is no
  second component of the carrier, no `lfpTuple` at width ≥ 2, no
  `lfpTuple_seg_congr`, no `L 1 = ⟦List⟧ (L 0)`.  The copy's carrier
  of the wide route is here simply `⟦List⟧ T*` — a *derived* set,
  equal to nothing by fiat.  (The two-component operator IS built once,
  below, as a transient BOUND for the infinitary case — D-b — and
  discarded: nothing reads it and no fixed point of it is taken.)

* **(i)/(iii) recursion is ∈-recursion on the GLOBAL subterm relation**
  over the tagged union of the two majors' ORDINARY carriers
  (`ConLeche/SetModel/WfRec.lean`): predecessors are the ∈-smaller
  members of the union, accessibility is regularity, and the kit
  assumes nothing of the carriers but that they are sets.

What this costs, against the wide route, is recorded at the two
`-- F5 FINDING:` markers: the clause must record the constructor **encoding's depth**
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

open Tower (natFibre natFibre_vnat)

/-! ## The block's datum, the container's env clause, the member's tags

These are the falsifier's HYPOTHESES, and they are this file's own
(decision D-e, DESIGN 2026-09-21): the wide-tuple falsifiers F0–F4,
which first stated them, are retired, so F5 carries its clause, its
minors, its transient bound and its standard model itself and imports
no other falsifier.  Nothing below is specific to the wide route: the
clause is `DESIGN-theory.md` §1.2's `BlockModelAt` at a one-member,
non-indexed, non-parametric-index container, and the tag laws are the
member's `mkZero`/`mkInj` plus formation. -/

/-! ## Two small facts about `univ` -/

/-- Application stays inside a universe: `app` is a union of a
separation of a double union. -/
theorem app_mem_univ {w : Nat} (hw : w ≠ 0) {g : V} (hg : g ∈ˢ (univ w : V)) (p : V) :
    app g p ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  unfold app
  split
  · exact hU.pt_mem hg
  · exact hU.sUnion_mem (hU.sep_mem (hU.sUnion_mem (hU.sUnion_mem hg)))

theorem pt_mem_univ {w : Nat} (hw : w ≠ 0) : (pt : V) ∈ˢ (univ w : V) :=
  (univ_isTGUniverse (V := V) hw).transitive (unitSet_mem_univ w) pt_mem_unitSet

/-! ## The index sets

`Tree` and `List` are both unindexed: every component's index set is
the one-point set, and every index tuple is `pt`. -/

/-- The index sets of a block of unindexed components. -/
noncomputable def uIs : Nat → V := fun _ => unitSet

@[simp] theorem uIs_apply (n : Nat) : (uIs n : V) = unitSet := rfl

/-! ## The container's env clause

What a LATER block reads about a stored container.  This is
`DESIGN-theory.md` §1.2's `BlockModelAt` at `N = 1` (`List` has one
member and no container instances of its own), no parameters beyond
the one type parameter `α`, and no indices:

* `leaf` — the recorded reading `LIST α` IS the one-component least
  tuple of the container's operator at `α`;
* `mono`/`maps`/`closed` — the `functor` clause;
* `fibre` — the constructor decomposition, in terms of the container's
  OWN injections `injL` (member-local tags);
* `mkZero`/`mkInj`.

Nothing here mentions trees: the clause is about `List` alone, at an
arbitrary parameter in its `Sat` domain `univ w`. -/
structure ListClause (w : Nat) (LIST : V → V) (ΨL : V → (Nat → V) → Nat → V)
    (injL : Nat → List V → V) : Prop where
  /-- `leaf`: the stored reading is the one-component least tuple. -/
  leaf : ∀ α, α ∈ˢ (univ w : V) → LIST α = lfpTuple w 1 uIs (ΨL α) 0
  /-- `functor`, monotonicity. -/
  mono : ∀ α, α ∈ˢ (univ w : V) → MonoTuple w 1 uIs (ΨL α)
  /-- `functor`, space preservation. -/
  maps : ∀ α, α ∈ˢ (univ w : V) → MapsTuple w 1 uIs (ΨL α)
  /-- `functor`, the closed tuple. -/
  closed : ∀ α, α ∈ˢ (univ w : V) → ∃ L, IsClosedTuple w 1 uIs (ΨL α) L
  /-- `fibre`: the constructor decomposition of the operator's values,
  at every tuple of the space and every parameter in the domain. -/
  fibre : ∀ α, α ∈ˢ (univ w : V) → ∀ Y, InTupleSpace w 1 uIs Y → ∀ t, t ∈ˢ (unitSet : V) →
    ∀ x, x ∈ˢ app (ΨL α Y 0) t ↔
      (x = injL 0 [] ∨ ∃ h, h ∈ˢ α ∧ ∃ t', t' ∈ˢ app (Y 0) pt ∧ x = injL 1 [h, t'])
  /-- `mkZero`: at a `Prop` container every value is the proof point. -/
  mkZero : w = 0 → ∀ j fs, injL j fs = (pt : V)
  /-- `mkInj`: above `Prop` the injections of ONE component are
  injective in the constructor tag and the fields together. -/
  mkInj : w ≠ 0 → ∀ j j' fs fs', injL j fs = injL j' fs' → j = j' ∧ fs = fs'

namespace ListClause

variable {w : Nat} {LIST : V → V} {ΨL : V → (Nat → V) → Nat → V} {injL : Nat → List V → V}

/-- A value built by the container's operator is a set of the
container's level — read off `maps` and `fibre`, at a parameter and a
tuple chosen to hold exactly the fields wanted.  This is how the
clause supplies the FORMATION of the copy's values: no extra clause is
needed. -/
theorem inj_mem_univ_of (hC : ListClause w LIST ΨL injL) (hw : w ≠ 0) {α : V}
    (hα : α ∈ˢ (univ w : V)) {Y : Nat → V} (hY : InTupleSpace w 1 uIs Y) {x : V}
    (hx : x = injL 0 [] ∨ ∃ h, h ∈ˢ α ∧ ∃ t', t' ∈ˢ app (Y 0) pt ∧ x = injL 1 [h, t']) :
    x ∈ˢ (univ w : V) :=
  (univ_isTGUniverse (V := V) hw).transitive
    (famSpace_app (hC.maps α hα Y hY 0 Nat.one_pos) pt_mem_unitSet)
    ((hC.fibre α hα Y hY pt pt_mem_unitSet x).mpr hx)

/-- `nil`'s value is a set of the container's level. -/
theorem nil_mem_univ (hC : ListClause w LIST ΨL injL) (hw : w ≠ 0) :
    injL 0 [] ∈ˢ (univ w : V) :=
  hC.inj_mem_univ_of hw (unitSet_mem_univ (V := V) w)
    (Y := fun _ => graph (fun _ => empty) unitSet)
    (fun _ _ => graph_mem_famSpace fun _ _ => empty_mem_univ w) (Or.inl rfl)

/-- `cons`'s value is a set of the container's level. -/
theorem cons_mem_univ (hC : ListClause w LIST ΨL injL) (hw : w ≠ 0) {h t : V}
    (hh : h ∈ˢ (univ w : V)) (ht : t ∈ˢ (univ w : V)) : injL 1 [h, t] ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  refine hC.inj_mem_univ_of hw (α := sing h) (hU.sing_mem hh hh)
    (Y := fun _ => graph (fun _ => sing t) unitSet)
    (fun _ _ => graph_mem_famSpace fun _ _ => hU.sing_mem ht ht) (Or.inr ⟨h, mem_sing.mpr rfl, t, ?_, rfl⟩)
  rw [app_graph pt_mem_unitSet]
  exact mem_sing.mpr rfl

end ListClause

/-! ## The member's own tags

`Tree.node`'s injection is the block's own datum (`mkZero`/`mkInj` of
`DESIGN-theory.md` §1.2 at component `0`); the falsifier keeps it
abstract under exactly those two laws plus formation, and exhibits a
witness (`stdInj`) so that nothing here is vacuous. -/
structure TreeTags (w : Nat) (injT : Nat → List V → V) : Prop where
  /-- Formation above `Prop`. -/
  memU : w ≠ 0 → ∀ l, l ∈ˢ (univ w : V) → injT 0 [l] ∈ˢ (univ w : V)
  /-- `mkZero`. -/
  mkZero : w = 0 → ∀ j fs, injT j fs = (pt : V)
  /-- `mkInj`, at the one constructor. -/
  mkInj : w ≠ 0 → ∀ l l', injT 0 [l] = injT 0 [l'] → l = l'

/-- A tuple of values as a `kpair` tower. -/
noncomputable def kTuple : List V → V
  | [] => pt
  | x :: xs => kpair x (kTuple xs)

open Classical in
/-- A witness for `TreeTags`: the tagged tower above `Prop`, the proof
point at `Prop`. -/
noncomputable def stdInj (w : Nat) (j : Nat) (fs : List V) : V :=
  if w = 0 then pt else kpair (vnat j) (kTuple fs)

theorem treeTags_stdInj (w : Nat) : TreeTags w (stdInj (V := V) w) := by
  refine ⟨fun hw l hl => ?_, fun hw j fs => ?_, fun hw l l' h => ?_⟩
  · have hU := univ_isTGUniverse (V := V) hw
    unfold stdInj
    rw [if_neg hw]
    exact hU.kpair_mem hl (vnat_mem_univ_pos hw 0)
      (hU.kpair_mem hl hl (pt_mem_univ hw))
  · unfold stdInj
    rw [if_pos hw]
  · unfold stdInj at h
    rw [if_neg hw, if_neg hw] at h
    exact (kpair_inj (kpair_inj h).2).1

/-! ## The block's datum and its two-component operator -/

/-- The data this file reasons about: the container's recorded reading and
operator, the container's injections, and the member's. -/
structure TreeListSig (V : Type u) [SetTheory V] where
  /-- The value level — ONE level: the sort gate makes the container's
  the block's (`DESIGN-theory.md` §2.5). -/
  w : Nat
  /-- The container's recorded reading `⟦List⟧`, as a family. -/
  LIST : V → V
  /-- The container's own one-component operator at a parameter. -/
  ΨL : V → (Nat → V) → Nat → V
  /-- The container's injections (member-local tags). -/
  injL : Nat → List V → V
  /-- `Tree`'s injections. -/
  injT : Nat → List V → V

/-- The hypotheses: the container's env clause, and the member's tag
laws.  Nothing else. -/
structure TreeListOk (S : TreeListSig V) : Prop where
  /-- The container's env clause, `DESIGN-theory.md` §1.2 at `N = 1`. -/
  list : ListClause S.w S.LIST S.ΨL S.injL
  /-- The member's own `mkZero`/`mkInj`/formation. -/
  tree : TreeTags S.w S.injT

variable {S : TreeListSig V}

/-- Component `0`'s fibre: `{ node l | l ∈ X₁ }`. -/
noncomputable def nodeFib (S : TreeListSig V) (X : Nat → V) : V :=
  image (fun l => S.injT 0 [l]) (app (X 1) pt)

/-- The `nil`/`cons` arm over a head set `A` and a tail set `B`, with
a given family of injections: `{ nil } ∪ { cons h t | h ∈ A, t ∈ B }`.
It serves both the COPY's fibre (heads in the member's component,
tails in the copy's) and, at a parameter, the container's own
operator. -/
noncomputable def consArm (inj : Nat → List V → V) (A B : V) : V :=
  binUnion (sing (inj 0 [])) (image (fun p => inj 1 [sfst p, ssnd p]) (sigmaPairs A fun _ => B))

theorem mem_consArm {inj : Nat → List V → V} {A B x : V} :
    x ∈ˢ consArm inj A B ↔
      x = inj 0 [] ∨ ∃ h t, h ∈ˢ A ∧ t ∈ˢ B ∧ x = inj 1 [h, t] := by
  unfold consArm
  rw [mem_binUnion, mem_sing]
  refine or_congr Iff.rfl ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    obtain ⟨h, hh, t, ht, rfl⟩ := mem_sigmaPairs.mp hp
    rw [sfst_kpair, ssnd_kpair]
    exact ⟨h, t, hh, ht, rfl⟩
  · obtain ⟨h, t, hh, ht, rfl⟩ := hx
    refine mem_image.mpr ⟨kpair h t, mem_sigmaPairs.mpr ⟨h, hh, t, ht, rfl⟩, ?_⟩
    rw [sfst_kpair, ssnd_kpair]

/-- The `nil`/`cons` arm's formation, above `Prop`. -/
theorem consArm_mem_univ {w : Nat} (hw : w ≠ 0) {inj : Nat → List V → V} {A B : V}
    (hA : A ∈ˢ (univ w : V)) (hB : B ∈ˢ (univ w : V))
    (hnil : inj 0 [] ∈ˢ (univ w : V))
    (hcons : ∀ h t, h ∈ˢ (univ w : V) → t ∈ˢ (univ w : V) → inj 1 [h, t] ∈ˢ (univ w : V)) :
    consArm inj A B ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  refine hU.binUnion_mem hnil (hU.sing_mem hnil hnil) ?_
  refine hU.image_mem (hU.sigmaPairs_mem hA fun _ _ => hB) fun p hp => ?_
  obtain ⟨h, hh, t, ht, rfl⟩ := mem_sigmaPairs.mp hp
  rw [sfst_kpair, ssnd_kpair]
  exact hcons h t (hU.transitive hA hh) (hU.transitive hB ht)

/-- Component `1`'s fibre — the abstract COPY of `List` at the pin
`Tree`: `nil : y₁`, `cons : x₀ → y₁ → y₁`, with the CONTAINER's own
injections. -/
noncomputable def listFib (S : TreeListSig V) (X : Nat → V) : V :=
  consArm S.injL (app (X 0) pt) (app (X 1) pt)

/-- **The block's operator**, a plain two-component block operator. -/
noncomputable def blkΨ (S : TreeListSig V) (X : Nat → V) : Nat → V
  | 0 => graph (fun _ => nodeFib S X) unitSet
  | _ + 1 => graph (fun _ => listFib S X) unitSet

theorem app_blkΨ_zero (S : TreeListSig V) (X : Nat → V) :
    app (blkΨ S X 0) pt = nodeFib S X := app_graph pt_mem_unitSet

theorem app_blkΨ_one (S : TreeListSig V) (X : Nat → V) :
    app (blkΨ S X 1) pt = listFib S X := app_graph pt_mem_unitSet

theorem mem_nodeFib {X : Nat → V} {x : V} :
    x ∈ˢ nodeFib S X ↔ ∃ l, l ∈ˢ app (X 1) pt ∧ x = S.injT 0 [l] := mem_image

theorem mem_listFib {X : Nat → V} {x : V} :
    x ∈ˢ listFib S X ↔
      x = S.injL 0 [] ∨
        ∃ h t, h ∈ˢ app (X 0) pt ∧ t ∈ˢ app (X 1) pt ∧ x = S.injL 1 [h, t] := mem_consArm

/-! ## (a) The functor clauses -/

theorem blkΨ_mono (S : TreeListSig V) : MonoTuple S.w 2 uIs (blkΨ S) := by
  intro X Y hX hY hle c hc i hi x hx
  obtain rfl := mem_unitSet_iff.mp hi
  match c, hc with
  | 0, _ =>
    rw [app_blkΨ_zero] at hx ⊢
    obtain ⟨l, hl, rfl⟩ := mem_nodeFib.mp hx
    exact mem_nodeFib.mpr ⟨l, hle 1 (by omega) pt pt_mem_unitSet l hl, rfl⟩
  | 1, _ =>
    rw [app_blkΨ_one] at hx ⊢
    rcases mem_listFib.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · exact mem_listFib.mpr (Or.inl rfl)
    · exact mem_listFib.mpr (Or.inr ⟨h, t, hle 0 (by omega) pt pt_mem_unitSet h hh,
        hle 1 (by omega) pt pt_mem_unitSet t ht, rfl⟩)

theorem blkΨ_fib_mem (hS : TreeListOk S) {X : Nat → V} (hX : InTupleSpace S.w 2 uIs X) :
    nodeFib S X ∈ˢ (univ S.w : V) ∧ listFib S X ∈ˢ (univ S.w : V) := by
  by_cases hw : S.w = 0
  · constructor
    · rw [hw, univ_zero]
      refine mem_univZero.mpr fun x hx => ?_
      obtain ⟨l, -, rfl⟩ := mem_nodeFib.mp hx
      rw [hS.tree.mkZero hw 0 [l]]
      exact pt_mem_unitSet
    · rw [hw, univ_zero]
      refine mem_univZero.mpr fun x hx => ?_
      rcases mem_listFib.mp hx with rfl | ⟨h, t, -, -, rfl⟩
      · rw [hS.list.mkZero hw 0 []]; exact pt_mem_unitSet
      · rw [hS.list.mkZero hw 1 [h, t]]; exact pt_mem_unitSet
  · have hU := univ_isTGUniverse (V := V) hw
    have h0 : app (X 0) pt ∈ˢ (univ S.w : V) := famSpace_app (hX 0 (by omega)) pt_mem_unitSet
    have h1 : app (X 1) pt ∈ˢ (univ S.w : V) := famSpace_app (hX 1 (by omega)) pt_mem_unitSet
    constructor
    · exact hU.image_mem h1 fun l hl => hS.tree.memU hw l (hU.transitive h1 hl)
    · exact consArm_mem_univ hw h0 h1 (hS.list.nil_mem_univ hw)
        fun _ _ hh ht => hS.list.cons_mem_univ hw hh ht

theorem blkΨ_maps (hS : TreeListOk S) : MapsTuple S.w 2 uIs (blkΨ S) := by
  intro X hX c hc
  match c, hc with
  | 0, _ =>
    show graph (fun _ => nodeFib S X) unitSet ∈ˢ famSpace S.w (unitSet : V)
    exact graph_mem_famSpace fun _ _ => (blkΨ_fib_mem hS hX).1
  | 1, _ =>
    show graph (fun _ => listFib S X) unitSet ∈ˢ famSpace S.w (unitSet : V)
    exact graph_mem_famSpace fun _ _ => (blkΨ_fib_mem hS hX).2

/-! ## (b) (W): the closed tuple

Above `Prop` the block is a plain member container — shapes are the
constructor tags (there are no hole-free fields), positions are the
slots — and `tupleContainer_closed_exists` applies with no container
law of `List` beyond the clause's own `fibre`.  At `Prop`,
`closedTuple_zero`. -/

/-! ## The datum's TRANSIENT two-component operator

The one place a wide operator appears, and it appears as a BOUND
(DESIGN 2026-09-21, D-b): `narΨ_closed_of_wide` below solves (W) for
an INFINITARY container by reading the block plus a COPY of the
container as a plain two-component member container, whose closed
tuple exists by `tupleContainer_closed_exists`, and whose component
`0` bounds the narrow operator by leastness.  Nothing is identified
with it, no fixed point of it is taken and no consumer of this file
sees it: it is built here and discarded.  The NARROW carrier below is
`lfpTuple … 1 …`, one component, as the file's headline says. -/

/-- The shapes: `vnat 0` = `node`, `vnat 1` = `nil`, `vnat 2` = `cons`. -/
noncomputable def shp : Nat → V → V
  | 0, _ => sing (vnat 0)
  | _ + 1, _ => upair (vnat 1) (vnat 2)

/-- The positions of a shape, by tag. -/
noncomputable def posN : Nat → V
  | 0 => sing (vnat 0)
  | 2 => upair (vnat 0) (vnat 1)
  | _ => empty

/-- The positions of a shape. -/
noncomputable def posns (a : V) : V := natFibre posN a

theorem posns_vnat (j : Nat) : posns (vnat j : V) = posN j := natFibre_vnat _ j

open Classical in
/-- The target component of a slot: `node`'s field targets the copy,
`cons`'s first field the member and its second the copy. -/
noncomputable def tgtC (a p : V) : Nat :=
  if a = (vnat 0 : V) then 1 else if p = (vnat 0 : V) then 0 else 1

open Classical in
/-- The builder. -/
noncomputable def mkC (S : TreeListSig V) (m : Nat) (a g : V) : V :=
  if m = 0 then S.injT 0 [app g (vnat 0)]
  else if a = (vnat 1 : V) then S.injL 0 []
  else S.injL 1 [app g (vnat 0), app g (vnat 1)]

theorem vnat_ne {j j' : Nat} (h : j ≠ j') : (vnat j : V) ≠ vnat j' := fun he => h (vnat_inj he)

open Classical in
/-- **(W)**: the block's operator has a closed tuple. -/
theorem blkΨ_closed (hS : TreeListOk S) : ∃ L, IsClosedTuple S.w 2 uIs (blkΨ S) L := by
  by_cases hw : S.w = 0
  · rw [hw]
    exact closedTuple_zero (hw ▸ blkΨ_maps hS)
  have hU := univ_isTGUniverse (V := V) hw
  have hv : ∀ j : Nat, (vnat j : V) ∈ˢ (univ S.w : V) := fun j => vnat_mem_univ_pos hw j
  refine tupleContainer_closed_exists hw (Is := uIs) (blkΨ S) (shp) posns tgtC (fun _ _ => pt)
    (mkC S) ?hA ?hB ?htgt ?hmkU ?helim
  case hA =>
    intro m hm i hi
    match m, hm with
    | 0, _ => exact hU.sing_mem (hv 0) (hv 0)
    | 1, _ => exact hU.upair_mem (hv 1) (hv 1) (hv 2)
  case hB =>
    intro m hm i a hi ha
    have hcases : a = (vnat 0 : V) ∨ a = (vnat 1 : V) ∨ a = (vnat 2 : V) := by
      match m, hm with
      | 0, _ => exact Or.inl (mem_sing.mp ha)
      | 1, _ => rcases mem_upair.mp ha with h | h
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr h)
    rcases hcases with rfl | rfl | rfl
    · rw [posns_vnat]; exact hU.sing_mem (hv 0) (hv 0)
    · rw [posns_vnat]; exact hU.empty_mem (hv 0)
    · rw [posns_vnat]; exact hU.upair_mem (hv 0) (hv 0) (hv 1)
  case htgt =>
    intro m hm i a p hi ha hp
    refine ⟨?_, pt_mem_unitSet⟩
    unfold tgtC
    split
    · omega
    · split <;> omega
  case hmkU =>
    intro m hm i a g hi ha hg
    unfold mkC
    split
    · exact hS.tree.memU hw _ (app_mem_univ hw hg _)
    · split
      · exact hS.list.nil_mem_univ hw
      · exact hS.list.cons_mem_univ hw (app_mem_univ hw hg _) (app_mem_univ hw hg _)
  case helim =>
    intro X hX m hm i hi x hx
    obtain rfl := mem_unitSet_iff.mp hi
    match m, hm with
    | 0, _ =>
      rw [app_blkΨ_zero] at hx
      obtain ⟨l, hl, rfl⟩ := mem_nodeFib.mp hx
      refine ⟨vnat 0, mem_sing.mpr rfl, graph (fun _ => l) (sing (vnat 0)), ?_, ?_⟩
      · rw [posns_vnat]
        refine graph_mem_piSet fun p hp => ?_
        obtain rfl := mem_sing.mp hp
        show l ∈ˢ app (X (tgtC (vnat 0) (vnat 0))) pt
        rw [show tgtC (vnat 0 : V) (vnat 0) = 1 from by unfold tgtC; rw [if_pos rfl]]
        exact hl
      · show _ = mkC S 0 (vnat 0) _
        unfold mkC
        rw [if_pos rfl, app_graph (mem_sing.mpr rfl)]
    | 1, _ =>
      rw [app_blkΨ_one] at hx
      rcases mem_listFib.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
      · refine ⟨vnat 1, mem_upair.mpr (Or.inl rfl), graph (fun _ => pt) empty, ?_, ?_⟩
        · rw [posns_vnat]
          exact graph_mem_piSet fun p hp => absurd hp (not_mem_empty p)
        · show _ = mkC S 1 (vnat 1) _
          unfold mkC
          rw [if_neg (by omega), if_pos rfl]
      · refine ⟨vnat 2, mem_upair.mpr (Or.inr rfl),
          graph (fun p => if p = (vnat 0 : V) then h else t) (upair (vnat 0) (vnat 1)), ?_, ?_⟩
        · rw [posns_vnat]
          refine graph_mem_piSet fun p hp => ?_
          rcases mem_upair.mp hp with rfl | rfl
          · rw [if_pos rfl]
            show h ∈ˢ app (X (tgtC (vnat 2) (vnat 0))) pt
            rw [show tgtC (vnat 2 : V) (vnat 0) = 0 from by
              unfold tgtC; rw [if_neg (vnat_ne (by omega)), if_pos rfl]]
            exact hh
          · rw [if_neg (vnat_ne (by omega))]
            show t ∈ˢ app (X (tgtC (vnat 2) (vnat 1))) pt
            rw [show tgtC (vnat 2 : V) (vnat 1) = 1 from by
              unfold tgtC; rw [if_neg (vnat_ne (by omega)), if_neg (vnat_ne (by omega))]]
            exact ht
        · show _ = mkC S 1 (vnat 2) _
          unfold mkC
          rw [if_neg (by omega), if_neg (vnat_ne (by omega)),
            app_graph (mem_upair.mpr (Or.inl rfl)), app_graph (mem_upair.mpr (Or.inr rfl)),
            if_pos rfl, if_neg (vnat_ne (by omega))]

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

/-- F5's hypotheses: the container's env clause and the
member's tag laws — plus the encoding depth of both. -/
structure NarOk (S : TreeListSig V) : Prop where
  /-- The container's env clause and the member's tag laws. -/
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
at the block+copy — `blkΨ_closed` above, whose component `0` bounds the
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
INFINITARY container, and because it costs nothing here: the
transient two-component operator above (the block plus a COPY of the
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

Two things are worth noting against the `UnionRecKit` instance the
wide falsifier F0 ran (retired, DESIGN 2026-09-21):

* the predecessor set is NOT characterised.  `tcPred` of `node l`
  contains `l` but also every sub-tree and sub-list of `l`; the step
  reads the entries it wants out of the graph and ignores the rest, so
  only the POSITIVE memberships (`list_pred_node`, `tree_pred_cons`,
  `list_pred_cons` — each one line off the encoding-depth clause) are
  ever proved.  The wide route had to pin the predecessor set down at
  every constructor (`mem_blkPred_node`, `not_mem_blkPred_nil`,
  `mem_blkPred_cons`, then `blkPred_predsFrom`: ~70 lines);
* the motives and the step are F0's, unchanged (`blkB`, `blkSt` and
  their five laws, carried above since D-e): the formulation changes
  the *recursion principle*, not the minors. -/

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

/-! ### The bound and the step -/

/-- The bound: the two motives' fibres, selected by the value's tag
(the block is unindexed, so the motive reads the value alone). -/
noncomputable def blkB (M₀ M₁ : V → V) (u : V) : V :=
  natFibre (fun c => (match c with | 0 => M₀ | _ + 1 => M₁) (ssnd (ssnd u))) (sfst u)

theorem blkB_tree (M₀ M₁ : V → V) (x : V) : blkB M₀ M₁ (tagged 0 pt x) = M₀ x := by
  unfold blkB tagged
  rw [sfst_kpair, ssnd_kpair, ssnd_kpair, natFibre_vnat]

theorem blkB_list (M₀ M₁ : V → V) (l : V) : blkB M₀ M₁ (tagged 1 pt l) = M₁ l := by
  unfold blkB tagged
  rw [sfst_kpair, ssnd_kpair, ssnd_kpair, natFibre_vnat]

open Classical in
/-- The step: the minors at the predecessors' recursive values. -/
noncomputable def blkSt (S : TreeListSig V) (mNode : V → V → V) (mNil : V)
    (mCons : V → V → V → V → V) (u g : V) : V :=
  if h : ∃ l, u = tagged 0 pt (S.injT 0 [l]) then
    mNode h.choose (app g (tagged 1 pt h.choose))
  else if u = tagged 1 pt (S.injL 0 []) then mNil
  else if h : ∃ q : V × V, u = tagged 1 pt (S.injL 1 [q.1, q.2]) then
    mCons h.choose.1 h.choose.2 (app g (tagged 0 pt h.choose.1))
      (app g (tagged 1 pt h.choose.2))
  else empty

theorem blkSt_node (hS : TreeListOk S) (hw : S.w ≠ 0) (l g : V) :
    blkSt S mNode mNil mCons (tagged 0 pt (S.injT 0 [l])) g
      = mNode l (app g (tagged 1 pt l)) := by
  unfold blkSt
  rw [dif_pos ⟨l, rfl⟩]
  have h := Exists.choose_spec
    (⟨l, rfl⟩ : ∃ y, (tagged 0 pt (S.injT 0 [l]) : V) = tagged 0 pt (S.injT 0 [y]))
  rw [← hS.tree.mkInj hw _ _ (tagged_inj h).2.2]

theorem blkSt_nil (g : V) :
    blkSt S mNode mNil mCons (tagged 1 pt (S.injL 0 [])) g = mNil := by
  unfold blkSt
  rw [dif_neg (fun ⟨_, h⟩ => Nat.one_ne_zero (tagged_inj h).1), if_pos rfl]

theorem blkSt_cons (hS : TreeListOk S) (hw : S.w ≠ 0) (h t g : V) :
    blkSt S mNode mNil mCons (tagged 1 pt (S.injL 1 [h, t])) g
      = mCons h t (app g (tagged 0 pt h)) (app g (tagged 1 pt t)) := by
  unfold blkSt
  rw [dif_neg (fun ⟨_, h'⟩ => Nat.one_ne_zero (tagged_inj h').1),
    if_neg (fun h' => by
      exact absurd (hS.list.mkInj hw _ _ _ _ (tagged_inj h').2.2).1 (by omega)),
    dif_pos ⟨(h, t), rfl⟩]
  have hs := Exists.choose_spec
    (⟨(h, t), rfl⟩ :
      ∃ q : V × V, (tagged 1 pt (S.injL 1 [h, t]) : V) = tagged 1 pt (S.injL 1 [q.1, q.2]))
  obtain ⟨-, he⟩ := hS.list.mkInj hw _ _ _ _ (tagged_inj hs).2.2
  obtain ⟨h₁, he'⟩ := List.cons.inj he
  obtain ⟨h₂, -⟩ := List.cons.inj he'
  rw [← h₁, ← h₂]

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

/-! ## Non-vacuity, part 1: the standard `List` models the env clause

The development is hypothetical in the container's env clause; this
section discharges the hypothesis at the STANDARD reading of `List` —
tagged towers for the injections, the least pre-fixed family of the
`nil`/`cons` arm for the carrier.  Its (W) is the recipe §2.2 (iii)
prescribes for the copies, at a container WITH A PARAMETER: the shapes
carry the HOLE-FREE entry (`cons`'s head, a value of the parameter)
and the positions are the slots alone. -/

/-! ## Non-vacuity: `ListClause` has a model

The development above is hypothetical in the container's env clause.
This section discharges the hypothesis at the STANDARD reading of
`List` — tagged towers for the injections, the least pre-fixed family
of the `nil`/`cons` arm for the carrier — so that `ListClause` is not
an empty assumption.  Its (W) is the same recipe §2.2 (iii) prescribes
for the copies, now at a container WITH A PARAMETER: the shapes carry
the HOLE-FREE entry (`cons`'s head, a value of the parameter) and the
positions are the slots alone. -/

section StdList

theorem kTuple_inj : ∀ fs fs' : List V, kTuple fs = kTuple fs' → fs = fs'
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (pt_ne_kpair _ _)
  | _ :: _, [], h => absurd h.symm (pt_ne_kpair _ _)
  | x :: xs, y :: ys, h => by
      obtain ⟨rfl, h'⟩ := kpair_inj h
      rw [kTuple_inj xs ys h']

theorem kTuple_mem_univ {w : Nat} (hw : w ≠ 0) :
    ∀ {fs : List V}, (∀ x, x ∈ fs → x ∈ˢ (univ w : V)) → kTuple fs ∈ˢ (univ w : V)
  | [], _ => pt_mem_univ hw
  | x :: _xs, h =>
    (univ_isTGUniverse (V := V) hw).kpair_mem (h x List.mem_cons_self)
      (h x List.mem_cons_self)
      (kTuple_mem_univ hw fun y hy => h y (List.mem_cons_of_mem x hy))

theorem stdInj_zero (j : Nat) (fs : List V) : stdInj (V := V) 0 j fs = pt := by
  unfold stdInj; rw [if_pos rfl]

theorem stdInj_mem_univ {w : Nat} (hw : w ≠ 0) {j : Nat} {fs : List V}
    (hfs : ∀ x, x ∈ fs → x ∈ˢ (univ w : V)) : stdInj w j fs ∈ˢ (univ w : V) := by
  unfold stdInj
  rw [if_neg hw]
  exact (univ_isTGUniverse (V := V) hw).kpair_mem (vnat_mem_univ_pos hw j)
    (vnat_mem_univ_pos hw j) (kTuple_mem_univ hw hfs)

theorem stdInj_inj {w : Nat} (hw : w ≠ 0) (j j' : Nat) (fs fs' : List V)
    (h : stdInj w j fs = stdInj (V := V) w j' fs') : j = j' ∧ fs = fs' := by
  unfold stdInj at h
  rw [if_neg hw, if_neg hw] at h
  obtain ⟨h₁, h₂⟩ := kpair_inj h
  exact ⟨vnat_inj h₁, kTuple_inj _ _ h₂⟩

/-- The container's own operator at a parameter `α`: one component,
the `nil`/`cons` arm with `α` for the heads. -/
noncomputable def stdΨL (w : Nat) (α : V) (Y : Nat → V) : Nat → V :=
  fun _ => graph (fun _ => consArm (stdInj w) α (app (Y 0) pt)) unitSet

theorem app_stdΨL (w : Nat) (α : V) (Y : Nat → V) :
    app (stdΨL w α Y 0) pt = consArm (stdInj w) α (app (Y 0) pt) := app_graph pt_mem_unitSet

/-- The container's recorded reading `⟦List⟧ α`. -/
noncomputable def stdLIST (w : Nat) (α : V) : V := lfpTuple w 1 uIs (stdΨL w α) 0

/-! ### (W) for the container: shapes carry the parameter value -/

/-- The shapes: `⟨1, pt⟩` for `nil`, `⟨2, h⟩` for `cons` at the head
`h` — a HOLE-FREE entry, so it lives in the shape, not in a
position. -/
noncomputable def lsShapes (α : V) : V :=
  binUnion (sing (kpair (vnat 1) pt)) (image (fun h => kpair (vnat 2) h) α)

theorem mem_lsShapes {α a : V} :
    a ∈ˢ lsShapes α ↔ a = kpair (vnat 1) pt ∨ ∃ h, h ∈ˢ α ∧ a = kpair (vnat 2) h := by
  unfold lsShapes
  rw [mem_binUnion, mem_sing]
  exact or_congr Iff.rfl ⟨fun hx => by
      obtain ⟨h, hh, rfl⟩ := mem_image.mp hx; exact ⟨h, hh, rfl⟩,
    fun ⟨h, hh, hx⟩ => mem_image.mpr ⟨h, hh, hx⟩⟩

/-- The positions of a shape: none for `nil`, one slot for `cons`. -/
noncomputable def lsPos (a : V) : V :=
  natFibre (fun j => if j = 2 then sing (vnat 0) else empty) (sfst a)

theorem lsPos_nil : lsPos (kpair (vnat 1) pt : V) = empty := by
  unfold lsPos; rw [sfst_kpair, natFibre_vnat, if_neg (by omega)]

theorem lsPos_cons (h : V) : lsPos (kpair (vnat 2) h) = sing (vnat 0) := by
  unfold lsPos; rw [sfst_kpair, natFibre_vnat, if_pos rfl]

/-- The builder: the head comes from the SHAPE, the tail from the
position function. -/
noncomputable def lsMk (w : Nat) (a g : V) : V :=
  natFibre (fun j => if j = 1 then stdInj w 0 [] else stdInj w 1 [ssnd a, app g (vnat 0)])
    (sfst a)

theorem lsMk_nil (w : Nat) (g : V) : lsMk w (kpair (vnat 1) pt) g = stdInj (V := V) w 0 [] := by
  unfold lsMk; rw [sfst_kpair, natFibre_vnat, if_pos rfl]

theorem lsMk_cons (w : Nat) (h g : V) :
    lsMk w (kpair (vnat 2) h) g = stdInj (V := V) w 1 [h, app g (vnat 0)] := by
  unfold lsMk; rw [sfst_kpair, natFibre_vnat, if_neg (by omega), ssnd_kpair]

theorem stdΨL_maps {w : Nat} {α : V} (hα : α ∈ˢ (univ w : V)) :
    MapsTuple w 1 uIs (stdΨL w α) := by
  intro Y hY m hm
  obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
  refine graph_mem_famSpace fun i hi => ?_
  by_cases hw : w = 0
  · rw [hw, univ_zero]
    refine mem_univZero.mpr fun x hx => ?_
    rcases mem_consArm.mp hx with rfl | ⟨h, t, -, -, rfl⟩
    · rw [stdInj_zero]; exact pt_mem_unitSet
    · rw [stdInj_zero]; exact pt_mem_unitSet
  · exact consArm_mem_univ hw hα (famSpace_app (hY 0 Nat.one_pos) pt_mem_unitSet)
      (stdInj_mem_univ hw (by simp))
      (fun h t hh ht => stdInj_mem_univ hw (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hh
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ht
          · exact absurd hx (List.not_mem_nil)))

theorem stdΨL_mono {w : Nat} (α : V) : MonoTuple w 1 uIs (stdΨL w α) := by
  intro X Y hX hY hle m hm i hi x hx
  obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
  obtain rfl := mem_unitSet_iff.mp hi
  rw [app_stdΨL] at hx ⊢
  rcases mem_consArm.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
  · exact mem_consArm.mpr (Or.inl rfl)
  · exact mem_consArm.mpr (Or.inr ⟨h, t, hh, hle 0 Nat.one_pos pt pt_mem_unitSet t ht, rfl⟩)

open Classical in
theorem stdΨL_closed {w : Nat} {α : V} (hα : α ∈ˢ (univ w : V)) :
    ∃ L, IsClosedTuple w 1 uIs (stdΨL w α) L := by
  by_cases hw : w = 0
  · rw [hw]; exact closedTuple_zero (hw ▸ stdΨL_maps hα)
  have hU := univ_isTGUniverse (V := V) hw
  refine tupleContainer_closed_exists hw (Is := uIs) (stdΨL w α) (fun _ _ => lsShapes α) lsPos
    (fun _ _ => 0) (fun _ _ => pt) (fun _ => lsMk w) ?hA ?hB ?htgt ?hmkU ?helim
  case hA =>
    intro m hm i hi
    have hnilS : (kpair (vnat 1) pt : V) ∈ˢ (univ w : V) :=
      hU.kpair_mem (vnat_mem_univ_pos hw 1) (vnat_mem_univ_pos hw 1) (pt_mem_univ hw)
    show lsShapes α ∈ˢ (univ w : V)
    unfold lsShapes
    exact hU.binUnion_mem hnilS (hU.sing_mem hnilS hnilS)
      (hU.image_mem hα fun h hh =>
        hU.kpair_mem hα (vnat_mem_univ_pos hw 2) (hU.transitive hα hh))
  case hB =>
    intro m hm i a hi ha
    rcases mem_lsShapes.mp ha with rfl | ⟨h, hh, rfl⟩
    · rw [lsPos_nil]; exact hU.empty_mem hα
    · rw [lsPos_cons]; exact hU.sing_mem (vnat_mem_univ_pos hw 0) (vnat_mem_univ_pos hw 0)
  case htgt => exact fun m hm i a p hi ha hp => ⟨Nat.one_pos, pt_mem_unitSet⟩
  case hmkU =>
    intro m hm i a g hi ha hg
    rcases mem_lsShapes.mp ha with rfl | ⟨h, hh, rfl⟩
    · rw [lsMk_nil]; exact stdInj_mem_univ hw (by simp)
    · rw [lsMk_cons]
      refine stdInj_mem_univ hw ?_
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hU.transitive hα hh
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact app_mem_univ hw hg _
        · exact absurd hx (List.not_mem_nil)
  case helim =>
    intro X hX m hm i hi x hx
    obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
    obtain rfl := mem_unitSet_iff.mp hi
    rw [app_stdΨL] at hx
    rcases mem_consArm.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · refine ⟨kpair (vnat 1) pt, mem_lsShapes.mpr (Or.inl rfl), graph (fun _ => pt) empty, ?_, ?_⟩
      · rw [lsPos_nil]
        exact graph_mem_piSet fun p hp => absurd hp (not_mem_empty p)
      · rw [lsMk_nil]
    · refine ⟨kpair (vnat 2) h, mem_lsShapes.mpr (Or.inr ⟨h, hh, rfl⟩),
        graph (fun _ => t) (sing (vnat 0)), ?_, ?_⟩
      · rw [lsPos_cons]
        exact graph_mem_piSet fun p hp => ht
      · rw [lsMk_cons, app_graph (mem_sing.mpr rfl)]

/-- **`ListClause` is not an empty hypothesis**: the standard reading
of `List` satisfies it at every level. -/
theorem stdListClause (w : Nat) :
    ListClause w (stdLIST (V := V) w) (stdΨL w) (stdInj w) where
  leaf := fun _ _ => rfl
  mono := fun α _ => stdΨL_mono α
  maps := fun _ hα => stdΨL_maps hα
  closed := fun _ hα => stdΨL_closed hα
  fibre := fun α hα Y hY t ht x => by
    obtain rfl := mem_unitSet_iff.mp ht
    rw [app_stdΨL]
    exact ⟨fun hx => by
        rcases mem_consArm.mp hx with rfl | ⟨h, t', hh, ht', rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h, hh, t', ht', rfl⟩,
      fun hx => by
        rcases hx with rfl | ⟨h, hh, t', ht', rfl⟩
        · exact mem_consArm.mpr (Or.inl rfl)
        · exact mem_consArm.mpr (Or.inr ⟨h, t', hh, ht', rfl⟩)⟩
  mkZero := fun hw j fs => by unfold stdInj; rw [if_pos hw]
  mkInj := fun hw j j' fs fs' h => stdInj_inj hw j j' fs fs' h

/-- The container's env clause and the member's tags are satisfiable:
the standard `List` together with the standard tagged towers. -/
theorem treeListOk_std (w : Nat) :
    TreeListOk (V := V) ⟨w, stdLIST w, stdΨL w, stdInj w, stdInj w⟩ :=
  ⟨stdListClause w, treeTags_stdInj w⟩

end StdList

/-! ## Non-vacuity, part 2: the standard encoding satisfies the depth clause

The section above exhibits a model of `ListClause`/`TreeTags`
(`stdInj`, the tagged `kpair` tower).  The only hypothesis F5 adds on
top is the encoding depth, and the same encoding satisfies it — so
every theorem of this file has a model at every level. -/

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
