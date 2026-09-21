module

public import ConLeche.SetModel.UnionRec
public import ConLeche.SetModel.TupleContainer
public import ConLeche.SetTheory.Derive.LfpCompose
@[expose] public section

/-!
# `Tree ::= node (List Tree)` through the container's ENV CLAUSE (falsifier F0)

The first falsifier of the *uniform* nested route (`DESIGN-theory.md`
§6.1 F0).  The block

    inductive Tree where | node : List Tree → Tree

is modelled as a **plain two-component block** — component `0` is
`Tree`, component `1` is the abstract COPY of `List` at the pin
`Tree` — and the copy's carrier is *identified* with the container's
recorded reading `⟦List⟧` through the container's **env-invariant
clause** (`ListClause` below, `DESIGN-theory.md` §1.2 restricted to a
one-member, non-indexed, non-parametric-index block).  No auxiliary
block is installed, no copy of `List` is stored, and the container is
read only through the clause.

What this file must NOT use, and does not (the pass criterion):

* `unionAcc_of_classAcc` / `unionRecC` — both recursion classes ARE
  components of the tuple lfp, so `unionAcc_all`'s simultaneous
  induction reaches them;
* any level fact `w ≤ w'` — the clause's `Sat` guard is `univ w`, the
  same `w` the tuple space uses (the sort gate of `DESIGN-theory.md`
  §2.5 makes the container's sort the block's), so the parameter
  `⟦Tree⟧` fits the guard by `famSpace_app` alone;
* the clamp (`meetT`), `composeΦ`, `pinsCar` — the operator is a plain
  block operator on two components and the identification is Bekić at
  a segment (`lfpTuple_seg_congr`).

The predecessor of this file is `mutual-direct`'s
`SetModel/NestedTreeList.lean` (739 lines), which composed the
container INTO the member's operator and therefore needed the level
fact, the container's map action in the parameter, the container's own
induction at a parameter, and `unionAcc_of_classAcc`.  None of that
survives.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

open Tower (natFibre natFibre_vnat)

universe u

variable {V : Type u} [SetTheory V]

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

/-- The data F0 reasons about: the container's recorded reading and
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

/-- Component `1`'s fibre — the abstract COPY of `List` at the pin
`Tree`: `nil : y₁`, `cons : x₀ → y₁ → y₁`, with the CONTAINER's own
injections. -/
noncomputable def listFib (S : TreeListSig V) (X : Nat → V) : V :=
  binUnion (sing (S.injL 0 []))
    (image (fun p => S.injL 1 [sfst p, ssnd p])
      (sigmaPairs (app (X 0) pt) (fun _ => app (X 1) pt)))

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
        ∃ h t, h ∈ˢ app (X 0) pt ∧ t ∈ˢ app (X 1) pt ∧ x = S.injL 1 [h, t] := by
  unfold listFib
  rw [mem_binUnion, mem_sing]
  refine or_congr Iff.rfl ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    obtain ⟨h, hh, t, ht, rfl⟩ := mem_sigmaPairs.mp hp
    rw [sfst_kpair, ssnd_kpair]
    exact ⟨h, t, hh, ht, rfl⟩
  · obtain ⟨h, t, hh, ht, rfl⟩ := hx
    refine mem_image.mpr ⟨kpair h t, mem_sigmaPairs.mpr ⟨h, hh, t, ht, rfl⟩, ?_⟩
    rw [sfst_kpair, ssnd_kpair]

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
    · refine hU.binUnion_mem (hS.list.nil_mem_univ hw)
        (hU.sing_mem (hS.list.nil_mem_univ hw) (hS.list.nil_mem_univ hw)) ?_
      refine hU.image_mem (hU.sigmaPairs_mem h0 fun _ _ => h1) fun p hp => ?_
      obtain ⟨h, hh, t, ht, rfl⟩ := mem_sigmaPairs.mp hp
      rw [sfst_kpair, ssnd_kpair]
      exact hS.list.cons_mem_univ hw (hU.transitive h0 hh) (hU.transitive h1 ht)

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

/-! ## The carrier -/

/-- The block's carrier tuple. -/
noncomputable def car (S : TreeListSig V) : Nat → V := lfpTuple S.w 2 uIs (blkΨ S)

/-- `⟦Tree⟧`, the member's value set. -/
noncomputable def carT (S : TreeListSig V) : V := app (car S 0) pt

/-- The copy's value set. -/
noncomputable def carL (S : TreeListSig V) : V := app (car S 1) pt

theorem car_mem (S : TreeListSig V) : InTupleSpace S.w 2 uIs (car S) := lfpTuple_mem _ _ _ _

/-- The parameter of the pin lies in the container's `Sat` domain —
`famSpace_app` at the SAME level.  This is where `NestedTreeList.lean`
needed the level fact `w ≤ w'`. -/
theorem carT_mem_univ (S : TreeListSig V) : carT S ∈ˢ (univ S.w : V) :=
  famSpace_app (car_mem S 0 (by omega)) pt_mem_unitSet

/-! ## (c) THE IDENTIFICATION: the copy's component IS `⟦List⟧ ⟦Tree⟧`

Bekić at the segment `[1, 2)` of the two-component tuple
(`lfpTuple_seg_congr`): the segment's section operator, read at the
least tuple, is the container's own operator at the parameter
`⟦Tree⟧` — entry by entry, by the clause's `fibre`.  The clause's
`leaf` then turns the segment's least tuple into the stored
reading. -/

/-- The segment's section operator agrees with the container's own
operator at the parameter `⟦Tree⟧`, on the whole one-tuple space. -/
theorem segSec_eq_ΨL (hS : TreeListOk S) {Y : Nat → V}
    (hY : InTupleSpace S.w 1 (fun i => uIs (1 + i)) Y) :
    blkΨ S (segJoin 1 1 (car S) Y) 1 = S.ΨL (carT S) Y 0 := by
  have hY' : InTupleSpace S.w 1 uIs Y := hY
  have hZ : InTupleSpace S.w 2 uIs (segJoin 1 1 (car S) Y) :=
    inTupleSpace_segJoin (car_mem S) hY'
  have h0 : segJoin 1 1 (car S) Y 0 = car S 0 := segJoin_lt _ _ (by omega)
  have h1 : segJoin 1 1 (car S) Y 1 = Y 0 := segJoin_add (q := 0) _ _ (by omega)
  refine famSpace_ext (?_) (hS.list.maps (carT S) (carT_mem_univ S) Y hY' 0 Nat.one_pos) ?_
  · exact blkΨ_maps hS _ hZ 1 (by omega)
  · intro i hi
    obtain rfl := mem_unitSet_iff.mp hi
    apply SetTheory.ext
    intro x
    rw [app_blkΨ_one, mem_listFib,
      hS.list.fibre (carT S) (carT_mem_univ S) Y hY' pt pt_mem_unitSet x, h0, h1]
    constructor
    · rintro (rfl | ⟨h, t, hh, ht, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨h, hh, t, ht, rfl⟩
    · rintro (rfl | ⟨h, hh, t, ht, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨h, t, hh, ht, rfl⟩

/-- **THE IDENTIFICATION.**  The copy's component of the block's
carrier IS the container's recorded reading at the member's value:
`L 1 = ⟦List⟧ ⟦Tree⟧`.  Proved from the container's ENV CLAUSE alone,
by Bekić at the segment — no level fact, no clamp, no second install. -/
theorem car_one_eq_LIST (hS : TreeListOk S) : car S 1 = S.LIST (carT S) := by
  have h : car S (1 + 0) = lfpTuple S.w 1 uIs (S.ΨL (carT S)) 0 :=
    lfpTuple_seg_congr (blkΨ_closed hS) (blkΨ_mono S) (by omega) (fun _ _ => rfl)
      (fun Y hY i hi => by
        obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
        exact segSec_eq_ΨL hS hY)
      (Nat.zero_lt_one)
  rw [hS.list.leaf (carT S) (carT_mem_univ S)]
  exact h

/-- The identification, at the value set: the domain of `Tree.node`
read ORDINARILY is the copy's component. -/
theorem carL_eq (hS : TreeListOk S) : carL S = app (S.LIST (carT S)) pt := by
  unfold carL
  rw [car_one_eq_LIST hS]

/-! ## (d) The fixed-point equations and the constructors' typing -/

/-- The carrier is a fixed point, componentwise at the point index. -/
theorem app_car_eq (hS : TreeListOk S) {c : Nat} (hc : c < 2) :
    app (car S c) pt = app (blkΨ S (car S) c) pt :=
  (app_lfpTuple_eq (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS) hc
    (show (pt : V) ∈ˢ uIs c from pt_mem_unitSet)).symm

theorem carT_eq_nodeFib (hS : TreeListOk S) : carT S = nodeFib S (car S) := by
  unfold carT
  rw [app_car_eq hS (show (0:Nat) < 2 by omega), app_blkΨ_zero]

theorem carL_eq_listFib (hS : TreeListOk S) : carL S = listFib S (car S) := by
  unfold carL
  rw [app_car_eq hS (show (1:Nat) < 2 by omega), app_blkΨ_one]

/-- `⟦Tree⟧ = { node l | l ∈ the copy's component }`. -/
theorem mem_carT (hS : TreeListOk S) {x : V} :
    x ∈ˢ carT S ↔ ∃ l, l ∈ˢ carL S ∧ x = S.injT 0 [l] := by
  constructor
  · intro hx
    rw [carT_eq_nodeFib hS] at hx
    exact mem_nodeFib.mp hx
  · intro hx
    rw [carT_eq_nodeFib hS]
    exact mem_nodeFib.mpr hx

/-- The copy's component `= nil ∪ { cons h t | h ∈ ⟦Tree⟧, t ∈ the copy }`. -/
theorem mem_carL (hS : TreeListOk S) {x : V} :
    x ∈ˢ carL S ↔
      x = S.injL 0 [] ∨ ∃ h t, h ∈ˢ carT S ∧ t ∈ˢ carL S ∧ x = S.injL 1 [h, t] := by
  constructor
  · intro hx
    rw [carL_eq_listFib hS] at hx
    exact mem_listFib.mp hx
  · intro hx
    rw [carL_eq_listFib hS]
    exact mem_listFib.mpr hx

/-- **`Tree.node`'s typing, with its domain read ordinarily.**  `l` is
a value of `⟦List⟧ ⟦Tree⟧` — the reading the checker produces for
`Tree.node : List Tree → Tree` — and `node l` is a value of the
member. -/
theorem node_mem_carT (hS : TreeListOk S) {l : V} (hl : l ∈ˢ app (S.LIST (carT S)) pt) :
    S.injT 0 [l] ∈ˢ carT S :=
  (mem_carT hS).mpr ⟨l, by rw [carL_eq hS]; exact hl, rfl⟩

/-- `List.nil`'s value, read ordinarily at `Tree`, is a value of the
copy's component. -/
theorem nil_mem_carL (hS : TreeListOk S) : S.injL 0 [] ∈ˢ app (S.LIST (carT S)) pt := by
  rw [← carL_eq hS]; exact (mem_carL hS).mpr (Or.inl rfl)

/-- `List.cons`'s value, read ordinarily at `Tree`. -/
theorem cons_mem_carL (hS : TreeListOk S) {h t : V} (hh : h ∈ˢ carT S)
    (ht : t ∈ˢ app (S.LIST (carT S)) pt) : S.injL 1 [h, t] ∈ˢ app (S.LIST (carT S)) pt := by
  rw [← carL_eq hS] at ht ⊢
  exact (mem_carL hS).mpr (Or.inr ⟨h, t, hh, ht, rfl⟩)

/-! ## (e) The recursor: `UnionRecKit` at TWO components

Both recursion classes — the member's values and the copy's — are
components of the tuple lfp, so `unionAcc_all`'s simultaneous
induction reaches both and `unionAcc_of_classAcc`/`unionRecC` are not
needed.  The three ι rules and the typing come out of `unionRec_eq`
and `unionRec_mem_B` at `N = 2`.

The section runs above `Prop` (`S.w ≠ 0`): the constructor
decomposition of a value must be unique, which is exactly `mkInj`'s
guard.  At `w = 0` a nested block is forced small
(`DESIGN-theory.md` §3.5) and the recursor is the trivial one. -/

section Rec

variable {S : TreeListSig V} {ℓ : Nat} {M₀ M₁ : V → V} {mNode : V → V → V} {mNil : V}
  {mCons : V → V → V → V → V}

/-- The index set of the recursion: the disjoint union of the two
components' values. -/
noncomputable def blkIdx (S : TreeListSig V) : V := unionSet 2 uIs (car S)

theorem mem_blkIdx {u : V} :
    u ∈ˢ blkIdx S ↔
      (∃ x, x ∈ˢ carT S ∧ u = tagged 0 pt x) ∨ (∃ l, l ∈ˢ carL S ∧ u = tagged 1 pt l) := by
  unfold blkIdx
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

theorem tree_mem_blkIdx {x : V} (hx : x ∈ˢ carT S) : tagged 0 pt x ∈ˢ blkIdx S :=
  mem_blkIdx.mpr (Or.inl ⟨x, hx, rfl⟩)

theorem list_mem_blkIdx {l : V} (hl : l ∈ˢ carL S) : tagged 1 pt l ∈ˢ blkIdx S :=
  mem_blkIdx.mpr (Or.inr ⟨l, hl, rfl⟩)

/-- The predecessor relation, read off the constructors of BOTH
components — the copy's `cons` crosses to the member's component. -/
def BlkRel (S : TreeListSig V) (u v : V) : Prop :=
  (∃ l, u = tagged 0 pt (S.injT 0 [l]) ∧ v = tagged 1 pt l) ∨
  (∃ h t, u = tagged 1 pt (S.injL 1 [h, t]) ∧ (v = tagged 0 pt h ∨ v = tagged 1 pt t))

/-- The predecessor sets. -/
noncomputable def blkPred (S : TreeListSig V) (u : V) : V := relPred (blkIdx S) (BlkRel S) u

theorem blkPred_subset (S : TreeListSig V) (u : V) : blkPred S u ⊆ˢ blkIdx S :=
  relPred_subset _ _ u

theorem mem_blkPred {u v : V} : v ∈ˢ blkPred S u ↔ v ∈ˢ blkIdx S ∧ BlkRel S u v := mem_relPred

theorem mem_blkPred_node (hS : TreeListOk S) (hw : S.w ≠ 0) {l v : V} :
    v ∈ˢ blkPred S (tagged 0 pt (S.injT 0 [l])) ↔ v ∈ˢ blkIdx S ∧ v = tagged 1 pt l := by
  rw [mem_blkPred]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inl ⟨l, rfl, h⟩⟩
  rcases h with ⟨l', h₁, h₂⟩ | ⟨h', t', h₁, -⟩
  · rw [h₂, hS.tree.mkInj hw l l' (tagged_inj h₁).2.2]
  · exact absurd (tagged_inj h₁).1 (by omega)

theorem not_mem_blkPred_nil (hS : TreeListOk S) (hw : S.w ≠ 0) {v : V} :
    ¬ v ∈ˢ blkPred S (tagged 1 pt (S.injL 0 [])) := by
  intro h
  rcases (mem_blkPred.mp h).2 with ⟨_, h₁, -⟩ | ⟨h', t', h₁, -⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · exact absurd (hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2).1 (by omega)

theorem mem_blkPred_cons (hS : TreeListOk S) (hw : S.w ≠ 0) {h t v : V} :
    v ∈ˢ blkPred S (tagged 1 pt (S.injL 1 [h, t])) ↔
      v ∈ˢ blkIdx S ∧ (v = tagged 0 pt h ∨ v = tagged 1 pt t) := by
  rw [mem_blkPred]
  refine and_congr_right fun _ => ⟨fun hv => ?_, fun hv => Or.inr ⟨h, t, rfl, hv⟩⟩
  rcases hv with ⟨_, h₁, -⟩ | ⟨h', t', h₁, h₂⟩
  · exact absurd (tagged_inj h₁).1 (by omega)
  · obtain ⟨-, he⟩ := hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
    obtain ⟨rfl, he'⟩ := List.cons.inj he
    obtain ⟨rfl, -⟩ := List.cons.inj he'
    exact h₂

/-- **The predecessors come from the argument tuple** — the ONE fact
the recursion theorem needs of the constructor decomposition. -/
theorem blkPred_predsFrom (hS : TreeListOk S) (hw : S.w ≠ 0) :
    PredsFrom S.w 2 uIs (blkΨ S) (blkPred S) := by
  intro X hX hXle c hc i hi x hx v hv
  obtain rfl := mem_unitSet_iff.mp hi
  obtain ⟨-, hrel⟩ := mem_relPred.mp hv
  match c, hc with
  | 0, _ =>
    rw [app_blkΨ_zero] at hx
    obtain ⟨l, hl, rfl⟩ := mem_nodeFib.mp hx
    rcases hrel with ⟨l', h₁, rfl⟩ | ⟨h', t', h₁, -⟩
    · obtain rfl := hS.tree.mkInj hw l l' (tagged_inj h₁).2.2
      exact tagged_mem_unionSet (by omega) pt_mem_unitSet hl
    · exact absurd (tagged_inj h₁).1 (by omega)
  | 1, _ =>
    rw [app_blkΨ_one] at hx
    rcases mem_listFib.mp hx with rfl | ⟨h, t, hh, ht, rfl⟩
    · rcases hrel with ⟨_, h₁, -⟩ | ⟨h', t', h₁, -⟩
      · exact absurd (tagged_inj h₁).1 (by omega)
      · exact absurd (hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2).1 (by omega)
    · rcases hrel with ⟨_, h₁, -⟩ | ⟨h', t', h₁, h₂⟩
      · exact absurd (tagged_inj h₁).1 (by omega)
      · obtain ⟨-, he⟩ := hS.list.mkInj hw _ _ _ _ (tagged_inj h₁).2.2
        obtain ⟨rfl, he'⟩ := List.cons.inj he
        obtain ⟨rfl, -⟩ := List.cons.inj he'
        rcases h₂ with rfl | rfl
        · exact tagged_mem_unionSet (by omega) pt_mem_unitSet hh
        · exact tagged_mem_unionSet (by omega) pt_mem_unitSet ht

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

variable (hS : TreeListOk S) (hw : S.w ≠ 0)
  (hM₀ : ∀ x, x ∈ˢ carT S → M₀ x ∈ˢ (univ ℓ : V))
  (hM₁ : ∀ l, l ∈ˢ carL S → M₁ l ∈ˢ (univ ℓ : V))
  (hmNode : ∀ l ih, l ∈ˢ carL S → ih ∈ˢ M₁ l → mNode l ih ∈ˢ M₀ (S.injT 0 [l]))
  (hmNil : mNil ∈ˢ M₁ (S.injL 0 []))
  (hmCons : ∀ h t ih₁ ih₂, h ∈ˢ carT S → t ∈ˢ carL S → ih₁ ∈ˢ M₀ h → ih₂ ∈ˢ M₁ t →
    mCons h t ih₁ ih₂ ∈ˢ M₁ (S.injL 1 [h, t]))

include hM₀ hM₁ in
theorem blkB_mem_univ : ∀ u, u ∈ˢ blkIdx S → blkB M₀ M₁ u ∈ˢ (univ ℓ : V) := by
  intro u hu
  rcases mem_blkIdx.mp hu with ⟨x, hx, rfl⟩ | ⟨l, hl, rfl⟩
  · rw [blkB_tree]; exact hM₀ x hx
  · rw [blkB_list]; exact hM₁ l hl

include hM₀ hM₁ in
theorem blkGraph_mem_B {u v : V} (hu : u ∈ˢ blkIdx S)
    (hv : v ∈ˢ app (recGraph ℓ (blkIdx S) (blkPred S) (blkB M₀ M₁)
      (blkSt S mNode mNil mCons)) u) : v ∈ˢ blkB M₀ M₁ u := by
  rw [app_recGraph_eq (blkB_mem_univ hM₀ hM₁) (fun u _ => blkPred_subset S u) hu] at hv
  exact (mem_recGraphFibre.mp hv).1

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- **The step is typed** — from the minors' typing alone. -/
theorem blkSt_mem : ∀ u, u ∈ˢ blkIdx S → ∀ g,
    g ∈ˢ piSet (blkPred S u) (fun j => app (recGraph ℓ (blkIdx S) (blkPred S) (blkB M₀ M₁)
      (blkSt S mNode mNil mCons)) j) →
    blkSt S mNode mNil mCons u g ∈ˢ blkB M₀ M₁ u := by
  intro u hu g hg
  have hval : ∀ v, v ∈ˢ blkPred S u → app g v ∈ˢ blkB M₀ M₁ v := fun v hv =>
    blkGraph_mem_B hM₀ hM₁ (blkPred_subset S u v hv) (app_mem_of_mem_piSet hg hv)
  rcases mem_blkIdx.mp hu with ⟨x, hx, rfl⟩ | ⟨l, hl, rfl⟩
  · obtain ⟨l, hl, rfl⟩ := (mem_carT hS).mp hx
    rw [blkSt_node hS hw, blkB_tree]
    have h := hval (tagged 1 pt l) ((mem_blkPred_node hS hw).mpr ⟨list_mem_blkIdx hl, rfl⟩)
    rw [blkB_list] at h
    exact hmNode l _ hl h
  · rcases (mem_carL hS).mp hl with rfl | ⟨h, t, hh, ht, rfl⟩
    · rw [blkSt_nil, blkB_list]; exact hmNil
    · rw [blkSt_cons hS hw, blkB_list]
      have h₁ := hval (tagged 0 pt h) ((mem_blkPred_cons hS hw).mpr
        ⟨tree_mem_blkIdx hh, Or.inl rfl⟩)
      have h₂ := hval (tagged 1 pt t) ((mem_blkPred_cons hS hw).mpr
        ⟨list_mem_blkIdx ht, Or.inr rfl⟩)
      rw [blkB_tree] at h₁
      rw [blkB_list] at h₂
      exact hmCons h t _ _ hh ht h₁ h₂

/-- **The block's recursion kit** at `N = 2` components. -/
noncomputable def blkKit : UnionRecKit ℓ S.w 2 uIs (blkΨ S) :=
  ⟨blkPred S, blkB M₀ M₁, blkSt S mNode mNil mCons, blkPred_predsFrom hS hw,
    blkB_mem_univ hM₀ hM₁, blkSt_mem hS hw hM₀ hM₁ hmNode hmNil hmCons⟩

local notation "K*" => blkKit hS hw hM₀ hM₁ hmNode hmNil hmCons

@[simp] theorem blkKit_pred : (K*).pred = blkPred S := rfl
@[simp] theorem blkKit_B : (K*).B = blkB M₀ M₁ := rfl
@[simp] theorem blkKit_st : (K*).st = blkSt S mNode mNil mCons := rfl

/-- The kit's recursor IS the selector of the recursion graph over the
two-component union. -/
theorem blkKit_recAt (c : Nat) (i x : V) :
    (K*).recAt c i x = recSel (recGraph ℓ (blkIdx S) (blkPred S) (blkB M₀ M₁)
      (blkSt S mNode mNil mCons)) (tagged c i x) := rfl

/-- `Tree.rec`. -/
noncomputable def recT (x : V) : V := (K*).recAt 0 pt x

/-- `Tree.rec_1` — the recursor of the copy's component, the one
official emits for the aux key `List Tree`. -/
noncomputable def recL (l : V) : V := (K*).recAt 1 pt l

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- **Typing**: `Tree.rec … x ∈ motive x`. -/
theorem recT_mem {x : V} (hx : x ∈ˢ carT S) :
    recT hS hw hM₀ hM₁ hmNode hmNil hmCons x ∈ˢ M₀ x := by
  have h := (K*).rec_mem_B (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS)
    (show (0:Nat) < 2 by omega) (show (pt : V) ∈ˢ uIs 0 from pt_mem_unitSet) hx
  rw [blkKit_B, blkB_tree] at h
  exact h

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- **Typing**: `Tree.rec_1 … l ∈ motive_1 l`. -/
theorem recL_mem {l : V} (hl : l ∈ˢ carL S) :
    recL hS hw hM₀ hM₁ hmNode hmNil hmCons l ∈ˢ M₁ l := by
  have h := (K*).rec_mem_B (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS)
    (show (1:Nat) < 2 by omega) (show (pt : V) ∈ˢ uIs 1 from pt_mem_unitSet) hl
  rw [blkKit_B, blkB_list] at h
  exact h

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- The recursion equation, in the engine's form. -/
theorem blkRec_eq {c : Nat} (hc : c < 2) {x : V} (hx : x ∈ˢ app (car S c) pt) :
    (K*).recAt c pt x
      = blkSt S mNode mNil mCons (tagged c pt x)
          (graph (fun j => recSel (recGraph ℓ (blkIdx S) (blkPred S) (blkB M₀ M₁)
            (blkSt S mNode mNil mCons)) j) (blkPred S (tagged c pt x))) := by
  have h := (K*).rec_eq (blkΨ_closed hS) (blkΨ_mono S) (blkΨ_maps hS) hc
    (show (pt : V) ∈ˢ uIs c from pt_mem_unitSet) hx
  exact h

/-! ### The three ι rules -/

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- ι 1: `Tree.rec … (node l) = mNode l (Tree.rec_1 … l)`. -/
theorem recT_node {l : V} (hl : l ∈ˢ carL S) :
    recT hS hw hM₀ hM₁ hmNode hmNil hmCons (S.injT 0 [l])
      = mNode l (recL hS hw hM₀ hM₁ hmNode hmNil hmCons l) := by
  show (K*).recAt 0 pt (S.injT 0 [l]) = mNode l ((K*).recAt 1 pt l)
  rw [blkRec_eq hS hw hM₀ hM₁ hmNode hmNil hmCons (show (0:Nat) < 2 by omega)
      ((mem_carT hS).mpr ⟨l, hl, rfl⟩),
    blkSt_node hS hw, app_graph ((mem_blkPred_node hS hw).mpr ⟨list_mem_blkIdx hl, rfl⟩),
    blkKit_recAt]

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- ι 2: `Tree.rec_1 … nil = mNil`. -/
theorem recL_nil : recL hS hw hM₀ hM₁ hmNode hmNil hmCons (S.injL 0 []) = mNil := by
  show (K*).recAt 1 pt (S.injL 0 []) = mNil
  rw [blkRec_eq hS hw hM₀ hM₁ hmNode hmNil hmCons (show (1:Nat) < 2 by omega)
      ((mem_carL hS).mpr (Or.inl rfl)),
    blkSt_nil]

include hS hw hM₀ hM₁ hmNode hmNil hmCons in
/-- ι 3: `Tree.rec_1 … (cons h t) = mCons h t (Tree.rec … h) (Tree.rec_1 … t)` —
the rule that CROSSES components, the one official emits for the
container's constructor at the pin. -/
theorem recL_cons {h t : V} (hh : h ∈ˢ carT S) (ht : t ∈ˢ carL S) :
    recL hS hw hM₀ hM₁ hmNode hmNil hmCons (S.injL 1 [h, t])
      = mCons h t (recT hS hw hM₀ hM₁ hmNode hmNil hmCons h)
          (recL hS hw hM₀ hM₁ hmNode hmNil hmCons t) := by
  show (K*).recAt 1 pt (S.injL 1 [h, t])
    = mCons h t ((K*).recAt 0 pt h) ((K*).recAt 1 pt t)
  rw [blkRec_eq hS hw hM₀ hM₁ hmNode hmNil hmCons (show (1:Nat) < 2 by omega)
      ((mem_carL hS).mpr (Or.inr ⟨h, t, hh, ht, rfl⟩)),
    blkSt_cons hS hw,
    app_graph ((mem_blkPred_cons hS hw).mpr ⟨tree_mem_blkIdx hh, Or.inl rfl⟩),
    app_graph ((mem_blkPred_cons hS hw).mpr ⟨list_mem_blkIdx ht, Or.inr rfl⟩),
    blkKit_recAt, blkKit_recAt]

end Kit

end Rec

end ConLeche.SetTheory
