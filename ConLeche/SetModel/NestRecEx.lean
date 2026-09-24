module

public import ConLeche.SetModel.NestRec
@[expose] public section

/-!
# Instances of the nested graph kit (lane NESTIND-KIT)

`SetModel/NestRec.lean`'s `NestKit` over the HOLEOP block data
(`SetModel/HoleOp.lean`), each at every level `w` — `Prop` (`w = 0`,
every closure hypothesis discharged) and `Type` (`w ≠ 0`, (W) a
hypothesis as in every set-level lane):

* `treeKit` — `Tree ::= node (List Tree)`: the classes `Tree` and
  `List Tree`; at `w = 0` the nested `Prop` example
  (`treeKit_exu_prop`, `huniq` by `huniq_of_prop`, injections NOT
  injective);
* `roseKit` — `Rose α ::= node α (List (Rose α))` at a parameter `α₀`:
  the classes `Rose α₀` and `List (Rose α₀)`; `roseKit_exu_type`
  (`huniq` from injective injections);
* `rtKit` — `T ::= leaf | mk (Rose T)`: TWO nesting levels, the classes
  `T`, `Rose T` and `List (Rose T)` (the last reached through `Rose`'s
  own field at `Rose`'s separated tuple); both regimes
  (`rtKit_exu_prop`, `rtKit_exu_type`).

Each instance's `ind` is `NestKit.ind` — no container
parameter-monotonicity is consumed by it: the `trans` premise is the
datum's own positivity (`UBlock.toSClause_fits_mono`), and `calls`
reads the fields off the fit.
-/

namespace ConLeche.SetTheory

open Tower

universe u

variable {V : Type u} [SetTheory V]

/-- The fixed frame of the HOLEOP instances' field readings. -/
noncomputable abbrev nestρ₀ : Nat → V := fun _ => empty

/-! ## The block data's fits, spelled out -/

theorem listD_fits {w : Nat} {α : V} {X : Nat → V} {t : V} {c j : Nat} {fs : List V}
    (h : ((listD (V := V) w).toSClause nestρ₀).Fits α X t c j fs) :
    (j = 0 ∧ fs = []) ∨ ∃ a l, j = 1 ∧ fs = [a, l] ∧ a ∈ˢ α ∧ l ∈ˢ app (X 0) pt := by
  obtain ⟨ct, hct, hf, -⟩ := h
  match j, fs, hct, hf with
  | 0, [], _, _ => exact Or.inl ⟨rfl, rfl⟩
  | 1, [a, l], rfl, hf => exact Or.inr ⟨a, l, rfl, rfl, hf.1, hf.2.1⟩

theorem treeD_fits {w : Nat} {hW : (listD (V := V) w).ClosedAll nestρ₀} {α : V} {X : Nat → V} {t : V}
    {c j : Nat} {fs : List V} (h : ((treeD w hW).toSClause nestρ₀).Fits α X t c j fs) :
    ∃ l, j = 0 ∧ fs = [l] ∧ l ∈ˢ LIST w (app (X 0) pt) := by
  obtain ⟨ct, hct, hf, -⟩ := h
  match j, fs, hct, hf with
  | 0, [l], rfl, hf => exact ⟨l, rfl, rfl, hf.1⟩

theorem roseD_fits {w : Nat} {hW : (listD (V := V) w).ClosedAll nestρ₀} {α : V} {X : Nat → V} {t : V}
    {c j : Nat} {fs : List V} (h : ((roseD w hW).toSClause nestρ₀).Fits α X t c j fs) :
    ∃ a l, j = 0 ∧ fs = [a, l] ∧ a ∈ˢ α ∧ l ∈ˢ LIST w (app (X 0) pt) := by
  obtain ⟨ct, hct, hf, -⟩ := h
  match j, fs, hct, hf with
  | 0, [a, l], rfl, hf => exact ⟨a, l, rfl, rfl, hf.1, hf.2.1⟩

theorem rtD_fits {w : Nat} {hW : (listD (V := V) w).ClosedAll nestρ₀}
    {hWR : (roseD w hW).ClosedAll nestρ₀} {α : V} {X : Nat → V} {t : V}
    {c j : Nat} {fs : List V} (h : ((rtD w hW hWR).toSClause nestρ₀).Fits α X t c j fs) :
    (j = 0 ∧ fs = []) ∨ ∃ r, j = 1 ∧ fs = [r] ∧ r ∈ˢ ROSE w hW (app (X 0) pt) := by
  obtain ⟨ct, hct, hf, -⟩ := h
  match j, fs, hct, hf with
  | 0, [], _, _ => exact Or.inl ⟨rfl, rfl⟩
  | 1, [r], rfl, hf => exact Or.inr ⟨r, rfl, rfl, hf.1⟩

/-- The hole of an unindexed one-member block's own tuple, read at the
point: a set of the level. -/
theorem app_hole_mem_univ {w : Nat} {Y : Nat → V} (hY : InTupleSpace w 1 unitIs Y) :
    app (Y 0) pt ∈ˢ (univ w : V) :=
  app_fam_mem_univ (hY 0 Nat.one_pos) pt

/-- The "own" extension at an unindexed one-member class holds at its
hole's elements. -/
theorem addOwn_hole {G : Nat → Nat → V → V → Prop} {b : Nat} {Y : Nat → V} {y : V}
    (hy : y ∈ˢ app (Y 0) pt) : addOwn G b 1 unitIs Y b 0 pt y :=
  Or.inr ⟨rfl, Nat.one_pos, by exact pt_mem_unitSet, hy⟩

private theorem lt_one_eq {c : Nat} (hc : c < 1) : c = 0 := by omega

/-! ## `Tree ::= node (List Tree)` — one nesting level -/

section Tree

variable (w : Nat) (hW : (listD (V := V) w).ClosedAll nestρ₀)

/-- The classes: `0` = `Tree`, `1` = `List` (at a frame). -/
noncomputable def treeCl : Nat → SClause V V
  | 0 => (treeD w hW).toSClause nestρ₀
  | _ + 1 => (listD w).toSClause nestρ₀

/-- The true frames: `List` at `⟦Tree⟧`. -/
noncomputable def treeFr : Nat → V
  | 0 => empty
  | _ + 1 => TREE w hW

/-- The admissible frames: `Tree` at its own (empty) frame; `List` at a
parameter of the level all of whose elements are good trees. -/
def treeAdm : Nat → (Nat → Nat → V → V → Prop) → V → Prop
  | 0, _, α => α = empty
  | _ + 1, G, α => α ∈ˢ (univ w : V) ∧ ∀ h, h ∈ˢ α → G 0 0 pt h

/-- The recursive calls: `node l` calls `l`; `cons h t` calls `h` and `t`. -/
noncomputable def treePred : NDec V → V
  | ⟨0, _, _, _, [l]⟩ => sing (nenc 1 0 pt l)
  | ⟨1, _, _, 1, [h, t]⟩ => upair (nenc 0 0 pt h) (nenc 1 0 pt t)
  | _ => empty

variable (hcl : (treeD w hW).Closed nestρ₀ empty)

/-- **The `Tree`/`List Tree` kit.** -/
noncomputable def treeKit : NestKit V V where
  nC := 2
  cl := treeCl w hW
  fr := treeFr w hW
  dp := id
  D := 2
  hD := fun _ hb => hb
  Adm := treeAdm w
  pred := treePred
  ok := by
    intro b hb G ρ hρ
    match b, hb, hρ with
    | 0, _, hρ =>
      cases (hρ : ρ = empty)
      exact (treeD w hW).toSClause_ok nestρ₀ (empty_mem_univ w) hcl
    | 1, _, hρ => exact (listD w).toSClause_ok nestρ₀ hρ.1 (hW ρ hρ.1)
  trans := by
    intro b hb G hG ρ hρ Y hY hYle t c j fs hf
    match b, hb, hρ with
    | 0, _, hρ =>
      cases (hρ : ρ = empty)
      exact (treeD w hW).toSClause_fits_mono nestρ₀ (empty_mem_univ w) (empty_mem_univ w)
        (Subset.refl _) hY ((treeD w hW).carrier_mem nestρ₀ empty) hYle hf
    | 1, _, hρ =>
      exact (listD w).toSClause_fits_mono nestρ₀ hρ.1
        ((treeD w hW).value_mem_univ Nat.one_pos nestρ₀ empty)
        (fun h hh => hG 0 0 pt h (hρ.2 h hh)) hY ((listD w).carrier_mem nestρ₀ _) hYle hf
  calls := by
    intro b hb G ρ hρ Y hY c t j fs hc ht hf u hu
    match b, hb, hρ with
    | 0, _, _ =>
      obtain ⟨l, rfl, rfl, hl⟩ := treeD_fits hf
      have hu : u ∈ˢ sing (nenc 1 0 pt l) := hu
      rw [mem_sing] at hu
      exact ⟨1, 0, pt, l, by decide, Nat.one_pos, pt_mem_unitSet, hu,
        Or.inr (Or.inr ⟨by decide, app (Y 0) pt,
          ⟨app_hole_mem_univ hY, fun _ hh => addOwn_hole hh⟩, hl⟩)⟩
    | 1, _, hρ =>
      rcases listD_fits hf with ⟨rfl, rfl⟩ | ⟨a, l, rfl, rfl, ha, hl⟩
      · exact (not_mem_empty u hu).elim
      · obtain rfl := lt_one_eq hc
        have hu : u ∈ˢ upair (nenc 0 0 pt a) (nenc 1 0 pt l) := hu
        rcases mem_upair.mp hu with rfl | rfl
        · exact ⟨0, 0, pt, a, by decide, Nat.one_pos, pt_mem_unitSet, rfl,
            Or.inr (Or.inl (hρ.2 a ha))⟩
        · exact ⟨1, 0, pt, l, by decide, Nat.one_pos, pt_mem_unitSet, rfl, Or.inl ⟨rfl, hl⟩⟩
  top := by
    intro b hb G hG
    match b, hb with
    | 0, _ => rfl
    | 1, _ =>
      exact ⟨(treeD w hW).value_mem_univ Nat.one_pos nestρ₀ empty, fun h hh =>
        hG 0 0 pt h (by decide) (by decide) Nat.one_pos pt_mem_unitSet hh⟩

/-- **The nested induction principle of `Tree`/`List Tree`**, from the two
blocks' own clauses. -/
theorem treeKit_ind : ∀ P : V → Prop,
    (∀ u, u ∈ˢ (treeKit w hW hcl).U →
      (∃ d, (treeKit w hW hcl).Dec u d ∧ ∀ j, j ∈ˢ (treeKit w hW hcl).pred d → P j) → P u) →
    ∀ u, u ∈ˢ (treeKit w hW hcl).U → P u :=
  (treeKit w hW hcl).ind

end Tree

/-- **The nested `Prop` example**: `Tree : Prop` through a `Prop`
container, every closure hypothesis discharged; `exu` at `ℓ = 0` by
`huniq_of_prop` — the injections are all the point, decodings are NOT
unique, and the induction runs on the decoding the fit carries. -/
theorem treeKit_exu_prop (B : V → V) (st : NDec V → V → V)
    (hB : ∀ u, u ∈ˢ (treeKit 0 listD_closedAll_zero (uPhi_closed_zero _ _ (empty_mem_univ 0))).U →
      B u ∈ˢ (univ 0 : V))
    (hst : ∀ u, u ∈ˢ (treeKit 0 listD_closedAll_zero (uPhi_closed_zero _ _ (empty_mem_univ 0))).U →
      ∀ d, (treeKit 0 listD_closedAll_zero (uPhi_closed_zero _ _ (empty_mem_univ 0))).Dec u d → ∀ g,
      g ∈ˢ piSet ((treeKit 0 listD_closedAll_zero (uPhi_closed_zero _ _ (empty_mem_univ 0))).pred d)
        (fun j => app (gGraph 0
          (treeKit 0 listD_closedAll_zero (uPhi_closed_zero _ _ (empty_mem_univ 0))).U
          (treeKit 0 listD_closedAll_zero (uPhi_closed_zero _ _ (empty_mem_univ 0))).Dec
          (treeKit 0 listD_closedAll_zero (uPhi_closed_zero _ _ (empty_mem_univ 0))).pred B st) j) →
      st d g ∈ˢ B u) :
    ∀ u, u ∈ˢ (treeKit 0 listD_closedAll_zero (uPhi_closed_zero _ _ (empty_mem_univ 0))).U →
      Single (gGraph 0
        (treeKit 0 listD_closedAll_zero (uPhi_closed_zero _ _ (empty_mem_univ 0))).U
        (treeKit 0 listD_closedAll_zero (uPhi_closed_zero _ _ (empty_mem_univ 0))).Dec
        (treeKit 0 listD_closedAll_zero (uPhi_closed_zero _ _ (empty_mem_univ 0))).pred B st) u :=
  NestKit.exu _ 0 B st hB hst (huniq_of_prop hB)

/-! ## `Rose α ::= node α (List (Rose α))` at a parameter -/

section Rose

variable (w : Nat) (hW : (listD (V := V) w).ClosedAll nestρ₀) (α₀ : V)

/-- The classes: `0` = `Rose` (at its parameter), `1` = `List` (at a frame). -/
noncomputable def roseCl : Nat → SClause V V
  | 0 => (roseD w hW).toSClause nestρ₀
  | _ + 1 => (listD w).toSClause nestρ₀

/-- The true frames: `Rose` at `α₀`, `List` at `⟦Rose α₀⟧`. -/
noncomputable def roseFr : Nat → V
  | 0 => α₀
  | _ + 1 => ROSE w hW α₀

/-- The admissible frames: `Rose` at its parameter; `List` at a
parameter of the level all of whose elements are good roses. -/
def roseAdm : Nat → (Nat → Nat → V → V → Prop) → V → Prop
  | 0, _, α => α = α₀
  | _ + 1, G, α => α ∈ˢ (univ w : V) ∧ ∀ h, h ∈ˢ α → G 0 0 pt h

/-- The recursive calls: `node a l` calls `l` (its label `a` is a
parameter, not a major); `cons h t` calls `h` and `t`. -/
noncomputable def rosePred : NDec V → V
  | ⟨0, _, _, _, [_, l]⟩ => sing (nenc 1 0 pt l)
  | ⟨1, _, _, 1, [h, t]⟩ => upair (nenc 0 0 pt h) (nenc 1 0 pt t)
  | _ => empty

variable (hα₀ : α₀ ∈ˢ (univ w : V)) (hcl : (roseD w hW).Closed nestρ₀ α₀)

/-- **The `Rose α₀`/`List (Rose α₀)` kit.** -/
noncomputable def roseKit : NestKit V V where
  nC := 2
  cl := roseCl w hW
  fr := roseFr w hW α₀
  dp := id
  D := 2
  hD := fun _ hb => hb
  Adm := roseAdm w α₀
  pred := rosePred
  ok := by
    intro b hb G ρ hρ
    match b, hb, hρ with
    | 0, _, hρ =>
      cases (hρ : ρ = α₀)
      exact (roseD w hW).toSClause_ok nestρ₀ hα₀ hcl
    | 1, _, hρ => exact (listD w).toSClause_ok nestρ₀ hρ.1 (hW ρ hρ.1)
  trans := by
    intro b hb G hG ρ hρ Y hY hYle t c j fs hf
    match b, hb, hρ with
    | 0, _, hρ =>
      cases (hρ : ρ = α₀)
      exact (roseD w hW).toSClause_fits_mono nestρ₀ hα₀ hα₀ (Subset.refl _) hY
        ((roseD w hW).carrier_mem nestρ₀ α₀) hYle hf
    | 1, _, hρ =>
      exact (listD w).toSClause_fits_mono nestρ₀ hρ.1 (ROSE_mem_univ hW α₀)
        (fun h hh => hG 0 0 pt h (hρ.2 h hh)) hY ((listD w).carrier_mem nestρ₀ _) hYle hf
  calls := by
    intro b hb G ρ hρ Y hY c t j fs hc ht hf u hu
    match b, hb, hρ with
    | 0, _, _ =>
      obtain ⟨a, l, rfl, rfl, -, hl⟩ := roseD_fits hf
      have hu : u ∈ˢ sing (nenc 1 0 pt l) := hu
      rw [mem_sing] at hu
      exact ⟨1, 0, pt, l, by decide, Nat.one_pos, pt_mem_unitSet, hu,
        Or.inr (Or.inr ⟨by decide, app (Y 0) pt,
          ⟨app_hole_mem_univ hY, fun _ hh => addOwn_hole hh⟩, hl⟩)⟩
    | 1, _, hρ =>
      rcases listD_fits hf with ⟨rfl, rfl⟩ | ⟨a, l, rfl, rfl, ha, hl⟩
      · exact (not_mem_empty u hu).elim
      · obtain rfl := lt_one_eq hc
        have hu : u ∈ˢ upair (nenc 0 0 pt a) (nenc 1 0 pt l) := hu
        rcases mem_upair.mp hu with rfl | rfl
        · exact ⟨0, 0, pt, a, by decide, Nat.one_pos, pt_mem_unitSet, rfl,
            Or.inr (Or.inl (hρ.2 a ha))⟩
        · exact ⟨1, 0, pt, l, by decide, Nat.one_pos, pt_mem_unitSet, rfl, Or.inl ⟨rfl, hl⟩⟩
  top := by
    intro b hb G hG
    match b, hb with
    | 0, _ => rfl
    | 1, _ =>
      exact ⟨ROSE_mem_univ hW α₀, fun h hh =>
        hG 0 0 pt h (by decide) (by decide) Nat.one_pos pt_mem_unitSet hh⟩

/-- **`exu` for `Rose α₀`/`List (Rose α₀)` at `Type`**: `huniq` from the
injections' injectivity at every class. -/
theorem roseKit_exu_type (hw : w ≠ 0) (ℓ : Nat) (B : V → V) (st : NDec V → V → V)
    (hB : ∀ u, u ∈ˢ (roseKit w hW α₀ hα₀ hcl).U → B u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ (roseKit w hW α₀ hα₀ hcl).U → ∀ d, (roseKit w hW α₀ hα₀ hcl).Dec u d → ∀ g,
      g ∈ˢ piSet ((roseKit w hW α₀ hα₀ hcl).pred d)
        (fun j => app (gGraph ℓ (roseKit w hW α₀ hα₀ hcl).U (roseKit w hW α₀ hα₀ hcl).Dec
          (roseKit w hW α₀ hα₀ hcl).pred B st) j) → st d g ∈ˢ B u) :
    ∀ u, u ∈ˢ (roseKit w hW α₀ hα₀ hcl).U →
      Single (gGraph ℓ (roseKit w hW α₀ hα₀ hcl).U (roseKit w hW α₀ hα₀ hcl).Dec
        (roseKit w hW α₀ hα₀ hcl).pred B st) u := by
  refine NestKit.exu _ ℓ B st hB hst (NestKit.huniq_of_inj _ ?_)
  intro b hb c t j fs j' fs' hf hf' h
  match b, hb with
  | 0, _ => exact (roseD w hW).toSClause_inj nestρ₀ hw hf hf' h
  | 1, _ => exact (listD w).toSClause_inj nestρ₀ hw hf hf' h

end Rose

/-! ## `T ::= leaf | mk (Rose T)` — two nesting levels -/

section RT

variable (w : Nat) (hW : (listD (V := V) w).ClosedAll nestρ₀) (hWR : (roseD w hW).ClosedAll nestρ₀)

/-- The classes: `0` = `T`, `1` = `Rose` (at a frame), `2` = `List` (at a
frame). -/
noncomputable def rtCl : Nat → SClause V V
  | 0 => (rtD w hW hWR).toSClause nestρ₀
  | 1 => (roseD w hW).toSClause nestρ₀
  | _ + 2 => (listD w).toSClause nestρ₀

/-- The true frames: `Rose` at `⟦T⟧`, `List` at `⟦Rose T⟧`. -/
noncomputable def rtFr : Nat → V
  | 0 => empty
  | 1 => RT w hW hWR
  | _ + 2 => ROSE w hW (RT w hW hWR)

/-- The admissible frames: `T` at its own frame; `Rose` at a parameter
of good `T`s; `List` at a parameter of good `Rose T`s. -/
def rtAdm : Nat → (Nat → Nat → V → V → Prop) → V → Prop
  | 0, _, α => α = empty
  | 1, G, α => α ∈ˢ (univ w : V) ∧ ∀ a, a ∈ˢ α → G 0 0 pt a
  | _ + 2, G, α => α ∈ˢ (univ w : V) ∧ ∀ h, h ∈ˢ α → G 1 0 pt h

/-- The recursive calls: `mk r` calls `r`; `node a l` (at the
instantiation `α := T`) calls `a` and `l`; `cons h t` calls `h` and `t`. -/
noncomputable def rtPred : NDec V → V
  | ⟨0, _, _, 1, [r]⟩ => sing (nenc 1 0 pt r)
  | ⟨1, _, _, _, [a, l]⟩ => upair (nenc 0 0 pt a) (nenc 2 0 pt l)
  | ⟨2, _, _, 1, [h, t]⟩ => upair (nenc 1 0 pt h) (nenc 2 0 pt t)
  | _ => empty

variable (hcl : (rtD w hW hWR).Closed nestρ₀ empty)

/-- **The `T`/`Rose T`/`List (Rose T)` kit** — the class `List (Rose T)` is
reached from `Rose`'s own field, at `Rose`'s separated tuple. -/
noncomputable def rtKit : NestKit V V where
  nC := 3
  cl := rtCl w hW hWR
  fr := rtFr w hW hWR
  dp := id
  D := 3
  hD := fun _ hb => hb
  Adm := rtAdm w
  pred := rtPred
  ok := by
    intro b hb G ρ hρ
    match b, hb, hρ with
    | 0, _, hρ =>
      cases (hρ : ρ = empty)
      exact (rtD w hW hWR).toSClause_ok nestρ₀ (empty_mem_univ w) hcl
    | 1, _, hρ => exact (roseD w hW).toSClause_ok nestρ₀ hρ.1 (hWR ρ hρ.1)
    | 2, _, hρ => exact (listD w).toSClause_ok nestρ₀ hρ.1 (hW ρ hρ.1)
  trans := by
    intro b hb G hG ρ hρ Y hY hYle t c j fs hf
    match b, hb, hρ with
    | 0, _, hρ =>
      cases (hρ : ρ = empty)
      exact (rtD w hW hWR).toSClause_fits_mono nestρ₀ (empty_mem_univ w) (empty_mem_univ w)
        (Subset.refl _) hY ((rtD w hW hWR).carrier_mem nestρ₀ empty) hYle hf
    | 1, _, hρ =>
      exact (roseD w hW).toSClause_fits_mono nestρ₀ hρ.1
        ((rtD w hW hWR).value_mem_univ Nat.one_pos nestρ₀ empty)
        (fun a ha => hG 0 0 pt a (hρ.2 a ha)) hY ((roseD w hW).carrier_mem nestρ₀ _) hYle hf
    | 2, _, hρ =>
      exact (listD w).toSClause_fits_mono nestρ₀ hρ.1 (ROSE_mem_univ hW _)
        (fun h hh => hG 1 0 pt h (hρ.2 h hh)) hY ((listD w).carrier_mem nestρ₀ _) hYle hf
  calls := by
    intro b hb G ρ hρ Y hY c t j fs hc ht hf u hu
    match b, hb, hρ with
    | 0, _, _ =>
      rcases rtD_fits hf with ⟨rfl, rfl⟩ | ⟨r, rfl, rfl, hr⟩
      · exact (not_mem_empty u hu).elim
      · have hu : u ∈ˢ sing (nenc 1 0 pt r) := hu
        rw [mem_sing] at hu
        exact ⟨1, 0, pt, r, by decide, Nat.one_pos, pt_mem_unitSet, hu,
          Or.inr (Or.inr ⟨by decide, app (Y 0) pt,
            ⟨app_hole_mem_univ hY, fun _ hh => addOwn_hole hh⟩, hr⟩)⟩
    | 1, _, hρ =>
      obtain ⟨a, l, rfl, rfl, ha, hl⟩ := roseD_fits hf
      have hu : u ∈ˢ upair (nenc 0 0 pt a) (nenc 2 0 pt l) := hu
      rcases mem_upair.mp hu with rfl | rfl
      · exact ⟨0, 0, pt, a, by decide, Nat.one_pos, pt_mem_unitSet, rfl,
          Or.inr (Or.inl (hρ.2 a ha))⟩
      · exact ⟨2, 0, pt, l, by decide, Nat.one_pos, pt_mem_unitSet, rfl,
          Or.inr (Or.inr ⟨by decide, app (Y 0) pt,
            ⟨app_hole_mem_univ hY, fun _ hh => addOwn_hole hh⟩, hl⟩)⟩
    | 2, _, hρ =>
      rcases listD_fits hf with ⟨rfl, rfl⟩ | ⟨a, l, rfl, rfl, ha, hl⟩
      · exact (not_mem_empty u hu).elim
      · obtain rfl := lt_one_eq hc
        have hu : u ∈ˢ upair (nenc 1 0 pt a) (nenc 2 0 pt l) := hu
        rcases mem_upair.mp hu with rfl | rfl
        · exact ⟨1, 0, pt, a, by decide, Nat.one_pos, pt_mem_unitSet, rfl,
            Or.inr (Or.inl (hρ.2 a ha))⟩
        · exact ⟨2, 0, pt, l, by decide, Nat.one_pos, pt_mem_unitSet, rfl, Or.inl ⟨rfl, hl⟩⟩
  top := by
    intro b hb G hG
    match b, hb with
    | 0, _ => rfl
    | 1, _ =>
      exact ⟨(rtD w hW hWR).value_mem_univ Nat.one_pos nestρ₀ empty, fun a ha =>
        hG 0 0 pt a (by decide) (by decide) Nat.one_pos pt_mem_unitSet ha⟩
    | 2, _ =>
      exact ⟨ROSE_mem_univ hW _, fun h hh =>
        hG 1 0 pt h (by decide) (by decide) Nat.one_pos pt_mem_unitSet hh⟩

/-- **`exu` for the two-level nest at `Type`.** -/
theorem rtKit_exu_type (hw : w ≠ 0) (ℓ : Nat) (B : V → V) (st : NDec V → V → V)
    (hB : ∀ u, u ∈ˢ (rtKit w hW hWR hcl).U → B u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ (rtKit w hW hWR hcl).U → ∀ d, (rtKit w hW hWR hcl).Dec u d → ∀ g,
      g ∈ˢ piSet ((rtKit w hW hWR hcl).pred d)
        (fun j => app (gGraph ℓ (rtKit w hW hWR hcl).U (rtKit w hW hWR hcl).Dec
          (rtKit w hW hWR hcl).pred B st) j) → st d g ∈ˢ B u) :
    ∀ u, u ∈ˢ (rtKit w hW hWR hcl).U →
      Single (gGraph ℓ (rtKit w hW hWR hcl).U (rtKit w hW hWR hcl).Dec
        (rtKit w hW hWR hcl).pred B st) u := by
  refine NestKit.exu _ ℓ B st hB hst (NestKit.huniq_of_inj _ ?_)
  intro b hb c t j fs j' fs' hf hf' h
  match b, hb with
  | 0, _ => exact (rtD w hW hWR).toSClause_inj nestρ₀ hw hf hf' h
  | 1, _ => exact (roseD w hW).toSClause_inj nestρ₀ hw hf hf' h
  | 2, _ => exact (listD w).toSClause_inj nestρ₀ hw hf hf' h

end RT

/-- **The two-level nest at `Prop`**: every closure hypothesis
discharged, `huniq` by `huniq_of_prop`. -/
theorem rtKit_exu_prop (B : V → V) (st : NDec V → V → V)
    (hB : ∀ u, u ∈ˢ (rtKit 0 listD_closedAll_zero roseD_closedAll_zero
      (uPhi_closed_zero _ _ (empty_mem_univ 0))).U → B u ∈ˢ (univ 0 : V))
    (hst : ∀ u, u ∈ˢ (rtKit 0 listD_closedAll_zero roseD_closedAll_zero
        (uPhi_closed_zero _ _ (empty_mem_univ 0))).U →
      ∀ d, (rtKit 0 listD_closedAll_zero roseD_closedAll_zero
        (uPhi_closed_zero _ _ (empty_mem_univ 0))).Dec u d → ∀ g,
      g ∈ˢ piSet ((rtKit 0 listD_closedAll_zero roseD_closedAll_zero
          (uPhi_closed_zero _ _ (empty_mem_univ 0))).pred d)
        (fun j => app (gGraph 0
          (rtKit 0 listD_closedAll_zero roseD_closedAll_zero
            (uPhi_closed_zero _ _ (empty_mem_univ 0))).U
          (rtKit 0 listD_closedAll_zero roseD_closedAll_zero
            (uPhi_closed_zero _ _ (empty_mem_univ 0))).Dec
          (rtKit 0 listD_closedAll_zero roseD_closedAll_zero
            (uPhi_closed_zero _ _ (empty_mem_univ 0))).pred B st) j) →
      st d g ∈ˢ B u) :
    ∀ u, u ∈ˢ (rtKit 0 listD_closedAll_zero roseD_closedAll_zero
        (uPhi_closed_zero _ _ (empty_mem_univ 0))).U →
      Single (gGraph 0
        (rtKit 0 listD_closedAll_zero roseD_closedAll_zero
          (uPhi_closed_zero _ _ (empty_mem_univ 0))).U
        (rtKit 0 listD_closedAll_zero roseD_closedAll_zero
          (uPhi_closed_zero _ _ (empty_mem_univ 0))).Dec
        (rtKit 0 listD_closedAll_zero roseD_closedAll_zero
          (uPhi_closed_zero _ _ (empty_mem_univ 0))).pred B st) u :=
  NestKit.exu _ 0 B st hB hst (huniq_of_prop hB)

end ConLeche.SetTheory
