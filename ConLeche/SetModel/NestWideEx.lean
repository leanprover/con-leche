module

public import ConLeche.SetModel.NestWideAt
@[expose] public section

/-!
# Instances of the nested (W) kit (lane NESTW-KIT)

`SetModel/NestWide.lean`'s `closed_of_wide_groups` over the HOLEOP block
data (`SetModel/HoleOp.lean`), each at EVERY level `w` — the wide
operator's closed tuple is `UBlock.closed_of_flatAll` (the flat kit at
`w ≠ 0`, free at `Prop`), so no closure hypothesis is left anywhere:

* **Rose/List** — `Rose α ::= node α (List (Rose α))` at a parameter
  `α₀`, one key `List (Rose α₀)`: `roseD_closedAll`, `mem_ROSE_all`;
  and composing the key away LEAVES `Rose`'s operator
  (`rose_composeKeys_eq`);
* **two-level nesting** — `T ::= leaf | mk (Rose T)`: two keys `Rose T`
  (depth 0) and `List (Rose T)` (depth 1, its parameter read off the
  `Rose T` key's slot); `Rose T`'s substitution law reads the deeper
  key's domination: `rtD_closedAll`, `mem_RT_all`;
* **a mutual container group reached by restart** — `A α ::= nilA |
  consA α (B α)`, `B α ::= consB α (A α)`, `T ::= node (A T)`: two keys
  `A T`, `B T` of ONE group, referring to each other: `taD_closedAll`,
  `mem_TA_all`;
* **`Prop`** — the same theorems at `w = 0` (`mem_TA_prop`,
  `mem_RT_prop`): the kit runs unchanged, the wide witness is
  `closedTuple_zero`.

Each container's (W) is its own clause's (`listD_closedAll`,
`altD_closedAll`: flat blocks; `roseD_closedAll`: this kit), consumed
only at the instantiation; no container is asked to be monotone in its
parameter.
-/

namespace ConLeche.SetTheory

namespace NestWideEx

open ConLeche.SetModel

universe u

variable {V : Type u} [SetTheory V]

/-! ## Flat fields of unindexed blocks -/

/-- The recursive field `T_m` of an unindexed member. -/
noncomputable def hF (m : Nat) : FField V := .recur (.hole m fun _ => pt)

/-- A constant ordinary field. -/
noncomputable def cF (A : V) : FField V := .plain fun _ => A

theorem hF_wf {w K m : Nat} (h : m < K) : (hF (V := V) m).WF w K := h
theorem cF_wf {w K : Nat} {A : V} (h : A ∈ˢ (univ w : V)) : (cF A).WF w K := fun _ => h
theorem hF_blind (m : Nat) : (hF (V := V) m).Blind := fun _ _ => rfl
omit [SetTheory V] in
theorem cF_blind (A : V) : (cF A).Blind := fun _ _ => rfl

omit [SetTheory V] in
theorem all_nil {P : FField V → Prop} : ∀ f ∈ ([] : List (FField V)), P f := fun _ h => nomatch h

omit [SetTheory V] in
theorem all_cons {P : FField V → Prop} {f : FField V} {ffs : List (FField V)} (h : P f)
    (hs : ∀ g ∈ ffs, P g) : ∀ g ∈ f :: ffs, P g :=
  List.forall_mem_cons.mpr ⟨h, hs⟩

/-- A constructor with no fields is flat. -/
theorem flat_nil {w K : Nat} {ρ : Nat → V} {α : V} {hp : ∀ F ∈ ([] : List ((Nat → V) → (Nat → V) → V → V)), Pos w K F} :
    FlatCtor w K ρ α (uctor [] hp) [] :=
  FlatCtor.of_blind trivial all_nil all_nil

/-- The fibre of an unindexed component through the unit index. -/
theorem famLe_unit {A B : V} (h : ∀ x, x ∈ˢ app A pt → x ∈ˢ app B pt) : FamLe (unitSet : V) A B := by
  intro i hi
  obtain rfl := mem_unitSet_iff.mp hi
  exact h

/-! ## `List` and the mutual group `A`/`B`: flat containers -/

theorem listD_flat (w : Nat) (ρ : Nat → V) {α : V} (hα : α ∈ˢ (univ w : V)) :
    (listD (V := V) w).FlatAt ρ α :=
  UBlock.flatAt_of fun _ _ => ⟨[[], [cF α, hF 0]], flat_nil,
    FlatCtor.of_blind ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩
      (all_cons (cF_wf hα) (all_cons (hF_wf Nat.one_pos) all_nil))
      (all_cons (cF_blind α) (all_cons (hF_blind 0) all_nil)), trivial⟩

/-- **`List`'s (W) at every level and parameter** — the flat kit. -/
theorem listD_closedAll (w : Nat) (ρ : Nat → V) : (listD (V := V) w).ClosedAll ρ :=
  fun _ hα => UBlock.closed_of_flatAll _ ρ hα fun _ => listD_flat w ρ hα

/-- `A α ::= nilA | consA α (B α)`, `B α ::= consB α (A α)`: a mutual
container group (alternating lists). -/
noncomputable def altD (w : Nat) : UBlock V w 2 where
  Is := unitIs
  ctors := fun c =>
    if c = 0 then
      [uctor [] pos_nil,
       uctor [fun _ _ α => α, holeF 1] (pos_cons Pos.param (pos_cons (pos_holeF (by decide)) pos_nil))]
    else [uctor [fun _ _ α => α, holeF 0] (pos_cons Pos.param (pos_cons (pos_holeF (by decide)) pos_nil))]

theorem altD_flat (w : Nat) (ρ : Nat → V) {α : V} (hα : α ∈ˢ (univ w : V)) :
    (altD (V := V) w).FlatAt ρ α :=
  UBlock.flatAt_of fun c hc => match c, hc with
    | 0, _ => ⟨[[], [cF α, hF 1]], flat_nil,
        FlatCtor.of_blind ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩
          (all_cons (cF_wf hα) (all_cons (hF_wf (by decide)) all_nil))
          (all_cons (cF_blind α) (all_cons (hF_blind 1) all_nil)), trivial⟩
    | 1, _ => ⟨[[cF α, hF 0]],
        FlatCtor.of_blind ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩
          (all_cons (cF_wf hα) (all_cons (hF_wf (by decide)) all_nil))
          (all_cons (cF_blind α) (all_cons (hF_blind 0) all_nil)), trivial⟩

theorem altD_closedAll (w : Nat) (ρ : Nat → V) : (altD (V := V) w).ClosedAll ρ :=
  fun _ hα => UBlock.closed_of_flatAll _ ρ hα fun _ => altD_flat w ρ hα

/-- `⟦A⟧ β`. -/
noncomputable def ALTA (w : Nat) (β : V) : V := (altD (V := V) w).value (fun _ => empty) β

/-! ## Rose/List: one key -/

section Rose

variable (w : Nat)

/-- **The wide datum of `Rose α₀`**: component 0 is `Rose` with its
`List (Rose α₀)` field the key's hole `hole 1`; component 1 is the key,
`listD`'s constructors with `param ↦ hole 0`, `hole 0 ↦ hole 1`. -/
noncomputable def roseWide : UBlock V w 2 where
  Is := unitIs
  ctors := fun c =>
    if c = 0 then
      [uctor [fun _ _ α => α, holeF 1] (pos_cons Pos.param (pos_cons (pos_holeF (by decide)) pos_nil))]
    else
      [uctor [] pos_nil,
       uctor [holeF 0, holeF 1] (pos_cons (pos_holeF (by decide)) (pos_cons (pos_holeF (by decide)) pos_nil))]

theorem roseWide_flat (ρ : Nat → V) {α : V} (hα : α ∈ˢ (univ w : V)) : (roseWide (V := V) w).FlatAt ρ α :=
  UBlock.flatAt_of fun c hc => match c, hc with
    | 0, _ => ⟨[[cF α, hF 1]],
        FlatCtor.of_blind ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩
          (all_cons (cF_wf hα) (all_cons (hF_wf (by decide)) all_nil))
          (all_cons (cF_blind α) (all_cons (hF_blind 1) all_nil)), trivial⟩
    | 1, _ => ⟨[[], [hF 0, hF 1]], flat_nil,
        FlatCtor.of_blind ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩
          (all_cons (hF_wf (by decide)) (all_cons (hF_wf (by decide)) all_nil))
          (all_cons (hF_blind 0) (all_cons (hF_blind 1) all_nil)), trivial⟩

/-- The key's container group: `List` at the parameter read off the
member slot. -/
noncomputable def roseKeys : KeyGroups V where
  grp := fun _ => 0
  cmp := fun _ => 0
  g := fun _ => 1
  IsG := fun _ _ => unitIs
  Θ := fun _ W => uPhi (listD w) (fun _ => empty) (app (W 0) pt)
  dep := fun _ => 0

theorem roseKeys_ok (ρ : Nat → V) (α₀ : V) :
    (roseKeys (V := V) w).Ok w 1 1 unitIs (uPhi (roseWide w) ρ α₀) where
  cmp_lt := fun _ _ => Nat.one_pos
  inj := fun q q' hq hq' _ _ => by omega
  idx := fun _ _ _ => rfl
  functor := fun W hW _ _ => by
    have hβ : app (W 0) pt ∈ˢ (univ w : V) := app_fam_mem_univ (hW 0 (by decide)) pt
    exact ⟨uPhi_mono (listD w) _ hβ, listD_closedAll w _ _ hβ⟩
  sub := fun W _ q hq _ => by
    obtain rfl : q = 0 := by omega
    show FamLe unitSet (uPhi (listD w) (fun _ => empty) (app (W 0) pt)
      ((roseKeys w).fill w 1 1 ((roseKeys w).grp 0) W) ((roseKeys w).cmp 0)) _
    have hfill : (roseKeys (V := V) w).fill w 1 1 0 W 0 = W 1 :=
      KeyGroups.fill_reached (q := 0) (by decide) (fun q q' hq hq' _ _ => by omega) W
    refine uPhi_famLe (listD w) (roseWide w) _ ρ _ α₀ _ W rfl ?_
    intro t _ j fs ct hct hf hi
    match j, fs, hct, hf with
    | 0, [], rfl, _ => exact ⟨_, rfl, trivial, hi⟩
    | 1, [h, l], rfl, hf => exact ⟨_, rfl, ⟨hf.1, by show _ ∈ˢ app (W 1) pt; rw [← hfill]; exact hf.2.1, trivial⟩, hi⟩

/-- **`Rose`'s (W) at every level and parameter — through the kit**:
the wide closed tuple (flat kit / `Prop`), the key composed away,
`Rose`'s operator below the composed one because `⟦List⟧ ⟦X⟧` lies in
any key slot dominating the key's value. -/
theorem roseD_closed (ρ : Nat → V) {α₀ : V} (hα₀ : α₀ ∈ˢ (univ w : V)) :
    (roseD w (listD_closedAll w _)).Closed ρ α₀ := by
  refine closed_of_wide_groups (k := 1) (n := 1) (Is := unitIs) (Ψ := uPhi (roseWide w) ρ α₀)
    (uPhi_mono (roseWide w) ρ hα₀) (UBlock.closed_of_flatAll _ ρ hα₀ fun _ => roseWide_flat w ρ hα₀)
    (roseKeys w) (roseKeys_ok w ρ α₀) ?_
  intro X Y _ _ hdom m hm
  obtain rfl : m = 0 := by omega
  refine uPhi_famLe (roseD w _) (roseWide w) ρ ρ α₀ α₀ X (catTup 1 X Y) rfl ?_
  intro t _ j fs ct hct hf hi
  match j, fs, hct, hf with
  | 0, [a, l], rfl, hf =>
    exact ⟨_, rfl, ⟨hf.1, hdom 0 Nat.one_pos pt pt_mem_unitSet l hf.2.1, trivial⟩, hi⟩

/-- **`Rose` as a `WideAt` record** (NESTW L7 step 2's check): the same
wide datum and key group, at the tagged-tower injection. -/
noncomputable def roseWideAt (hw : w ≠ 0) (ρ : Nat → V) {α₀ : V} (hα₀ : α₀ ∈ˢ (univ w : V)) :
    WideAt w 1 unitIs (uPhi (roseD w (listD_closedAll w _)) ρ α₀) where
  n := 1
  ub := roseWide w
  isLo := fun _ _ => rfl
  ι := towerInj
  ρ := ρ
  α := α₀
  hα := hα₀
  hι := towerInj_mem hw _ ρ hα₀
  flat := roseWide_flat w ρ hα₀
  P := roseKeys w
  hP := by
    rw [show uPhiI (roseWide (V := V) w) towerInj ρ α₀ = uPhi (roseWide w) ρ α₀ from
      funext fun X => funext (uPhiI_tower _ ρ α₀ X)]
    exact roseKeys_ok w ρ α₀
  mem := fun X Y _ _ hdom m hm => by
    rw [show uPhiI (roseWide (V := V) w) towerInj ρ α₀ = uPhi (roseWide w) ρ α₀ from
      funext fun X => funext (uPhiI_tower _ ρ α₀ X)]
    obtain rfl : m = 0 := by omega
    refine uPhi_famLe (roseD w _) (roseWide w) ρ ρ α₀ α₀ X (catTup 1 X Y) rfl ?_
    intro t _ j fs ct hct hf hi
    match j, fs, hct, hf with
    | 0, [a, l], rfl, hf =>
      exact ⟨_, rfl, ⟨hf.1, hdom 0 Nat.one_pos pt pt_mem_unitSet l hf.2.1, trivial⟩, hi⟩

example (hw : w ≠ 0) (ρ : Nat → V) {α₀ : V} (hα₀ : α₀ ∈ˢ (univ w : V)) :
    (roseD w (listD_closedAll w _)).Closed ρ α₀ :=
  (roseWideAt w hw ρ hα₀).closed hw

theorem roseD_closedAll (ρ : Nat → V) : (roseD (V := V) w (listD_closedAll w _)).ClosedAll ρ :=
  fun _ hα => roseD_closed w ρ hα

/-- **`⟦Rose⟧ α`'s fibre law at every level, no hypothesis left.** -/
theorem mem_ROSE_all {α : V} (hα : α ∈ˢ (univ w : V)) {x : V} :
    x ∈ˢ ROSE w (listD_closedAll w _) α ↔
      ∃ a l, a ∈ˢ α ∧ l ∈ˢ LIST w (ROSE w (listD_closedAll (V := V) w _) α) ∧ x = uinj w 0 [a, l] :=
  mem_ROSE _ hα (roseD_closed w _ hα)

/-- **Composing the key away LEAVES `Rose`'s operator**: on the member
tuple space, `Ψ` with the key replaced by the keys' least tuple IS
`Rose`'s hole operator (`composeKeys_eq` at the container's value, then
the fibre laws). -/
theorem rose_composeKeys_eq (ρ : Nat → V) {α₀ : V} (hα₀ : α₀ ∈ˢ (univ w : V)) {X : Nat → V}
    (hX : InTupleSpace w 1 unitIs X) :
    composeKeys w 1 1 unitIs (uPhi (roseWide w) ρ α₀) X 0 =
      uPhi (roseD w (listD_closedAll w _)) ρ α₀ X 0 := by
  let T : Nat → V := fun _ => (listD w).carrier (fun _ => empty) (app (X 0) pt) 0
  have hβ : app (X 0) pt ∈ˢ (univ w : V) := app_fam_mem_univ (hX 0 Nat.one_pos) pt
  have hclL := listD_closedAll w (fun _ => empty) _ hβ
  have hT : InTupleSpace w 1 (dropTup 1 unitIs) T := fun _ _ => (listD w).carrier_mem _ _ 0 Nat.one_pos
  have hpre : TupleLe 1 (dropTup 1 unitIs) (keySec 1 (uPhi (roseWide w) ρ α₀) X T) T := by
    intro q hq
    obtain rfl : q = 0 := by omega
    refine FamLe.trans (Y := uPhi (listD w) (fun _ => empty) (app (X 0) pt)
      ((listD w).carrier (fun _ => empty) (app (X 0) pt)) 0) ?_
      (lfpTuple_closed hclL (uPhi_mono _ _ hβ) 0 Nat.one_pos)
    refine uPhi_famLe (roseWide w) (listD w) ρ (fun _ => empty) α₀ (app (X 0) pt) (catTup 1 X T) _
      (c := 1) (c' := 0) rfl ?_
    intro t _ j fs ct hct hf hi
    match j, fs, hct, hf with
    | 0, [], rfl, _ => exact ⟨_, rfl, trivial, hi⟩
    | 1, [h, l], rfl, hf => exact ⟨_, rfl, ⟨hf.1, hf.2.1, trivial⟩, hi⟩
  have hle : TupleLe 1 (dropTup 1 unitIs) T (keyLfp w 1 1 unitIs (uPhi (roseWide w) ρ α₀) X) := by
    have hd := KeyGroups.dominated_of_groups (roseKeys_ok w ρ α₀) (uPhi_mono (roseWide w) ρ hα₀) hX ⟨T, hT, hpre⟩
    intro q hq
    obtain rfl : q = 0 := by omega
    exact hd 0 Nat.one_pos
  rw [composeKeys_eq (uPhi_mono (roseWide w) ρ hα₀) (uPhi_maps (roseWide w) ρ hα₀) hX hT hpre hle 0
    (by decide)]
  have hS := inTupleSpace_catTup hX hT
  have h1 : FamLe unitSet (uPhi (roseWide w) ρ α₀ (catTup 1 X T) 0)
      (uPhi (roseD w (listD_closedAll w _)) ρ α₀ X 0) := by
    refine uPhi_famLe (roseWide w) (roseD w _) ρ ρ α₀ α₀ (catTup 1 X T) X (c := 0) (c' := 0) rfl ?_
    intro t _ j fs ct hct hf hi
    match j, fs, hct, hf with
    | 0, [a, l], rfl, hf => exact ⟨_, rfl, ⟨hf.1, hf.2.1, trivial⟩, hi⟩
  have h2 : FamLe unitSet (uPhi (roseD w (listD_closedAll w _)) ρ α₀ X 0)
      (uPhi (roseWide w) ρ α₀ (catTup 1 X T) 0) := by
    refine uPhi_famLe (roseD w _) (roseWide w) ρ ρ α₀ α₀ X (catTup 1 X T) (c := 0) (c' := 0) rfl ?_
    intro t _ j fs ct hct hf hi
    match j, fs, hct, hf with
    | 0, [a, l], rfl, hf => exact ⟨_, rfl, ⟨hf.1, hf.2.1, trivial⟩, hi⟩
  exact famSpace_ext (uPhi_maps (roseWide w) ρ hα₀ _ hS 0 Nat.two_pos)
    (uPhi_maps (roseD w (listD_closedAll w _)) ρ hα₀ _ hX 0 Nat.one_pos)
    fun i hi => Subset.antisymm (h1 i hi) (h2 i hi)

end Rose

/-! ## Two-level nesting: `T ::= leaf | mk (Rose T)` — two keys, two depths -/

section RT

variable (w : Nat)

/-- **The wide datum**: component 0 is `T` (`mk`'s field the key
`Rose T`'s hole `hole 1`); component 1 the key `Rose T` (`node T (List
(Rose T))`: `hole 0`, then the deeper key's hole `hole 2`); component 2
the key `List (Rose T)` (`nil | cons (Rose T) (List (Rose T))`: `hole 1`,
`hole 2`). -/
noncomputable def rtWide : UBlock V w 3 where
  Is := unitIs
  ctors := fun c =>
    if c = 0 then [uctor [] pos_nil, uctor [holeF 1] (pos_cons (pos_holeF (by decide)) pos_nil)]
    else if c = 1 then
      [uctor [holeF 0, holeF 2] (pos_cons (pos_holeF (by decide)) (pos_cons (pos_holeF (by decide)) pos_nil))]
    else
      [uctor [] pos_nil,
       uctor [holeF 1, holeF 2] (pos_cons (pos_holeF (by decide)) (pos_cons (pos_holeF (by decide)) pos_nil))]

theorem rtWide_flat (ρ : Nat → V) (α : V) : (rtWide (V := V) w).FlatAt ρ α :=
  UBlock.flatAt_of fun c hc => match c, hc with
    | 0, _ => ⟨[[], [hF 1]], flat_nil,
        FlatCtor.of_blind ⟨fun _ _ => rfl, trivial⟩ (all_cons (hF_wf (by decide)) all_nil)
          (all_cons (hF_blind 1) all_nil), trivial⟩
    | 1, _ => ⟨[[hF 0, hF 2]],
        FlatCtor.of_blind ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩
          (all_cons (hF_wf (by decide)) (all_cons (hF_wf (by decide)) all_nil))
          (all_cons (hF_blind 0) (all_cons (hF_blind 2) all_nil)), trivial⟩
    | 2, _ => ⟨[[], [hF 1, hF 2]], flat_nil,
        FlatCtor.of_blind ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩
          (all_cons (hF_wf (by decide)) (all_cons (hF_wf (by decide)) all_nil))
          (all_cons (hF_blind 1) (all_cons (hF_blind 2) all_nil)), trivial⟩

/-- The keys' groups: `Rose` at the member slot (depth 0), `List` at
the `Rose T` key's slot (depth 1). -/
noncomputable def rtKeys : KeyGroups V where
  grp := fun q => q
  cmp := fun _ => 0
  g := fun _ => 1
  IsG := fun _ _ => unitIs
  Θ := fun G W => if G = 0 then uPhi (roseD w (listD_closedAll w _)) (fun _ => empty) (app (W 0) pt)
    else uPhi (listD w) (fun _ => empty) (app (W 1) pt)
  dep := fun G => G

theorem rtKeys_ok (ρ : Nat → V) (α : V) :
    (rtKeys (V := V) w).Ok w 1 2 unitIs (uPhi (rtWide w) ρ α) where
  cmp_lt := fun _ _ => Nat.one_pos
  inj := fun _ _ _ _ h _ => h
  idx := fun _ _ _ => rfl
  functor := fun W hW q hq => by
    have hβ0 : app (W 0) pt ∈ˢ (univ w : V) := app_fam_mem_univ (hW 0 (by decide)) pt
    have hβ1 : app (W 1) pt ∈ˢ (univ w : V) := app_fam_mem_univ (hW 1 (by decide)) pt
    match q, hq with
    | 0, _ => exact ⟨uPhi_mono (roseD w _) _ hβ0, roseD_closed w _ hβ0⟩
    | 1, _ => exact ⟨uPhi_mono (listD w) _ hβ1, listD_closedAll w _ _ hβ1⟩
  sub := fun W _ q hq hdeep => by
    have hinj : ∀ q q', q < 2 → q' < 2 → (rtKeys (V := V) w).grp q = (rtKeys (V := V) w).grp q' →
        (rtKeys (V := V) w).cmp q = (rtKeys (V := V) w).cmp q' → q = q' := fun _ _ _ _ h _ => h
    match q, hq with
    | 0, _ =>
      have hfill : (rtKeys (V := V) w).fill w 1 2 0 W 0 = W 1 :=
        KeyGroups.fill_reached (q := 0) (by decide) hinj W
      have hd := hdeep 1 (by decide) (by show 0 < 1; decide)
      show FamLe unitSet (uPhi (roseD w (listD_closedAll w _)) (fun _ => empty) (app (W 0) pt)
        ((rtKeys w).fill w 1 2 0 W) 0) (uPhi (rtWide w) ρ α W 1)
      refine uPhi_famLe (roseD w _) (rtWide w) _ ρ _ α _ W rfl ?_
      intro t _ j fs ct hct hf hi
      match j, fs, hct, hf with
      | 0, [a, l], rfl, hf =>
        have hl : l ∈ˢ LIST w (app ((rtKeys (V := V) w).fill w 1 2 0 W 0) pt) := hf.2.1
        rw [hfill] at hl
        exact ⟨_, rfl, ⟨hf.1, hd pt pt_mem_unitSet l hl, trivial⟩, hi⟩
    | 1, _ =>
      have hfill : (rtKeys (V := V) w).fill w 1 2 1 W 0 = W 2 :=
        KeyGroups.fill_reached (q := 1) (by decide) hinj W
      show FamLe unitSet (uPhi (listD w) (fun _ => empty) (app (W 1) pt)
        ((rtKeys w).fill w 1 2 1 W) 0) (uPhi (rtWide w) ρ α W 2)
      refine uPhi_famLe (listD w) (rtWide w) _ ρ _ α _ W rfl ?_
      intro t _ j fs ct hct hf hi
      match j, fs, hct, hf with
      | 0, [], rfl, _ => exact ⟨_, rfl, trivial, hi⟩
      | 1, [h, l], rfl, hf =>
        exact ⟨_, rfl, ⟨hf.1, by show _ ∈ˢ app (W 2) pt; rw [← hfill]; exact hf.2.1, trivial⟩, hi⟩

/-- **`T`'s (W) at every level — through the kit, two keys deep.** -/
theorem rtD_closed (ρ : Nat → V) {α : V} (hα : α ∈ˢ (univ w : V)) :
    (rtD w (listD_closedAll w _) (roseD_closedAll w _)).Closed ρ α := by
  refine closed_of_wide_groups (k := 1) (n := 2) (Is := unitIs) (Ψ := uPhi (rtWide w) ρ α)
    (uPhi_mono (rtWide w) ρ hα) (UBlock.closed_of_flatAll _ ρ hα fun _ => rtWide_flat w ρ α)
    (rtKeys w) (rtKeys_ok w ρ α) ?_
  intro X Y _ _ hdom m hm
  obtain rfl : m = 0 := by omega
  refine uPhi_famLe (rtD w _ _) (rtWide w) ρ ρ α α X (catTup 1 X Y) rfl ?_
  intro t _ j fs ct hct hf hi
  match j, fs, hct, hf with
  | 0, [], rfl, _ => exact ⟨_, rfl, trivial, hi⟩
  | 1, [r], rfl, hf => exact ⟨_, rfl, ⟨hdom 0 (by decide) pt pt_mem_unitSet r hf.1, trivial⟩, hi⟩

/-- **`⟦T⟧`'s fibre law at every level, no hypothesis left.** -/
theorem mem_RT_all {x : V} :
    x ∈ˢ RT w (listD_closedAll w _) (roseD_closedAll w _) ↔
      x = uinj w 0 [] ∨ ∃ r, r ∈ˢ ROSE w (listD_closedAll w _)
        (RT (V := V) w (listD_closedAll w _) (roseD_closedAll w _)) ∧ x = uinj w 1 [r] :=
  mem_RT _ _ (rtD_closed w _ (empty_mem_univ w))

/-- The two-level block at `Prop`, through the same kit. -/
theorem mem_RT_prop {x : V} :
    x ∈ˢ RT 0 (listD_closedAll 0 _) (roseD_closedAll 0 _) ↔
      x = pt ∨ ∃ r, r ∈ˢ ROSE 0 (listD_closedAll 0 _)
        (RT (V := V) 0 (listD_closedAll 0 _) (roseD_closedAll 0 _)) ∧ x = pt := by
  rw [mem_RT_all]
  simp only [uinj_zero]

end RT

/-! ## A mutual container group reached by restart: `T ::= node (A T)` -/

section TA

variable (w : Nat)

/-- `T ::= node (A T)`, the container `A` of the mutual group `A`/`B`. -/
noncomputable def taD : UBlock V w 1 where
  Is := unitIs
  ctors := fun _ =>
    [uctor [fun _ X _ => ALTA w (app (X 0) pt)]
      (pos_cons (Pos.cont (ALTA w) (fun β _ => (altD w).value_mem_univ (by decide) _ β)
        ((altD w).value_mono (by decide) _ (altD_closedAll w _)) (holeF 0) (pos_holeF Nat.one_pos))
        pos_nil)]

/-- `⟦T⟧`. -/
noncomputable def TA : V := (taD (V := V) w).value (fun _ => empty) empty

/-- **The wide datum**: component 0 is `T` (`node`'s field the key
`A T`'s hole `hole 1`); components 1 and 2 are the keys `A T` and `B T`
— ONE container group, reached by restart, each key's constructors
reading the other key's hole. -/
noncomputable def taWide : UBlock V w 3 where
  Is := unitIs
  ctors := fun c =>
    if c = 0 then [uctor [holeF 1] (pos_cons (pos_holeF (by decide)) pos_nil)]
    else if c = 1 then
      [uctor [] pos_nil,
       uctor [holeF 0, holeF 2] (pos_cons (pos_holeF (by decide)) (pos_cons (pos_holeF (by decide)) pos_nil))]
    else
      [uctor [holeF 0, holeF 1] (pos_cons (pos_holeF (by decide)) (pos_cons (pos_holeF (by decide)) pos_nil))]

theorem taWide_flat (ρ : Nat → V) (α : V) : (taWide (V := V) w).FlatAt ρ α :=
  UBlock.flatAt_of fun c hc => match c, hc with
    | 0, _ => ⟨[[hF 1]],
        FlatCtor.of_blind ⟨fun _ _ => rfl, trivial⟩ (all_cons (hF_wf (by decide)) all_nil)
          (all_cons (hF_blind 1) all_nil), trivial⟩
    | 1, _ => ⟨[[], [hF 0, hF 2]], flat_nil,
        FlatCtor.of_blind ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩
          (all_cons (hF_wf (by decide)) (all_cons (hF_wf (by decide)) all_nil))
          (all_cons (hF_blind 0) (all_cons (hF_blind 2) all_nil)), trivial⟩
    | 2, _ => ⟨[[hF 0, hF 1]],
        FlatCtor.of_blind ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩
          (all_cons (hF_wf (by decide)) (all_cons (hF_wf (by decide)) all_nil))
          (all_cons (hF_blind 0) (all_cons (hF_blind 1) all_nil)), trivial⟩

/-- ONE group (`A`/`B` at the member slot), both components reached. -/
noncomputable def taKeys : KeyGroups V where
  grp := fun _ => 0
  cmp := fun q => q
  g := fun _ => 2
  IsG := fun _ _ => unitIs
  Θ := fun _ W => uPhi (altD w) (fun _ => empty) (app (W 0) pt)
  dep := fun _ => 0

theorem taKeys_ok (ρ : Nat → V) (α : V) :
    (taKeys (V := V) w).Ok w 1 2 unitIs (uPhi (taWide w) ρ α) where
  cmp_lt := fun _ hq => hq
  inj := fun _ _ _ _ _ h => h
  idx := fun _ _ _ => rfl
  functor := fun W hW _ _ => by
    have hβ : app (W 0) pt ∈ˢ (univ w : V) := app_fam_mem_univ (hW 0 (by decide)) pt
    exact ⟨uPhi_mono (altD w) _ hβ, altD_closedAll w _ _ hβ⟩
  sub := fun W _ q hq _ => by
    have hinj : ∀ q q', q < 2 → q' < 2 → (taKeys (V := V) w).grp q = (taKeys (V := V) w).grp q' →
        (taKeys (V := V) w).cmp q = (taKeys (V := V) w).cmp q' → q = q' := fun _ _ _ _ _ h => h
    have hfill0 : (taKeys (V := V) w).fill w 1 2 0 W 0 = W 1 :=
      KeyGroups.fill_reached (q := 0) (by decide) hinj W
    have hfill1 : (taKeys (V := V) w).fill w 1 2 0 W 1 = W 2 :=
      KeyGroups.fill_reached (q := 1) (by decide) hinj W
    match q, hq with
    | 0, _ =>
      show FamLe unitSet (uPhi (altD w) (fun _ => empty) (app (W 0) pt)
        ((taKeys w).fill w 1 2 0 W) 0) (uPhi (taWide w) ρ α W 1)
      refine uPhi_famLe (altD w) (taWide w) _ ρ _ α _ W rfl ?_
      intro t _ j fs ct hct hf hi
      match j, fs, hct, hf with
      | 0, [], rfl, _ => exact ⟨_, rfl, trivial, hi⟩
      | 1, [a, b], rfl, hf =>
        exact ⟨_, rfl, ⟨hf.1, by show _ ∈ˢ app (W 2) pt; rw [← hfill1]; exact hf.2.1, trivial⟩, hi⟩
    | 1, _ =>
      show FamLe unitSet (uPhi (altD w) (fun _ => empty) (app (W 0) pt)
        ((taKeys w).fill w 1 2 0 W) 1) (uPhi (taWide w) ρ α W 2)
      refine uPhi_famLe (altD w) (taWide w) _ ρ _ α _ W rfl ?_
      intro t _ j fs ct hct hf hi
      match j, fs, hct, hf with
      | 0, [a, x], rfl, hf =>
        exact ⟨_, rfl, ⟨hf.1, by show _ ∈ˢ app (W 1) pt; rw [← hfill0]; exact hf.2.1, trivial⟩, hi⟩

/-- **`T`'s (W) at every level — through the kit, one group of two
mutually referring keys.** -/
theorem taD_closed (ρ : Nat → V) {α : V} (hα : α ∈ˢ (univ w : V)) : (taD (V := V) w).Closed ρ α := by
  refine closed_of_wide_groups (k := 1) (n := 2) (Is := unitIs) (Ψ := uPhi (taWide w) ρ α)
    (uPhi_mono (taWide w) ρ hα) (UBlock.closed_of_flatAll _ ρ hα fun _ => taWide_flat w ρ α)
    (taKeys w) (taKeys_ok w ρ α) ?_
  intro X Y _ _ hdom m hm
  obtain rfl : m = 0 := by omega
  refine uPhi_famLe (taD w) (taWide w) ρ ρ α α X (catTup 1 X Y) rfl ?_
  intro t _ j fs ct hct hf hi
  match j, fs, hct, hf with
  | 0, [l], rfl, hf => exact ⟨_, rfl, ⟨hdom 0 (by decide) pt pt_mem_unitSet l hf.1, trivial⟩, hi⟩

theorem taD_closedAll (ρ : Nat → V) : (taD (V := V) w).ClosedAll ρ := fun _ hα => taD_closed w ρ hα

/-- **`⟦T⟧`'s fibre law at every level, no hypothesis left**: `node l`
with `l ∈ ⟦A⟧ ⟦T⟧`. -/
theorem mem_TA_all {x : V} : x ∈ˢ TA (V := V) w ↔ ∃ l, l ∈ˢ ALTA w (TA (V := V) w) ∧ x = uinj w 0 [l] := by
  unfold TA UBlock.value
  rw [(taD w).mem_carrier (empty_mem_univ w) (taD_closed w _ (empty_mem_univ w)) Nat.one_pos
    (by exact pt_mem_unitSet)]
  constructor
  · rintro ⟨j, fs, ct, hct, hf, -, rfl⟩
    match j, fs, hct, hf with
    | 0, [l], rfl, hf => exact ⟨l, hf.1, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨0, [l], _, rfl, ⟨hl, trivial⟩, rfl, rfl⟩

/-- **The `Prop` example**: the nested-through-a-mutual-group block at
`w = 0`, through the same kit. -/
theorem mem_TA_prop {x : V} : x ∈ˢ TA (V := V) 0 ↔ ∃ l, l ∈ˢ ALTA 0 (TA (V := V) 0) ∧ x = pt := by
  rw [mem_TA_all]
  simp only [uinj_zero]

end TA

end NestWideEx

end ConLeche.SetTheory
