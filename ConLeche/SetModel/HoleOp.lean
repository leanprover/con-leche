module

public import ConLeche.SetTheory.Derive.LfpTuple
public import ConLeche.SetModel.TowerMono
import ConLeche.SetModel.Access
public import ConLeche.SetModel.Ops
@[expose] public section

/-!
# The HOLE operator — the uniform block operator without field kinds (design lane HOLEOP)

The maintainer's operator (2026-09-23):

    Φ(X) = Σ ctor, Π fields, ⟦field type⟧[members := X]

**No field kinds.**  A constructor's field telescope is read as a
dependent telescope of POSITIVE TYPES (`Pos`): a type in which the
block's members (the HOLE tuple `X`) occur only positively —
under Π-codomains, applied to hole-free index tuples, or as
parameters of a container that is itself monotone in that parameter.
A direct recursive field `T p⃗ e⃗` is the node `hole m e⃗`
(`app (X m) ⟨e⃗⟩`), a reflexive field `Π a⃗, T p⃗ e⃗(a⃗)` is `pi` over
`hole`, a nested field `List (T p⃗)` is `cont ⟦List⟧ (hole 0 pt)`,
an ordinary field is `const`.  The same syntax has a `param` node
for a CONTAINER's own parameter position, so that "monotone in the
hole" and "monotone in the parameter" are ONE theorem (`Pos.mono`),
and a container's parameter-monotonicity (`UBlock.carrier_mono_param`,
NESTTREE's `value_mono`) is leastness plus that theorem at its own
fields — nothing recorded, nothing special about nesting.

What is proved here, sorry-free, over the bare `SetTheory` interface:

* `Pos.graded`/`Pos.mono` — grading and monotonicity of a positive type
  in the hole tuple and the parameter, by induction on the derivation;
* `uPhi` — the operator of a block datum (`UBlock`: index sets and,
  per component, constructors = positive field telescopes + a result
  index tuple); `uPhi_mono` (`MonoTuple`), `uPhi_maps` (`MapsTuple`),
  `uPhi_closed_zero` ((W) at `Prop`);
* `mem_uPhi` — **the fibre law**: component `c`'s fibre at `(X, t)` is
  exactly the injections `uinj w j fs` of the spines fitting one of
  `c`'s constructors' telescopes at `X` whose result index is `t`;
  `mem_carrier` is the same at the least pre-fixed tuple;
* `carrier_mono_param` — a block's carrier is monotone in the
  parameter `α`, by leastness (the `cont` node's premise for using
  the block as a container of a LATER block);
* instances: `natD` (direct), `wD` (reflexive over a large domain),
  `vecD` (indexed), `evenOddD` (mutual), `listD` and `treeD` (nested
  through `List`, `List` itself a `UBlock`), `roseD` and `rtD`
  (nested through `Rose`, itself nested through `List`), `abD`
  (mutual and nested) — each parametric in the level `w`, `Prop`
  (`w = 0`) and `Type` (`w ≠ 0`) one definition; at `w = 0` every
  closure hypothesis is discharged (`closed_zero`), at `w ≠ 0` (W)
  stays a hypothesis, as in every set-level lane so far.

Not built here (argued in `_tmp/uniform-inds/HOLEOP.md`): the closed
tuple at `w ≠ 0` (the transient wide operator route of DESIGN
document 2 v2 §2.5 is unchanged by this operator), and the
term-level reading of a field as an `AnnotTerm` with the members as
free variables (the `denoteMeta` override).
-/

namespace ConLeche.SetTheory

open Tower
open ConLeche.SetModel

universe u

variable {V : Type u} [SetTheory V]

/-! ## Frames -/

/-- Frame extension: the new value innermost. -/
def fcons (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

omit [SetTheory V] in
@[simp] theorem fcons_zero (x : V) (ρ : Nat → V) : fcons x ρ 0 = x := rfl
omit [SetTheory V] in
@[simp] theorem fcons_succ (x : V) (ρ : Nat → V) (i : Nat) : fcons x ρ (i + 1) = ρ i := rfl

/-- The frame extended by a list of field values in order, the LAST
value innermost. -/
def fconsList : List V → (Nat → V) → Nat → V
  | [], ρ => ρ
  | a :: as, ρ => fconsList as (fcons a ρ)

/-! ## Two facts about families and products -/

/-- A family applied anywhere is a set of its level (off the index
set the application is the junk `∅`). -/
theorem app_fam_mem_univ {w : Nat} {I X : V} (hX : X ∈ˢ famSpace w I) (t : V) :
    app X t ∈ˢ (univ w : V) := by
  by_cases ht : t ∈ˢ I
  · exact famSpace_app hX ht
  · rw [app_off_dom_of_mem_piSet hX ht]; exact empty_mem_univ w

/-- Families in the order `FamLe` compare pointwise EVERYWHERE. -/
theorem app_fam_mono {w : Nat} {I X Y : V} (hX : X ∈ˢ famSpace w I) (hXY : FamLe I X Y) (t : V) :
    app X t ⊆ˢ app Y t := by
  by_cases ht : t ∈ˢ I
  · exact hXY t ht
  · rw [app_off_dom_of_mem_piSet hX ht]; exact fun z hz => (not_mem_empty z hz).elim


/-- Formation of a product at a codomain bit at most the level. -/
theorem piR_mem_univ {w v : Nat} (hv : w = 0 → v = 0) {A : V} {B : V → V}
    (hA : A ∈ˢ (univ w : V)) (hB : ∀ a, a ∈ˢ A → B a ∈ˢ (univ w : V)) :
    piR v A B ∈ˢ (univ w : V) := by
  by_cases hv0 : v = 0
  · subst hv0
    rw [piR_zero]
    refine univ_mono (V := V) (Nat.zero_le w) _ ?_
    rw [univ_zero (V := V)]
    exact truthVal_mem_univZero _
  · have hw : w ≠ 0 := fun h => hv0 (hv h)
    rw [piR_pos hv0]
    exact (univ_isTGUniverse hw).piSet_mem hA hB

/-! ## Positive types

A type over a frame `ρ` (the parameters and the earlier fields), the
hole tuple `X` (the block's members, as families over their index
sets) and a parameter `α` (a container's own parameter position),
in which `X` and `α` occur only positively.  The grading premises
(`hA`) stand in for the fields' certified typing. -/

/-- **Positive types.** -/
inductive Pos (w k : Nat) : ((Nat → V) → (Nat → V) → V → V) → Prop
  /-- a hole-free type, read at the frame -/
  | const (A : (Nat → V) → V) (hA : ∀ ρ, A ρ ∈ˢ (univ w : V)) :
      Pos w k fun ρ _ _ => A ρ
  /-- the parameter itself -/
  | param : Pos w k fun _ _ α => α
  /-- member `m` at a hole-free index tuple: `T_m p⃗ e⃗` -/
  | hole (m : Nat) (hm : m < k) (es : (Nat → V) → V) :
      Pos w k fun ρ X _ => app (X m) (es ρ)
  /-- a product with a hole-free domain and a positive codomain (the
  codomain bit `v` is `0` at a `Prop` block) -/
  | pi (v : Nat) (hv : w = 0 → v = 0) (A : (Nat → V) → V) (hA : ∀ ρ, A ρ ∈ˢ (univ w : V))
      (B : (Nat → V) → (Nat → V) → V → V) (hB : Pos w k B) :
      Pos w k fun ρ X α => piR v (A ρ) fun a => B (fcons a ρ) X α
  /-- a container, graded and monotone in its parameter, at a
  positive parameter -/
  | cont (C : V → V) (hC : ∀ β, β ∈ˢ (univ w : V) → C β ∈ˢ (univ w : V))
      (hmono : ∀ β γ, β ∈ˢ (univ w : V) → γ ∈ˢ (univ w : V) → β ⊆ˢ γ → C β ⊆ˢ C γ)
      (D : (Nat → V) → (Nat → V) → V → V) (hD : Pos w k D) :
      Pos w k fun ρ X α => C (D ρ X α)

namespace Pos

variable {w k : Nat}

/-- **Grading**: a positive type at a tuple of the space and a
parameter of the level is a set of the level. -/
theorem graded {F : (Nat → V) → (Nat → V) → V → V} (h : Pos w k F) {Is X : Nat → V}
    (hX : InTupleSpace w k Is X) {α : V} (hα : α ∈ˢ (univ w : V)) :
    ∀ ρ, F ρ X α ∈ˢ (univ w : V) := by
  induction h with
  | const A hA => exact fun ρ => hA ρ
  | param => exact fun _ => hα
  | hole m hm es => exact fun ρ => app_fam_mem_univ (hX m hm) _
  | pi v hv A hA B _ ih => exact fun ρ => piR_mem_univ hv (hA ρ) fun a _ => ih (fcons a ρ)
  | cont C hC _ D _ ih => exact fun ρ => hC _ (ih ρ)

/-- **THE theorem: monotonicity from positivity.**  A positive type is
monotone in the hole tuple and in the parameter, by induction on the
derivation: a product through its codomain, a member application
through the tuple's order (off the index set both sides are `∅`), a
container through its own parameter-monotonicity at the positive
parameter, a constant trivially. -/
theorem mono {F : (Nat → V) → (Nat → V) → V → V} (h : Pos w k F) {Is X Y : Nat → V}
    (hX : InTupleSpace w k Is X) (hY : InTupleSpace w k Is Y) (hXY : TupleLe k Is X Y)
    {α β : V} (hα : α ∈ˢ (univ w : V)) (hβ : β ∈ˢ (univ w : V)) (hαβ : α ⊆ˢ β) :
    ∀ ρ, F ρ X α ⊆ˢ F ρ Y β := by
  induction h with
  | const A _ => exact fun _ => Subset.refl _
  | param => exact fun _ => hαβ
  | hole m hm es => exact fun ρ => app_fam_mono (hX m hm) (hXY m hm) _
  | pi v _ A _ B _ ih => exact fun ρ => piR_subset_mono fun a _ => ih (fcons a ρ)
  | cont C _ hmono D hD ih =>
    exact fun ρ => hmono _ _ (hD.graded hX hα ρ) (hD.graded hY hβ ρ) (ih ρ)

end Pos

/-! ## Constructors, telescopes, the operator -/

/-- **A constructor**: a dependent telescope of positive field types
(field `i` read at the frame extended by fields `0..i-1`) and its
result index tuple, read at the frame extended by all fields. -/
structure UCtor (V : Type u) [SetTheory V] (w k : Nat) where
  /-- the field types -/
  fields : List ((Nat → V) → (Nat → V) → V → V)
  /-- every field type is positive -/
  pos : ∀ F ∈ fields, Pos w k F
  /-- the result index tuple -/
  idx : (Nat → V) → V

/-- The field telescope of a constructor at a frame, a hole tuple and
a parameter. -/
noncomputable def teleOf : (Fs : List ((Nat → V) → (Nat → V) → V → V)) →
    (Nat → V) → (Nat → V) → V → TeleS V Fs.length
  | [], _, _, _ => .nil
  | F :: Fs, ρ, X, α => .cons (F ρ X α) fun a => teleOf Fs (fcons a ρ) X α

/-- **A block datum**: per component its index-tuple set and its
constructors. -/
structure UBlock (V : Type u) [SetTheory V] (w k : Nat) where
  /-- per component: the index-tuple set -/
  Is : Nat → V
  /-- per component: the constructors, in order -/
  ctors : Nat → List (UCtor V w k)

/-- The value of a field spine: the point at `Prop`, the tuple tower
above. -/
noncomputable def towOf (w : Nat) (fs : List V) : V := if w = 0 then pt else mkTower fs

/-- **The constructor injection**: the point at `Prop`, the tagged
tuple tower above (`inj j (mkTower fs)`, the encoding in force). -/
noncomputable def uinj (w j : Nat) (fs : List V) : V := if w = 0 then pt else inj j (mkTower fs)

theorem uinj_zero (j : Nat) (fs : List V) : uinj 0 j fs = (pt : V) := if_pos rfl
theorem uinj_pos {w : Nat} (hw : w ≠ 0) (j : Nat) (fs : List V) :
    uinj w j fs = inj j (mkTower fs) := if_neg hw
theorem towOf_pos {w : Nat} (hw : w ≠ 0) (fs : List V) : towOf w fs = mkTower fs := if_neg hw

/-- The fibre of one constructor at `(ρ, X, α, t)`: the values of the
spines fitting its telescope whose result index is `t`. -/
noncomputable def ctorFibre {w k : Nat} (ct : UCtor V w k) (ρ : Nat → V) (X : Nat → V) (α t : V) : V :=
  sep (towerSet w (teleOf ct.fields ρ X α)) fun x =>
    ∃ fs, FitsS (teleOf ct.fields ρ X α) fs ∧ ct.idx (fconsList fs ρ) = t ∧ x = towOf w fs

/-- Constructor `j`'s fibre (`∅` past the constructor list). -/
noncomputable def fibreAt {w k : Nat} (d : UBlock V w k) (ρ : Nat → V) (α : V) (X : Nat → V)
    (c : Nat) (t : V) (j : Nat) : V :=
  match (d.ctors c)[j]? with
  | some ct => ctorFibre ct ρ X α t
  | none => empty

/-- **The hole operator**: component `c` is the family over its index
set whose fibre at `t` is the tagged sum of the constructors' fibres. -/
noncomputable def uPhi {w k : Nat} (d : UBlock V w k) (ρ : Nat → V) (α : V) (X : Nat → V) (c : Nat) : V :=
  lamR (w + 1) (d.Is c) fun t => sumSet w (fibreAt d ρ α X c t)

/-! ### The fibre law -/

theorem towOf_mem_towerSet {w : Nat} {n : Nat} {T : TeleS V n} {fs : List V} (hf : FitsS T fs) :
    towOf w fs ∈ˢ towerSet w T := by
  unfold towOf
  split
  · next hw => subst hw; exact pt_mem_tower hf
  · next hw => exact mkTower_mem hw hf

theorem mem_ctorFibre {w k : Nat} {ct : UCtor V w k} {ρ : Nat → V} {X : Nat → V} {α t x : V} :
    x ∈ˢ ctorFibre ct ρ X α t ↔
      ∃ fs, FitsS (teleOf ct.fields ρ X α) fs ∧ ct.idx (fconsList fs ρ) = t ∧ x = towOf w fs := by
  unfold ctorFibre
  rw [mem_sep]
  constructor
  · exact fun h => h.2
  · rintro ⟨fs, hf, hi, rfl⟩
    exact ⟨towOf_mem_towerSet hf, fs, hf, hi, rfl⟩

/-- **The fibre law**: an element of component `c`'s fibre at `(X, t)`
is the injection of a spine fitting one of `c`'s constructors at `X`
with result index `t`, and conversely. -/
theorem mem_uPhi {w k : Nat} (d : UBlock V w k) (ρ : Nat → V) (α : V) (X : Nat → V) {c : Nat} {t : V}
    (ht : t ∈ˢ d.Is c) {x : V} :
    x ∈ˢ app (uPhi d ρ α X c) t ↔
      ∃ j fs ct, (d.ctors c)[j]? = some ct ∧ FitsS (teleOf ct.fields ρ X α) fs ∧
        ct.idx (fconsList fs ρ) = t ∧ x = uinj w j fs := by
  unfold uPhi
  rw [app_lamR_pos (Nat.succ_ne_zero w) ht]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · constructor
    · intro hx
      obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx
      unfold fibreAt at ha
      split at ha
      · next ct hct =>
        obtain ⟨fs, hf, hi, -⟩ := mem_ctorFibre.mp ha
        exact ⟨j, fs, ct, hct, hf, hi, (uinj_zero j fs).symm⟩
      · exact (not_mem_empty _ ha).elim
    · rintro ⟨j, fs, ct, hct, hf, hi, rfl⟩
      rw [uinj_zero]
      refine pt_mem_sumSet_zero (i := j) (a := towOf 0 fs) ?_
      unfold fibreAt
      rw [hct]
      exact mem_ctorFibre.mpr ⟨fs, hf, hi, rfl⟩
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    constructor
    · intro hx
      obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw' hx
      unfold fibreAt at ha
      split at ha
      · next ct hct =>
        obtain ⟨fs, hf, hi, rfl⟩ := mem_ctorFibre.mp ha
        exact ⟨j, fs, ct, hct, hf, hi, by rw [uinj_pos hw', towOf_pos hw']⟩
      · exact (not_mem_empty _ ha).elim
    · rintro ⟨j, fs, ct, hct, hf, hi, rfl⟩
      rw [uinj_pos hw', ← towOf_pos hw']
      refine inj_mem hw' ?_
      unfold fibreAt
      rw [hct]
      exact mem_ctorFibre.mpr ⟨fs, hf, hi, rfl⟩

/-! ### The functor laws -/

/-- The telescope is pointwise monotone in the hole and the parameter. -/
theorem teleOf_sub {w k : Nat} {Is X Y : Nat → V} (hX : InTupleSpace w k Is X)
    (hY : InTupleSpace w k Is Y) (hXY : TupleLe k Is X Y) {α β : V} (hα : α ∈ˢ (univ w : V))
    (hβ : β ∈ˢ (univ w : V)) (hαβ : α ⊆ˢ β) :
    ∀ (Fs : List ((Nat → V) → (Nat → V) → V → V)), (∀ F ∈ Fs, Pos w k F) →
      ∀ ρ, TeleS.Sub (teleOf Fs ρ X α) (teleOf Fs ρ Y β)
  | [], _, _ => .nil
  | F :: Fs, hpos, ρ =>
    .cons ((hpos F List.mem_cons_self).mono hX hY hXY hα hβ hαβ ρ)
      fun a _ => teleOf_sub hX hY hXY hα hβ hαβ Fs (fun G hG => hpos G (List.mem_cons_of_mem F hG))
        (fcons a ρ)

/-- The telescope is bounded at the level. -/
theorem teleOf_bound {w k : Nat} {Is X : Nat → V} (hX : InTupleSpace w k Is X) {α : V}
    (hα : α ∈ˢ (univ w : V)) :
    ∀ (Fs : List ((Nat → V) → (Nat → V) → V → V)), (∀ F ∈ Fs, Pos w k F) →
      ∀ ρ, BoundS w (teleOf Fs ρ X α)
  | [], _, _ => trivial
  | F :: Fs, hpos, ρ =>
    ⟨(hpos F List.mem_cons_self).graded hX hα ρ,
      fun a _ => teleOf_bound hX hα Fs (fun G hG => hpos G (List.mem_cons_of_mem F hG)) (fcons a ρ)⟩

theorem ctorFibre_mono {w k : Nat} {ct : UCtor V w k} {Is X Y : Nat → V} (hX : InTupleSpace w k Is X)
    (hY : InTupleSpace w k Is Y) (hXY : TupleLe k Is X Y) {α β : V} (hα : α ∈ˢ (univ w : V))
    (hβ : β ∈ˢ (univ w : V)) (hαβ : α ⊆ˢ β) (ρ : Nat → V) (t : V) :
    ctorFibre ct ρ X α t ⊆ˢ ctorFibre ct ρ Y β t := by
  have hs := teleOf_sub hX hY hXY hα hβ hαβ ct.fields ct.pos ρ
  intro x hx
  obtain ⟨fs, hf, hi, rfl⟩ := mem_ctorFibre.mp hx
  exact mem_ctorFibre.mpr ⟨fs, FitsS.mono hs hf, hi, rfl⟩

/-- **The operator is monotone in the hole AND the parameter.** -/
theorem uPhi_mono2 {w k : Nat} (d : UBlock V w k) (ρ : Nat → V) {α β : V} (hα : α ∈ˢ (univ w : V))
    (hβ : β ∈ˢ (univ w : V)) (hαβ : α ⊆ˢ β) {X Y : Nat → V} (hX : InTupleSpace w k d.Is X)
    (hY : InTupleSpace w k d.Is Y) (hXY : TupleLe k d.Is X Y) :
    TupleLe k d.Is (uPhi d ρ α X) (uPhi d ρ β Y) := by
  intro c _ t ht
  unfold uPhi
  rw [app_lamR_pos (Nat.succ_ne_zero w) ht, app_lamR_pos (Nat.succ_ne_zero w) ht]
  refine sumSet_mono fun j => ?_
  unfold fibreAt
  split
  · exact ctorFibre_mono hX hY hXY hα hβ hαβ ρ t
  · exact Subset.refl _

/-- **`MonoTuple`.** -/
theorem uPhi_mono {w k : Nat} (d : UBlock V w k) (ρ : Nat → V) {α : V} (hα : α ∈ˢ (univ w : V)) :
    MonoTuple w k d.Is (uPhi d ρ α) :=
  fun _ _ hX hY hXY => uPhi_mono2 d ρ hα hα (Subset.refl α) hX hY hXY

theorem fibreAt_mem_univ {w k : Nat} (d : UBlock V w k) (ρ : Nat → V) {α : V} (hα : α ∈ˢ (univ w : V))
    {X : Nat → V} (hX : InTupleSpace w k d.Is X) (c : Nat) (t : V) (j : Nat) :
    fibreAt d ρ α X c t j ∈ˢ (univ w : V) := by
  unfold fibreAt
  split
  · next ct _ => exact univ_sep_mem (towerSet_mem_univ _ (teleOf_bound hX hα ct.fields ct.pos ρ))
  · exact empty_mem_univ w

/-- **`MapsTuple`.** -/
theorem uPhi_maps {w k : Nat} (d : UBlock V w k) (ρ : Nat → V) {α : V} (hα : α ∈ˢ (univ w : V)) :
    MapsTuple w k d.Is (uPhi d ρ α) := by
  intro X hX c _
  show lamR (w + 1) (d.Is c) _ ∈ˢ piSet (d.Is c) fun _ => univ w
  rw [lamR_pos (Nat.succ_ne_zero w)]
  refine graph_mem_piSet fun t _ => ?_
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [univ_zero]; exact sumSet_zero_mem_univZero _
  · exact sumSet_mem_univ (Nat.pos_iff_ne_zero.mp hw) fun j => fibreAt_mem_univ d ρ hα hX c t j

/-- **(W) at `Prop`**: free. -/
theorem uPhi_closed_zero {k : Nat} (d : UBlock V 0 k) (ρ : Nat → V) {α : V} (hα : α ∈ˢ (univ 0 : V)) :
    ∃ L, IsClosedTuple 0 k d.Is (uPhi d ρ α) L :=
  closedTuple_zero (uPhi_maps d ρ hα)

/-! ## The carrier -/

namespace UBlock

variable {w k : Nat} (d : UBlock V w k)

/-- **The carrier**: the least pre-fixed tuple of the hole operator. -/
noncomputable def carrier (ρ : Nat → V) (α : V) : Nat → V := lfpTuple w k d.Is (uPhi d ρ α)

/-- (W): a closed tuple exists (free at `w = 0`, a hypothesis above). -/
def Closed (ρ : Nat → V) (α : V) : Prop := ∃ L, IsClosedTuple w k d.Is (uPhi d ρ α) L

/-- (W) at every parameter of the level. -/
def ClosedAll (ρ : Nat → V) : Prop := ∀ α, α ∈ˢ (univ w : V) → d.Closed ρ α

theorem carrier_mem (ρ : Nat → V) (α : V) : InTupleSpace w k d.Is (d.carrier ρ α) :=
  lfpTuple_mem _ _ _ _


/-- **Parameter-monotonicity, by leastness** (NESTTREE's `value_mono`
for EVERY block): the carrier at the larger parameter is closed for
the operator at the smaller one, because the operator is monotone in
the parameter (`Pos.mono` at the `param` nodes). -/
theorem carrier_mono_param (ρ : Nat → V) {α β : V} (hα : α ∈ˢ (univ w : V)) (hβ : β ∈ˢ (univ w : V))
    (hαβ : α ⊆ˢ β) (hclβ : d.Closed ρ β) :
    TupleLe k d.Is (d.carrier ρ α) (d.carrier ρ β) := by
  refine lfpTuple_le ⟨lfpTuple_mem _ _ _ _, ?_⟩
  refine TupleLe.trans ?_ (lfpTuple_closed hclβ (uPhi_mono d ρ hβ))
  exact uPhi_mono2 d ρ hα hβ hαβ (lfpTuple_mem _ _ _ _) (lfpTuple_mem _ _ _ _)
    (TupleLe.refl _ _ _)

/-! ### Reading a one-member block as a CONTAINER of a later block -/

/-- The ordinary reading of an unindexed one-member block at a
parameter: its carrier's fibre at the point. -/
noncomputable def value (ρ : Nat → V) (α : V) : V := app (d.carrier ρ α 0) pt

/-- The `cont` node's grading premise, unconditionally. -/
theorem value_mem_univ (hk : 0 < k) (ρ : Nat → V) (α : V) : d.value ρ α ∈ˢ (univ w : V) :=
  app_fam_mem_univ (d.carrier_mem ρ α 0 hk) pt

/-- The `cont` node's monotonicity premise, from (W) at every
parameter — DERIVED, never recorded. -/
theorem value_mono (hk : 0 < k) (ρ : Nat → V) (hW : d.ClosedAll ρ) :
    ∀ β γ, β ∈ˢ (univ w : V) → γ ∈ˢ (univ w : V) → β ⊆ˢ γ → d.value ρ β ⊆ˢ d.value ρ γ :=
  fun _ _ hβ hγ hβγ =>
    app_fam_mono (d.carrier_mem ρ _ 0 hk) (d.carrier_mono_param ρ hβ hγ hβγ (hW _ hγ) 0 hk) pt

end UBlock

/-! ## Instances

Every instance is one definition at every level `w`.  The
constructor lists are spelled with the frame convention `ρ 0` = the
most recent field. -/

/-- The unit index set of an unindexed block. -/
noncomputable def unitIs : Nat → V := fun _ => unitSet

/-- The field `T_m p⃗` of an unindexed member: `hole m` at the point. -/
noncomputable def holeF (m : Nat) : (Nat → V) → (Nat → V) → V → V := fun _ X _ => app (X m) pt

theorem pos_holeF {w k m : Nat} (hm : m < k) : Pos w k (holeF (V := V) m) :=
  Pos.hole m hm fun _ => pt

/-- A constructor of an unindexed block. -/
noncomputable def uctor {w k : Nat} (Fs : List ((Nat → V) → (Nat → V) → V → V))
    (hpos : ∀ F ∈ Fs, Pos w k F) : UCtor V w k :=
  ⟨Fs, hpos, fun _ => pt⟩

theorem pos_nil {w k : Nat} : ∀ F ∈ ([] : List ((Nat → V) → (Nat → V) → V → V)), Pos w k F :=
  fun _ h => nomatch h

theorem pos_cons {w k : Nat} {F : (Nat → V) → (Nat → V) → V → V}
    {Fs : List ((Nat → V) → (Nat → V) → V → V)} (hF : Pos w k F) (hFs : ∀ G ∈ Fs, Pos w k G) :
    ∀ G ∈ F :: Fs, Pos w k G := by
  intro G hG
  rcases List.mem_cons.mp hG with rfl | h
  · exact hF
  · exact hFs G h

/-! ### `Nat ::= zero | succ Nat` — a direct recursive field -/

/-- The block datum. -/
noncomputable def natD (w : Nat) : UBlock V w 1 where
  Is := unitIs
  ctors := fun _ => [uctor [] pos_nil, uctor [holeF 0] (pos_cons (pos_holeF Nat.one_pos) pos_nil)]


/-! ### `W α β ::= sup (a : α) (β a → W α β)` — a reflexive field over a large domain -/


/-! ### `Vec α : Nat → Type` — an indexed family -/


/-! ### `Even/Odd` — a mutual block -/


/-! ### `List α ::= nil | cons α (List α)` — a container, itself a block -/

/-- The block datum of `List` at its parameter: `cons`'s head is the
`param` node. -/
noncomputable def listD (w : Nat) : UBlock V w 1 where
  Is := unitIs
  ctors := fun _ =>
    [uctor [] pos_nil,
     uctor [fun _ _ α => α, holeF 0] (pos_cons Pos.param (pos_cons (pos_holeF Nat.one_pos) pos_nil))]

/-- `⟦List⟧ α`, the ordinary reading. -/
noncomputable def LIST (w : Nat) (α : V) : V := (listD (V := V) w).value (fun _ => empty) α


/-- **`List` is monotone in its parameter** — from its block datum by
leastness, given (W) at every parameter. -/
theorem LIST_mono {w : Nat} (hW : (listD (V := V) w).ClosedAll fun _ => empty) :
    ∀ β γ, β ∈ˢ (univ w : V) → γ ∈ˢ (univ w : V) → β ⊆ˢ γ → LIST w β ⊆ˢ LIST w γ :=
  (listD w).value_mono Nat.one_pos _ hW

theorem LIST_mem_univ (w : Nat) (β : V) : LIST (V := V) w β ∈ˢ (univ w : V) :=
  (listD w).value_mem_univ Nat.one_pos _ β

/-! ### `Tree ::= node (List Tree)` — nested through `List` -/

/-- The block datum: ONE field, the `cont` node at `List` with the
hole as its parameter.  Nothing about nesting appears. -/
noncomputable def treeD (w : Nat) (hW : (listD (V := V) w).ClosedAll fun _ => empty) : UBlock V w 1 where
  Is := unitIs
  ctors := fun _ =>
    [uctor [fun _ X _ => LIST w (app (X 0) pt)]
      (pos_cons (Pos.cont (LIST w) (fun β _ => LIST_mem_univ w β) (LIST_mono hW) (holeF 0) (pos_holeF Nat.one_pos))
        pos_nil)]

/-- `⟦Tree⟧`. -/
noncomputable def TREE (w : Nat) (hW : (listD (V := V) w).ClosedAll fun _ => empty) : V :=
  (treeD w hW).value (fun _ => empty) empty


/-! ### `Rose α ::= node α (List (Rose α))`, `T ::= leaf | mk (Rose T)` — nested through a nested container -/

/-- The block datum of `Rose` at its parameter: `param`, then `cont`
at `List` with the hole as `List`'s parameter. -/
noncomputable def roseD (w : Nat) (hW : (listD (V := V) w).ClosedAll fun _ => empty) : UBlock V w 1 where
  Is := unitIs
  ctors := fun _ =>
    [uctor [fun _ _ α => α, fun _ X _ => LIST w (app (X 0) pt)]
      (pos_cons Pos.param
        (pos_cons (Pos.cont (LIST w) (fun β _ => LIST_mem_univ w β) (LIST_mono hW) (holeF 0) (pos_holeF Nat.one_pos))
          pos_nil))]

/-- `⟦Rose⟧ α`. -/
noncomputable def ROSE (w : Nat) (hW : (listD (V := V) w).ClosedAll fun _ => empty) (α : V) : V :=
  (roseD w hW).value (fun _ => empty) α


/-- **`Rose` is monotone in its parameter** — the same theorem as
`List`'s, nothing about `List` consumed beyond its `cont` premises. -/
theorem ROSE_mono {w : Nat} (hW : (listD (V := V) w).ClosedAll fun _ => empty)
    (hWR : (roseD w hW).ClosedAll fun _ => empty) :
    ∀ β γ, β ∈ˢ (univ w : V) → γ ∈ˢ (univ w : V) → β ⊆ˢ γ → ROSE w hW β ⊆ˢ ROSE w hW γ :=
  (roseD w hW).value_mono Nat.one_pos _ hWR

theorem ROSE_mem_univ {w : Nat} (hW : (listD (V := V) w).ClosedAll fun _ => empty) (β : V) :
    ROSE w hW β ∈ˢ (univ w : V) :=
  (roseD w hW).value_mem_univ Nat.one_pos _ β

/-- The block datum of `T ::= leaf | mk (Rose T)`. -/
noncomputable def rtD (w : Nat) (hW : (listD (V := V) w).ClosedAll fun _ => empty)
    (hWR : (roseD w hW).ClosedAll fun _ => empty) : UBlock V w 1 where
  Is := unitIs
  ctors := fun _ =>
    [uctor [] pos_nil,
     uctor [fun _ X _ => ROSE w hW (app (X 0) pt)]
      (pos_cons (Pos.cont (ROSE w hW) (fun β _ => ROSE_mem_univ hW β) (ROSE_mono hW hWR) (holeF 0)
          (pos_holeF Nat.one_pos))
        pos_nil)]

/-- `⟦T⟧`. -/
noncomputable def RT (w : Nat) (hW : (listD (V := V) w).ClosedAll fun _ => empty)
    (hWR : (roseD w hW).ClosedAll fun _ => empty) : V :=
  (rtD w hW hWR).value (fun _ => empty) empty


/-! ### `A ::= mk (List B)`, `B ::= leaf | mk A` — mutual AND nested -/


/-! ## `Prop`: every closure hypothesis discharged

At `w = 0` the instances above need NO hypothesis: (W) is
`uPhi_closed_zero`, so the nested `Prop` blocks (`Q ::= mk (ListP Q)`,
the `Prop` `Rose`/`T` family) are fully built. -/

theorem listD_closedAll_zero : (listD (V := V) 0).ClosedAll fun _ => empty :=
  fun _ hα => uPhi_closed_zero _ _ hα

theorem roseD_closedAll_zero : (roseD (V := V) 0 listD_closedAll_zero).ClosedAll fun _ => empty :=
  fun _ hα => uPhi_closed_zero _ _ hα


end ConLeche.SetTheory
