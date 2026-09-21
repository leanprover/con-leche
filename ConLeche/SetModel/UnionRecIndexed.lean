module

public import ConLeche.SetModel.EnvClauseTreeList
import ConLeche.SetModel.TupleContainer
@[expose] public section

/-!
# The union recursion kit at an INDEXED, PARAMETRIC block with a REFLEXIVE field (falsifier F3)

The three earlier falsifiers of the uniform route
(`SetModel/EnvClauseTreeList.lean`, `EnvClauseP3.lean`,
`EnvClauseP4.lean`) all exercise `UnionRec.lean`'s kit on blocks that
are **unindexed, parameter-free and finitary**: every index set is
`unitSet`, every constructor's fields are finitely many named values,
and every predecessor set is a finite list of tagged values.  The
recursor review (`_tmp/uniform-inds/REVIEW-recursors.md`, attack 1)
closes with exactly that reservation — "the union kit has NOT been
exercised with indices, parameters or reflexive fields".  This file
exercises it on a block that has all three at once, at the set level,
with abstract injections:

    inductive W (α : Sort) (r : α → α → Prop) : α → Type
      | intro (x : α) (h : (y : α) → r y x → W α r y) : W α r x

`Acc`-shaped, but in `Type` (`w ≠ 0`, large elimination): the INDEX is
`x`, the PARAMETERS are `α` and `r`, and the single field `h` is
**reflexive** — a function under a two-binder telescope whose second
binder is a `Prop`, whose values are members of the block at the
*varying* index `y`.  Its predecessor set is therefore infinite in
general and depends on the parameters AND on the index, which is what
`PredsFrom` has never been asked to carry.

Everything below is stated at a width `k` with a per-component target
function `tg` (component `c`'s field targets component `tg c`), so the
same development covers, with no extra proof:

| instance | `k` | `tg` | the block |
|---|---|---|---|
| `W` | `1` | `fun _ => 0` | `W α r x ::= intro ((y : α) → r y x → W α r y)` |
| `Mut` | `2` | `fun c => 1 - c` | `A x ::= mkA ((y : α) → r y x → B y)`, `B x ::= mkB (… → A y)` — MUTUAL, indexed, cross-recursive |

so indices are exercised at `k ≥ 2` as well (§4).

What the file checks, against the kit as it stands:

* (§2) `PredsFrom` at a predecessor SET that depends on the parameter
  values (`α`, `rel`) and on the index — `relPred` off the union, read
  through the field's telescope;
* (§2) the ih value's **λ-tower** domain: the minor receives
  `ih : (y : α) → (hy : r y x) → M (tg c) y (h y hy)`, a CURRIED
  two-level graph whose outer domain is the whole of `α` and whose
  inner domain is the truth value `rel y x` — while `pred u` holds
  only the images `h y hy`.  The graph's totality over the telescope
  is what connects them;
* (§2) the ι rule `rec c x (intro x h) = mIntro c x h (fun y hy => rec (tg c) y (h y hy))`
  and the typing `rec c x v ∈ M c x v`, from the minor's typing alone;
* (§3) the `ℓ = 0` arm of the review's G4, at the same block and
  abstractly (`indStep_sound`, `indStep_pt`): the motive fibre's
  inhabitation by `lfpTuple_induction` DIRECTLY, with no `unionRec`,
  no accessibility and no bound — the arm the model lane will
  implement;
* (§5) non-vacuity: `WOk` has a model at F0's standard tags, whose
  carrier is inhabited.

**PASS** — no hypothesis beyond the fibre law (here: the operator's
own definition), mono/maps/(W) and `mkInj`/formation was needed.  Two
presentation constraints the recursor lane must respect are marked
`-- F3 FINDING:` and collected in §6; neither is a soundness gap.

Everything here is over the bare `SetTheory` interface; no syntax.
The standard tags (`stdInj`) are F0's, reused for §5.
-/

namespace ConLeche.SetTheory

open Tower (natFibre natFibre_vnat)

universe u

variable {V : Type u} [SetTheory V]

namespace WBlock

/-! ## §1 The block: its datum, its telescope and its operator -/

/-- The data F3 reasons about: one level, a width, the per-component
target of the reflexive field, the two PARAMETERS (`α` and the
relation `rel`, whose fibres are truth values) and the block's
injections. -/
structure WSig (V : Type u) [SetTheory V] where
  /-- The value level.  `w ≠ 0` is carried separately, as in F0–F2. -/
  w : Nat
  /-- The number of members. -/
  k : Nat
  /-- Component `c`'s reflexive field targets component `tg c`. -/
  tg : Nat → Nat
  /-- The parameter `α` — the index type. -/
  α : V
  /-- The parameter `r : α → α → Prop`, as a family of truth values. -/
  rel : V → V → V
  /-- The block's injections, one constructor per member. -/
  inj : Nat → List V → V

/-- The block's laws: the parameters are a set and a `Prop`-valued
relation, the targets are members, and the tags have formation and
`mkInj` (`DESIGN-theory.md` §1.2's `ctor` clause at one field). -/
structure WOk (S : WSig V) : Prop where
  /-- Every member's field targets a member. -/
  htg : ∀ c, c < S.k → S.tg c < S.k
  /-- The index type is a set at the block's level. -/
  hα : S.α ∈ˢ (univ S.w : V)
  /-- `r y x` is a `Prop`: its fibre is a truth value. -/
  relSub : ∀ y x : V, S.rel y x ⊆ˢ (unitSet : V)
  /-- Formation above `Prop`. -/
  memU : S.w ≠ 0 → ∀ c h, h ∈ˢ (univ S.w : V) → S.inj c [h] ∈ˢ (univ S.w : V)
  /-- `mkInj`. -/
  mkInj : S.w ≠ 0 → ∀ j j' fs fs', S.inj j fs = S.inj j' fs' → j = j' ∧ fs = fs'

variable {S : WSig V}

/-- `mkInj` at the block's one-field constructors. -/
theorem inj_inj (hS : WOk S) (hw : S.w ≠ 0) {c c' : Nat} {h h' : V}
    (he : S.inj c [h] = S.inj c' [h']) : c = c' ∧ h = h' := by
  obtain ⟨rfl, hl⟩ := hS.mkInj hw _ _ _ _ he
  exact ⟨rfl, (List.cons.inj hl).1⟩

/-- **The index sets**: EVERY member is indexed by the parameter `α`
— no component's index set is a one-point set (this is what F0–F2
lacked). -/
noncomputable def wIs (S : WSig V) : Nat → V := fun _ => S.α

@[simp] theorem wIs_apply (c : Nat) : wIs S c = S.α := rfl

/-! ### The reflexive field's telescope

The field of `intro x _` has type `(y : α) → r y x → W α r y`: its
binder telescope at the index `x` is the set of PAIRS `⟨y, hy⟩` with
`y ∈ α` and `hy ∈ r y x`, and the value at such a pair lies at index
`y = sfst p`. -/

/-- The telescope of the reflexive field at the index `x`. -/
noncomputable def tele (S : WSig V) (x : V) : V := sigmaPairs S.α fun y => S.rel y x

theorem mem_tele {x p : V} :
    p ∈ˢ tele S x ↔ ∃ y, y ∈ˢ S.α ∧ ∃ hy, hy ∈ˢ S.rel y x ∧ p = kpair y hy := mem_sigmaPairs

theorem kpair_mem_tele {x y hy : V} (hyα : y ∈ˢ S.α) (hhy : hy ∈ˢ S.rel y x) :
    kpair y hy ∈ˢ tele S x := mem_tele.mpr ⟨y, hyα, hy, hhy, rfl⟩

/-- A telescope position's index is a member of `α`. -/
theorem sfst_mem_of_mem_tele {x p : V} (hp : p ∈ˢ tele S x) : sfst p ∈ˢ S.α := by
  obtain ⟨y, hy, hh, -, rfl⟩ := mem_tele.mp hp
  rw [sfst_kpair]
  exact hy

/-- The telescope is a set at the block's level: `α` is, and each
`rel y x` is a truth value, hence a member of `univ 0 ⊆ univ w`. -/
theorem tele_mem_univ (hS : WOk S) (hw : S.w ≠ 0) {x : V} : tele S x ∈ˢ (univ S.w : V) :=
  (univ_isTGUniverse (V := V) hw).sigmaPairs_mem hS.hα fun y _ =>
    univ_mono (Nat.zero_le S.w) _ (univ_zero (V := V) ▸ mem_univZero.mpr (hS.relSub y x))

/-! ### The operator -/

/-- **The reflexive slot** at component `c` and index `x`: the
functions from the telescope into the ARGUMENT tuple's component
`tg c`, at the position's own index. -/
noncomputable def slot (S : WSig V) (X : Nat → V) (c : Nat) (x : V) : V :=
  piSet (tele S x) fun p => app (X (S.tg c)) (sfst p)

/-- Component `c`'s fibre at the index `x`: the single constructor's
image. -/
noncomputable def wFib (S : WSig V) (X : Nat → V) (c : Nat) (x : V) : V :=
  image (fun h => S.inj c [h]) (slot S X c x)

theorem mem_wFib {X : Nat → V} {c : Nat} {x v : V} :
    v ∈ˢ wFib S X c x ↔ ∃ h, h ∈ˢ slot S X c x ∧ v = S.inj c [h] := mem_image

/-- **The block's operator**, indexed: component `c` is a family over
`α`. -/
noncomputable def wΨ (S : WSig V) (X : Nat → V) (c : Nat) : V :=
  graph (fun x => wFib S X c x) S.α

theorem app_wΨ {X : Nat → V} {c : Nat} {x : V} (hx : x ∈ˢ S.α) :
    app (wΨ S X c) x = wFib S X c x := app_graph hx

/-- `piSet` is monotone in its fibres (the one order fact the
reflexive slot needs). -/
theorem piSet_mono {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x ⊆ˢ B' x) :
    piSet A B ⊆ˢ piSet A B' := by
  intro f hf
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hf
  refine mem_piSet.mpr ⟨fun p hp => ?_, htot⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_sigmaPairs.mp (hsub p hp)
  exact mem_sigmaPairs.mpr ⟨x, hx, y, h x hx y hy, rfl⟩

theorem wΨ_mono (hS : WOk S) : MonoTuple S.w S.k (wIs S) (wΨ S) := by
  intro X Y hX hY hle c hc x hx v hv
  rw [app_wΨ hx] at hv ⊢
  obtain ⟨h, hh, rfl⟩ := mem_wFib.mp hv
  refine mem_wFib.mpr ⟨h, ?_, rfl⟩
  exact piSet_mono (fun p hp =>
    hle (S.tg c) (hS.htg c hc) (sfst p) (sfst_mem_of_mem_tele hp)) h hh

theorem slot_mem_univ (hS : WOk S) (hw : S.w ≠ 0) {X : Nat → V}
    (hX : InTupleSpace S.w S.k (wIs S) X) {c : Nat} (hc : c < S.k) {x : V} :
    slot S X c x ∈ˢ (univ S.w : V) :=
  (univ_isTGUniverse (V := V) hw).piSet_mem (tele_mem_univ hS hw) fun _p hp =>
    famSpace_app (hX (S.tg c) (hS.htg c hc)) (sfst_mem_of_mem_tele hp)

theorem wΨ_maps (hS : WOk S) (hw : S.w ≠ 0) : MapsTuple S.w S.k (wIs S) (wΨ S) := by
  intro X hX c hc
  have hU := univ_isTGUniverse (V := V) hw
  refine graph_mem_famSpace fun x _ => ?_
  exact hU.image_mem (slot_mem_univ hS hw hX hc) fun h hh =>
    hS.memU hw c h (hU.transitive (slot_mem_univ hS hw hX hc) hh)

/-! ### (W): the closed tuple

`tupleContainer_closed_exists` reads the position set `B` and the
targets off the SHAPE alone, so an INDEXED block must carry the index
inside the shape (and a MUTUAL one its member): the shape at
component `c`, index `x` is `⟨c, x⟩`.  -- F3 FINDING (1), §6. -/

open Classical in
/-- The `Nat` read back from a numeral tag: the inverse of `vnat` on
the numerals (`natFibre`'s `Nat`-valued twin, needed because
`tupleContainer_closed_exists`'s `tgtM` is `V → V → Nat`). -/
noncomputable def tagOf (v : V) : Nat := if h : ∃ n, v = vnat (V := V) n then h.choose else 0

theorem tagOf_vnat (n : Nat) : tagOf (vnat n : V) = n := by
  unfold tagOf
  rw [dif_pos ⟨n, rfl⟩]
  exact (vnat_inj (Classical.choose_spec (⟨n, rfl⟩ : ∃ n', (vnat n : V) = vnat n'))).symm

/-- The shapes at component `c`, index `x`: the one constructor,
tagged by its member AND by the index. -/
noncomputable def wShp (c : Nat) (x : V) : V := sing (kpair (vnat c) x)

/-- A shape's positions: the telescope at the shape's index. -/
noncomputable def wPos (S : WSig V) (a : V) : V := tele S (ssnd a)

/-- A position's target member: the shape's own member, through `tg`. -/
noncomputable def wTgtM (S : WSig V) (a : V) (_p : V) : Nat := S.tg (tagOf (sfst a))

/-- A position's target index: the position's own first component. -/
noncomputable def wTgtI (_a p : V) : V := sfst p

/-- The builder: the shape's member's injection at the slot. -/
noncomputable def wMk (S : WSig V) (_m : Nat) (a g : V) : V := S.inj (tagOf (sfst a)) [g]

/-- **(W)**: the block's operator has a closed tuple. -/
theorem wΨ_closed (hS : WOk S) (hw : S.w ≠ 0) :
    ∃ L, IsClosedTuple S.w S.k (wIs S) (wΨ S) L := by
  have hU := univ_isTGUniverse (V := V) hw
  refine tupleContainer_closed_exists hw (Is := wIs S) (wΨ S) wShp (wPos S) (wTgtM S) wTgtI
    (wMk S) ?hA ?hB ?htgt ?hmkU ?helim
  case hA =>
    intro c _ x hx
    exact hU.sing_mem hS.hα (hU.kpair_mem hS.hα (vnat_mem_univ_pos hw c) (hU.transitive hS.hα hx))
  case hB =>
    intro c _ x a hx ha
    obtain rfl := mem_sing.mp ha
    show tele S (ssnd (kpair (vnat c) x)) ∈ˢ _
    rw [ssnd_kpair]
    exact tele_mem_univ hS hw
  case htgt =>
    intro c hc x a p hx ha hp
    obtain rfl := mem_sing.mp ha
    have hp' : p ∈ˢ tele S x := by
      have h : p ∈ˢ tele S (ssnd (kpair (vnat c) x)) := hp
      rwa [ssnd_kpair] at h
    refine ⟨?_, ?_⟩
    · show S.tg (tagOf (sfst (kpair (vnat c) x))) < S.k
      rw [sfst_kpair, tagOf_vnat]
      exact hS.htg c hc
    · show sfst p ∈ˢ S.α
      exact sfst_mem_of_mem_tele hp'
  case hmkU =>
    intro c _ x a g hx ha hg
    obtain rfl := mem_sing.mp ha
    show S.inj (tagOf (sfst (kpair (vnat c) x))) [g] ∈ˢ _
    rw [sfst_kpair, tagOf_vnat]
    exact hS.memU hw c g hg
  case helim =>
    intro X hX c hc x hx v hv
    rw [app_wΨ hx] at hv
    obtain ⟨h, hh, rfl⟩ := mem_wFib.mp hv
    refine ⟨kpair (vnat c) x, mem_sing.mpr rfl, h, ?_, ?_⟩
    · show h ∈ˢ piSet (tele S (ssnd (kpair (vnat c) x)))
        fun p => app (X (S.tg (tagOf (sfst (kpair (vnat c) x))))) (sfst p)
      rw [sfst_kpair, ssnd_kpair, tagOf_vnat]
      exact hh
    · show _ = S.inj (tagOf (sfst (kpair (vnat c) x))) [h]
      rw [sfst_kpair, tagOf_vnat]

/-! ### The carrier and its constructors -/

/-- The block's carrier tuple. -/
noncomputable def car (S : WSig V) : Nat → V := lfpTuple S.w S.k (wIs S) (wΨ S)

theorem car_mem (S : WSig V) : InTupleSpace S.w S.k (wIs S) (car S) := lfpTuple_mem _ _ _ _

/-- **The fixed-point equation**, fibrewise: a value at component `c`,
index `x`, IS `intro x h` for a field `h` fitting the telescope with
values in the carrier at the positions' own indices. -/
theorem mem_car (hS : WOk S) (hw : S.w ≠ 0) {c : Nat} (hc : c < S.k) {x : V} (hx : x ∈ˢ S.α)
    {v : V} : v ∈ˢ app (car S c) x ↔ ∃ h, h ∈ˢ slot S (car S) c x ∧ v = S.inj c [h] := by
  unfold car
  rw [← app_lfpTuple_eq (wΨ_closed hS hw) (wΨ_mono hS) (wΨ_maps hS hw) hc hx, app_wΨ hx]
  exact mem_wFib

/-- **The constructor is typed**: `intro x h` is a carrier value. -/
theorem intro_mem_car (hS : WOk S) (hw : S.w ≠ 0) {c : Nat} (hc : c < S.k) {x : V}
    (hx : x ∈ˢ S.α) {h : V} (hh : h ∈ˢ slot S (car S) c x) :
    S.inj c [h] ∈ˢ app (car S c) x := (mem_car hS hw hc hx).mpr ⟨h, hh, rfl⟩

/-- The field's value at a telescope position is a carrier value AT
THE POSITION'S OWN INDEX — the reflexive field's reading. -/
theorem field_mem_car {c : Nat} {x h p : V} (hh : h ∈ˢ slot S (car S) c x)
    (hp : p ∈ˢ tele S x) : app h p ∈ˢ app (car S (S.tg c)) (sfst p) :=
  app_mem_of_mem_piSet hh hp

/-! ## §2 The recursor: `UnionRecKit` at the indexed block

The recursion's index set is the union of the carrier's values
(`unionSet`), tagged by the member AND by the member's own index — at
an indexed block the tag `⟨c, x, v⟩` carries a real index, not `pt`. -/

section Rec

/-- The motives and the minors of the block's recursion. -/
structure RecData (V : Type u) [SetTheory V] where
  /-- The motives, one per member, at the member's index and value. -/
  M : Nat → V → V → V
  /-- The one minor per member: the index, the field, the ih tower. -/
  mIntro : Nat → V → V → V → V

variable {ℓ : Nat} {R : RecData V}

/-- **The ih tower's type** at component `c`, index `x` and field `h`:
the CURRIED product over the reflexive field's two binders —
`(y : α) → (hy : r y x) → M (tg c) y (h y hy)`.  Its outer domain is
the whole of `α` and its inner domain the truth value `rel y x`, while
the predecessor set holds only the images `h ⟨y, hy⟩`. -/
noncomputable def ihTy (S : WSig V) (R : RecData V) (c : Nat) (x h : V) : V :=
  piSet S.α fun y => piSet (S.rel y x) fun hy => R.M (S.tg c) y (app h (kpair y hy))

/-- The minors' typing hypotheses — the ONLY thing the recursor's
typing and its ι rule consume. -/
structure RecOk (S : WSig V) (ℓ : Nat) (R : RecData V) : Prop where
  /-- The motives take values in `univ ℓ`. -/
  motive : ∀ c, c < S.k → ∀ x, x ∈ˢ S.α → ∀ v, v ∈ˢ app (car S c) x → R.M c x v ∈ˢ (univ ℓ : V)
  /-- The minor of member `c`, at a fitting field and a fitting ih
  tower. -/
  minor : ∀ c, c < S.k → ∀ x, x ∈ˢ S.α → ∀ h, h ∈ˢ slot S (car S) c x →
    ∀ ih, ih ∈ˢ ihTy S R c x h → R.mIntro c x h ih ∈ˢ R.M c x (S.inj c [h])

/-- The index set of the recursion: the union of the carrier's values. -/
noncomputable def wIdx (S : WSig V) : V := unionSet S.k (wIs S) (car S)

theorem tagged_mem_wIdx {c : Nat} (hc : c < S.k) {x : V} (hx : x ∈ˢ S.α) {v : V}
    (hv : v ∈ˢ app (car S c) x) : tagged c x v ∈ˢ wIdx S :=
  tagged_mem_unionSet hc hx hv

theorem mem_wIdx {u : V} :
    u ∈ˢ wIdx S ↔ ∃ c, c < S.k ∧ ∃ x, x ∈ˢ S.α ∧ ∃ v, v ∈ˢ app (car S c) x ∧ u = tagged c x v :=
  mem_unionSet

/-! ### The predecessors: a SET that depends on the parameters and on the index

`intro x h`'s predecessors are the images of its reflexive field over
the field's whole telescope — `{ ⟨tg c, y, h ⟨y, hy⟩⟩ | y ∈ α, hy ∈ r y x }`.
The set is infinite in general, its indexing set depends on both
parameters and on the index `x`, and its elements sit at the VARYING
index `y`.  As in F0–F2 it is a `relPred`: a separation of the union
by a relation, so nothing has to be shown to be a set. -/

/-- The predecessor relation: the field's images over its telescope. -/
def WRel (S : WSig V) (u v : V) : Prop :=
  ∃ c x h p, u = tagged c x (S.inj c [h]) ∧ p ∈ˢ tele S x ∧
    v = tagged (S.tg c) (sfst p) (app h p)

/-- The predecessor sets. -/
noncomputable def wPred (S : WSig V) (u : V) : V := relPred (wIdx S) (WRel S) u

theorem wPred_subset (S : WSig V) (u : V) : wPred S u ⊆ˢ wIdx S := relPred_subset _ _ u

/-- **The predecessors of a constructor value**, decomposed: exactly
the images of the field over the telescope (`mkInj` identifies the
field, `tagged_inj` the member and the index). -/
theorem mem_wPred_intro (hS : WOk S) (hw : S.w ≠ 0) {c : Nat} {x h v : V} :
    v ∈ˢ wPred S (tagged c x (S.inj c [h])) ↔
      v ∈ˢ wIdx S ∧ ∃ p, p ∈ˢ tele S x ∧ v = tagged (S.tg c) (sfst p) (app h p) := by
  unfold wPred
  rw [mem_relPred]
  refine and_congr_right fun _ => ⟨fun hv => ?_, ?_⟩
  · obtain ⟨c', x', h', p, he, hp, rfl⟩ := hv
    obtain ⟨rfl, rfl, hinj⟩ := tagged_inj he
    obtain ⟨-, rfl⟩ := inj_inj hS hw hinj
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨c, x, h, p, rfl, hp, rfl⟩

/-- **The predecessors come from the argument tuple** — at EVERY tuple
`X` in the space, because a fitting field at `X` has its values in
`X`'s own components, at the positions' own indices. -/
theorem wPred_predsFrom (hS : WOk S) (hw : S.w ≠ 0) :
    PredsFrom S.w S.k (wIs S) (wΨ S) (wPred S) := by
  intro X hX _hXle c hc x hx v hv z hz
  rw [app_wΨ hx] at hv
  obtain ⟨h, hh, rfl⟩ := mem_wFib.mp hv
  obtain ⟨-, c', x', h', p, he, hp, rfl⟩ := mem_relPred.mp hz
  obtain ⟨rfl, rfl, hinj⟩ := tagged_inj he
  obtain ⟨-, rfl⟩ := inj_inj hS hw hinj
  exact tagged_mem_unionSet (hS.htg c hc) (sfst_mem_of_mem_tele hp)
    (app_mem_of_mem_piSet hh hp)

/-! ### The ih tower, the bound and the step -/

/-- **The ih tower** at a graph `g` of recursive values: the CURRIED
two-level λ-tower `fun y hy => g ⟨tg c, y, h ⟨y, hy⟩⟩` over the field's
two binders. -/
noncomputable def ihFun (S : WSig V) (g h : V) (c : Nat) (x : V) : V :=
  graph (fun y => graph (fun hy => app g (tagged (S.tg c) y (app h (kpair y hy)))) (S.rel y x))
    S.α

theorem app_ihFun {g h : V} {c : Nat} {x y : V} (hy : y ∈ˢ S.α) :
    app (ihFun S g h c x) y
      = graph (fun hy' => app g (tagged (S.tg c) y (app h (kpair y hy')))) (S.rel y x) :=
  app_graph hy

theorem app_app_ihFun {g h : V} {c : Nat} {x y hy : V} (hyα : y ∈ˢ S.α)
    (hhy : hy ∈ˢ S.rel y x) :
    app (app (ihFun S g h c x) y) hy = app g (tagged (S.tg c) y (app h (kpair y hy))) := by
  rw [app_ihFun hyα, app_graph hhy]

/-- The bound: the motive of the value's member, at the value's own
index and value. -/
noncomputable def wB (M : Nat → V → V → V) (u : V) : V :=
  natFibre (fun c => M c (sfst (ssnd u)) (ssnd (ssnd u))) (sfst u)

theorem wB_at (M : Nat → V → V → V) (c : Nat) (x v : V) : wB M (tagged c x v) = M c x v := by
  unfold wB tagged
  rw [sfst_kpair, ssnd_kpair, sfst_kpair, ssnd_kpair, natFibre_vnat]

open Classical in
/-- The step at a decomposed value: the member's minor at the index,
the field and the ih tower. -/
noncomputable def stAt (S : WSig V) (R : RecData V) (g : V) (c : Nat) (x v : V) : V :=
  if hh : ∃ h, v = S.inj c [h] then R.mIntro c x hh.choose (ihFun S g hh.choose c x) else empty

/-- **The step**: the member is read back off the tag, the index and
the value off the pair. -/
noncomputable def wSt (S : WSig V) (R : RecData V) (u g : V) : V :=
  natFibre (fun c => stAt S R g c (sfst (ssnd u)) (ssnd (ssnd u))) (sfst u)

theorem wSt_at (c : Nat) (x v g : V) : wSt S R (tagged c x v) g = stAt S R g c x v := by
  unfold wSt tagged
  rw [sfst_kpair, ssnd_kpair, sfst_kpair, ssnd_kpair, natFibre_vnat]

theorem stAt_intro (hS : WOk S) (hw : S.w ≠ 0) (g : V) (c : Nat) (x h : V) :
    stAt S R g c x (S.inj c [h]) = R.mIntro c x h (ihFun S g h c x) := by
  unfold stAt
  rw [dif_pos ⟨h, rfl⟩]
  have hs := Exists.choose_spec (⟨h, rfl⟩ : ∃ h', S.inj c [h] = S.inj (V := V) c [h'])
  rw [← (inj_inj hS hw hs).2]

theorem wSt_intro (hS : WOk S) (hw : S.w ≠ 0) (g : V) (c : Nat) (x h : V) :
    wSt S R (tagged c x (S.inj c [h])) g = R.mIntro c x h (ihFun S g h c x) := by
  rw [wSt_at, stAt_intro hS hw]

/-! ### The kit -/

section Kit

variable (hS : WOk S) (hw : S.w ≠ 0) (hR : RecOk S ℓ R)

include hR in
theorem wB_mem_univ : ∀ u, u ∈ˢ wIdx S → wB R.M u ∈ˢ (univ ℓ : V) := by
  intro u hu
  obtain ⟨c, hc, x, hx, v, hv, rfl⟩ := mem_wIdx.mp hu
  rw [wB_at]
  exact hR.motive c hc x hx v hv

include hR in
theorem wGraph_mem_B {u v : V} (hu : u ∈ˢ wIdx S)
    (hv : v ∈ˢ app (recGraph ℓ (wIdx S) (wPred S) (wB R.M) (wSt S R)) u) : v ∈ˢ wB R.M u := by
  rw [app_recGraph_eq (wB_mem_univ hR) (fun u _ => wPred_subset S u) hu] at hv
  exact (mem_recGraphFibre.mp hv).1

include hS hw hR in
/-- **The step is typed** — from the minor's typing alone.  The work
is the ih tower: its outer domain is `α` and its inner domain
`rel y x`, and at every pair of those the tower's value is the graph's
value at a PREDECESSOR (`kpair_mem_tele` puts the pair in the
telescope), hence in the motive at the field's value. -/
theorem wSt_mem : ∀ u, u ∈ˢ wIdx S → ∀ g,
    g ∈ˢ piSet (wPred S u)
      (fun j => app (recGraph ℓ (wIdx S) (wPred S) (wB R.M) (wSt S R)) j) →
    wSt S R u g ∈ˢ wB R.M u := by
  intro u hu g hg
  have hval : ∀ v, v ∈ˢ wPred S u → app g v ∈ˢ wB R.M v := fun v hv =>
    wGraph_mem_B hR (wPred_subset S u v hv) (app_mem_of_mem_piSet hg hv)
  obtain ⟨c, hc, x, hx, v, hv, rfl⟩ := mem_wIdx.mp hu
  obtain ⟨h, hh, rfl⟩ := (mem_car hS hw hc hx).mp hv
  rw [wSt_intro hS hw, wB_at]
  refine hR.minor c hc x hx h hh _ ?_
  refine graph_mem_piSet fun y hy => ?_
  refine graph_mem_piSet fun hyv hhy => ?_
  have hp : kpair y hyv ∈ˢ tele S x := kpair_mem_tele hy hhy
  have hmem : tagged (S.tg c) (sfst (kpair y hyv)) (app h (kpair y hyv))
      ∈ˢ wPred S (tagged c x (S.inj c [h])) :=
    (mem_wPred_intro hS hw).mpr
      ⟨tagged_mem_wIdx (hS.htg c hc) (sfst_mem_of_mem_tele hp) (field_mem_car hh hp),
        kpair y hyv, hp, rfl⟩
  rw [sfst_kpair] at hmem
  have := hval _ hmem
  rwa [wB_at] at this

/-- **The block's recursion kit** at an indexed, parametric block with
a reflexive field. -/
noncomputable def wKit : UnionRecKit ℓ S.w S.k (wIs S) (wΨ S) :=
  ⟨wPred S, wB R.M, wSt S R, wPred_predsFrom hS hw, wB_mem_univ hR, wSt_mem hS hw hR⟩

local notation "K*" => wKit hS hw hR

@[simp] theorem wKit_pred : (K*).pred = wPred S := rfl
@[simp] theorem wKit_B : (K*).B = wB R.M := rfl
@[simp] theorem wKit_st : (K*).st = wSt S R := rfl

theorem wKit_recAt (c : Nat) (x v : V) :
    (K*).recAt c x v = recSel (recGraph ℓ (wIdx S) (wPred S) (wB R.M) (wSt S R)) (tagged c x v) :=
  rfl

/-- Member `c`'s recursor, at the index and the value. -/
noncomputable def recAt (c : Nat) (x v : V) : V := (wKit hS hw hR).recAt c x v

include hS hw hR in
/-- **Typing**: the recursor's value lies in the member's motive at
the index and the value. -/
theorem recAt_mem {c : Nat} (hc : c < S.k) {x : V} (hx : x ∈ˢ S.α) {v : V}
    (hv : v ∈ˢ app (car S c) x) : recAt hS hw hR c x v ∈ˢ R.M c x v := by
  have h := (K*).rec_mem_B (wΨ_closed hS hw) (wΨ_mono hS) (wΨ_maps hS hw) hc hx hv
  rw [wKit_B, wB_at] at h
  exact h

include hS hw hR in
theorem wRec_eq {c : Nat} (hc : c < S.k) {x : V} (hx : x ∈ˢ S.α) {v : V}
    (hv : v ∈ˢ app (car S c) x) :
    (K*).recAt c x v
      = wSt S R (tagged c x v)
          (graph (fun j => recSel (recGraph ℓ (wIdx S) (wPred S) (wB R.M) (wSt S R)) j)
            (wPred S (tagged c x v))) :=
  (K*).rec_eq (wΨ_closed hS hw) (wΨ_mono hS) (wΨ_maps hS hw) hc hx hv

include hS hw hR in
/-- **The ι rule** of member `c`:

    rec c x (intro x h) = mIntro c x h (fun y hy => rec (tg c) y (h y hy))

— the ih tower is the tower of recursive calls at the field's images,
each at ITS OWN index `y`. -/
theorem rec_intro {c : Nat} (hc : c < S.k) {x : V} (hx : x ∈ˢ S.α) {h : V}
    (hh : h ∈ˢ slot S (car S) c x) :
    recAt hS hw hR c x (S.inj c [h])
      = R.mIntro c x h
          (graph (fun y => graph (fun hy =>
            recAt hS hw hR (S.tg c) y (app h (kpair y hy))) (S.rel y x)) S.α) := by
  show (K*).recAt c x (S.inj c [h]) = _
  rw [wRec_eq hS hw hR hc hx (intro_mem_car hS hw hc hx hh), wSt_intro hS hw]
  congr 1
  unfold ihFun
  refine graph_congr fun y hy => graph_congr fun hyv hhy => ?_
  have hp : kpair y hyv ∈ˢ tele S x := kpair_mem_tele hy hhy
  have hmem : tagged (S.tg c) (sfst (kpair y hyv)) (app h (kpair y hyv))
      ∈ˢ wPred S (tagged c x (S.inj c [h])) :=
    (mem_wPred_intro hS hw).mpr
      ⟨tagged_mem_wIdx (hS.htg c hc) (sfst_mem_of_mem_tele hp) (field_mem_car hh hp),
        kpair y hyv, hp, rfl⟩
  rw [sfst_kpair] at hmem
  rw [app_graph hmem]
  rfl

end Kit

end Rec

/-! ## §3 The `ℓ = 0` arm: `mem_type` by induction, with no recursor

The recursor review's G4: at a `Prop`-valued motive (`ℓ = 0`) the
union kit is the wrong instrument — at `w = 0` `PredsFrom` even forces
`pred u = ∅` at a field-free constructor, and `hst` becomes the
theorem itself.  The repair the model lane will implement is this
section: `mem_type` — "every carrier value's motive fibre is
inhabited" — comes DIRECTLY from `lfpTuple_induction` with
`P := "the motive fibre is inhabited"`, consuming only the step's
typing at the `sepTuple` frame with the ih values `pt`; and the ι rule
is `pt = pt`.  No accessibility, no graph, no bound, at ANY `w` —
including this file's `w ≠ 0` block with its reflexive field under
`Π`.

The arm is stated abstractly (`InductionKit`, over any tuple functor
at any width) and then instantiated at the block of §1 — the shape the
model lane needs at a reflexive field. -/

section Zero

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}

/-- **The induction kit**: at `ℓ = 0` the recursion data degenerates
to the motive alone.  `step` is the residue's typing at the `sepTuple`
frame — the ih values are `pt` (`lamR 0 = pt`), so the only thing the
frame carries is that the recursive fields' values lie in the carrier
AND have inhabited motive fibres, which is exactly what `sepTuple`
says. -/
structure InductionKit (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) where
  /-- The motive fibre at member `c`, index `i`, value `x`. -/
  B : Nat → V → V → V
  /-- The step, at the separated tuple. -/
  step : ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x,
    x ∈ˢ app (Φ (sepTuple w k Is Φ (fun c i x => ∃ z, z ∈ˢ B c i x)) c) i →
      ∃ z, z ∈ˢ B c i x

namespace InductionKit

variable (K : InductionKit w k Is Φ)

/-- **`mem_type` at `ℓ = 0`**: every carrier value's motive fibre is
inhabited.  The whole proof is `lfpTuple_induction` at the kit's own
step — no `unionRec`, no `PredsFrom`, no `accFam`. -/
theorem mem_type (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ) :
    ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ c) i →
      ∃ z, z ∈ˢ K.B c i x :=
  lfpTuple_induction h hmono (fun c i x => ∃ z, z ∈ˢ K.B c i x) K.step

/-- At a `Prop`-valued motive the fibre is a truth value, so
"inhabited" IS "`pt` is a member" — the recursor's value at every
point. -/
theorem pt_mem_B (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hB : ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ c) i →
      K.B c i x ∈ˢ (univ 0 : V)) :
    ∀ c, c < k → ∀ i, i ∈ˢ Is c → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ c) i →
      (pt : V) ∈ˢ K.B c i x := by
  intro c hc i hi x hx
  obtain ⟨z, hz⟩ := K.mem_type h hmono c hc i hi x hx
  have hsub : K.B c i x ⊆ˢ (unitSet : V) := by
    have := hB c hc i hi x hx
    rw [univ_zero] at this
    exact mem_univZero.mp this
  rwa [← mem_unitSet_iff.mp (hsub z hz)]

end InductionKit

/-- **ι at `ℓ = 0` is `pt = pt`**: a leaf lying in a truth value IS
`pt`, and every application of `pt` is `pt` (`app_pt`), so the ι
equation's left-hand side reads `pt` whatever its arguments are — for
a reflexive field's two-binder telescope as much as for a plain one.
No typing of the rule's body enters. -/
theorem app₂_of_mem_unitSet {f : V} (hf : f ∈ˢ (unitSet : V)) (a b : V) :
    app (app f a) b = (pt : V) := by
  rw [mem_unitSet_iff.mp hf, app_pt, app_pt]

/-- Both sides of an ι equation at `ℓ = 0` read `pt`. -/
theorem eq_of_mem_unitSet {lhs rhs : V} (hl : lhs ∈ˢ (unitSet : V))
    (hr : rhs ∈ˢ (unitSet : V)) : lhs = rhs := by
  rw [mem_unitSet_iff.mp hl, mem_unitSet_iff.mp hr]

end Zero

/-! ### The `ℓ = 0` arm at the block of §1

The step the model lane owes at a REFLEXIVE field: the minor's
conclusion at the induction hypothesis "every image of the field over
its telescope has an inhabited motive fibre" — the ih is a
*proposition about the whole telescope*, not a value, and the field's
values are read at their OWN indices. -/

/-- The block's `ℓ = 0` induction kit. -/
noncomputable def wIndKit (hS : WOk S) (M : Nat → V → V → V)
    (hmin : ∀ c, c < S.k → ∀ x, x ∈ˢ S.α → ∀ h, h ∈ˢ slot S (car S) c x →
      (∀ y hy, y ∈ˢ S.α → hy ∈ˢ S.rel y x →
        ∃ z, z ∈ˢ M (S.tg c) y (app h (kpair y hy))) →
      ∃ z, z ∈ˢ M c x (S.inj c [h])) :
    InductionKit S.w S.k (wIs S) (wΨ S) where
  B := M
  step := by
    intro c hc x hx v hv
    rw [app_wΨ hx] at hv
    obtain ⟨h, hh, rfl⟩ := mem_wFib.mp hv
    -- the field fits the CARRIER (the separated tuple lies below it) …
    have hle := sepTuple_le S.w S.k (wIs S) (wΨ S) (fun c i x => ∃ z, z ∈ˢ M c i x)
    have hcar : h ∈ˢ slot S (car S) c x :=
      piSet_mono (fun p hp => hle (S.tg c) (hS.htg c hc) (sfst p)
        (sfst_mem_of_mem_tele hp)) h hh
    -- … and every one of its images has an inhabited motive fibre
    refine hmin c hc x hx h hcar fun y hy hyα hhy => ?_
    have hmem : app h (kpair y hy)
        ∈ˢ app (sepTuple S.w S.k (wIs S) (wΨ S) (fun c i x => ∃ z, z ∈ˢ M c i x) (S.tg c)) y := by
      have := app_mem_of_mem_piSet hh (kpair_mem_tele hyα hhy)
      rwa [sfst_kpair] at this
    unfold sepTuple at hmem
    rw [app_graph (show y ∈ˢ wIs S (S.tg c) from hyα)] at hmem
    exact (mem_sep.mp hmem).2

/-- **The `ℓ = 0` arm at the block**: every carrier value's motive
fibre is inhabited, by induction alone — the recursor of §2 is not
built, and no bound, accessibility or graph is needed.  Compare
`recAt_mem` (§2), which needs the whole kit. -/
theorem w_mem_type_zero (hS : WOk S) (hw : S.w ≠ 0) (M : Nat → V → V → V)
    (hmin : ∀ c, c < S.k → ∀ x, x ∈ˢ S.α → ∀ h, h ∈ˢ slot S (car S) c x →
      (∀ y hy, y ∈ˢ S.α → hy ∈ˢ S.rel y x →
        ∃ z, z ∈ˢ M (S.tg c) y (app h (kpair y hy))) →
      ∃ z, z ∈ˢ M c x (S.inj c [h])) :
    ∀ c, c < S.k → ∀ x, x ∈ˢ S.α → ∀ v, v ∈ˢ app (car S c) x → ∃ z, z ∈ˢ M c x v :=
  (wIndKit hS M hmin).mem_type (wΨ_closed hS hw) (wΨ_mono hS)

/-! ## §4 The two instances: `W` (k = 1) and a MUTUAL indexed block (k = 2)

Everything above is at a width `k` with a target function `tg`, so
both instances are the same theorems read at a datum; the mutual one
exercises indices at `k ≥ 2` with a CROSSING reflexive field
(component `0`'s field lands at component `1`, at the varying index
`y`). -/

section Instances

variable {ℓ : Nat} {R : RecData V}

/-- `W α r x ::= intro (h : (y : α) → r y x → W α r y)` — one member,
the reflexive field targeting its own member. -/
noncomputable def wSigOne (w : Nat) (α : V) (rel : V → V → V) (inj : Nat → List V → V) :
    WSig V := ⟨w, 1, fun _ => 0, α, rel, inj⟩

/-- `A x ::= mkA (h : (y : α) → r y x → B y)`,
`B x ::= mkB (h : (y : α) → r y x → A y)` — two members, indexed, each
member's reflexive field CROSSING to the other. -/
noncomputable def wSigMut (w : Nat) (α : V) (rel : V → V → V) (inj : Nat → List V → V) :
    WSig V := ⟨w, 2, fun c => 1 - c, α, rel, inj⟩

variable {w : Nat} {α : V} {rel : V → V → V} {inj : Nat → List V → V}

/-- `W`'s ι rule: the ih tower is `fun y hy => rec y (h y hy)`, at the
field's own varying index. -/
theorem rec_intro_one (hS : WOk (wSigOne (V := V) w α rel inj)) (hw : w ≠ 0)
    (hR : RecOk (wSigOne w α rel inj) ℓ R) {x : V} (hx : x ∈ˢ α)
    {h : V} (hh : h ∈ˢ slot (wSigOne w α rel inj) (car (wSigOne w α rel inj)) 0 x) :
    recAt hS hw hR 0 x (inj 0 [h])
      = R.mIntro 0 x h
          (graph (fun y => graph (fun hy =>
            recAt hS hw hR 0 y (app h (kpair y hy))) (rel y x)) α) :=
  rec_intro hS hw hR (show 0 < 1 by omega) hx hh

/-- The MUTUAL block's ι rule at member `0`: the ih tower recurses at
member `1`. -/
theorem rec_intro_mut_zero (hS : WOk (wSigMut (V := V) w α rel inj)) (hw : w ≠ 0)
    (hR : RecOk (wSigMut w α rel inj) ℓ R) {x : V} (hx : x ∈ˢ α)
    {h : V} (hh : h ∈ˢ slot (wSigMut w α rel inj) (car (wSigMut w α rel inj)) 0 x) :
    recAt hS hw hR 0 x (inj 0 [h])
      = R.mIntro 0 x h
          (graph (fun y => graph (fun hy =>
            recAt hS hw hR 1 y (app h (kpair y hy))) (rel y x)) α) :=
  rec_intro hS hw hR (show 0 < 2 by omega) hx hh

/-- The MUTUAL block's ι rule at member `1`: the ih tower recurses at
member `0`. -/
theorem rec_intro_mut_one (hS : WOk (wSigMut (V := V) w α rel inj)) (hw : w ≠ 0)
    (hR : RecOk (wSigMut w α rel inj) ℓ R) {x : V} (hx : x ∈ˢ α)
    {h : V} (hh : h ∈ˢ slot (wSigMut w α rel inj) (car (wSigMut w α rel inj)) 1 x) :
    recAt hS hw hR 1 x (inj 1 [h])
      = R.mIntro 1 x h
          (graph (fun y => graph (fun hy =>
            recAt hS hw hR 0 y (app h (kpair y hy))) (rel y x)) α) :=
  rec_intro hS hw hR (show 1 < 2 by omega) hx hh

end Instances

/-! ## §5 Non-vacuity

`WOk` has a model — F0's standard tags at any width, with the index
type `unitSet` and the empty relation — whose CARRIER is inhabited at
every index, so §2's recursor and §3's induction are about a real
set. -/

/-- The standard datum: F0's tags, `α := unitSet`, `r := ⊥`. -/
noncomputable def stdSig (w k : Nat) (tg : Nat → Nat) : WSig V :=
  ⟨w, k, tg, unitSet, fun _ _ => empty, stdInj w⟩

/-- The standard datum satisfies the block's laws. -/
theorem wOk_std {w : Nat} (hw : w ≠ 0) {k : Nat} {tg : Nat → Nat}
    (htg : ∀ c, c < k → tg c < k) : WOk (stdSig (V := V) w k tg) where
  htg := htg
  hα := unitSet_mem_univ w
  relSub := fun _ _ => empty_subset _
  memU := fun _ _ h hh => stdInj_mem_univ hw (by
    intro z hz
    rw [List.mem_singleton.mp hz]
    exact hh)
  mkInj := fun hw' j j' fs fs' he => stdInj_inj hw' j j' fs fs' he

/-- **The carrier is inhabited at every index**: the empty relation
makes every telescope empty, so the reflexive field is the empty
function and every member has a value at every index. -/
theorem std_car_nonempty {w : Nat} (hw : w ≠ 0) {k : Nat} {tg : Nat → Nat}
    (htg : ∀ c, c < k → tg c < k) {c : Nat} (hc : c < k) {x : V}
    (hx : x ∈ˢ (unitSet : V)) :
    ∃ v, v ∈ˢ app (car (stdSig (V := V) w k tg) c) x := by
  refine ⟨stdInj w c [graph (fun _ => (pt : V)) (tele (stdSig (V := V) w k tg) x)],
    intro_mem_car (wOk_std hw htg) hw hc hx (graph_mem_piSet fun p hp => ?_)⟩
  obtain ⟨y, -, hy, hhy, -⟩ := mem_tele.mp hp
  exact absurd hhy (not_mem_empty _)

/-! ## §6 The findings

Two PRESENTATION constraints, neither a soundness gap; both are about
what the recursor lane's `BlockModelAt` must supply, not about what
`UnionRec.lean` proves.

**F3 FINDING (1) — (W)'s container reads the positions off the SHAPE
alone.**  `tupleContainer_closed_exists` takes
`B : V → V`, `tgtM : V → V → Nat`, `tgtI : V → V → V` — all functions
of the SHAPE (and the position), with no access to the member `m` or
the index `i`.  At an INDEXED block the position set of a constructor
depends on the index (here `tele S x`, the reflexive field's
telescope), and at a MUTUAL block the target member depends on the
member — so the shape has to carry BOTH: `wShp c x = {⟨c, x⟩}`, with a
`Nat` readback of the member's numeral tag (`tagOf`) because `tgtM`'s
codomain is `Nat`.  Nothing breaks, and the shape family `A m i` is
already index-dependent, so the block model's container presentation
must simply be *stated* with member-and-index-tagged shapes.  (The
alternative — widening the kit to `B : Nat → V → V → V`,
`tgtM : Nat → V → V → Nat` — is a mechanical change to
`SetModel/TupleContainer.lean` and would delete `tagOf`.)

**F3 FINDING (2) — the ih tower's domain is NOT the predecessor set.**
`UnionRecKit.hst` hands the step a function `g` on `pred u`, i.e. on
the tagged IMAGES `⟨tg c, y, h ⟨y, hy⟩⟩` of the reflexive field.  The
minor of a reflexive field, however, is applied to a CURRIED λ-tower
`ih : (y : α) → (hy : r y x) → M (tg c) y (h y hy)` whose outer domain
is the whole of `α` and whose inner domain is the truth value
`r y x` — an object of a different shape, built here by `ihFun` and
typed by `graph_mem_piSet` twice (`wSt_mem`).  The kit supplies
exactly what is needed for that (the graph is total on `pred u` and
`pred u` contains every image, `mem_wPred_intro`), but the
CONVERSION is the recursor lane's obligation: `BlockModelAt` must
record, per recursive field, the telescope `tele`, the target member
and the index map `p ↦ sfst p`, and the model's `st` must be the minor
at `ihFun`, not at `g` itself.  §2's `wSt`/`rec_intro` are that
conversion in the smallest instance that has it.

Two non-findings worth recording, because the review left them open:

* `PredsFrom` at an INFINITE, parameter- and index-dependent
  predecessor set needed nothing new: `relPred` keeps `pred u` a `sep`
  of the union (never a `piSet`-indexed family that would have to be
  shown to be a set), and the fitting field at an ARBITRARY tuple `X`
  — `PredsFrom`'s quantifier — gives the membership directly
  (`wPred_predsFrom`, five lines).
* the `ℓ = 0` arm (§3) needs neither `hst` nor accessibility nor a
  bound, exactly as the review's G4 says: `InductionKit.mem_type` is
  `lfpTuple_induction` at the motive-fibre predicate, and it is
  stated at an arbitrary width over an arbitrary tuple functor, so the
  model lane can consume it for every block, reflexive fields
  included.
-/

end WBlock

end ConLeche.SetTheory
