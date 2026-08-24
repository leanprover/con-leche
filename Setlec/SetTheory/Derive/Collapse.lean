import Setlec.SetTheory.Basic

/-!
# Level-free `pi`/`lam` via the domain-relative point collapse (task #100)

The level-free binder operators `piC`/`lamC` (with the collapse `pcol`)
that are to replace the leveled `pi`/`lam` of `Derive/Pi.lean` in the
annotation-erasure migration, together with their full law battery and
the design evidence that fixed this construction.  **Nothing here is
consumed by the checker or the current model yet**: the module lands
ahead of the model flip (see DESIGN.md, "Annotation erasure: the
domain-relative collapse (task #100)", for the migration order and for
why the flip is blocked on de-gating the kernel's annotation-guarded
reduction paths first).

## Verdict summary (canon-model spike, 2026-08-24)

* The **literal proposal** — a global `canon : V → V` by ∈-induction
  ("a set of pairs all of whose second components canonicalize to `pt`
  collapses to `pt`; everything else canonicalizes memberwise") — is
  **refuted**, by two formal horns exhausting the choice of `canon ∅`:

  - Horn A (`hereditary_canon_pt_not_fixed`): if the collapse clause
    applies vacuously to `∅` (the empty function graph — forced if
    `pi ∅ B` is to come out `{pt}`), then `canon ∅ = pt`, and since
    `pt = {∅}` contains no Kuratowski pair, memberwise recursion gives
    `canon pt = {canon ∅} = {pt} ≠ pt`: **the proof point itself is not
    canonical**, idempotence fails at `∅`, and no interpretation value
    of a proof can satisfy the global-canonicity invariant.

  - Horn B (`hereditary_canon_pi_empty_not_prop`): if the collapse
    clause is guarded to nonempty graphs, then `canon ∅ = ∅` and
    `image canon (piSet ∅ B) = {∅} = pt ∉ univZero` — but the value of
    an empty-domain `Prop`-product (e.g. `⟦False → False⟧`) is
    **forced** to be `{pt}` by `mem_type` at its sort together with the
    intro law (`pi_empty_forced`, stated generically over any level-free
    `pi'`/`lam'` pair).  The prop-formation law therefore fails.

  The root cause is extensional: `∅` is simultaneously the empty
  function graph (which must collapse) and falsity (which must not),
  and `pt = {∅}` is pinned by `Derive/Pt.lean`.  A secondary defect
  (not formalized): a hereditary memberwise recursion
  through Kuratowski pairs `{{a},{a,b}}` collapses *components* of
  pairs that accidentally read as all-`pt` graphs, corrupting
  `sfst`/`ssnd` on values containing `∅ = ⟦Nat.zero⟧`.

* The proposal's **goal** — level-free `pi`/`lam`/`app` with the
  `Prop` cases as theorems, evaluated per valuation so that no
  syntactic Prop-bit is needed — is **validated** by an amended,
  *domain-relative* collapse that needs no recursion at all:

  - `pcol A g` — collapse a member `g` of `piSet A B` to `pt` iff its
    application values on `A` are all `pt` (for `A = ∅`: vacuously);
  - `piC A B := image (pcol A) (piSet A B)` — level-free product;
  - `lamC A F := if (∀ x ∈ A, F x = pt) then pt else graph F A` —
    level-free abstraction (`lamC A F = pcol A (graph F A)`,
    `pcol_graph`);
  - `app` unchanged (`app pt x = pt` is already the tag).

  `pcol A` is injective on `piSet A B` (a graph is determined by its
  values on its domain, and the all-`pt` graph is the unique collapsing
  one), so `piC` is a *relabeling* of `piSet` — no information the laws
  consume is lost.  Heredity is built into `piC`-membership (members
  are `pcol`-fixed, `pcol_fix_of_mem_piC`); no global invariant exists
  or is needed.

## The re-derived law surface (old `Derive/Pi.lean` law ↦ new law)

| old (level `v`)            | new (level-free)             | change |
|----------------------------|------------------------------|--------|
| `pi_zero` (def)            | `piC_prop_eq`                | becomes a **theorem** |
| `pi_pos` (def)             | `mem_piC` / `mem_piC_cases`  | characterization |
| `lam_zero`/`lam_pos` (def) | `lamC_of_forall`/`lamC_of_not` | collapse test replaces level test |
| `pi_congr`/`lam_congr`     | `piC_congr`/`lamC_congr`     | verbatim (on-domain) |
| `pi/lam_level_indifferent`, `pi/lam_congr_zero_agree` | — | **moot** (no level) |
| `lam_mem`                  | `lamC_mem`                   | verbatim |
| `mem_pi_zero`              | `eq_pt_of_mem_piC_prop`      | premise moves to fibres |
| `app_mem'` (`hB0` at 0)    | `app_mem_piC`                | **fibre-universe premise deleted** |
| `app_lam'` (`hF`+`hB0`)    | `app_lamC`                   | **both premises deleted** |
| `lam_eta`                  | `lamC_eta`                   | verbatim |
| `eq_of_mem_pi_app_eq`      | `eq_of_mem_piC_app_eq`       | verbatim |
| `pi_zero_mem_univZero`     | `piC_prop_mem_univZero`      | theorem, from fibre facts |
| `IsTGUniverse.pi_mem`      | `IsTGUniverse.piC_mem`       | verbatim (`∪ {pt}` detour) |
| `pi_mem_univ`              | `piC_mem_univ` (+`piC_mem_univ_max`) | same statement; collapsed values may land in `univ 0`, cumulativity covers it |
| `lam_ne_pt`                | **false** (that is the point)| consumers must re-audit |
| `lam_dom`                  | `lamC_dom_of_ne`             | premise `v' ≠ 0` becomes `≠ pt` |

The two prior refutation witnesses (`Setlec/Model/RawEnvNoAnnot.lean`)
re-run **positively**: the λ-terms `fun (_ : PUnit) => (1 : Nat)` and
`fun (_ : PUnit) => True.intro` now receive the *same* interpretation
`pt` (`lamC_witnesses_identified`), and `mem_type` holds for both
against their `∀`-types (`pt_mem_piC_punit_nat`,
`pt_mem_piC_punit_true`) — evading `lam_interp_not_value_determined`
exactly because the type-side target moved from `piSet` to its
collapse image.

## Basis ports (evidence)

* PSigma/projection (`proj_fst_value_collapses`): over a prop-first
  pair set the stored first-projection *value* itself collapses to
  `pt`, and the projection law survives because the new beta is
  premise-free; `sfst`/`ssnd` are componentwise-unconditional, so
  pair laws with collapsed components hold verbatim
  (`sfst_spair_collapsed`).
* Iota with a collapsed minor premise (`natrec_iota_collapsed`): under
  a `Prop`-valued motive the minor-premise *space* is `⊆ {pt}`, the
  stored minor's value is forcibly `pt`, and both the firing equation
  and the recursion-theorem membership go through with `s = pt`.
* The full `Nat.rec.{0}`-shaped λ-tower collapses to `pt`
  (`natrec_tower_collapses`) while its `mem_type` against the
  `Π`-tower holds (`natrec_tower_mem`) — the graph-based `lamC_mem`
  absorbs motives with empty fibres via `piC ∅ B = {pt}` silently.
-/

namespace Setlec.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The domain-relative point collapse -/

open Classical in
/-- Collapse a function value to the proof point iff its applications
on the domain `A` are all `pt` (vacuously so over the empty domain). -/
noncomputable def pcol (A g : V) : V :=
  if ∀ x, x ∈ˢ A → app g x = pt then pt else g

open Classical in
/-- Level-free abstraction: the graph, collapsed to `pt` iff all its
values on the domain are `pt`. -/
noncomputable def lamC (A : V) (F : V → V) : V :=
  if ∀ x, x ∈ˢ A → F x = pt then pt else graph F A

/-- Level-free dependent product: the collapse image of the raw
dependent-function set. -/
noncomputable def piC (A : V) (B : V → V) : V := image (pcol A) (piSet A B)

theorem pcol_of_forall {A g : V} (h : ∀ x, x ∈ˢ A → app g x = pt) :
    pcol A g = pt := by
  unfold pcol; exact if_pos h

theorem pcol_of_not {A g : V} (h : ¬ ∀ x, x ∈ˢ A → app g x = pt) :
    pcol A g = g := by
  unfold pcol; exact if_neg h

theorem lamC_of_forall {A : V} {F : V → V} (h : ∀ x, x ∈ˢ A → F x = pt) :
    lamC A F = pt := by
  unfold lamC; exact if_pos h

theorem lamC_of_not {A : V} {F : V → V} (h : ¬ ∀ x, x ∈ˢ A → F x = pt) :
    lamC A F = graph F A := by
  unfold lamC; exact if_neg h

/-- Abstraction is the collapse of the graph. -/
theorem pcol_graph {A : V} {F : V → V} : pcol A (graph F A) = lamC A F := by
  by_cases h : ∀ x, x ∈ˢ A → F x = pt
  · rw [pcol_of_forall (fun x hx => (app_graph hx).trans (h x hx)),
      lamC_of_forall h]
  · rw [pcol_of_not (fun hc => h fun x hx => (app_graph hx).symm.trans (hc x hx)),
      lamC_of_not h]

/-- The fixed-point lemma: the collapse is idempotent. -/
theorem pcol_idem {A g : V} : pcol A (pcol A g) = pcol A g := by
  by_cases h : ∀ x, x ∈ˢ A → app g x = pt
  · rw [pcol_of_forall h, pcol_of_forall (fun x _hx => app_pt x)]
  · rw [pcol_of_not h, pcol_of_not h]

/-- Membership characterization of the level-free product. -/
theorem mem_piC {A f : V} {B : V → V} :
    f ∈ˢ piC A B ↔ ∃ g, g ∈ˢ piSet A B ∧ f = pcol A g := mem_image

/-- Where the global-canonicity invariant lives: members of `piC` are
collapse-fixed — heredity is a closure property of `piC`-membership,
not a global condition on `V`. -/
theorem pcol_fix_of_mem_piC {A f : V} {B : V → V} (hf : f ∈ˢ piC A B) :
    pcol A f = f := by
  obtain ⟨g, hg, rfl⟩ := mem_piC.mp hf
  exact pcol_idem

/-! ## Congruence -/

theorem lamC_congr {A : V} {F F' : V → V} (h : ∀ x, x ∈ˢ A → F x = F' x) :
    lamC A F = lamC A F' := by
  by_cases hp : ∀ x, x ∈ˢ A → F x = pt
  · rw [lamC_of_forall hp,
      lamC_of_forall (fun x hx => (h x hx).symm.trans (hp x hx))]
  · rw [lamC_of_not hp,
      lamC_of_not (fun hc => hp fun x hx => (h x hx).trans (hc x hx)),
      graph_congr h]

theorem piC_congr {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x = B' x) :
    piC A B = piC A B' := by
  unfold piC
  rw [piSet_congr h]

/-! ## Introduction, elimination, beta, eta -/

/-- Introduction: fibre-wise members abstract into the product —
uniformly, with no level and no `Prop` side condition. -/
theorem lamC_mem {A : V} {F B : V → V} (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) :
    lamC A F ∈ˢ piC A B :=
  mem_piC.mpr ⟨graph F A, graph_mem_piSet hF, pcol_graph.symm⟩

/-- Beta — with **no** fibre-membership and **no** fibre-universe
premise (strictly stronger than the old `app_lam'`): in the collapsed
case the collapse condition itself supplies `F a = pt`. -/
theorem app_lamC {A a : V} {F : V → V} (ha : a ∈ˢ A) :
    app (lamC A F) a = F a := by
  by_cases h : ∀ x, x ∈ˢ A → F x = pt
  · rw [lamC_of_forall h, app_pt, h a ha]
  · rw [lamC_of_not h, app_graph ha]

/-- Case split on a product member: the collapsed point (with every
fibre over the domain containing `pt`), or an uncollapsed raw graph. -/
theorem mem_piC_cases {A f : V} {B : V → V} (hf : f ∈ˢ piC A B) :
    (f = pt ∧ ∀ x, x ∈ˢ A → (pt : V) ∈ˢ B x) ∨
    (f ∈ˢ piSet A B ∧ ¬ ∀ x, x ∈ˢ A → app f x = pt) := by
  obtain ⟨g, hg, rfl⟩ := mem_piC.mp hf
  by_cases h : ∀ x, x ∈ˢ A → app g x = pt
  · exact Or.inl ⟨pcol_of_forall h,
      fun x hx => h x hx ▸ app_mem_of_mem_piSet hg hx⟩
  · rw [pcol_of_not h]
    exact Or.inr ⟨hg, h⟩

/-- Elimination — with **no** fibre-universe premise (the old
`app_mem'` needed the fibres to be truth values at `v = 0`; here the
collapse condition plus `app_mem_of_mem_piSet` supply
`pt ∈ˢ B a` directly). -/
theorem app_mem_piC {A f a : V} {B : V → V} (hf : f ∈ˢ piC A B)
    (ha : a ∈ˢ A) : app f a ∈ˢ B a := by
  rcases mem_piC_cases hf with ⟨rfl, hall⟩ | ⟨hmem, -⟩
  · rw [app_pt]; exact hall a ha
  · exact app_mem_of_mem_piSet hmem ha

/-- The point inhabits the product iff it inhabits every fibre over
the domain (vacuously over the empty domain). -/
theorem pt_mem_piC_iff {A : V} {B : V → V} :
    (pt : V) ∈ˢ piC A B ↔ ∀ x, x ∈ˢ A → (pt : V) ∈ˢ B x := by
  constructor
  · intro h
    rcases mem_piC_cases h with ⟨-, hall⟩ | ⟨hmem, -⟩
    · exact hall
    · exact absurd rfl (ne_pt_of_mem_piSet hmem)
  · intro h
    exact mem_piC.mpr ⟨graph (fun _ => pt) A, graph_mem_piSet h,
      (pcol_of_forall (fun x hx => app_graph hx)).symm⟩

/-- Eta: a member of the product is the abstraction of its
applications.  In the collapsed case `app pt · = pt` re-fires the
collapse test; in the graph case the test provably fails. -/
theorem lamC_eta {A f : V} {B : V → V} (hf : f ∈ˢ piC A B) :
    lamC A (fun x => app f x) = f := by
  rcases mem_piC_cases hf with ⟨rfl, -⟩ | ⟨hmem, hne⟩
  · exact lamC_of_forall fun x _hx => app_pt x
  · rw [lamC_of_not hne]
    exact eq_graph_app_of_mem_piSet hmem

/-- Function extensionality for product members: on-domain agreement is
total agreement (off-domain the collapsed point and graphs differ —
`pt` vs `∅` junk — but eta re-canonicalizes both sides). -/
theorem eq_of_mem_piC_app_eq {A f g : V} {B B' : V → V}
    (hf : f ∈ˢ piC A B) (hg : g ∈ˢ piC A B')
    (h : ∀ x, x ∈ˢ A → app f x = app g x) : f = g := by
  rw [← lamC_eta hf, ← lamC_eta hg]
  exact lamC_congr h

/-! ## The `Prop` cases as theorems -/

/-- **The old `pi_zero` definition is now a theorem**: over truth-value
fibres the collapse image *computes* the truth value of fibre-wise
inhabitedness. -/
theorem piC_prop_eq {A : V} {B : V → V}
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) :
    piC A B = truthVal (∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) := by
  by_cases hin : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x
  · rw [truthVal_eq_unitSet hin]
    apply ext fun z => ?_
    rw [mem_unitSet_iff]
    constructor
    · intro hz
      obtain ⟨g, hg, rfl⟩ := mem_piC.mp hz
      exact pcol_of_forall fun x hx =>
        eq_pt_of_mem_univZero (hB x hx) (app_mem_of_mem_piSet hg hx)
    · rintro rfl
      refine pt_mem_piC_iff.mpr fun x hx => ?_
      obtain ⟨y, hy⟩ := hin x hx
      exact eq_pt_of_mem_univZero (hB x hx) hy ▸ hy
  · rw [truthVal_eq_empty hin]
    refine eq_empty fun z hz => ?_
    obtain ⟨g, hg, -⟩ := mem_piC.mp hz
    exact hin fun x hx => ⟨app g x, app_mem_of_mem_piSet hg hx⟩

/-- Prop-formation (old `pi_zero_mem_univZero`), now conditional on the
fibres rather than on a level. -/
theorem piC_prop_mem_univZero {A : V} {B : V → V}
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) :
    piC A B ∈ˢ (univZero : V) := by
  rw [piC_prop_eq hB]
  exact truthVal_mem_univZero _

/-- Proof irrelevance at products (old `mem_pi_zero`): members of a
`Prop`-fibred product are the point. -/
theorem eq_pt_of_mem_piC_prop {A f : V} {B : V → V}
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) (hf : f ∈ˢ piC A B) :
    f = pt :=
  eq_pt_of_mem_univZero (piC_prop_mem_univZero hB) hf

/-- The empty-domain product is truth — for *every* fibre family, `Prop`-
or `Type`-valued alike (this is what the hereditary canon cannot
produce; see Horn B below). -/
theorem piC_empty (B : V → V) : piC (empty : V) B = unitSet := by
  rw [piC_prop_eq (fun x hx => absurd hx (not_mem_empty x)),
    truthVal_eq_unitSet (fun x hx => absurd hx (not_mem_empty x))]

/-! ## Universe closure -/

/-- Grothendieck-universe closure: the collapse image sits inside
`piSet ∪ {pt}`, both members of the universe. -/
theorem _root_.Setlec.IsTGUniverse.piC_mem {U A : V} {B : V → V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ U) : piC A B ∈ˢ U := by
  refine hU.mem_of_subset_mem
    (hU.binUnion_mem hA (hU.piSet_mem hA hB) (hU.unitSet_mem hA))
    fun z hz => ?_
  obtain ⟨g, hg, rfl⟩ := mem_piC.mp hz
  by_cases h : ∀ x, x ∈ˢ A → app g x = pt
  · rw [pcol_of_forall h]
    exact mem_binUnion.mpr (Or.inr pt_mem_unitSet)
  · rw [pcol_of_not h]
    exact mem_binUnion.mpr (Or.inl hg)

/-- Formation along the tower — the same `imax`-shaped statement as the
old `pi_mem_univ`, but with the `v = 0` branch a consequence of the
fibre facts rather than of the operator's level argument. -/
theorem piC_mem_univ {u v : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ (univ u : V)) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ v : V)) :
    piC A B ∈ˢ (univ (if v = 0 then 0 else Nat.max u v) : V) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [if_pos rfl, univ_zero]
    exact piC_prop_mem_univZero fun x hx => univ_zero (V := V) ▸ hB x hx
  · have hv' : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
    rw [if_neg hv']
    have hw : (Nat.max u v : Nat) ≠ 0 :=
      fun h => hv' (Nat.le_zero.mp (h ▸ Nat.le_max_right u v))
    exact (univ_isTGUniverse hw).piC_mem
      (univ_mono (Nat.le_max_left u v) A hA)
      (fun x hx => univ_mono (Nat.le_max_right u v) _ (hB x hx))

/-- Collapsed values may land *smaller* (a `Type`-level product can be
a truth value), and nothing needs exact placement: cumulativity
recovers the unconditional `max`-level bound. -/
theorem piC_mem_univ_max {u v : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ (univ u : V)) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ v : V)) :
    piC A B ∈ˢ (univ (Nat.max u v) : V) := by
  have h := piC_mem_univ hA hB
  split at h
  · exact univ_mono (Nat.zero_le _) _ h
  · exact h

/-! ## Domain recovery (the weakened `lam_dom`) -/

/-- Graphs still determine their domains — but only *uncollapsed* ones:
the premise `v' ≠ 0 ∧ v ≠ 0` of the old `lam_dom` becomes `≠ pt`.
Consumers that derived non-`pt`-ness from a nonzero level
(`lam_ne_pt`) must re-derive it — and for the kernel's
annotation-guarded beta they provably cannot (the level no longer
bounds the value away from `pt`: an empty-domain abstraction collapses
at every level); see DESIGN.md, "Annotation erasure", for the
countermodel and the de-gating consequence. -/
theorem lamC_dom_of_ne {A A' : V} {F : V → V} {B : V → V}
    (hne : lamC A F ≠ pt) (hf : lamC A F ∈ˢ piC A' B) :
    ∀ x, x ∈ˢ A' → x ∈ˢ A := by
  have hnot : ¬ ∀ x, x ∈ˢ A → F x = pt := fun h => hne (lamC_of_forall h)
  rw [lamC_of_not hnot] at hf
  rcases mem_piC_cases hf with ⟨heq, -⟩ | ⟨hmem, -⟩
  · exact absurd heq graph_ne_pt
  · exact graph_dom_of_mem_piSet hmem

/-! ## The prior refutation witnesses, re-run positively

`Setlec/Model/RawEnvNoAnnot.lean` proved that under the *old* operators
`fun (_ : PUnit) => (1 : Nat)` and `fun (_ : PUnit) => True.intro`
present identical semantic data yet require distinct interpretations.
Under the collapse they receive the **same** value `pt`, and `mem_type`
holds for both against their `∀`-types: the structural refutation is
evaded because the type-side target moved. -/

/-- The von Neumann `1` is the proof point (local copy of the
`Model`-layer lemma; the `SetTheory` layer must not import it). -/
theorem vsucc_empty_eq_pt' : vsucc (empty : V) = pt := by
  apply ext fun z => ?_
  rw [mem_vsucc, mem_pt]
  constructor
  · rintro (hz | rfl)
    · exact absurd hz (not_mem_empty z)
    · rfl
  · rintro rfl
    exact Or.inr rfl

/-- The two witness λ-terms of `lam_interp_not_value_determined` get
**equal** interpretations, namely the point. -/
theorem lamC_witnesses_identified :
    lamC (unitSet : V) (fun _ => vsucc empty) =
      lamC (unitSet : V) (fun _ => pt) ∧
    lamC (unitSet : V) (fun _ => pt) = pt :=
  ⟨lamC_congr fun _ _ => vsucc_empty_eq_pt',
   lamC_of_forall fun _ _ => rfl⟩

/-- … and `mem_type` holds for the `Type`-level witness: the point is a
member of the collapsed `⟦PUnit → Nat⟧` (the all-`pt` graph is total
since `1 = pt ∈ ω`). -/
theorem pt_mem_piC_punit_nat :
    (pt : V) ∈ˢ piC unitSet (fun _ => omega) :=
  pt_mem_piC_iff.mpr fun _ _ =>
    vsucc_empty_eq_pt' (V := V) ▸ vsucc_mem_omega empty_mem_omega

/-- … and for the `Prop`-level witness against `⟦PUnit → True⟧`. -/
theorem pt_mem_piC_punit_true :
    (pt : V) ∈ˢ piC unitSet (fun _ => unitSet) :=
  pt_mem_piC_iff.mpr fun _ _ => pt_mem_unitSet

/-! ## The de-gating finding, formal core

The kernel's annotation-guarded reduction paths are unsound to model
under the collapse (DESIGN.md, "Annotation erasure": the flip must
follow kernel de-gating).  The checkable heart: an empty-domain
abstraction collapses to the proof point at **every** codomain sort —
there is no `lam_ne_pt` analogue — so off-domain "beta" produces `pt`
regardless of the body, e.g. against the body `fun _ => univZero`.
The claim-level countermodel wrapping this into an AnnotOk-satisfiable
guarded-beta redex (`(fun (x : ∀ p : Prop, p) => Prop) Prop`, in the
empty environment) is in the DESIGN section, together with
`piC_univZero_id_empty` below giving its `⟦∀ p : Prop, p⟧ = ∅`
domain. -/

/-- Every empty-domain abstraction is the point — at every codomain
sort, since there is no sort to consult. -/
theorem lamC_empty (F : V → V) : lamC (empty : V) F = pt :=
  lamC_of_forall fun x hx => absurd hx (not_mem_empty x)

/-- Off-domain "beta" on a collapsed abstraction yields the point,
regardless of the body. -/
theorem app_lamC_empty (F : V → V) (a : V) :
    app (lamC (empty : V) F) a = pt := by
  rw [lamC_empty, app_pt]

theorem univZero_ne_pt : (univZero : V) ≠ pt := fun h =>
  not_mem_empty (pt : V)
    (mem_pt.mp (h ▸ mem_univZero.mpr (Subset.refl _)) ▸ pt_mem_unitSet)

/-- The interpretation of `∀ p : Prop, p` under the collapse: the
`p := ⟦False⟧ = ∅` fibre admits no choice, so the raw function set —
and hence its collapse image — is empty. -/
theorem piC_univZero_id_empty : piC (univZero : V) (fun x => x) = empty := by
  have hraw : piSet (univZero : V) (fun x => x) = empty := by
    refine eq_empty fun f hf => ?_
    obtain ⟨y, hy, -⟩ := (mem_piSet.mp hf).2 empty
      (mem_univZero.mpr (empty_subset _))
    have := (mem_piSet.mp hf).1 _ hy
    obtain ⟨x, -, y', hy', hp⟩ := mem_sigmaPairs.mp this
    obtain ⟨rfl, rfl⟩ := kpair_inj hp
    exact not_mem_empty _ hy'
  unfold piC
  rw [hraw]
  exact eq_empty fun z hz => by
    obtain ⟨w, hw, -⟩ := mem_image.mp hz
    exact not_mem_empty w hw

/-- The beta-failure witness of the guarded-beta countermodel:
applying the collapsed `⟦fun (x : ∀ p : Prop, p) => Prop⟧` to
anything gives `pt`, never `⟦Prop⟧`. -/
theorem guarded_beta_countermodel_core (a : V) :
    app (lamC (piC (univZero : V) (fun x => x)) (fun _ => univZero)) a ≠
      univZero := by
  rw [piC_univZero_id_empty, app_lamC_empty]
  exact fun h => univZero_ne_pt h.symm

/-! ## The hereditary canon, refuted

The literal proposal's `canon` clauses, as hypotheses on an arbitrary
function (so the refutation covers every realization of the
∈-recursion, however the recursion is justified). -/

/-- The proposal's collapse condition on a set `x`: every member is a
Kuratowski pair whose second component canonicalizes to the point. -/
def HereditaryCollapse (canon : V → V) (x : V) : Prop :=
  ∀ p, p ∈ˢ x → ∃ a b, p = kpair a b ∧ canon b = pt

/-- The literal spec: collapsible sets collapse (vacuously including
`∅`, as required for `canon (piSet ∅ B) = {pt}`); everything else
canonicalizes memberwise. -/
structure HereditaryCanonSpec (canon : V → V) : Prop where
  collapse : ∀ x : V, HereditaryCollapse canon x → canon x = pt
  memberwise : ∀ x : V, ¬ HereditaryCollapse canon x → canon x = image canon x

/-- The nonempty-guarded variant (collapse only nonempty graphs, so
that falsity `∅` stays `∅`). -/
structure HereditaryCanonSpecNE (canon : V → V) : Prop where
  collapse : ∀ x : V, (∃ w, w ∈ˢ x) → HereditaryCollapse canon x →
    canon x = pt
  memberwise : ∀ x : V, ¬ ((∃ w, w ∈ˢ x) ∧ HereditaryCollapse canon x) →
    canon x = image canon x

/-- **Horn A**: under the literal spec the proof point is not a `canon`
fixed point — `canon ∅ = pt` (vacuous collapse), `pt = {∅}` contains no
pair, so memberwise recursion yields `canon pt = {pt} ≠ pt`.  Every
proof's interpretation violates the global-canonicity invariant. -/
theorem hereditary_canon_pt_not_fixed {canon : V → V}
    (h : HereditaryCanonSpec canon) : canon pt ≠ pt := by
  have h0 : canon empty = pt :=
    h.collapse empty fun p hp => absurd hp (not_mem_empty p)
  have hpt : canon pt = unitSet := by
    have hnc : ¬ HereditaryCollapse canon pt := fun hc => by
      obtain ⟨a, b, hab, -⟩ := hc empty (mem_pt.mpr rfl)
      exact kpair_ne_empty hab.symm
    rw [h.memberwise pt hnc]
    apply ext fun z => ?_
    rw [mem_image, mem_unitSet_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_pt.mp hw, h0]
    · rintro rfl
      exact ⟨empty, mem_pt.mpr rfl, h0.symm⟩
  intro heq
  rw [hpt] at heq
  exact pt_ne_empty (mem_pt.mp (heq ▸ pt_mem_unitSet))

/-- **Horn A, idempotence form**: the proposal's fixed-point/idempotence
lemma is unprovable — it is false at `∅`. -/
theorem hereditary_canon_not_idempotent {canon : V → V}
    (h : HereditaryCanonSpec canon) : canon (canon empty) ≠ canon empty := by
  have h0 : canon empty = pt :=
    h.collapse empty fun p hp => absurd hp (not_mem_empty p)
  rw [h0]
  exact hereditary_canon_pt_not_fixed h

/-- Over the empty domain the raw dependent-function set is the
singleton of the empty graph. -/
theorem mem_piSet_empty {B : V → V} {f : V} :
    f ∈ˢ piSet (empty : V) B ↔ f = empty := by
  rw [mem_piSet]
  constructor
  · rintro ⟨hsub, -⟩
    refine eq_empty fun z hz => ?_
    obtain ⟨x, hx, -⟩ := mem_sigmaPairs.mp (hsub z hz)
    exact not_mem_empty x hx
  · rintro rfl
    exact ⟨empty_subset _, fun x hx => absurd hx (not_mem_empty x)⟩

/-- **Horn B**: under the nonempty-guarded spec, `canon ∅ = ∅` and the
proposed product `image canon (piSet ∅ B)` is `{∅} = pt`, which is
**not** a truth value — the prop-formation law
(`fibres ∈ univ 0 → product ∈ univ 0`, vacuously applicable at
`A = ∅`) fails, e.g. at `⟦False → False⟧`. -/
theorem hereditary_canon_pi_empty_not_prop {canon : V → V}
    (h : HereditaryCanonSpecNE canon) (B : V → V) :
    ¬ image canon (piSet (empty : V) B) ∈ˢ (univZero : V) := by
  have h0 : canon empty = empty := by
    rw [h.memberwise empty (fun hc => not_mem_empty _ hc.1.choose_spec)]
    exact eq_empty fun z hz => by
      obtain ⟨w, hw, -⟩ := mem_image.mp hz
      exact not_mem_empty w hw
  intro hmem
  have hin : (empty : V) ∈ˢ image canon (piSet (empty : V) B) :=
    mem_image.mpr ⟨empty, mem_piSet_empty.mpr rfl, h0.symm⟩
  exact pt_ne_empty (eq_pt_of_mem_univZero hmem hin).symm

/-- Why Horn B is not an artifact of chosen definitions: **any**
level-free pair `pi'`/`lam'` satisfying just the intro law and
prop-formation is *forced* to `pi' ∅ B = {pt}` — which `piC` delivers
(`piC_empty`) and the hereditary canon cannot. -/
theorem pi_empty_forced (pi' lam' : V → (V → V) → V)
    (hmem : ∀ (A : V) (B F : V → V), (∀ x, x ∈ˢ A → F x ∈ˢ B x) →
      lam' A F ∈ˢ pi' A B)
    (hprop : ∀ (A : V) (B : V → V), (∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) →
      pi' A B ∈ˢ (univZero : V))
    (B : V → V) : pi' empty B = unitSet := by
  have hz : pi' empty B ∈ˢ (univZero : V) :=
    hprop _ _ fun x hx => absurd hx (not_mem_empty x)
  have hne : lam' empty id ∈ˢ pi' empty B :=
    hmem _ B id fun x hx => absurd hx (not_mem_empty x)
  have hpt : (pt : V) ∈ˢ pi' empty B := eq_pt_of_mem_univZero hz hne ▸ hne
  apply ext fun z => ?_
  rw [mem_unitSet_iff]
  exact ⟨fun hzm => eq_pt_of_mem_univZero hz hzm,
    fun hzm => hzm.symm ▸ hpt⟩

/-! ## Basis port 1: PSigma pairing/projection under the collapse -/

/-- Pair laws with collapsed components hold verbatim: `sfst`/`ssnd`
are unconditional in the components (a collapsed abstraction is just a
value). -/
theorem sfst_spair_collapsed (A c : V) (F : V → V) :
    sfst (spair (lamC A F) c) = lamC A F := sfst_spair _ _

theorem ssnd_spair_collapsed (A c : V) (F : V → V) :
    ssnd (spair c (lamC A F)) = lamC A F := ssnd_spair _ _

/-- The projection **function value** over a prop-first pair set
collapses to the point — and the projection law survives anyway,
because the collapsed beta is premise-free.  (This is the situation the
old encoding could not express: a `Type`-level projection function
whose value is `pt`.) -/
theorem proj_fst_value_collapses {A : V} {B : V → V}
    (hA : A ∈ˢ (univZero : V)) :
    lamC (sigmaSet 1 A B) sfst = pt ∧
    ∀ p, p ∈ˢ sigmaSet 1 A B →
      app (lamC (sigmaSet 1 A B) sfst) p = sfst p := by
  have hall : ∀ p, p ∈ˢ sigmaSet 1 A B → sfst p = pt := by
    intro p hp
    obtain ⟨a, b, ha, -, -, hne⟩ := mem_sigma_elim hp
    rw [hne (by decide), sfst_spair]
    exact eq_pt_of_mem_univZero hA ha
  exact ⟨lamC_of_forall hall, fun p hp => app_lamC hp⟩

/-- The uncollapsed side of the same law, for contrast: over any pair
set the projection value fires by beta alone. -/
theorem proj_fst_law {w : Nat} {A p : V} {B : V → V}
    (hp : p ∈ˢ sigmaSet w A B) :
    app (lamC (sigmaSet w A B) sfst) p = sfst p :=
  app_lamC hp

/-! ## Basis port 2: iota with a collapsed minor premise -/

/-- Iota under a `Prop`-valued motive: the minor-premise space is
`⊆ {pt}`, so the stored minor's value is forcibly the point; the
firing equation (`natrec_vsucc` is `s`-generic) and the
recursion-theorem membership both go through with `s = pt`, the
membership because the collapsed `s`'s type membership *itself* says
`pt` inhabits every successor fibre over an inhabited fibre. -/
theorem natrec_iota_collapsed {M s : V}
    (hM : ∀ n, n ∈ˢ (omega : V) → app M n ∈ˢ (univZero : V))
    (hs : s ∈ˢ piC (omega : V)
      (fun n => piC (app M n) (fun _ => app M (vsucc n)))) :
    s = pt ∧
    (∀ z n, n ∈ˢ (omega : V) →
      natrec z s (vsucc n) = app (app s n) (natrec z s n)) ∧
    ∀ z n, z ∈ˢ app M empty → n ∈ˢ (omega : V) →
      natrec z s n ∈ˢ app M n := by
  have hfib : ∀ n, n ∈ˢ (omega : V) →
      piC (app M n) (fun _ => app M (vsucc n)) ∈ˢ (univZero : V) :=
    fun n hn => piC_prop_mem_univZero fun _x _hx =>
      hM (vsucc n) (vsucc_mem_omega hn)
  have hspt : s = pt := eq_pt_of_mem_piC_prop hfib hs
  subst hspt
  refine ⟨rfl, fun z n hn => natrec_vsucc z pt hn,
    fun z n hz hn => ?_⟩
  refine natrec_mem_vsucc hz (fun k hk ih hih => ?_) hn
  rw [app_pt, app_pt]
  exact pt_mem_piC_iff.mp (pt_mem_piC_iff.mp hs k hk) ih hih

/-! ## Basis port 2b: the `Nat.rec.{0}`-shaped tower, end to end

At a `Prop` motive-space the whole four-binder recursor value collapses
to the point, while `mem_type` against the corresponding `Π`-tower
holds — including for motives with empty fibres, which the empty-domain
collapse (`piC ∅ B = {pt}`) absorbs without any case analysis. -/

/-- `mem_type` for the recursor tower — provable *uniformly* by nested
`lamC_mem` + the recursion theorem, whether or not anything collapses.
(Motive space `⟦Nat → Prop⟧`; minor-premise space
`⟦∀ n, motive n → motive (n+1)⟧`.) -/
theorem natrec_tower_mem :
    lamC (piC (omega : V) (fun _ => univZero)) (fun M =>
      lamC (app M empty) (fun z =>
        lamC (piC omega (fun n => piC (app M n) (fun _ => app M (vsucc n))))
          (fun s => lamC omega (fun n => natrec z s n)))) ∈ˢ
    piC (piC (omega : V) (fun _ => univZero)) (fun M =>
      piC (app M empty) (fun _z =>
        piC (piC omega (fun n => piC (app M n) (fun _ => app M (vsucc n))))
          (fun _s => piC omega (fun n => app M n)))) := by
  refine lamC_mem fun M _hM => ?_
  refine lamC_mem fun z hz => ?_
  refine lamC_mem fun s hs => ?_
  refine lamC_mem fun n hn => ?_
  refine natrec_mem_vsucc hz (fun k hk ih hih => ?_) hn
  have h1 : app s k ∈ˢ piC (app M k) (fun _ => app M (vsucc k)) :=
    app_mem_piC hs hk
  exact app_mem_piC h1 hih

/-- The recursor value at the `Prop` instance **is the point**: every
layer's body is forced to `pt` from the motive fibres being truth
values, cascading outward. -/
theorem natrec_tower_collapses :
    lamC (piC (omega : V) (fun _ => univZero)) (fun M =>
      lamC (app M empty) (fun z =>
        lamC (piC omega (fun n => piC (app M n) (fun _ => app M (vsucc n))))
          (fun s => lamC omega (fun n => natrec z s n)))) = pt := by
  refine lamC_of_forall fun M hM => ?_
  refine lamC_of_forall fun z hz => ?_
  refine lamC_of_forall fun s hs => ?_
  refine lamC_of_forall fun n hn => ?_
  have hval : natrec z s n ∈ˢ app M n := by
    refine natrec_mem_vsucc hz (fun k hk ih hih => ?_) hn
    have h1 : app s k ∈ˢ piC (app M k) (fun _ => app M (vsucc k)) :=
      app_mem_piC hs hk
    exact app_mem_piC h1 hih
  have hMn : app M n ∈ˢ (univZero : V) := app_mem_piC hM hn
  exact eq_pt_of_mem_univZero hMn hval

end Setlec.SetTheory
