import Lech.SetTheory.Derive.Graphs

/-!
# The dependent product and abstraction, level-free (task #100)

The domain-relative point collapse of DESIGN.md, "Annotation erasure":

* `pcol A g` collapses a member of `piSet A B` to the proof point iff
  its application values on `A` are all `pt` (vacuously over `A = ∅`);
* `piC A B := image (pcol A) (piSet A B)` — the level-free product;
* `lamC A F` — the graph of `F` over `A`, collapsed to `pt` iff all
  its values on the domain are `pt`;
* `app` unchanged (`app pt x = pt` is already the tag).

`pcol A` is injective on `piSet A B` (a graph is determined by its
values on its domain, and the all-`pt` graph is the unique collapsing
one), so `piC` is a *relabeling* of `piSet`.  Heredity is built into
`piC`-membership (members are `pcol`-fixed, `pcol_fix_of_mem_piC`).

The old leveled operators of Mario Carneiro's §6.2 conventions
(`pi v`/`lam v` with the `v = 0` truth-value truncation) survive as
**vestigial-level abbreviations** over `piC`/`lamC` — definitional
level-erasure, so the explicit-level call sites elaborate unchanged
and goals display `piC`/`lamC`.  The abbrevs die with the kernel-side
erasure (stage 6).  The old law surface splits:

* laws that survive keep their names as corollaries of the level-free
  laws (`pi_congr`, `lam_congr`, `lam_mem`, `app_mem'`, `app_lam'`,
  `lam_eta`, `eq_of_mem_pi_app_eq`, `IsTGUniverse.pi_mem`) — vestigial
  premises are kept so call sites need not change;
* the level-dispatch laws are **false** under the collapse and are
  deleted (`pi_zero`, `pi_pos`, `lam_zero`, `lam_pos`, `mem_pi_zero`,
  `lam_ne_pt`, `lam_dom`, `pi_zero_mem_univZero`); their replacements
  are the collapse laws below (`piC_prop_eq`, `mem_piC_cases`,
  `lamC_of_forall`/`lamC_of_not`, `eq_pt_of_mem_piC_prop`,
  `lamC_dom_of_ne`, `piC_prop_mem_univZero`);
* the zero-ness bookkeeping (`pi/lam_level_indifferent`,
  `pi/lam_congr_zero_agree`) is moot — levels are definitionally
  erased (`pi_level_indifferent` survives as `rfl` for reference).
-/

namespace Lech.SetTheory

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

/-- The dependent product, with a vestigial level (definitional
level-erasure; see module docs).  Dies in the kernel-side erasure. -/
noncomputable abbrev pi (_v : Nat) (A : V) (B : V → V) : V := piC A B

/-- Abstraction, with a vestigial level (see `pi`). -/
noncomputable abbrev lam (_v : Nat) (A : V) (F : V → V) : V := lamC A F

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

/-- An abstraction is the point exactly when all its values on the
domain are (`graph_ne_pt` closes the other branch). -/
theorem lamC_eq_pt_iff {A : V} {F : V → V} :
    lamC A F = pt ↔ ∀ x, x ∈ˢ A → F x = pt := by
  constructor
  · intro h
    by_cases hc : ∀ x, x ∈ˢ A → F x = pt
    · exact hc
    · rw [lamC_of_not hc] at h
      exact absurd h graph_ne_pt
  · exact lamC_of_forall

/-- Non-collapse from a single non-`pt` value on the domain. -/
theorem lamC_ne_pt_of_witness {A : V} {F : V → V} {x : V}
    (hx : x ∈ˢ A) (hne : F x ≠ pt) : lamC A F ≠ pt :=
  fun h => hne (lamC_eq_pt_iff.mp h x hx)

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

/-- Compat (vestigial level): `piC_congr`. -/
theorem pi_congr {v : Nat} {A : V} {B B' : V → V}
    (h : ∀ x, x ∈ˢ A → B x = B' x) : pi v A B = pi v A B' :=
  piC_congr h

/-- Compat (vestigial level): `lamC_congr`. -/
theorem lam_congr {v : Nat} {A : V} {F F' : V → V}
    (h : ∀ x, x ∈ˢ A → F x = F' x) : lam v A F = lam v A F' :=
  lamC_congr h

/-- The level is definitionally erased (kept for reference; the old
leveled operators read their level through the `v = 0` test, and the
kernel's binder-defeq comparison tracked its zero-ness — both gone). -/
theorem pi_level_indifferent {u v : Nat} {A : V} {B : V → V} :
    pi u A B = pi v A B := rfl

/-! ## Introduction, elimination, beta, eta -/

/-- Introduction: fibre-wise members abstract into the product —
uniformly, with no level and no `Prop` side condition. -/
theorem lamC_mem {A : V} {F B : V → V} (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) :
    lamC A F ∈ˢ piC A B :=
  mem_piC.mpr ⟨graph F A, graph_mem_piSet hF, pcol_graph.symm⟩

/-- Compat (vestigial level): `lamC_mem`. -/
theorem lam_mem {v : Nat} {A : V} {F B : V → V}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) : lam v A F ∈ˢ pi v A B :=
  lamC_mem hF

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

/-- Compat (vestigial level and premise): `app_mem_piC`. -/
theorem app_mem' {v : Nat} {A f a : V} {B : V → V}
    (hf : f ∈ˢ pi v A B) (ha : a ∈ˢ A)
    (_hB0 : v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) :
    app f a ∈ˢ B a :=
  app_mem_piC hf ha

/-- Compat (vestigial level and premises): `app_lamC`. -/
theorem app_lam' {v : Nat} {A a : V} {F B : V → V}
    (ha : a ∈ˢ A) (_hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x)
    (_hB0 : v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) :
    app (lam v A F) a = F a :=
  app_lamC ha

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

/-- Compat (vestigial level): `lamC_eta`. -/
theorem lam_eta {v : Nat} {A f : V} {B : V → V} (hf : f ∈ˢ pi v A B) :
    lam v A (fun x => app f x) = f :=
  lamC_eta hf

/-- A non-`pt` product member is a genuine graph, and a graph's domain
is recoverable from the set itself (its pairs' first components) — so
membership in two products pins one domain (task #148 T5: the
slot-sort recovery of the modeled-iota derivation, replacing the
tt-only #146 check). -/
theorem piC_dom_unique {A A' f : V} {B B' : V → V}
    (h1 : f ∈ˢ piC A B) (h2 : f ∈ˢ piC A' B') (hne : f ≠ pt) :
    A = A' := by
  obtain ⟨g, hg, rfl⟩ := mem_piC.mp h1
  have hgne : pcol A g = g := by
    by_cases hc : ∀ x, x ∈ˢ A → app g x = pt
    · exact absurd (pcol_of_forall hc) hne
    · exact pcol_of_not hc
  rw [hgne] at h2 hne
  have hgA : g ∈ˢ piSet A B := hg
  obtain ⟨g', hg', hgg'⟩ := mem_piC.mp h2
  have hgA' : g ∈ˢ piSet A' B' := by
    by_cases hc : ∀ x, x ∈ˢ A' → app g' x = pt
    · rw [pcol_of_forall hc] at hgg'
      exact absurd hgg' hne
    · rw [pcol_of_not hc] at hgg'
      rw [hgg']
      exact hg'
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hgA
  obtain ⟨hsub', htot'⟩ := mem_piSet.mp hgA'
  refine ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy, -⟩ := htot x hx
    obtain ⟨x2, hx2, y2, -, hp⟩ := mem_sigmaPairs.mp (hsub' _ hy)
    obtain ⟨rfl, rfl⟩ := kpair_inj hp
    exact hx2
  · obtain ⟨y, hy, -⟩ := htot' x hx
    obtain ⟨x2, hx2, y2, -, hp⟩ := mem_sigmaPairs.mp (hsub _ hy)
    obtain ⟨rfl, rfl⟩ := kpair_inj hp
    exact hx2

/-- Function extensionality for product members: on-domain agreement is
total agreement (off-domain the collapsed point and graphs differ —
`pt` vs `∅` junk — but eta re-canonicalizes both sides). -/
theorem eq_of_mem_piC_app_eq {A f g : V} {B B' : V → V}
    (hf : f ∈ˢ piC A B) (hg : g ∈ˢ piC A B')
    (h : ∀ x, x ∈ˢ A → app f x = app g x) : f = g := by
  rw [← lamC_eta hf, ← lamC_eta hg]
  exact lamC_congr h

/-- Compat (vestigial level): `eq_of_mem_piC_app_eq`. -/
theorem eq_of_mem_pi_app_eq {v : Nat} {A f g : V} {B B' : V → V}
    (hf : f ∈ˢ pi v A B) (hg : g ∈ˢ pi v A B')
    (h : ∀ x, x ∈ˢ A → app f x = app g x) : f = g :=
  eq_of_mem_piC_app_eq hf hg h

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

/-- The empty-domain product is truth — for *every* fibre family,
`Prop`- or `Type`-valued alike. -/
theorem piC_empty (B : V → V) : piC (empty : V) B = unitSet := by
  rw [piC_prop_eq (fun x hx => absurd hx (not_mem_empty x)),
    truthVal_eq_unitSet (fun x hx => absurd hx (not_mem_empty x))]

/-- Every empty-domain abstraction is the point — at every codomain
sort, since there is no sort to consult. -/
theorem lamC_empty (F : V → V) : lamC (empty : V) F = pt :=
  lamC_of_forall fun x hx => absurd hx (not_mem_empty x)

/-- Off-domain "beta" on a collapsed abstraction yields the point,
regardless of the body. -/
theorem app_lamC_empty (F : V → V) (a : V) :
    app (lamC (empty : V) F) a = pt := by
  rw [lamC_empty, app_pt]

/-! ## Universe closure -/

/-- Grothendieck-universe closure: the collapse image sits inside
`piSet ∪ {pt}`, both members of the universe. -/
theorem _root_.Lech.IsTGUniverse.piC_mem {U A : V} {B : V → V}
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

/-- Compat (vestigial level and premise): `IsTGUniverse.piC_mem`. -/
theorem _root_.Lech.IsTGUniverse.pi_mem {U A : V} {B : V → V} {v : Nat}
    (hU : IsTGUniverse (Mem (V := V)) U) (_hv : v ≠ 0) (hA : A ∈ˢ U)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ U) : pi v A B ∈ˢ U :=
  hU.piC_mem hA hB

/-! ## Domain recovery (the weakened `lam_dom`) -/

/-- Graphs still determine their domains — but only *uncollapsed* ones:
the premise `v' ≠ 0 ∧ v ≠ 0` of the old `lam_dom` becomes `≠ pt`.
Consumers that derived non-`pt`-ness from a nonzero level
(`lam_ne_pt`) must dispatch through `mem_piC_cases` instead. -/
theorem lamC_dom_of_ne {A A' : V} {F : V → V} {B : V → V}
    (hne : lamC A F ≠ pt) (hf : lamC A F ∈ˢ piC A' B) :
    ∀ x, x ∈ˢ A' → x ∈ˢ A := by
  have hnot : ¬ ∀ x, x ∈ˢ A → F x = pt := fun h => hne (lamC_of_forall h)
  rw [lamC_of_not hnot] at hf
  rcases mem_piC_cases hf with ⟨heq, -⟩ | ⟨hmem, -⟩
  · exact absurd heq graph_ne_pt
  · exact graph_dom_of_mem_piSet hmem

/- No compiler stubs (see `Derive/Empty.lean`): the `implemented_by … unsafeCast ()`
stubs for these operators were removed 2026-09-06. -/

/- Opaque interface operators (see `Derive/Empty.lean`). -/
attribute [irreducible] pcol piC lamC

end Lech.SetTheory
