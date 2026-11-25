module

public import ConLeche.SetTheory.Derive.Pt

@[expose] public section

/-!
# Function graphs, application, and the raw dependent-function set

* `HasGraph A F := HasImage (fun x => kpair x (F x)) A` and
  proof-carrying, zero-junk `graph F A h = {⟨x, F x⟩ : x ∈ A}`; never
  equal to `pt`, since `pt`'s element `ptTag` has an empty member and
  so is not a Kuratowski pair.
* `app f a = ⋃ {y : ⟨a, y⟩ ∈ f}` — untagged total application on
  non-`pt` arguments (`app pt a = pt` is the tag that makes proofs
  degenerate); unconditionally `DefFun 2`.
* `HasSigmaPairs A B` and proof-carrying, zero-junk
  `sigmaPairs A B h = {⟨x, y⟩ : x ∈ A, y ∈ B x}` (and unconditional
  `prod A B`).
* `piSet A B h ⊆ power (sigmaPairs A B h)` — the total single-valued
  graphs: the `v ≠ 0` dependent function space.

The level-`0` truncations (`lam 0 = pt`, `pi 0` a truth value) live
in the numeral-indexed `piR`/`lamR` (`SetModel/Ops.lean`), which
dispatch on the regime numeral.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ### Function graphs -/

/-- Proof-carrying predicate asserting that the function graph
`{⟨x, F x⟩ : x ∈ A}` exists as a set in `V`. -/
def HasGraph (A : V) (F : V → V) : Prop :=
  HasImage (fun x => kpair x (F x)) A

theorem hasGraph_of_defFunOn {A : V} {F : V → V} (h : DefFunOn A F) :
    HasGraph A F :=
  hasImage_kpair h

theorem hasGraph_of_defFun1 {A : V} {F : V → V}
    (h : DefFun 1 fun v => F (v 0)) : HasGraph A F :=
  hasGraph_of_defFunOn (DefFunOn.of_defFun1 h)

theorem hasGraph_empty (F : V → V) : HasGraph empty F :=
  hasImage_empty _

theorem HasGraph.congr {A : V} {F G : V → V}
    (hFG : ∀ x, x ∈ˢ A → F x = G x) (h : HasGraph A F) : HasGraph A G :=
  HasImage.congr (fun x hx => by rw [hFG x hx]) h

theorem HasGraph.ext {A B : V} {F G : V → V} (hAB : A = B)
    (hFG : ∀ x, x ∈ˢ A → F x = G x) (h : HasGraph A F) : HasGraph B G :=
  hAB ▸ h.congr hFG

/-- Proof-carrying, zero-junk function graph `{⟨x, F x⟩ : x ∈ A}`. -/
noncomputable def graph (F : V → V) (A : V) (h : HasGraph A F) : V :=
  image (fun x => kpair x (F x)) A h

theorem mem_graph {F : V → V} {A p : V} {h : HasGraph A F} :
    p ∈ˢ graph F A h ↔ ∃ x, x ∈ˢ A ∧ p = kpair x (F x) :=
  mem_image

theorem graph_ne_pt {F : V → V} {A : V} {h : HasGraph A F} :
    graph F A h ≠ (pt : V) := by
  intro heq
  obtain ⟨x, -, hx⟩ :=
    mem_graph.mp (heq ▸ ptTag_mem_pt : (ptTag : V) ∈ˢ graph F A h)
  exact ptTag_ne_kpair x (F x) hx

/-- No graph is a member of the point (a point law, task #342): the
point's one member `ptTag` has the empty set as a member, while every
member of a graph is a Kuratowski pair, hence nonempty. -/
theorem graph_not_mem_pt {F : V → V} {A : V} {h : HasGraph A F} :
    ¬ graph F A h ∈ˢ (pt : V) := by
  intro heq
  have h' : (empty : V) ∈ˢ graph F A h := mem_pt.mp heq ▸ empty_mem_ptTag
  obtain ⟨x, -, hx⟩ := mem_graph.mp h'
  have hs : sing x ∈ˢ (empty : V) := hx ▸ mem_upair_left _ _
  exact not_mem_empty _ hs

theorem graph_congr {F F' : V → V} {A : V} (hF : HasGraph A F)
    (hF' : HasGraph A F') (h : ∀ x, x ∈ˢ A → F x = F' x) :
    graph F A hF = graph F' A hF' :=
  image_congr hF hF' fun x hx => by rw [h x hx]

theorem graph_ext {F F' : V → V} {A A' : V} (hA : A = A')
    (hF : HasGraph A F) (hF' : HasGraph A' F')
    (h : ∀ x, x ∈ˢ A → F x = F' x) :
    graph F A hF = graph F' A' hF' := by
  subst hA
  exact graph_congr hF hF' h

/-- **A graph determines its domain**: the first components of its pairs
are exactly the domain's members. -/
theorem graph_dom_unique {F F' : V → V} {A A' : V}
    {hF : HasGraph A F} {hF' : HasGraph A' F'}
    (h : graph F A hF = graph F' A' hF') : A = A' := by
  have key : ∀ {F F' : V → V} {A A' : V} {hF : HasGraph A F} {hF' : HasGraph A' F'},
      graph F A hF = graph F' A' hF' → ∀ x, x ∈ˢ A → x ∈ˢ A' := by
    intro F F' A A' hF hF' h x hx
    have hp : kpair x (F x) ∈ˢ graph F' A' hF' := h ▸ mem_graph.mpr ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hq⟩ := mem_graph.mp hp
    obtain ⟨rfl, -⟩ := kpair_inj hq
    exact hx'
  exact ext fun x => ⟨key h x, key h.symm x⟩

theorem DefFun.graph_apply {k : Nat}
    {F : (Fin (k + 1) → V) → V} {A : (Fin k → V) → V}
    {h : ∀ env, HasGraph (A env) (fun x => F (fcons x env))}
    (hF : DefFun (k + 1) F) (hA : DefFun k A) :
    DefFun k fun env => graph (fun x => F (fcons x env)) (A env) (h env) :=
  DefFun.image_kpair (F := fun x env => F (fcons x env))
    (hF.congr fun v => by rw [fcons_zero_ftail]) hA

theorem DefFun.graph_apply_curry {k : Nat}
    {F : V → (Fin k → V) → V} {A : (Fin k → V) → V}
    {h : ∀ env, HasGraph (A env) (fun x => F x env)}
    (hF : DefFun (k + 1) fun v => F (v 0) (ftail v)) (hA : DefFun k A) :
    DefFun k fun env => graph (fun x => F x env) (A env) (h env) :=
  DefFun.image_kpair hF hA

/-! ### Application -/

open Classical in
/-- Tagged set-theoretic application: the union of the values paired
with `a` in `f` — except at the proof point, which applies to `pt`
again. -/
noncomputable def app (f a : V) : V :=
  if f = pt then pt
  else sUnion (sep (sUnion (sUnion f)) (fun y => kpair a y ∈ˢ f)
    (hasSep_of_def (by fo_def [DefFun.kpair_apply])))

theorem app_pt (a : V) : app (pt : V) a = pt := by
  unfold app; exact ite_eq_left rfl

/-- Application computes on single-valued positions. -/
theorem app_eq_of_unique {f a b : V} (hf : f ≠ pt) (hab : kpair a b ∈ˢ f)
    (huniq : ∀ y, kpair a y ∈ˢ f → y = b) : app f a = b := by
  unfold app
  rw [ite_eq_right hf]
  have heq : sep (sUnion (sUnion f)) (fun y => kpair a y ∈ˢ f)
      (hasSep_of_def (by fo_def [DefFun.kpair_apply])) = sing b := by
    apply ext fun z => ?_
    rw [mem_sep, mem_sing]
    constructor
    · exact fun ⟨_, hz⟩ => huniq z hz
    · rintro rfl
      refine ⟨?_, hab⟩
      exact mem_sUnion.mpr ⟨upair a z, mem_sUnion.mpr ⟨kpair a z, hab, mem_upair_right _ _⟩,
        mem_upair_right a z⟩
  rw [heq, sUnion_sing]

/-- Beta on graphs. -/
theorem app_graph {F : V → V} {A a : V} {h : HasGraph A F} (ha : a ∈ˢ A) :
    app (graph F A h) a = F a := by
  refine app_eq_of_unique graph_ne_pt (mem_graph.mpr ⟨a, ha, rfl⟩) ?_
  intro y hy
  obtain ⟨x, -, hx⟩ := mem_graph.mp hy
  obtain ⟨rfl, rfl⟩ := kpair_inj hx
  rfl

private theorem app_base : DefFun (V := V) 2 fun v => app (v 0) (v 1) := by
  unfold app
  fo_def [DefFun.pt, DefFun.sep_apply_curry, DefFun.kpair_apply]

theorem DefFun.app_apply {k : Nat} {F A : (Fin k → V) → V}
    (hF : DefFun k F) (hA : DefFun k A) :
    DefFun k fun env => app (F env) (A env) :=
  DefFun.comp2 (app_base (V := V)) hF hA

theorem hasGraph_app (f A : V) : HasGraph A (fun x => app f x) :=
  hasGraph_of_defFun1 (DefFun.app_apply (DefFun.const f) (DefFun.proj 0))

/-! ### Dependent pairs and product sets -/

/-- Proof-carrying predicate asserting that `{⟨x, y⟩ : x ∈ A, y ∈ B x}`
exists as a set in `V`. -/
def HasSigmaPairs (A : V) (B : V → V) : Prop :=
  ∃ s : V, ∀ p, p ∈ˢ s ↔ ∃ x y, x ∈ˢ A ∧ y ∈ˢ B x ∧ p = kpair x y

theorem hasSigmaPairs_empty (B : V → V) : HasSigmaPairs empty B :=
  ⟨empty, fun p =>
    ⟨fun hp => absurd hp (not_mem_empty p),
     fun ⟨x, _, hx, _⟩ => absurd hx (not_mem_empty x)⟩⟩

theorem HasSigmaPairs.congr {A : V} {B B' : V → V}
    (hBB' : ∀ x, x ∈ˢ A → B x = B' x) (h : HasSigmaPairs A B) :
    HasSigmaPairs A B' := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, fun p => (hs p).trans ?_⟩
  exact ⟨fun ⟨x, y, hx, hy, hp⟩ => ⟨x, y, hx, (hBB' x hx) ▸ hy, hp⟩,
         fun ⟨x, y, hx, hy, hp⟩ => ⟨x, y, hx, (hBB' x hx) ▸ hy, hp⟩⟩

theorem HasSigmaPairs.ext {A A' : V} {B B' : V → V} (hAA' : A = A')
    (hBB' : ∀ x, x ∈ˢ A → B x = B' x) (h : HasSigmaPairs A B) :
    HasSigmaPairs A' B' :=
  hAA' ▸ h.congr hBB'

theorem hasSigmaPairs_of_defFun1 {A : V} {B : V → V}
    (hB : DefFun 1 fun v => B (v 0)) : HasSigmaPairs A B := by
  have himg_y : ∀ x : V, HasImage (fun y => kpair x y) (B x) := fun x => by
    fo_def [DefFun.kpair_apply]
  let F : V → V := fun x => image (fun y => kpair x y) (B x) (himg_y x)
  have hF : DefFun 1 fun v => F (v 0) := by
    dsimp only [F]
    fo_def [DefFun.kpair_apply, hB]
  have himg_F : HasImage F A := hasImage_of_defFun1 hF A
  refine ⟨sUnion (image F A himg_F), fun p => ?_⟩
  rw [mem_sUnion]
  constructor
  · rintro ⟨s, hs, hps⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hps
    exact ⟨x, y, hx, hy, rfl⟩
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact ⟨F x, mem_image.mpr ⟨x, hx, rfl⟩, mem_image.mpr ⟨y, hy, rfl⟩⟩

theorem hasSigmaPairs_of_defFunOn {A : V} {B : V → V} (hB : DefFunOn A B) :
    HasSigmaPairs A B := by
  obtain ⟨G, hG, heq⟩ := hB
  exact (hasSigmaPairs_of_defFun1 hG).congr fun x hx => (heq x hx).symm

theorem hasSigmaPairs_const (A B : V) : HasSigmaPairs A fun _ => B :=
  hasSigmaPairs_of_defFun1 (DefFun.const B)

/-- Proof-carrying, zero-junk raw dependent pair set `{⟨x, y⟩ : x ∈ A, y ∈ B x}`. -/
noncomputable def sigmaPairs (A : V) (B : V → V) (h : HasSigmaPairs A B) : V :=
  Classical.choose h

theorem mem_sigmaPairs {A p : V} {B : V → V} {h : HasSigmaPairs A B} :
    p ∈ˢ sigmaPairs A B h ↔ ∃ x, x ∈ˢ A ∧ ∃ y, y ∈ˢ B x ∧ p = kpair x y := by
  have hs := Classical.choose_spec h p
  constructor
  · intro hp
    obtain ⟨x, y, hx, hy, rfl⟩ := hs.mp hp
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact hs.mpr ⟨x, y, hx, hy, rfl⟩

theorem sigmaPairs_congr {A : V} {B B' : V → V}
    (hB : HasSigmaPairs A B) (hB' : HasSigmaPairs A B')
    (h : ∀ x, x ∈ˢ A → B x = B' x) :
    sigmaPairs A B hB = sigmaPairs A B' hB' :=
  ext fun p => by
    rw [mem_sigmaPairs, mem_sigmaPairs]
    exact ⟨fun ⟨x, hx, y, hy, hp⟩ => ⟨x, hx, y, (h x hx) ▸ hy, hp⟩,
           fun ⟨x, hx, y, hy, hp⟩ => ⟨x, hx, y, (h x hx) ▸ hy, hp⟩⟩

theorem sigmaPairs_ext {A A' : V} {B B' : V → V} (hA : A = A')
    (hB : HasSigmaPairs A B) (hB' : HasSigmaPairs A' B')
    (h : ∀ x, x ∈ˢ A → B x = B' x) :
    sigmaPairs A B hB = sigmaPairs A' B' hB' := by
  subst hA
  exact sigmaPairs_congr hB hB' h

theorem DefFun.sigmaPairs_apply {k : Nat}
    {A : (Fin k → V) → V} {B : (Fin (k + 1) → V) → V}
    {h : ∀ env, HasSigmaPairs (A env) (fun x => B (fcons x env))}
    (hA : DefFun k A) (hB : DefFun (k + 1) B) :
    DefFun k fun env => sigmaPairs (A env) (fun x => B (fcons x env)) (h env) := by
  let reB : Fin (k + 1) → Fin (k + 3)
    | ⟨0, _⟩ => 0
    | ⟨i + 1, hi⟩ => ⟨i + 3, by omega⟩
  have hB' : DefFun (k + 3) fun w => B (fcons (w 0) (ftail (ftail (ftail w)))) :=
    (hB.reIndex reB).congr fun w => by
      congr 1
      funext ⟨j, hj⟩
      cases j with
      | zero => rfl
      | succ j => rfl
  have hrel : DefRel (k + 1) fun v =>
      ∀ p, p ∈ˢ v 0 ↔
        ∃ x, x ∈ˢ A (ftail v) ∧ ∃ y, y ∈ˢ B (fcons x (ftail v)) ∧ p = kpair x y := by
    refine DefRel.forall_curry
      ((DefRel.mem_apply (DefFun.proj 0) (DefFun.proj 1)).iff
        (DefRel.bExists_curry hA.weaken.weaken
          (DefRel.bExists_curry hB' ?_)))
    fo_def [DefFun.kpair_apply]
  refine hrel.congr fun v => ?_
  exact ⟨fun hp => ext fun p => (hp p).trans mem_sigmaPairs.symm,
    fun heq p => by rw [heq, mem_sigmaPairs]⟩

theorem DefFun.sigmaPairs_apply_curry {k : Nat}
    {A : (Fin k → V) → V} {B : V → (Fin k → V) → V}
    {h : ∀ env, HasSigmaPairs (A env) (fun x => B x env)}
    (hA : DefFun k A) (hB : DefFun (k + 1) fun v => B (v 0) (ftail v)) :
    DefFun k fun env => sigmaPairs (A env) (fun x => B x env) (h env) :=
  DefFun.sigmaPairs_apply (B := fun v => B (v 0) (ftail v)) hA hB

/-- Non-dependent Cartesian product `A × B`, unconditionally defined. -/
noncomputable def prod (A B : V) : V :=
  sigmaPairs A (fun _ => B) (hasSigmaPairs_const A B)

theorem mem_prod {A B p : V} :
    p ∈ˢ prod A B ↔ ∃ x, x ∈ˢ A ∧ ∃ y, y ∈ˢ B ∧ p = kpair x y :=
  mem_sigmaPairs

theorem DefFun.prod_apply {k : Nat} {A B : (Fin k → V) → V}
    (hA : DefFun k A) (hB : DefFun k B) :
    DefFun k fun env => prod (A env) (B env) := by
  unfold prod
  exact DefFun.sigmaPairs_apply_curry hA hB.weaken

theorem _root_.ConLeche.IsGrothendieck.sigmaPairs_mem {U A : V} {B : V → V}
    (hU : IsGrothendieck (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ U) (hS : HasSigmaPairs A B) :
    sigmaPairs A B hS ∈ˢ U := by
  let S := sigmaPairs A B hS
  have hsepSlice : ∀ a : V, HasSep S (fun p => ∃ y, p = kpair a y) := fun a =>
    hasSep_of_def (by fo_def [DefFun.kpair_apply])
  let slice : V → V := fun a => sep S (fun p => ∃ y, p = kpair a y) (hsepSlice a)
  have hslice_def : DefFun 1 fun v => slice (v 0) := by
    dsimp only [slice]
    fo_def [DefFun.sep_apply_curry, DefFun.kpair_apply]
  have hslice_mem : ∀ a, a ∈ˢ A → slice a ∈ˢ U := by
    intro a ha
    have himg : HasImage (fun y => kpair a y) (B a) := by
      fo_def [DefFun.kpair_apply]
    have hgraph : HasImage (fun y => kpair y (kpair a y)) (B a) := by
      fo_def [DefFun.kpair_apply]
    have himg_mem : image (fun y => kpair a y) (B a) himg ∈ˢ U :=
      hU.image_mem (hB a ha)
        (fun y hy => hU.kpair_mem (hU.transitive hA ha) (hU.transitive (hB a ha) hy))
        himg hgraph
    have heq : slice a = image (fun y => kpair a y) (B a) himg := by
      apply ext fun p => ?_
      rw [mem_sep, mem_image, mem_sigmaPairs]
      constructor
      · rintro ⟨⟨x, hx, y, hy, rfl⟩, y', hkp⟩
        obtain ⟨rfl, rfl⟩ := kpair_inj hkp
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨a, ha, y, hy, rfl⟩, y, rfl⟩
    exact heq ▸ himg_mem
  have hgImg : HasImage (fun a => kpair a (slice a)) A := by
    fo_def [DefFun.kpair_apply, hslice_def]
  let g := image (fun a => kpair a (slice a)) A hgImg
  have hfg : IsFunGraph (Mem (V := V)) g A U := by
    constructor
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hp
      exact ⟨a, slice a, ha, hslice_mem a ha, isKPair_kpair a (slice a)⟩
    · intro a ha
      refine ⟨slice a, ⟨hslice_mem a ha, kpair a (slice a),
        mem_image.mpr ⟨a, ha, rfl⟩, isKPair_kpair a (slice a)⟩, ?_⟩
      rintro y ⟨_, p, hp, hkp⟩
      obtain ⟨a', _, rfl⟩ := mem_image.mp hp
      rw [isKPair_iff] at hkp
      obtain ⟨rfl, rfl⟩ := kpair_inj hkp
      rfl
  obtain ⟨w, hw, hzw⟩ := hU.indexedUnion A g hA hfg
  have heq : w = sigmaPairs A B hS := ext fun p => by
    rw [hzw p, mem_sigmaPairs]
    constructor
    · rintro ⟨i, y, q, hi, _, hq, hkp, hpq⟩
      obtain ⟨a, _, rfl⟩ := mem_image.mp hq
      rw [isKPair_iff] at hkp
      obtain ⟨rfl, rfl⟩ := kpair_inj hkp
      exact mem_sigmaPairs.mp (mem_sep.mp hpq).1
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, slice x, kpair x (slice x), hx, hslice_mem x hx,
        mem_image.mpr ⟨x, hx, rfl⟩, isKPair_kpair x (slice x),
        mem_sep.mpr ⟨mem_sigmaPairs.mpr ⟨x, hx, y, hy, rfl⟩, y, rfl⟩⟩
  exact heq ▸ hw

/-! ### Dependent function space `piSet` -/

theorem hasSep_piSet (A : V) (B : V → V) (h : HasSigmaPairs A B) :
    HasSep (power (sigmaPairs A B h))
      (fun f => ∀ x, x ∈ˢ A → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y) :=
  hasSep_of_def (by fo_def [DefFun.kpair_apply])

/-- The set of total single-valued dependent graphs on `A` with fibres
`B`: the `v ≠ 0` dependent function space. -/
noncomputable def piSet (A : V) (B : V → V) (h : HasSigmaPairs A B) : V :=
  sep (power (sigmaPairs A B h))
    (fun f => ∀ x, x ∈ˢ A → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y)
    (hasSep_piSet A B h)

theorem mem_piSet {A f : V} {B : V → V} {h : HasSigmaPairs A B} :
    f ∈ˢ piSet A B h ↔ f ⊆ˢ sigmaPairs A B h ∧
      ∀ x, x ∈ˢ A → ∃ y, kpair x y ∈ˢ f ∧ ∀ y', kpair x y' ∈ˢ f → y' = y := by
  unfold piSet
  rw [mem_sep, mem_power_iff_subset]

theorem piSet_congr {A : V} {B B' : V → V}
    (hB : HasSigmaPairs A B) (hB' : HasSigmaPairs A B')
    (h : ∀ x, x ∈ˢ A → B x = B' x) :
    piSet A B hB = piSet A B' hB' :=
  ext fun f => by
    rw [mem_piSet, mem_piSet, sigmaPairs_congr hB hB' h]

theorem piSet_ext {A A' : V} {B B' : V → V} (hA : A = A')
    (hB : HasSigmaPairs A B) (hB' : HasSigmaPairs A' B')
    (h : ∀ x, x ∈ˢ A → B x = B' x) :
    piSet A B hB = piSet A' B' hB' := by
  subst hA
  exact piSet_congr hB hB' h

theorem DefFun.piSet_apply {k : Nat}
    {A : (Fin k → V) → V} {B : (Fin (k + 1) → V) → V}
    {h : ∀ env, HasSigmaPairs (A env) (fun x => B (fcons x env))}
    (hA : DefFun k A) (hB : DefFun (k + 1) B) :
    DefFun k fun env => piSet (A env) (fun x => B (fcons x env)) (h env) := by
  unfold piSet
  exact DefFun.sep_apply_curry
    (DefFun.power_apply (DefFun.sigmaPairs_apply hA hB))
    (by fo_def [DefFun.kpair_apply, hA.weaken])

theorem DefFun.piSet_apply_curry {k : Nat}
    {A : (Fin k → V) → V} {B : V → (Fin k → V) → V}
    {h : ∀ env, HasSigmaPairs (A env) (fun x => B x env)}
    (hA : DefFun k A) (hB : DefFun (k + 1) fun v => B (v 0) (ftail v)) :
    DefFun k fun env => piSet (A env) (fun x => B x env) (h env) :=
  DefFun.piSet_apply (B := fun v => B (v 0) (ftail v)) hA hB

theorem _root_.ConLeche.IsGrothendieck.piSet_mem {U A : V} {B : V → V}
    (hU : IsGrothendieck (Mem (V := V)) U) (hA : A ∈ˢ U)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ U) (hS : HasSigmaPairs A B) :
    piSet A B hS ∈ˢ U :=
  hU.mem_of_subset_mem (hU.power_mem (hU.sigmaPairs_mem hA hB hS)) sep_subset

theorem graph_mem_piSet {A : V} {B F : V → V}
    {hG : HasGraph A F} {hS : HasSigmaPairs A B}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) : graph F A hG ∈ˢ piSet A B hS := by
  rw [mem_piSet]
  constructor
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := mem_graph.mp hp
    exact mem_sigmaPairs.mpr ⟨x, hx, F x, hF x hx, rfl⟩
  · intro x hx
    refine ⟨F x, mem_graph.mpr ⟨x, hx, rfl⟩, ?_⟩
    intro y' hy'
    obtain ⟨x', -, hx'⟩ := mem_graph.mp hy'
    obtain ⟨rfl, rfl⟩ := kpair_inj hx'
    rfl

theorem ne_pt_of_mem_piSet {A f : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piSet A B hS) : f ≠ pt := by
  rintro rfl
  have htag := (mem_piSet.mp hf).1 ptTag ptTag_mem_pt
  obtain ⟨x, -, y, -, hy⟩ := mem_sigmaPairs.mp htag
  exact ptTag_ne_kpair x y hy

theorem app_mem_of_mem_piSet {A f a : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piSet A B hS) (ha : a ∈ˢ A) : app f a ∈ˢ B a := by
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hf
  obtain ⟨y, hy, huniq⟩ := htot a ha
  rw [app_eq_of_unique (ne_pt_of_mem_piSet hf) hy huniq]
  obtain ⟨x', -, y', hy', hp⟩ := mem_sigmaPairs.mp (hsub _ hy)
  obtain ⟨rfl, rfl⟩ := kpair_inj hp
  exact hy'

/-- Eta: a member of `piSet A B` is the graph of its own application. -/
theorem eq_graph_app_of_mem_piSet {A f : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piSet A B hS) :
    graph (fun x => app f x) A (hasGraph_app f A) = f := by
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hf
  apply ext fun p => ?_
  rw [mem_graph]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, huniq⟩ := htot x hx
    rwa [app_eq_of_unique (ne_pt_of_mem_piSet hf) hy huniq]
  · intro hp
    obtain ⟨x, hx, y, -, rfl⟩ := mem_sigmaPairs.mp (hsub p hp)
    obtain ⟨y', hy', huniq⟩ := htot x hx
    refine ⟨x, hx, ?_⟩
    rw [app_eq_of_unique (ne_pt_of_mem_piSet hf) hy' huniq, huniq y hp]

/-! ### Off-domain and junk behavior of `app` -/

theorem app_eq_empty_of_not_mem {f a : V} (hf : f ≠ pt)
    (h : ∀ y, ¬ kpair a y ∈ˢ f) : app f a = empty := by
  unfold app
  rw [ite_eq_right hf]
  refine eq_empty fun z hz => ?_
  obtain ⟨y, hy, -⟩ := mem_sUnion.mp hz
  exact h y (mem_sep.mp hy).2

/-- `app` off a graph's domain is the canonical junk value. -/
theorem app_graph_of_not_mem {F : V → V} {A a : V} {h : HasGraph A F}
    (ha : ¬ a ∈ˢ A) : app (graph F A h) a = empty := by
  refine app_eq_empty_of_not_mem graph_ne_pt fun y hy => ?_
  obtain ⟨x, hx, hp⟩ := mem_graph.mp hy
  obtain ⟨rfl, rfl⟩ := kpair_inj hp
  exact ha hx

/-- `app` on the canonical junk value returns junk: junk propagates
through applications. -/
theorem app_empty (a : V) : app (empty : V) a = empty :=
  app_eq_empty_of_not_mem (Ne.symm pt_ne_empty)
    (fun _y hy => not_mem_empty _ hy)

/-- A member of `piSet` applied off the domain is junk. -/
theorem app_off_dom_of_mem_piSet {A f a : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hf : f ∈ˢ piSet A B hS) (ha : ¬ a ∈ˢ A) : app f a = empty := by
  rw [← eq_graph_app_of_mem_piSet hf, app_graph_of_not_mem ha]

/-- Function extensionality for members of the raw dependent function space:
two total single-valued graphs over the same domain that agree under
application on every domain member are equal. -/
theorem eq_of_mem_piSet_app_eq {A f g : V} {B B' : V → V}
    {hB : HasSigmaPairs A B} {hB' : HasSigmaPairs A B'}
    (hf : f ∈ˢ piSet A B hB) (hg : g ∈ˢ piSet A B' hB')
    (h : ∀ x, x ∈ˢ A → app f x = app g x) : f = g := by
  rw [← eq_graph_app_of_mem_piSet hf, ← eq_graph_app_of_mem_piSet hg]
  exact graph_congr (hasGraph_app f A) (hasGraph_app g A) h

/- Opaque interface operators (see `Derive/Empty.lean`). -/
attribute [irreducible] graph sigmaPairs piSet app

end ConLeche.SetTheory
