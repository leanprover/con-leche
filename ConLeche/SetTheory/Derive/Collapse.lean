import Lech.SetTheory.Basic

/-!
# Design evidence for the domain-relative point collapse (task #100)

The operator layer this file validated — `pcol`/`lamC`/`piC` with the
level-free law battery — **is landed in `Derive/Pi.lean`** (with the
tower-formation laws in `Derive/Univ.lean`); the model consumes it
through the vestigial-level abbrevs `pi`/`lam`.  This module keeps the
*evidence* that fixed the construction (see DESIGN.md, "Annotation
erasure: the domain-relative collapse"):

* the refutation of the literal proposal — a global hereditary
  canonicalization `canon : V → V` — by two formal horns exhausting the
  choice of `canon ∅` (`hereditary_canon_pt_not_fixed`,
  `hereditary_canon_pi_empty_not_prop`; the root cause is that `∅` is
  both the empty function graph and falsity, so the vacuous collapse
  clause pins `canon ∅` inconsistently — the horns survive the #109
  proof-point re-choice unchanged in statement),
  and the forcing lemma `pi_empty_forced` showing Horn B is not an
  artifact of chosen definitions;

* the prior refutation witnesses (`Lech/Model/RawEnvNoAnnot.lean`)
  re-run **positively**: the λ-terms `fun (_ : PUnit) => (1 : Nat)` and
  `fun (_ : PUnit) => True.intro` are both interpreted annotation-free
  — `lamC` is a function of domain and body values alone.  (History:
  under the pre-#109 `pt = {∅}` the numeral `1` *was* `pt` and the two
  witnesses were identified; with the fresh proof point the `Nat`
  witness is a genuine graph and the `Prop` witness collapses —
  `lamC_witnesses_distinguished` — with `mem_type` for both
  (`graph_witness_mem_piC_punit_nat`, `pt_mem_piC_punit_true`).  The
  collapse never *needed* the identification, only level-freedom.);

* the formal core of the de-gating finding (the kernel's
  annotation-guarded reduction gates are unsound to model under the
  collapse): `⟦∀ p : Prop, p⟧ = ∅` (`piC_univZero_id_empty`) and the
  beta-failure witness (`guarded_beta_countermodel_core`);

* the basis ports that checked out during the spike: PSigma projection
  with a collapsed stored value, iota with a collapsed minor premise,
  and the full `Nat.rec.{0}`-shaped λ-tower.
-/

namespace Lech.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The prior refutation witnesses, re-run positively

(Since task #109 the proof point is data-fresh — `vsucc_ne_pt`,
`Derive/PtFresh.lean` — so the numeral `1` is no longer `pt` and the
two witnesses receive *different* values.  Both are still interpreted
with no annotation in sight, which is all the collapse ever claimed:
`lamC` is a function of the domain and the body values alone.) -/

/-- The two witness λ-terms of the old `lam_interp_not_value_determined`
refutation, annotation-free: the `Nat`-valued one is a genuine graph
(its body value `1 ≠ pt` by the #109 freshness battery), the
`Prop`-valued one collapses to the point. -/
theorem lamC_witnesses_distinguished :
    lamC (unitSet : V) (fun _ => vsucc empty) ≠ pt ∧
    lamC (unitSet : V) (fun _ => pt) = pt :=
  ⟨lamC_ne_pt_of_witness pt_mem_unitSet (vsucc_ne_pt empty),
   lamC_of_forall fun _ _ => rfl⟩

/-- … and `mem_type` holds for the `Type`-level witness against the
collapsed `⟦PUnit → Nat⟧`, by ordinary introduction (`1 ∈ ω`). -/
theorem graph_witness_mem_piC_punit_nat :
    lamC (unitSet : V) (fun _ => vsucc empty) ∈ˢ
      piC unitSet (fun _ => omega) :=
  lamC_mem fun _ _ => vsucc_mem_omega empty_mem_omega

/-- … and for the `Prop`-level witness against `⟦PUnit → True⟧`. -/
theorem pt_mem_piC_punit_true :
    (pt : V) ∈ˢ piC unitSet (fun _ => unitSet) :=
  pt_mem_piC_iff.mpr fun _ _ => pt_mem_unitSet

/-! ## The de-gating finding, formal core

The kernel's annotation-guarded reduction paths were unsound to model
under the collapse (DESIGN.md, "Annotation erasure": the flip had to
follow kernel de-gating).  The checkable heart: an empty-domain
abstraction collapses to the proof point at **every** codomain sort —
there is no `lam_ne_pt` analogue — so off-domain "beta" produces `pt`
regardless of the body. -/

theorem univZero_ne_pt : (univZero : V) ≠ pt := by
  intro h
  have hu : (unitSet : V) = ptTag :=
    mem_pt.mp (h ▸ mem_univZero.mpr (Subset.refl _))
  have hm := pt_mem_unitSet (V := V)
  rw [hu] at hm
  exact pt_not_mem_ptTag hm

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
  refine eq_empty fun z hz => ?_
  obtain ⟨g, hg, -⟩ := mem_piC.mp hz
  rw [hraw] at hg
  exact not_mem_empty g hg

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
fixed point — `canon ∅ = pt` (vacuous collapse), `pt = {ptTag}`
contains no pair, so memberwise recursion moves `pt` unless the tag is
`canon`-fixed; the tag recurses memberwise too, landing `pt = canon ∅`
among its members — impossible for both members of the tag.  Every
proof's interpretation violates the global-canonicity invariant. -/
theorem hereditary_canon_pt_not_fixed {canon : V → V}
    (h : HereditaryCanonSpec canon) : canon pt ≠ pt := by
  have h0 : canon empty = pt :=
    h.collapse empty fun p hp => absurd hp (not_mem_empty p)
  have hpt : canon pt = image canon pt := by
    refine h.memberwise pt fun hc => ?_
    obtain ⟨a, b, hab, -⟩ := hc ptTag ptTag_mem_pt
    exact ptTag_ne_kpair a b hab
  intro heq
  have htag : canon ptTag = ptTag := by
    have hm : canon ptTag ∈ˢ (pt : V) := by
      rw [← heq, hpt]
      exact mem_image.mpr ⟨ptTag, ptTag_mem_pt, rfl⟩
    exact mem_pt.mp hm
  have htagm : canon ptTag = image canon ptTag := by
    refine h.memberwise ptTag fun hc => ?_
    obtain ⟨a, b, hab, -⟩ := hc empty empty_mem_ptTag
    exact kpair_ne_empty hab.symm
  have hin : (pt : V) ∈ˢ ptTag := by
    rw [← htag, htagm]
    exact mem_image.mpr ⟨empty, empty_mem_ptTag, h0.symm⟩
  exact pt_not_mem_ptTag hin

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

end Lech.SetTheory
