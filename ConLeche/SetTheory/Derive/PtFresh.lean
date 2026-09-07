import ConLeche.SetTheory.Derive.Sigma

/-!
# The pt-freshness battery: data values are never the proof point (task #109)

`pt = {ptTag}` is chosen so that **no data-value encoding produces it**
(`Derive/Pt.lean` states the selection principle).  This module proves

* the per-encoding collision-freedom lemmas: no von Neumann natural, no
  successor image, no pair, no raw graph and no truth value is `pt`,
  and the type-former values themselves (`omega`, `sigmaSet`, `piC`,
  `univ`, `univZero`) are never `pt` either;
* the semantic freshness predicate `PtFresh` with per-former
  characterizations — the recursive pi clause (`ptFresh_piC_iff`, from
  `pt_mem_piC_iff`) is **existential**: a product is fresh iff *some*
  fibre over the domain is; the consumer-facing under-approximation
  `ptFresh_piC_of` (uniformly fresh fibres over a *nonempty* domain)
  is exactly what re-blocks the task-#100 de-gating countermodel
  `(fun (x : ∀ p : Prop, p) => …)` — its domain is empty, the
  nonemptiness conjunct fails, no restored gate can fire on it;
* domain determination: a non-`pt` member of `piC A B` is a genuine
  graph whose domain *is* `A` (`piSet_dom_eq`, `piC_dom_eq_of_ne_pt`),
  so an ambient argument fact transfers to any computed domain
  (`mem_dom_of_piC_fresh` — task #124 route (iii)).

Hard walls, recorded so they are not re-attempted:

* `pt ∈ univ (u+1)` is **forced** for every buildable proof point
  (`univZero ∈ univ 1` plus transitivity gives `unitSet ∈ univ 1`,
  hence `pt ∈ univ 1`), so sorts above `Prop` are never fresh
  (`not_ptFresh_univ_succ`) — while `Prop` itself *is*
  (`ptFresh_univZero`: truth values are never the point);
* unit-like types are non-fresh **by design** (`⟦PUnit⟧ = {pt}`,
  `not_ptFresh_unitSet`);
* quotients are not unconditionally fresh:
  `quotSet_eq_pt_countermodel` (`Derive/Quot.lean`) exhibits
  `quotSet 1 A R = pt`; a `quotSet_ne_pt` must never be resurrected —
  the syntactic freshness guards exclude `Quot`-typed slots instead.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## Collision lemmas, per encoding -/

/-- No successor image is the proof point — even off `ω`: `vsucc n = pt`
would force `n = ptTag`, whose member `∅` would then be the tag. -/
theorem vsucc_ne_pt (n : V) : vsucc n ≠ pt := by
  intro h
  have hn : n = ptTag := mem_pt.mp (h ▸ self_mem_vsucc n)
  subst hn
  have h0 : (empty : V) ∈ˢ vsucc ptTag :=
    mem_vsucc.mpr (Or.inl empty_mem_ptTag)
  rw [h] at h0
  exact ptTag_ne_empty (mem_pt.mp h0).symm

/-- No von Neumann natural is the proof point.  (Before task #109 this
was **false**: the old `pt = {∅}` *was* the numeral `1`.) -/
theorem vnat_ne_pt : ∀ k, (vnat k : V) ≠ pt
  | 0 => fun h => pt_ne_empty h.symm
  | k + 1 => vsucc_ne_pt (vnat k)

/-- The proof point is not a natural: `pt ∉ ω`. -/
theorem pt_not_mem_omega : ¬ (pt : V) ∈ˢ omega := by
  intro h
  obtain ⟨k, hk⟩ := mem_omega_iff.mp h
  exact vnat_ne_pt k hk.symm

/-- The proof point is not a member of any raw pair set. -/
theorem pt_not_mem_sigmaPairs {A : V} {B : V → V} :
    ¬ (pt : V) ∈ˢ sigmaPairs A B := by
  intro h
  obtain ⟨x, -, y, -, hp⟩ := mem_sigmaPairs.mp h
  exact pt_ne_kpair x y hp

/-- Pair types at a provably positive level are fresh with **no** fibre
condition (their members are Kuratowski pairs). -/
theorem pt_not_mem_sigmaSet_pos {w : Nat} (hw : w ≠ 0) {A : V} {B : V → V} :
    ¬ (pt : V) ∈ˢ sigmaSet w A B := by
  rw [sigmaSet_pos hw]
  exact pt_not_mem_sigmaPairs

/-- The proof point is not a member of any raw dependent-function set. -/
theorem pt_not_mem_piSet {A : V} {B : V → V} :
    ¬ (pt : V) ∈ˢ piSet A B :=
  fun h => ne_pt_of_mem_piSet h rfl

/-- `⟦Prop⟧` is fresh: truth values are never the proof point. -/
theorem pt_not_mem_univZero : ¬ (pt : V) ∈ˢ univZero := by
  intro h
  have htag : (ptTag : V) ∈ˢ unitSet := mem_univZero.mp h ptTag ptTag_mem_pt
  have heq : (ptTag : V) = pt := mem_unitSet_iff.mp htag
  have hm := ptTag_mem_pt (V := V)
  rw [heq] at hm
  exact not_mem_self (pt : V) hm

/-- **The forced wall**: the proof point is a member of every positive
universe — `pt` is hereditarily small, and `univZero ∈ univ 1` with
transitivity forces it for *any* buildable choice of `pt`.  Sorts above
`Prop` can never be pt-fresh; consumers must exclude them. -/
theorem pt_mem_univ_succ (n : Nat) : (pt : V) ∈ˢ univ (n + 1) :=
  (univ_isTGUniverse (Nat.succ_ne_zero n)).pt_mem
    (univChain_one_mem_univ_succ n)

/-! ## Type-former values are never the proof point -/

theorem omega_ne_pt : (omega : V) ≠ pt := by
  intro h
  have h0 : (empty : V) ∈ˢ omega := empty_mem_omega
  rw [h] at h0
  exact ptTag_ne_empty (mem_pt.mp h0).symm

theorem univ_ne_pt (n : Nat) : (univ n : V) ≠ pt := by
  intro h
  have h0 : (empty : V) ∈ˢ univ n := empty_mem_univ n
  rw [h] at h0
  exact ptTag_ne_empty (mem_pt.mp h0).symm

/-- A collapsed product is never the proof point: its sole member would
have to be the tag, which is neither `pt` nor a set of pairs. -/
theorem piC_ne_pt {A : V} {B : V → V} : piC A B ≠ (pt : V) := by
  intro h
  have htag : (ptTag : V) ∈ˢ piC A B := by
    rw [h]; exact ptTag_mem_pt
  rcases mem_piC_cases htag with ⟨heq, -⟩ | ⟨hmem, -⟩
  · have hm := ptTag_mem_pt (V := V)
    rw [heq] at hm
    exact not_mem_self (pt : V) hm
  · have hsub := (mem_piSet.mp hmem).1 empty empty_mem_ptTag
    obtain ⟨x, -, y, -, hp⟩ := mem_sigmaPairs.mp hsub
    exact kpair_ne_empty hp.symm

/-! ## The freshness predicate -/

/-- Semantic pt-freshness of a type value: no member is the proof
point. -/
def PtFresh (T : V) : Prop := ¬ (pt : V) ∈ˢ T

/-- **Data values are never `pt`** — the battery's namesake. -/
theorem ne_pt_of_mem_fresh {T v : V} (hT : PtFresh T) (hv : v ∈ˢ T) :
    v ≠ pt :=
  fun h => hT (h ▸ hv)

/-- The recursive pi clause (`pt_mem_piC_iff`, negated): a product is
fresh iff **some** fibre over the domain is.  Existential, not
universal — over the empty domain every product collapses onto `pt`
(`piC_empty`), so nonemptiness is part of any sufficient condition. -/
theorem ptFresh_piC_iff {A : V} {B : V → V} :
    PtFresh (piC A B) ↔ ∃ x, x ∈ˢ A ∧ PtFresh (B x) := by
  unfold PtFresh
  rw [pt_mem_piC_iff]
  constructor
  · intro h
    rcases Classical.em (∃ x, x ∈ˢ A ∧ ¬ (pt : V) ∈ˢ B x) with hex | hnex
    · exact hex
    · exact absurd
        (fun x hx => Classical.byContradiction fun hnp => hnex ⟨x, hx, hnp⟩) h
  · rintro ⟨x, hx, hfx⟩ hall
    exact hfx (hall x hx)

/-- The consumer-facing under-approximation: uniformly fresh fibres
over a **nonempty** domain.  The nonemptiness conjunct is what
re-blocks the task-#100 empty-domain countermodel
(`⟦∀ p : Prop, p⟧ = ∅`). -/
theorem ptFresh_piC_of {A : V} {B : V → V} (hne : ∃ x, x ∈ˢ A)
    (hB : ∀ x, x ∈ˢ A → PtFresh (B x)) : PtFresh (piC A B) := by
  obtain ⟨x, hx⟩ := hne
  exact ptFresh_piC_iff.mpr ⟨x, hx, hB x hx⟩

/-! ### Base clauses -/

theorem ptFresh_empty : PtFresh (empty : V) :=
  fun h => not_mem_empty _ h

theorem ptFresh_omega : PtFresh (omega : V) := pt_not_mem_omega

theorem ptFresh_sigmaSet_pos {w : Nat} (hw : w ≠ 0) {A : V} {B : V → V} :
    PtFresh (sigmaSet w A B) := pt_not_mem_sigmaSet_pos hw

theorem ptFresh_univZero : PtFresh (univZero : V) := pt_not_mem_univZero

theorem ptFresh_truthVal_of_not {p : Prop} (hp : ¬ p) :
    PtFresh (truthVal p : V) := by
  rw [truthVal_eq_empty hp]
  exact ptFresh_empty

/-! ### Negative records (the excluded classes) -/

/-- Unit-likes are non-fresh by design: `⟦PUnit⟧ = {pt}`. -/
theorem not_ptFresh_unitSet : ¬ PtFresh (unitSet : V) :=
  fun h => h pt_mem_unitSet

/-- Sorts above `Prop` are never fresh (the forced wall). -/
theorem not_ptFresh_univ_succ (n : Nat) : ¬ PtFresh (univ (n + 1) : V) :=
  fun h => h (pt_mem_univ_succ n)

/-- Inhabited propositions are non-fresh (their member *is* `pt`). -/
theorem not_ptFresh_truthVal_of {p : Prop} (hp : p) :
    ¬ PtFresh (truthVal p : V) :=
  fun h => h (pt_mem_truthVal hp)

/-! ## Domain determination (task #124 route (iii)) -/

/-- Total single-valued graphs determine their domains **exactly**:
membership in two raw products pins the domains equal (both directions
of the one-directional `graph_dom_of_mem_piSet`, via totality and the
pair-set bound). -/
theorem piSet_dom_eq {A A' f : V} {B B' : V → V}
    (hf : f ∈ˢ piSet A B) (hf' : f ∈ˢ piSet A' B') : A = A' := by
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hf
  obtain ⟨hsub', htot'⟩ := mem_piSet.mp hf'
  apply ext fun z => ?_
  constructor
  · intro hz
    obtain ⟨y, hy, -⟩ := htot z hz
    obtain ⟨x, hx, y', -, hp⟩ := mem_sigmaPairs.mp (hsub' _ hy)
    obtain ⟨rfl, rfl⟩ := kpair_inj hp
    exact hx
  · intro hz
    obtain ⟨y, hy, -⟩ := htot' z hz
    obtain ⟨x, hx, y', -, hp⟩ := mem_sigmaPairs.mp (hsub _ hy)
    obtain ⟨rfl, rfl⟩ := kpair_inj hp
    exact hx

/-- A non-`pt` member of two collapsed products pins the domains equal:
it is a genuine graph, and graphs determine their domains. -/
theorem piC_dom_eq_of_ne_pt {A A' f : V} {B B' : V → V}
    (hf : f ∈ˢ piC A B) (hf' : f ∈ˢ piC A' B') (hne : f ≠ pt) :
    A = A' := by
  rcases mem_piC_cases hf with ⟨heq, -⟩ | ⟨hmem, -⟩
  · exact absurd heq hne
  rcases mem_piC_cases hf' with ⟨heq, -⟩ | ⟨hmem', -⟩
  · exact absurd heq hne
  exact piSet_dom_eq hmem hmem'

/-- The guard-clear argument transfer: an ambient argument fact
(`va ∈ ⟦A⟧`) transfers to any computed domain `A'` in which the same
non-`pt` function value sits. -/
theorem mem_dom_of_piC_of_ne_pt {A A' f va : V} {B B' : V → V}
    (hf : f ∈ˢ piC A B) (hva : va ∈ˢ A) (hf' : f ∈ˢ piC A' B')
    (hne : f ≠ pt) : va ∈ˢ A' :=
  piC_dom_eq_of_ne_pt hf hf' hne ▸ hva

/-- … with the `≠ pt` premise discharged by freshness of the ambient
product type. -/
theorem mem_dom_of_piC_fresh {A A' f va : V} {B B' : V → V}
    (hT : PtFresh (piC A B)) (hf : f ∈ˢ piC A B) (hva : va ∈ˢ A)
    (hf' : f ∈ˢ piC A' B') : va ∈ˢ A' :=
  mem_dom_of_piC_of_ne_pt hf hva hf' (ne_pt_of_mem_fresh hT hf)

end ConLeche.SetTheory
