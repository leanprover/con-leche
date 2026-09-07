import ConLeche.SetTheory.Basic

/-!
# Probes: the annotation-free semantic-projection design (agent/proj-semantic)

Design study for `.proj` handling without annotations: the environment
invariant carries, per valid projection, a parameter-free semantic
function `projS : V → V` with a membership law and an iota law, and the
interpretation of `.proj T i e` is `projS ⟦e⟧`.

Everything here is over the bare `SetTheory` interface.  An
"instantiation" `i : ι` abstracts a (level valuation, parameter tuple,
earlier-field tuple) triple; `C i` is the carrier at that
instantiation, `F i` the projected field's set, `mk i : V → V` the
semantic constructor restricted to the projected component (all other
components fixed by `i`).  Every artifact/recursor law the install can
consume is *per-instantiation* (one `i` at a time); the design's
`projS` is a *cross-instantiation* object.  The probes locate the
boundary exactly there.
-/

namespace ProjSemanticProbe

open ConLeche ConLeche.SetTheory

universe u v

variable {V : Type u} [SetTheory V]

/-! ## Part 1 — one instantiation: what the recursor supplies (Q1) -/

/-- The `motive : … → Prop` slice of a stored structure recursor's
semantic laws at ONE instantiation: constructor typing plus Prop
elimination (elimination into `Prop` is always allowed, so this slice
exists for every structure).  `M` enters as a meta-level function; in
the real invariant it is a `lam`-graph and `app_lam`/`app_mem` mediate,
which changes nothing below. -/
structure RecElim0 (C F : V) (mk : V → V) : Prop where
  mk_mem : ∀ a, a ∈ˢ F → mk a ∈ˢ C
  elim : ∀ M : V → V,
    (∀ x, x ∈ˢ C → M x ∈ˢ (univZero : V)) →
    (∀ a, a ∈ˢ F → (pt : V) ∈ˢ M (mk a)) →
    ∀ x, x ∈ˢ C → ∃ y, y ∈ˢ M x

/-- **P1 (Q1, positive half).**  Prop elimination proves every carrier
member constructor-shaped — the "instantiate the motive at
`∃ a…, x = mk a…`" step of the user's design, mechanized. -/
theorem mk_surjective {C F : V} {mk : V → V} (h : RecElim0 C F mk) :
    ∀ x, x ∈ˢ C → ∃ a, a ∈ˢ F ∧ x = mk a := by
  intro x hx
  obtain ⟨y, hy⟩ := h.elim (fun x => truthVal (∃ a, a ∈ˢ F ∧ x = mk a))
    (fun _ _ => truthVal_mem_univZero _)
    (fun a ha => pt_mem_truthVal ⟨a, ha, rfl⟩) x hx
  exact of_mem_truthVal hy

/-- The large-elimination slice (motive at the field's own sort),
abstracted the same way: the recursor applied to a motive/minor pair is
a set-level function with its typing and iota equation. -/
structure RecElimU (C F : V) (mk : V → V) : Prop where
  elim : ∀ (M m : V → V),
    (∀ a, a ∈ˢ F → m a ∈ˢ M (mk a)) →
    ∃ r : V → V, (∀ x, x ∈ˢ C → r x ∈ˢ M x) ∧
      (∀ a, a ∈ˢ F → r (mk a) = m a)

/-- **P1b (Q1).**  Large elimination yields the PER-INSTANTIATION
projection outright (motive := the field set, minor := the identity):
per instantiation, the recursor route works.  The design needs the
*glued* global function; the gluing is Part 2's `ProjCoh`. -/
theorem per_instantiation_proj {C F : V} {mk : V → V}
    (h : RecElimU C F mk) :
    ∃ projS : V → V, (∀ x, x ∈ˢ C → projS x ∈ˢ F) ∧
      (∀ a, a ∈ˢ F → projS (mk a) = a) := by
  obtain ⟨r, hr₁, hr₂⟩ := h.elim (fun _ => F) (fun a => a) (fun _ ha => ha)
  exact ⟨r, hr₁, hr₂⟩

/-! ## Part 2 — the squash break (Q2): Prop elimination can never
supply a data-field projection

The one-instantiation instance below is `Exists`-shaped: a squashed
carrier (`{pt}`) over a field set with two distinct members.  The
Prop-elimination package HOLDS — so no argument from `RecElim0` alone
can ever produce an iota-lawful projection — while the iota law is
REFUTABLE for every candidate function.  This is the semantic content
of the missing large elimination, and it is the same line as the #107
squashing countermodel (there the squash was adversarial-model-made;
here proof irrelevance makes it). -/

/-- The squashed instance satisfies the whole Prop-elimination
package. -/
theorem squash_recElim0 :
    RecElim0 (unitSet : V) (upair empty pt) (fun _ => pt) := by
  refine ⟨fun _ _ => pt_mem_unitSet, ?_⟩
  intro M _ hmin x hx
  have hx' : x = pt := mem_unitSet_iff.mp hx
  subst hx'
  exact ⟨pt, hmin empty (mem_upair.mpr (Or.inl rfl))⟩

/-- …yet NO function satisfies the iota law on it: the constructor is
squashed, so iota forces `empty = pt`. -/
theorem squash_no_iota :
    ¬ ∃ projS : V → V, ∀ a, a ∈ˢ (upair empty pt : V) →
      projS ((fun _ => (pt : V)) a) = a := by
  rintro ⟨projS, hiota⟩
  have h1 : projS pt = empty := hiota empty (mem_upair.mpr (Or.inl rfl))
  have h2 : projS pt = pt := hiota pt (mem_upair.mpr (Or.inr rfl))
  exact pt_ne_empty (h2.symm.trans h1)

/-- **Q2's positive half**: on PROOF fields — the field set a truth
value at every legal instantiation, which is what the official
`infer_proj` Prop restriction licenses — the constant-`pt` function is
a lawful semantic projection, uniformly across ALL instantiations at
once.  (Membership needs the field inhabited; that is exactly P1's
surjectivity.)  This covers task #107 Finding A's template class
semantically. -/
theorem propField_projS {ι : Sort v} (C F : ι → V) (mk : ι → V → V)
    (hprop : ∀ i, F i ∈ˢ (univZero : V))
    (hsurj : ∀ i x, x ∈ˢ C i → ∃ a, a ∈ˢ F i ∧ x = mk i a) :
    (∀ i x, x ∈ˢ C i → (pt : V) ∈ˢ F i) ∧
    (∀ i a, a ∈ˢ F i → (pt : V) = a) := by
  refine ⟨fun i x hx => ?_, fun i a ha =>
    (eq_pt_of_mem_univZero (hprop i) ha).symm⟩
  obtain ⟨a, ha, -⟩ := hsurj i x hx
  exact eq_pt_of_mem_univZero (hprop i) ha ▸ ha

/-! ## Part 3 — across instantiations: the exact boundary (Q3, Q4) -/

/-- **ProjCoherence**: cross-instantiation injectivity of the semantic
constructor on the projected component.  (Instantiations `i j` range
over level valuations AND parameter/earlier-field tuples.) -/
def ProjCoh {ι : Sort v} (F : ι → V) (mk : ι → V → V) : Prop :=
  ∀ i j a b, a ∈ˢ F i → b ∈ˢ F j → mk i a = mk j b → a = b

open Classical in
/-- **Q4's classical candidate**: choose any constructor preimage,
across all instantiations at once. -/
noncomputable def projChoice {ι : Type v} (F : ι → V) (mk : ι → V → V)
    (x : V) : V :=
  if h : ∃ i a, a ∈ˢ F i ∧ x = mk i a then h.choose_spec.choose else x

/-- **P4a (Q4, iota).**  Under ProjCoherence the choice function
satisfies iota — coherence is exactly what makes the chosen preimage's
component agree with every actual one. -/
theorem projChoice_iota {ι : Type v} (F : ι → V) (mk : ι → V → V)
    (hcoh : ProjCoh F mk) {i : ι} {a : V} (ha : a ∈ˢ F i) :
    projChoice F mk (mk i a) = a := by
  have h : ∃ j b, b ∈ˢ F j ∧ mk i a = mk j b := ⟨i, a, ha, rfl⟩
  unfold projChoice
  rw [dif_pos h]
  obtain ⟨hb, heq⟩ := h.choose_spec.choose_spec
  exact hcoh _ _ _ _ hb ha heq.symm

/-- **P4b (Q4, membership).**  Under surjectivity (P1, from the
recursor) and ProjCoherence, the choice function satisfies the
membership law at EVERY instantiation. -/
theorem projChoice_mem {ι : Type v} (C F : ι → V) (mk : ι → V → V)
    (hsurj : ∀ i x, x ∈ˢ C i → ∃ a, a ∈ˢ F i ∧ x = mk i a)
    (hcoh : ProjCoh F mk) {i : ι} {x : V} (hx : x ∈ˢ C i) :
    projChoice F mk x ∈ˢ F i := by
  obtain ⟨a, ha, rfl⟩ := hsurj i x hx
  rw [projChoice_iota F mk hcoh ha]
  exact ha

/-- **Necessity**: the iota law alone forces ProjCoherence. -/
theorem coh_of_iota {ι : Sort v} (F : ι → V) (mk : ι → V → V)
    (projS : V → V)
    (hiota : ∀ i a, a ∈ˢ F i → projS (mk i a) = a) : ProjCoh F mk := by
  intro i j a b ha hb heq
  have h := hiota i a ha
  rw [heq, hiota j b hb] at h
  exact h.symm

/-- **THE BOUNDARY THEOREM** (as it would be frozen): given
surjectivity — which the recursor's Prop-motive slice supplies at every
instantiation (P1) — a lawful global semantic projection exists **iff**
ProjCoherence holds.  Everything about the design's reach is this
one equivalence. -/
theorem projS_exists_iff {ι : Type v} (C F : ι → V) (mk : ι → V → V)
    (hsurj : ∀ i x, x ∈ˢ C i → ∃ a, a ∈ˢ F i ∧ x = mk i a) :
    (∃ projS : V → V,
      (∀ i x, x ∈ˢ C i → projS x ∈ˢ F i) ∧
      (∀ i a, a ∈ˢ F i → projS (mk i a) = a)) ↔ ProjCoh F mk :=
  ⟨fun h => coh_of_iota F mk h.choose h.choose_spec.2,
   fun hcoh => ⟨projChoice F mk,
     fun _ _ hx => projChoice_mem C F mk hsurj hcoh hx,
     fun _ _ ha => projChoice_iota F mk hcoh ha⟩⟩

/-! ### The cross-instantiation countermodel (Q3) — #107 Finding B's
shape, realized in interface values

Two instantiations (`ι := Bool`): carriers collide at `pt`, field sets
are DISJOINT singletons.  Each instantiation is perfectly healthy —
injective constructor (singleton field set), full large elimination
(`RecElimU` below) — so every per-instantiation artifact/recursor law
holds; only the gluing fails, and here even the MEMBERSHIP half alone
is unsatisfiable.  This is the subtype-field countermodel
(`T (p : Nat) : Type` with field `{v // v = p}`, model `PUnit'`)
reduced to its semantic core. -/

/-- The countermodel's field sets. -/
noncomputable def cmF : Bool → V
  | true => sing empty
  | false => sing pt

/-- The countermodel's per-instantiation witness value. -/
noncomputable def cmW : Bool → V
  | true => empty
  | false => pt

/-- Each instantiation carries full large elimination. -/
theorem crossing_per_inst_ok (i : Bool) :
    RecElimU (unitSet : V) (cmF i) (fun _ => (pt : V)) := by
  refine ⟨fun M m hm => ?_⟩
  refine ⟨fun _ => m (cmW i), fun x hx => ?_, fun a ha => ?_⟩
  · have hx' : x = pt := mem_unitSet_iff.mp hx
    subst hx'
    cases i with
    | false => exact hm pt (mem_sing.mpr rfl)
    | true => exact hm empty (mem_sing.mpr rfl)
  · cases i with
    | false =>
      show m (cmW false) = m a
      rw [mem_sing.mp ha]
      rfl
    | true =>
      show m (cmW true) = m a
      rw [mem_sing.mp ha]
      rfl

/-- …yet no global function satisfies even the membership law at both
instantiations. -/
theorem crossing_no_mem :
    ¬ ∃ projS : V → V, ∀ (i : Bool) (x : V), x ∈ˢ (unitSet : V) →
      projS x ∈ˢ cmF i := by
  rintro ⟨projS, hmem⟩
  have h1 : projS pt = empty := mem_sing.mp (by
    have := hmem true pt pt_mem_unitSet; simpa [cmF] using this)
  have h2 : projS pt = pt := mem_sing.mp (by
    have := hmem false pt pt_mem_unitSet; simpa [cmF] using this)
  exact pt_ne_empty (h2.symm.trans h1)

/-! ### The two natural sufficient conditions for ProjCoherence (Q3) -/

/-- **Uniform tupling** (the pair's and the built-tower's shape): if
the constructor is one instantiation-independent function with one
global left inverse, coherence is immediate.  (`kpair`/`sfst` is
exactly this pattern.) -/
theorem coh_of_uniform {ι : Sort v} (F : ι → V) (mkG pG : V → V)
    (hinv : ∀ i a, a ∈ˢ F i → pG (mkG a) = a) :
    ProjCoh F (fun _ => mkG) :=
  coh_of_iota F _ pG hinv

/-- **Carrier disjointness + per-instantiation injectivity**: if the
model remembers its instantiation (disjoint carriers) then the
per-instantiation projections (P1b) glue. -/
theorem coh_of_disjoint {ι : Sort v} (C F : ι → V) (mk : ι → V → V)
    (hmk : ∀ i a, a ∈ˢ F i → mk i a ∈ˢ C i)
    (hdisj : ∀ i j x, x ∈ˢ C i → x ∈ˢ C j → i = j)
    (hinj : ∀ i a b, a ∈ˢ F i → b ∈ˢ F i → mk i a = mk i b → a = b) :
    ProjCoh F mk := by
  intro i j a b ha hb heq
  have hij : i = j := hdisj i j _ (hmk i a ha) (heq ▸ hmk j b hb)
  subst hij
  exact hinj i a b ha hb heq

/-! ## Part 4 — the ADDENDUM variant: the proof tier builds the model
(generalizing the pinned `PSigma'` basis)

For a qualifying structure the carrier is not read off a `_model`
artifact at all: it is BUILT as (an iteration of) `sigmaSet`, the
constructor is the uniform Kuratowski tupler `spair`, and the semantic
projections are the interface's own global destructors `sfst`/`ssnd` —
classically defined, well-defined by `kpair_inj`, i.e. by the
uniform-tupling instance of ProjCoherence.  The laws are free; and the
RECURSOR's semantics is then DERIVED from the built model (the reverse
of Q1), with structure ETA (`mem_sigma_elim`: every member is the pair
of its components) as the load-bearing step of its typing. -/

/-- The two-component analog of `RecElimU`, dependent second
component. -/
structure RecElimU2 (C A : V) (B : V → V) (mk : V → V → V) : Prop where
  elim : ∀ (M : V → V) (m : V → V → V),
    (∀ a, a ∈ˢ A → ∀ b, b ∈ˢ B a → m a b ∈ˢ M (mk a b)) →
    ∃ r : V → V, (∀ x, x ∈ˢ C → r x ∈ˢ M x) ∧
      (∀ a b, a ∈ˢ A → b ∈ˢ B a → r (mk a b) = m a b)

/-- **P5a**: the built model's projections satisfy both laws by
construction, at every graph-regime instantiation (`w ≠ 0`) — for
every `A`, `B` at once, i.e. uniformly across instantiations. -/
theorem builtModel_projections {w : Nat} (hw : w ≠ 0) (A : V) (B : V → V) :
    (∀ x, x ∈ˢ sigmaSet w A B → sfst x ∈ˢ A ∧ ssnd x ∈ˢ B (sfst x)) ∧
    (∀ a b, a ∈ˢ A → b ∈ˢ B a → sfst (spair a b) = a ∧
      ssnd (spair a b) = b) := by
  refine ⟨fun x hx => ?_, fun a b _ _ => ⟨sfst_spair a b, ssnd_spair a b⟩⟩
  obtain ⟨a, b, ha, hb, -, hpos⟩ := mem_sigma_elim hx
  rw [hpos hw, sfst_spair, ssnd_spair]
  exact ⟨ha, hb⟩

/-- **P5b (addendum, item d)**: the recursor DERIVED from the built
model — `r x := m (sfst x) (ssnd x)` — satisfies large-elimination
typing and iota.  The typing step is exactly structure eta: `x` IS
`spair (sfst x) (ssnd x)`. -/
theorem builtModel_recElimU2 {w : Nat} (hw : w ≠ 0) (A : V) (B : V → V) :
    RecElimU2 (sigmaSet w A B) A B spair := by
  refine ⟨fun M m hm => ⟨fun x => m (sfst x) (ssnd x), fun x hx => ?_,
    fun a b ha hb => ?_⟩⟩
  · obtain ⟨a, b, ha, hb, -, hpos⟩ := mem_sigma_elim hx
    have hx' : x = spair a b := hpos hw
    subst hx'
    show m (sfst (spair a b)) (ssnd (spair a b)) ∈ˢ M (spair a b)
    rw [sfst_spair, ssnd_spair]
    exact hm a ha b hb
  · show m (sfst (spair a b)) (ssnd (spair a b)) = m a b
    rw [sfst_spair, ssnd_spair]

/-- **P5c**: at a squash instantiation (`w = 0`) the built carrier is a
truth value and the destructors return `pt` (`sfst_pt`); the laws
survive exactly for PROOF components — `sfst pt = pt` is the correct
answer iff the component's set is a truth value, which is the levelwise
`fieldSort ≤ structSort` bound.  For a data component the squashed
instance of Part 2 applies verbatim.  Here: the proof-component half,
by construction. -/
theorem builtModel_squash_proofField (A : V) (B : V → V)
    (hA : A ∈ˢ (univZero : V)) :
    ∀ x, x ∈ˢ sigmaSet 0 A B → sfst x ∈ˢ A := by
  intro x hx
  obtain ⟨a, b, ha, hb, hz, -⟩ := mem_sigma_elim hx
  rw [hz rfl, sfst_pt]
  exact eq_pt_of_mem_univZero hA ha ▸ ha

end ProjSemanticProbe
