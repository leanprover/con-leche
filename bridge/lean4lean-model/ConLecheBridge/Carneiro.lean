import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.SetTheory.ZFC.Cardinal
import ConLeche.SetTheory.Core

/-!
# Carneiro's hypothesis implies ConLeche's `SetTheory` (task #204)

Mario Carneiro's lean4lean-model (`Lean4LeanModel/Consistency.lean`,
<https://github.com/digama0/lean4lean-model>) states the consistency of
Lean's type theory relative to one hypothesis, `OmegaInaccessibles`:
*there are `ω` inaccessible cardinals — a strictly increasing
`ℕ`-indexed sequence of them, one to interpret each Lean universe*.
ConLeche's consistency proof is parametric in the `ConLeche.SetTheory` class
(`ConLeche/SetTheory/Core.lean`): strictly first-order ZFC⁻ plus an
ω-chain of SGA4 Grothendieck universes (`ConLeche.IsGrothendieck`).  This
module proves, in Lean, that his hypothesis implies ours:

* `OmegaInaccessibles` is transcribed **verbatim** from his file (same
  Mathlib notions — `Cardinal.IsInaccessible`, `StrictMono`; his file is
  internal to his repository, which additionally depends on lean4lean,
  so it is copied rather than imported; the text is identical).
* `setTheoryOfChain κ` is an explicit `ConLeche.SetTheory` instance on
  Mathlib's `ZFSet.{u}` for any strictly increasing sequence of
  inaccessibles `κ`, with `univChain n := V_ (κ n).ord` (Mathlib's
  von Neumann hierarchy).  The ZFC fields are Mathlib's; the work is
  `isGrothendieck_vonNeumann`: `V_ κ` for `κ` inaccessible is an SGA4
  Grothendieck universe.
* `carneiro_implies_conleche : OmegaInaccessibles.{u} →
  Nonempty (Σ V : Type (u + 1), ConLeche.SetTheory V)`.

The proof of the indexed-union clause (`I ∈ V_ κ` and an internal
function graph `g : I → V_ κ` imply `⋃ (range g) ∈ V_ κ`) is where
inaccessibility enters: `I ∈ V_ κ` gives `I ⊆ V_{rank I}` so
`|I| ≤ ℶ_{rank I} < κ` by **strong limitness** (`preBeth_lt_of_lt_ord`),
and then **regularity** bounds the supremum of `< κ` many ordinals
`< κ.ord` below `κ.ord`.

Nothing here is imported by the ConLeche libraries: this is a separate Lake
package so that ConLeche never acquires a Mathlib dependency.  The closing
`#print axioms` guard pins the bridge theorem to Lean's three standard
axioms.
-/

universe u

open Cardinal Order ZFSet

namespace ConLecheBridge

/-- **Carneiro's hypothesis**, transcribed verbatim from
`Lean4LeanModel/Consistency.lean` (lean4lean-model, pinned in
`_tmp/lean4lean-model`; Mathlib `v4.30.0` there, `v4.33.0` here — the
definition of `Cardinal.IsInaccessible` is the same structure in both):

> There are `ω` inaccessible cardinals: a strictly increasing
> `ℕ`-indexed sequence of them, one to interpret each Lean universe
> `Sort 0, Sort 1, ...`.

His consistency theorem is
`theorem consistency (_ : OmegaInaccessibles.{u}) {env : VEnv} (_ : env.WF) (U : Nat) :
  ¬ ∃ e, env.HasType U [] e Term.false`. -/
def OmegaInaccessibles : Prop :=
  ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible

/-! ### `V_ κ` is an SGA4 Grothendieck universe, for `κ` inaccessible -/

variable {κ : Cardinal.{u}}

/-- A subset of `V_ κ.ord` of cardinality `< κ` has rank `< κ.ord`:
regularity of `κ` bounds the least strict upper bound of `< κ` many
ordinals below `κ.ord`. -/
theorem rank_lt_ord_of_card_lt (hκ : κ.IsRegular) {y : ZFSet.{u}}
    (hy : y ⊆ V_ κ.ord) (hc : y.card < κ) : y.rank < κ.ord := by
  let e : y ≃ Shrink.{u} y := equivShrink _
  let f : Shrink.{u} y → Ordinal.{u} := fun z => rank (e.symm z).1
  have hlt : ⨆ z, f z + 1 < κ.ord :=
    Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hκ.cof_ord]) fun z =>
      mem_vonNeumann.mp (hy (e.symm z).2)
  refine lt_of_le_of_lt ?_ hlt
  rw [rank_le_iff]
  intro z hz
  have := Ordinal.lt_iSup_add_one f (e ⟨z, hz⟩)
  simpa [f, e] using this

/-- Below an inaccessible, the beth function stays below it. -/
theorem preBeth_lt_of_lt_ord (hκ : κ.IsInaccessible) :
    ∀ {a : Ordinal.{u}}, a < κ.ord → preBeth a < κ := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => intro _; rw [preBeth_zero]; exact hκ.pos
  | add_one a ih =>
    intro h
    rw [preBeth_add_one]
    exact hκ.isStrongLimit.isStrongPrelimit (ih ((lt_add_one a).trans h))
  | limit a ha ih =>
    intro h
    rw [preBeth_limit ha.isSuccPrelimit]
    refine Cardinal.lift_iSup_lt_of_lt_cof_ord ?_ fun b => ih b b.2 (b.2.trans h)
    rw [hκ.isRegular.lift.cof_ord, Ordinal.cardinalMk_Iio, lift_lift, lift_lt]
    exact lt_ord.mp h

/-- `|V_ κ| = κ` for `κ` inaccessible. -/
theorem card_vonNeumann_ord (hκ : κ.IsInaccessible) : card (V_ κ.ord) = κ := by
  rw [card_vonNeumann]
  refine le_antisymm ?_ (le_preBeth_ord κ)
  rw [preBeth_limit (isSuccLimit_ord hκ.aleph0_lt.le).isSuccPrelimit]
  exact ciSup_le' fun b => (preBeth_lt_of_lt_ord hκ b.2).le

/-- Every member of `V_ κ.ord` has cardinality strictly below `κ`. -/
theorem card_lt_of_mem_vonNeumann (hκ : κ.IsInaccessible) {I : ZFSet.{u}}
    (hI : I ∈ V_ κ.ord) : I.card < κ := by
  have hsub : I ⊆ V_ I.rank := fun z hz =>
    mem_vonNeumann.mpr (rank_le_iff.mp le_rfl hz)
  have hle : I.card ≤ preBeth I.rank := by
    have h := card_mono hsub
    rwa [card_vonNeumann] at h
  exact lt_of_le_of_lt hle (preBeth_lt_of_lt_ord hκ (mem_vonNeumann.mp hI))

/-- **`V_ κ` is an SGA4 Grothendieck universe** (ConLeche's
`IsGrothendieck`) for every inaccessible `κ`. -/
theorem isGrothendieck_vonNeumann (hκ : κ.IsInaccessible) :
    ConLeche.IsGrothendieck (· ∈ ·) (V_ κ.ord) := by
  have hlim : IsSuccLimit κ.ord := isSuccLimit_ord hκ.aleph0_lt.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- transitivity
    intro y z (hy : y ∈ V_ κ.ord) (hz : z ∈ y)
    exact isTransitive_vonNeumann _ y hy hz
  · -- pairing
    intro a b (ha : a ∈ V_ κ.ord) (hb : b ∈ V_ κ.ord)
    refine ⟨{a, b}, ?_, fun _ => mem_pair⟩
    have ha' : a.rank < κ.ord := mem_vonNeumann.mp ha
    have hb' : b.rank < κ.ord := mem_vonNeumann.mp hb
    have hle : ({a, b} : ZFSet.{u}).rank ≤ Order.succ (max a.rank b.rank) := by
      rw [rank_le_iff]
      intro z hz
      rcases mem_pair.mp hz with rfl | rfl
      · exact Order.lt_succ_of_le (le_max_left _ _)
      · exact Order.lt_succ_of_le (le_max_right _ _)
    exact mem_vonNeumann.mpr (lt_of_le_of_lt hle (hlim.succ_lt (max_lt ha' hb')))
  · -- power sets stay inside
    intro y (hy : y ∈ V_ κ.ord)
    refine ⟨powerset y, ?_, fun _ => mem_powerset⟩
    show powerset y ∈ V_ κ.ord
    rw [mem_vonNeumann, rank_powerset]
    exact hlim.succ_lt (mem_vonNeumann.mp hy)
  · -- indexed union over an internal function graph `g : I → V_ κ.ord`
    intro I g (hI : I ∈ V_ κ.ord) hg
    classical
    let F : ZFSet.{u} → ZFSet.{u} := fun i =>
      if hi : i ∈ I then Classical.choose (hg.2 i hi).exists else ∅
    have hF : ∀ i, i ∈ I → F i ∈ V_ κ.ord := fun i hi => by
      dsimp only [F]
      rw [dite_eq_left hi]
      exact (Classical.choose_spec (hg.2 i hi).exists).1
    let w : ZFSet.{u} := ZFSet.sUnion (@ZFSet.image F (Classical.allZFSetDefinable _) I)
    refine ⟨w, ?_, fun z => ?_⟩
    · have hIc : I.card < κ := card_lt_of_mem_vonNeumann hκ hI
      let e : I ≃ Shrink.{u} I := equivShrink _
      let f : Shrink.{u} I → Ordinal.{u} := fun z => (F (e.symm z).1).rank
      have hlt : ⨆ z, f z + 1 < κ.ord :=
        Ordinal.iSup_add_one_lt_of_lt_cof (by rwa [hκ.isRegular.cof_ord]) fun z =>
          mem_vonNeumann.mp (hF _ (e.symm z).2)
      have hrank : w.rank ≤ ⨆ z, f z + 1 := by
        rw [rank_le_iff]
        intro x hx
        obtain ⟨y, hy, hxy⟩ := mem_sUnion.mp hx
        rw [@mem_image F (Classical.allZFSetDefinable _)] at hy
        obtain ⟨i, hi, rfl⟩ := hy
        have hxF : x.rank < (F i).rank := rank_le_iff.mp le_rfl hxy
        have hFi : (F i).rank < ⨆ z, f z + 1 := by
          have := Ordinal.lt_iSup_add_one f (e ⟨i, hi⟩)
          simpa [f, e] using this
        exact hxF.trans hFi
      exact mem_vonNeumann.mpr (lt_of_le_of_lt hrank hlt)
    · dsimp only [w]
      rw [mem_sUnion]
      constructor
      · rintro ⟨y, hy, hzy⟩
        rw [@mem_image F (Classical.allZFSetDefinable _)] at hy
        obtain ⟨i, hi, rfl⟩ := hy
        have hspec := Classical.choose_spec (hg.2 i hi).exists
        have hyU : F i ∈ V_ κ.ord := by
          dsimp only [F]
          rw [dite_eq_left hi]
          exact hspec.1
        have hp : ∃ p, p ∈ g ∧ ConLeche.IsKPair (· ∈ ·) p i (F i) := by
          dsimp only [F]
          rw [dite_eq_left hi]
          exact hspec.2
        obtain ⟨p, hpg, hkp⟩ := hp
        exact ⟨i, F i, p, hi, hyU, hpg, hkp, hzy⟩
      · rintro ⟨i, y, p, hi, hyU, hpg, hkp, hzy⟩
        have hspec : F i ∈ V_ κ.ord ∧ ∃ p, p ∈ g ∧ ConLeche.IsKPair (· ∈ ·) p i (F i) := by
          dsimp only [F]
          rw [dite_eq_left hi]
          exact Classical.choose_spec (hg.2 i hi).exists
        have hy_eq : y = F i :=
          (hg.2 i hi).unique ⟨hyU, p, hpg, hkp⟩ hspec
        refine ⟨F i, ?_, hy_eq ▸ hzy⟩
        rw [@mem_image F (Classical.allZFSetDefinable _)]
        exact ⟨i, hi, rfl⟩

/-! ### Kuratowski pairs on `ZFSet` for Jech choice -/

private def zfKPair (a b : ZFSet.{u}) : ZFSet.{u} := {{a, a}, {a, b}}

private theorem pair_eq_self {a b c : ZFSet.{u}} (h : ({a, b} : ZFSet.{u}) = {c, c}) :
    a = c ∧ b = c := by
  have hmem : ∀ z, z ∈ ({c, c} : ZFSet.{u}) → z = c := fun z hz => by
    rcases mem_pair.mp hz with rfl | rfl <;> rfl
  exact ⟨hmem a (h ▸ mem_pair.mpr (Or.inl rfl)),
         hmem b (h ▸ mem_pair.mpr (Or.inr rfl))⟩

private theorem zfKPair_inj_left {a b c d : ZFSet.{u}}
    (h : zfKPair a b = zfKPair c d) : a = c := by
  have hac : ({a, a} : ZFSet.{u}) ∈ zfKPair c d := h ▸ mem_pair.mpr (Or.inl rfl)
  rcases mem_pair.mp hac with h1 | h1
  · exact (pair_eq_self h1).1
  · exact (pair_eq_self h1.symm).1.symm

private theorem zfKPair_inj {a b c d : ZFSet.{u}}
    (h : zfKPair a b = zfKPair c d) : a = c ∧ b = d := by
  obtain rfl : a = c := zfKPair_inj_left h
  refine ⟨rfl, ?_⟩
  have hb : ({a, b} : ZFSet.{u}) ∈ zfKPair a d := h ▸ mem_pair.mpr (Or.inr rfl)
  have hd : ({a, d} : ZFSet.{u}) ∈ zfKPair a b := h.symm ▸ mem_pair.mpr (Or.inr rfl)
  rcases mem_pair.mp hb with h1 | h1
  · obtain ⟨-, hba⟩ := pair_eq_self h1
    rcases mem_pair.mp hd with h2 | h2
    · obtain ⟨-, hda⟩ := pair_eq_self h2
      exact hba.trans hda.symm
    · rcases mem_pair.mp (h2 ▸ mem_pair.mpr (Or.inr rfl)) with hda | hdb
      · exact hba.trans hda.symm
      · exact hdb.symm
  · rcases mem_pair.mp (h1 ▸ mem_pair.mpr (Or.inr rfl)) with hba | hbd
    · rcases mem_pair.mp (h1.symm ▸ mem_pair.mpr (Or.inr rfl)) with hda | hdb
      · exact hba.trans hda.symm
      · exact hdb.symm
    · exact hbd

private theorem isKPair_zfKPair (a b : ZFSet.{u}) :
    ConLeche.IsKPair (· ∈ ·) (zfKPair a b) a b :=
  ⟨{a, a}, {a, b}, fun _ => mem_pair, fun _ => mem_pair, fun _ => mem_pair⟩

private theorem isKPair_zfKPair_iff {p a b : ZFSet.{u}} :
    ConLeche.IsKPair (· ∈ ·) p a b ↔ p = zfKPair a b := by
  constructor
  · rintro ⟨s, t, hs, ht, hp⟩
    have hs' : s = {a, a} := ZFSet.ext fun z => (hs z).trans mem_pair.symm
    have ht' : t = {a, b} := ZFSet.ext fun z => (ht z).trans mem_pair.symm
    subst hs'; subst ht'
    exact ZFSet.ext fun z => (hp z).trans mem_pair.symm
  · rintro rfl
    exact isKPair_zfKPair a b

/-! ### The `ConLeche.SetTheory` instance on `ZFSet` -/

set_option warn.classDefReducibility false in
/-- ConLeche's set theory on Mathlib's `ZFSet.{u}`, from any strictly
increasing sequence of inaccessibles: the ZFC fields are Mathlib's
(`ZFSet.ext`, pairs, `⋃₀`, `powerset`, `mem_wf`, `image` under
`Classical.allZFSetDefinable`), choice uses `Classical.choose` with
Kuratowski pairs, and `univChain n := V_ (κ n).ord`. -/
noncomputable def setTheoryOfChain (κ : ℕ → Cardinal.{u}) (hmono : StrictMono κ)
    (hinacc : ∀ n, (κ n).IsInaccessible) : ConLeche.SetTheory ZFSet.{u} where
  Mem := (· ∈ ·)
  ext h := ZFSet.ext h
  upair a b := {a, b}
  mem_upair := mem_pair
  sUnion := ZFSet.sUnion
  mem_sUnion := mem_sUnion
  power := powerset
  mem_power := mem_powerset
  regularity x h := by
    obtain ⟨y, hy, hmin⟩ := mem_wf.has_min {y | y ∈ x} h
    exact ⟨y, hy, fun ⟨z, hzy, hzx⟩ => hmin z hzx hzy⟩
  replacement := by
    intro p φ params a h
    classical
    let f : ZFSet.{u} → ZFSet.{u} := fun x =>
      if hx : x ∈ a then Classical.choose (h x hx).exists else ∅
    refine ⟨@ZFSet.image f (Classical.allZFSetDefinable _) a, fun z => ?_⟩
    rw [@mem_image f (Classical.allZFSetDefinable _)]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      dsimp only [f]
      rw [dite_eq_left hx]
      exact Classical.choose_spec (h x hx).exists
    · rintro ⟨x, hx, hφ⟩
      refine ⟨x, hx, ?_⟩
      dsimp only [f]
      rw [dite_eq_left hx]
      exact (h x hx).unique (Classical.choose_spec (h x hx).exists) hφ
  choice := by
    intro x h
    classical
    let F : ZFSet.{u} → ZFSet.{u} := fun a =>
      if ha : a ∈ x then zfKPair a (Classical.choose (h a ha)) else ∅
    refine ⟨@ZFSet.image F (Classical.allZFSetDefinable _) x, ?_, ?_⟩
    · intro p hp
      rw [@mem_image F (Classical.allZFSetDefinable _)] at hp
      obtain ⟨a, ha, rfl⟩ := hp
      dsimp only [F]
      rw [dite_eq_left ha]
      exact ⟨a, Classical.choose (h a ha), ha, Classical.choose_spec (h a ha),
        isKPair_zfKPair a _⟩
    · intro a ha
      refine ⟨Classical.choose (h a ha), ⟨Classical.choose_spec (h a ha),
        zfKPair a (Classical.choose (h a ha)), ?_, isKPair_zfKPair a _⟩, ?_⟩
      · dsimp only; rw [@mem_image F (Classical.allZFSetDefinable _)]
        refine ⟨a, ha, ?_⟩
        dsimp only [F]
        rw [dite_eq_left ha]
      · rintro y ⟨_, p, hp, hkp⟩
        rw [@mem_image F (Classical.allZFSetDefinable _)] at hp
        obtain ⟨a', ha', rfl⟩ := hp
        dsimp only [F] at hkp
        rw [dite_eq_left ha'] at hkp
        rw [isKPair_zfKPair_iff] at hkp
        obtain ⟨rfl, hy⟩ := zfKPair_inj hkp; exact hy.symm
  univChain n := V_ (κ n).ord
  univChain_mem n := vonNeumann_mem_of_lt (ord_lt_ord.mpr (hmono (Nat.lt_succ_self n)))
  univChain_grothendieck n := isGrothendieck_vonNeumann (hinacc n)

set_option warn.classDefReducibility false in
/-- ConLeche's set theory on `ZFSet.{u}` under Carneiro's hypothesis. -/
noncomputable def setTheoryOfCarneiro (h : OmegaInaccessibles.{u}) : ConLeche.SetTheory ZFSet.{u} :=
  setTheoryOfChain (Classical.choose h) (Classical.choose_spec h).1 (Classical.choose_spec h).2

/-- **Carneiro's hypothesis implies ConLeche's.**  `ω` strongly inaccessible
cardinals (lean4lean-model's `OmegaInaccessibles`) give a model of
ConLeche's `SetTheory` interface — on Mathlib's `ZFSet.{u}`, with the
universe chain `V_ (κ n).ord`. -/
theorem carneiro_implies_conleche :
    OmegaInaccessibles.{u} → Nonempty (Σ V : Type (u + 1), ConLeche.SetTheory V) :=
  fun h => ⟨⟨ZFSet.{u}, setTheoryOfCarneiro h⟩⟩

/--
info: 'ConLecheBridge.carneiro_implies_conleche' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms carneiro_implies_conleche

end ConLecheBridge
