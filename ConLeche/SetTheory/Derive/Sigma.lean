module

public import ConLeche.SetTheory.Derive.Univ

@[expose] public section

/-!
# Dependent pairs, with the level-0 truncation

`sigmaSet w A B h` is, for `w ≠ 0`, the raw pair set `sigmaPairs A B h`
(Kuratowski pairs `⟨a, b⟩` with `a ∈ A`, `b ∈ B a`); for `w = 0` the
truth value `[∃ a ∈ A, B a inhabited]` (the `Prop` collapse).

`spair` is the Kuratowski pair; `sfst`/`ssnd` extract the components
classically (well-defined by `kpair_inj`) and default to `pt` on
non-pairs — in particular on `pt` itself, which is never a pair, so
`sfst pt = ssnd pt = pt` holds by the tag.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

open Classical in
/-- Proof-carrying dependent pair set at level `w` (see module docs). -/
noncomputable def sigmaSet (w : Nat) (A : V) (B : V → V) (h : HasSigmaPairs A B) : V :=
  if w = 0 then truthVal (∃ x, x ∈ˢ A ∧ ∃ y, y ∈ˢ B x) else sigmaPairs A B h

/-- Pairing: the Kuratowski pair. -/
noncomputable def spair (a b : V) : V := kpair a b

open Classical in
/-- First projection, `pt` on non-pairs. -/
noncomputable def sfst (p : V) : V :=
  if h : ∃ a b, p = kpair a b then Classical.choose h else pt

open Classical in
/-- Second projection, `pt` on non-pairs. -/
noncomputable def ssnd (p : V) : V :=
  if h : ∃ a b, p = kpair a b then Classical.choose (Classical.choose_spec h)
  else pt

theorem sigmaSet_zero {A : V} {B : V → V} {h : HasSigmaPairs A B} :
    sigmaSet 0 A B h = truthVal (∃ x, x ∈ˢ A ∧ ∃ y, y ∈ˢ B x) := by
  unfold sigmaSet; exact ite_eq_left rfl

theorem sigmaSet_pos {w : Nat} (hw : w ≠ 0) {A : V} {B : V → V} {h : HasSigmaPairs A B} :
    sigmaSet w A B h = sigmaPairs A B h := by
  unfold sigmaSet; exact ite_eq_right hw

theorem sigmaSet_congr {w : Nat} {A : V} {B B' : V → V}
    (hB : HasSigmaPairs A B) (hB' : HasSigmaPairs A B')
    (h : ∀ x, x ∈ˢ A → B x = B' x) :
    sigmaSet w A B hB = sigmaSet w A B' hB' := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [sigmaSet_zero, sigmaSet_zero]
    refine truthVal_congr ⟨?_, ?_⟩
    · rintro ⟨x, hx, y, hy⟩; exact ⟨x, hx, y, h x hx ▸ hy⟩
    · rintro ⟨x, hx, y, hy⟩; exact ⟨x, hx, y, (h x hx).symm ▸ hy⟩
  · rw [sigmaSet_pos (Nat.pos_iff_ne_zero.mp hw), sigmaSet_pos (Nat.pos_iff_ne_zero.mp hw)]
    exact sigmaPairs_congr hB hB' h

theorem sigma_congr {w : Nat} {A : V} {B B' : V → V}
    {hB : HasSigmaPairs A B} {hB' : HasSigmaPairs A B'}
    (h : ∀ x, x ∈ˢ A → B x = B' x) : sigmaSet w A B hB = sigmaSet w A B' hB' :=
  sigmaSet_congr hB hB' h

theorem sigmaSet_ext {w : Nat} {A A' : V} {B B' : V → V} (hA : A = A')
    (hB : HasSigmaPairs A B) (hB' : HasSigmaPairs A' B')
    (h : ∀ x, x ∈ˢ A → B x = B' x) :
    sigmaSet w A B hB = sigmaSet w A' B' hB' := by
  subst hA
  exact sigmaSet_congr hB hB' h

theorem sigmaSet_level_congr {w w' : Nat} (hw : w = 0 ↔ w' = 0)
    {A : V} {B : V → V} (hB : HasSigmaPairs A B) :
    sigmaSet w A B hB = sigmaSet w' A B hB := by
  by_cases h0 : w = 0
  · have h0' : w' = 0 := hw.mp h0
    subst h0; subst h0'; rfl
  · have h0' : w' ≠ 0 := fun h => h0 (hw.mpr h)
    rw [sigmaSet_pos h0, sigmaSet_pos h0']

theorem spair_mem {w : Nat} {A : V} {B : V → V} {h : HasSigmaPairs A B} {a b : V}
    (hw : w ≠ 0) (ha : a ∈ˢ A) (hb : b ∈ˢ B a) : spair a b ∈ˢ sigmaSet w A B h := by
  rw [sigmaSet_pos hw]
  exact mem_sigmaPairs.mpr ⟨a, ha, b, hb, rfl⟩

theorem pt_mem_sigma {A : V} {B : V → V} {h : HasSigmaPairs A B} {a b : V}
    (ha : a ∈ˢ A) (hb : b ∈ˢ B a) : (pt : V) ∈ˢ sigmaSet 0 A B h := by
  rw [sigmaSet_zero]
  exact pt_mem_truthVal ⟨a, ha, b, hb⟩

theorem mem_sigma_elim {w : Nat} {A : V} {B : V → V} {h : HasSigmaPairs A B} {t : V}
    (ht : t ∈ˢ sigmaSet w A B h) :
    ∃ a b, a ∈ˢ A ∧ b ∈ˢ B a ∧ (w = 0 → t = pt) ∧ (w ≠ 0 → t = spair a b) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [sigmaSet_zero] at ht
    obtain ⟨a, ha, b, hb⟩ := of_mem_truthVal ht
    exact ⟨a, b, ha, hb, fun _ => eq_pt_of_mem_truthVal ht, fun h0 => absurd rfl h0⟩
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    rw [sigmaSet_pos hw'] at ht
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sigmaPairs.mp ht
    exact ⟨a, b, ha, hb, fun h0 => absurd h0 hw', fun _ => rfl⟩

theorem sfst_spair (a b : V) : sfst (spair a b) = a := by
  unfold sfst spair
  rw [dite_eq_left ⟨a, b, rfl⟩]
  have hs := Classical.choose_spec
    (⟨a, b, rfl⟩ : ∃ a' b', (kpair a b : V) = kpair a' b')
  have hs2 := Classical.choose_spec hs
  exact (kpair_inj hs2).1.symm

theorem ssnd_spair (a b : V) : ssnd (spair a b) = b := by
  unfold ssnd spair
  rw [dite_eq_left ⟨a, b, rfl⟩]
  have hs := Classical.choose_spec
    (⟨a, b, rfl⟩ : ∃ a' b', (kpair a b : V) = kpair a' b')
  have hs2 := Classical.choose_spec hs
  exact (kpair_inj hs2).2.symm

theorem spair_eq_kpair (a b : V) : spair a b = kpair a b := by unfold spair; rfl

theorem spair_inj {a b c d : V} (h : spair a b = spair c d) : a = c ∧ b = d := by
  rw [spair_eq_kpair, spair_eq_kpair] at h
  exact kpair_inj h

theorem spair_ne_pt (a b : V) : spair a b ≠ (pt : V) := by
  rw [spair_eq_kpair]
  exact fun h => pt_ne_kpair a b h.symm

theorem sfst_kpair (a b : V) : sfst (kpair a b) = a := by rw [← spair_eq_kpair]; exact sfst_spair a b
theorem ssnd_kpair (a b : V) : ssnd (kpair a b) = b := by rw [← spair_eq_kpair]; exact ssnd_spair a b

theorem sfst_pt : sfst (pt : V) = pt := by
  unfold sfst
  rw [dite_eq_right]
  rintro ⟨a, b, h⟩
  exact pt_ne_kpair a b h

theorem ssnd_pt : ssnd (pt : V) = pt := by
  unfold ssnd
  rw [dite_eq_right]
  rintro ⟨a, b, h⟩
  exact pt_ne_kpair a b h

theorem empty_ne_kpair (a b : V) : (empty : V) ≠ kpair a b := by
  intro h
  have hs : sing a ∈ˢ kpair a b := mem_upair_left (sing a) (upair a b)
  rw [← h] at hs
  exact not_mem_empty _ hs

theorem sfst_empty : sfst (empty : V) = pt := by
  unfold sfst
  rw [dite_eq_right]
  rintro ⟨a, b, h⟩
  exact empty_ne_kpair a b h

theorem ssnd_empty : ssnd (empty : V) = pt := by
  unfold ssnd
  rw [dite_eq_right]
  rintro ⟨a, b, h⟩
  exact empty_ne_kpair a b h

theorem sfst_mem_sigma_pos {w : Nat} (hw : w ≠ 0) {A : V} {B : V → V}
    {h : HasSigmaPairs A B} {p : V} (hp : p ∈ˢ sigmaSet w A B h) : sfst p ∈ˢ A := by
  obtain ⟨a, _, ha, _, _, hpos⟩ := mem_sigma_elim hp
  rw [hpos hw, sfst_spair]
  exact ha

theorem ssnd_mem_sigma_pos {w : Nat} (hw : w ≠ 0) {A : V} {B : V → V}
    {h : HasSigmaPairs A B} {p : V} (hp : p ∈ˢ sigmaSet w A B h) : ssnd p ∈ˢ B (sfst p) := by
  obtain ⟨_, _, _, hb, _, hpos⟩ := mem_sigma_elim hp
  rw [hpos hw, sfst_spair, ssnd_spair]
  exact hb

theorem spair_sfst_ssnd_of_mem_pos {w : Nat} (hw : w ≠ 0) {A : V} {B : V → V}
    {h : HasSigmaPairs A B} {p : V} (hp : p ∈ˢ sigmaSet w A B h) :
    spair (sfst p) (ssnd p) = p := by
  obtain ⟨_, _, _, _, _, hpos⟩ := mem_sigma_elim hp
  rw [hpos hw, sfst_spair, ssnd_spair]

/-- Formation along the tower, at the joint level `max u v`, from the
size bounds alone: above `0` a pair set is strict (task #342). -/
theorem sigma_mem_univ_tg {u v : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ (tg u : V)) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (tg v : V))
    (hS : HasSigmaPairs A B) :
    sigmaSet (Nat.max u v) A B hS ∈ˢ (univ (Nat.max u v) : V) := by
  rcases Nat.eq_zero_or_pos (Nat.max u v) with hw | hw
  · rw [hw, sigmaSet_zero, univ_zero]
    exact truthVal_mem_univZero _
  · have hw' : Nat.max u v ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    rw [sigmaSet_pos hw']
    exact mem_univ_of_tg_strict ((tg_isGrothendieck hw').sigmaPairs_mem
      (tg_mono (Nat.le_max_left u v) A hA)
      (fun x hx => tg_mono (Nat.le_max_right u v) _ (hB x hx)) hS)
      strict_sigmaPairs

/-- Formation along the tower, at the joint level `max u v`. -/
theorem sigma_mem_univ {u v : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ (univ u : V)) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ v : V))
    (hS : HasSigmaPairs A B) :
    sigmaSet (Nat.max u v) A B hS ∈ˢ (univ (Nat.max u v) : V) :=
  sigma_mem_univ_tg (mem_tg_of_mem_univ hA) (fun x hx => mem_tg_of_mem_univ (hB x hx)) hS

/-- A pair set is in the regime of its level: a truth value at `0`,
strict above (task #342, L6). -/
theorem Fib_sigmaSet (w : Nat) (A : V) (B : V → V) {h : HasSigmaPairs A B} :
    Fib (decide (w = 0)) (sigmaSet w A B h) := by
  by_cases hw : w = 0
  · subst hw
    simp only [decide_true, Fib_true]
    rw [sigmaSet_zero]; exact truthVal_mem_univZero _
  · simp only [hw, decide_false, Fib_false]
    rw [sigmaSet_pos hw]; exact strict_sigmaPairs

theorem IsTy_sigmaSet (w : Nat) (A : V) (B : V → V) {h : HasSigmaPairs A B} :
    IsTy (sigmaSet w A B h) :=
  IsTy_of_Fib (Fib_sigmaSet w A B)

theorem sigmaSet_ne_pt {w : Nat} {A : V} {B : V → V} {h : HasSigmaPairs A B} :
    sigmaSet w A B h ≠ (pt : V) :=
  (IsTy_sigmaSet w A B).ne_pt

theorem pt_not_mem_sigmaSet_pos {w : Nat} (hw : w ≠ 0) {A : V} {B : V → V}
    {h : HasSigmaPairs A B} : ¬ (pt : V) ∈ˢ sigmaSet w A B h := by
  rw [sigmaSet_pos hw]
  exact strict_sigmaPairs.2

/-! ## The unit at a level (task #342, items B and C)

`PUnit.{w}` and the pair towers' terminator.  At `0` the unit is the
truth value `True = {pt}` with its proof `pt`; above `0` it is `{∅}`
with the member `∅` — a set that is neither the proof point nor
contains it, so it is strict (a member of the strict universe, and so
a type of every positive sort).  Nothing reads the terminator's member: `∅` is
no Kuratowski pair, so `sfst ∅ = ssnd ∅ = pt` by the non-pair default,
exactly as at `pt`. -/

open Classical in
/-- The unit type at level `w` (see the section docstring). -/
noncomputable def unitSetAt (w : Nat) : V := if w = 0 then unitSet else sing empty

open Classical in
/-- The unit type's sole member at level `w`. -/
noncomputable def unitAt (w : Nat) : V := if w = 0 then pt else empty

theorem unitSetAt_zero : (unitSetAt 0 : V) = unitSet := ite_eq_left rfl
theorem unitSetAt_pos {w : Nat} (hw : w ≠ 0) : (unitSetAt w : V) = sing empty := ite_eq_right hw
theorem unitAt_zero : (unitAt 0 : V) = pt := ite_eq_left rfl
theorem unitAt_pos {w : Nat} (hw : w ≠ 0) : (unitAt w : V) = empty := ite_eq_right hw

theorem mem_unitSetAt_iff {w : Nat} {z : V} : z ∈ˢ (unitSetAt w : V) ↔ z = unitAt w := by
  by_cases hw : w = 0
  · subst hw; rw [unitSetAt_zero, unitAt_zero]; exact mem_unitSet_iff
  · rw [unitSetAt_pos hw, unitAt_pos hw]; exact mem_sing

theorem unitAt_mem_unitSetAt (w : Nat) : (unitAt w : V) ∈ˢ unitSetAt w :=
  mem_unitSetAt_iff.mpr rfl

/-- `{∅}` is strict: it is not the point (whose one member is `ptTag`,
not `∅`), and its one member `∅` is not the point. -/
theorem strict_sing_empty : Strict (sing empty : V) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : (empty : V) = ptTag := mem_pt.mp (h ▸ mem_sing.mpr rfl)
    have h2 := empty_mem_ptTag (V := V)
    rw [← h1] at h2
    exact not_mem_empty _ h2
  · exact pt_ne_empty (mem_sing.mp h)

theorem unitSetAt_mem_univ : ∀ w : Nat, (unitSetAt w : V) ∈ˢ univ w
  | 0 => unitSetAt_zero (V := V) ▸ unitSet_mem_univ 0
  | n + 1 => by
    rw [unitSetAt_pos (Nat.succ_ne_zero n)]
    exact mem_univ_of_tg_strict ((tg_isGrothendieck (Nat.succ_ne_zero n)).sing_mem
      (empty_mem_tg _)) strict_sing_empty

/-- The unit is in the regime of its level: `{pt}` at `0`, strict
above (task #342, L6). -/
theorem Fib_unitSetAt (w : Nat) : Fib (decide (w = 0)) (unitSetAt w : V) := by
  by_cases hw : w = 0
  · subst hw
    simp only [decide_true, Fib_true]
    rw [unitSetAt_zero, ← univ_zero]; exact unitSet_mem_univ 0
  · simp only [hw, decide_false, Fib_false]
    rw [unitSetAt_pos hw]; exact strict_sing_empty

theorem IsTy_unitSetAt (w : Nat) : IsTy (unitSetAt w : V) :=
  IsTy_of_Fib (Fib_unitSetAt w)

/-! ## First-order definability closure -/

theorem DefFun.spair_apply {k : Nat} {A B : (Fin k → V) → V}
    (hA : DefFun k A) (hB : DefFun k B) :
    DefFun k fun env => spair (A env) (B env) := by
  unfold spair
  exact DefFun.kpair_apply hA hB

private theorem sfst_base : DefFun (V := V) 1 fun v => sfst (v 0) := by
  have hisPair : DefRel (V := V) 2 fun v => ∃ a b, v 1 = kpair a b :=
    DefRel.exists_curry (DefRel.exists_curry
      (DefRel.eq_apply (DefFun.proj 3) (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0))))
  have hfst : DefRel (V := V) 2 fun v => ∃ a b, v 1 = kpair a b ∧ v 0 = a :=
    DefRel.exists_curry (DefRel.exists_curry
      (DefRel.and
        (DefRel.eq_apply (DefFun.proj 3) (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0)))
        (DefRel.eq_apply (DefFun.proj 2) (DefFun.proj 1))))
  have hrel : DefRel (V := V) 2 fun v =>
      (∃ a b, v 1 = kpair a b ∧ v 0 = a) ∨ ((¬ ∃ a b, v 1 = kpair a b) ∧ v 0 = pt) :=
    hfst.or (hisPair.not.and (DefRel.eq_apply (DefFun.proj 0) DefFun.pt))
  refine hrel.congr fun v => ?_
  change _ ↔ v 0 = sfst (v 1)
  constructor
  · rintro (⟨a, b, hkp, hy⟩ | ⟨hnp, hy⟩)
    · rw [hy, hkp, sfst_kpair]
    · unfold sfst
      rw [dite_eq_right hnp]
      exact hy
  · intro heq
    by_cases h : ∃ a b, v 1 = kpair a b
    · have hspec := Classical.choose_spec (Classical.choose_spec h)
      have hval : sfst (v 1) = Classical.choose h := by
        unfold sfst; exact dite_eq_left h
      exact Or.inl ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
        hspec, heq.trans hval⟩
    · have hval : sfst (v 1) = pt := by
        unfold sfst; exact dite_eq_right h
      exact Or.inr ⟨h, heq.trans hval⟩

theorem DefFun.sfst_apply {k : Nat} {P : (Fin k → V) → V} (hP : DefFun k P) :
    DefFun k fun env => sfst (P env) :=
  DefFun.comp1 (sfst_base (V := V)) hP

private theorem ssnd_base : DefFun (V := V) 1 fun v => ssnd (v 0) := by
  have hisPair : DefRel (V := V) 2 fun v => ∃ a b, v 1 = kpair a b :=
    DefRel.exists_curry (DefRel.exists_curry
      (DefRel.eq_apply (DefFun.proj 3) (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0))))
  have hsnd : DefRel (V := V) 2 fun v => ∃ a b, v 1 = kpair a b ∧ v 0 = b :=
    DefRel.exists_curry (DefRel.exists_curry
      (DefRel.and
        (DefRel.eq_apply (DefFun.proj 3) (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0)))
        (DefRel.eq_apply (DefFun.proj 2) (DefFun.proj 0))))
  have hrel : DefRel (V := V) 2 fun v =>
      (∃ a b, v 1 = kpair a b ∧ v 0 = b) ∨ ((¬ ∃ a b, v 1 = kpair a b) ∧ v 0 = pt) :=
    hsnd.or (hisPair.not.and (DefRel.eq_apply (DefFun.proj 0) DefFun.pt))
  refine hrel.congr fun v => ?_
  change _ ↔ v 0 = ssnd (v 1)
  constructor
  · rintro (⟨a, b, hkp, hy⟩ | ⟨hnp, hy⟩)
    · rw [hy, hkp, ssnd_kpair]
    · unfold ssnd
      rw [dite_eq_right hnp]
      exact hy
  · intro heq
    by_cases h : ∃ a b, v 1 = kpair a b
    · have hspec := Classical.choose_spec (Classical.choose_spec h)
      have hval : ssnd (v 1) = Classical.choose (Classical.choose_spec h) := by
        unfold ssnd; exact dite_eq_left h
      exact Or.inl ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
        hspec, heq.trans hval⟩
    · have hval : ssnd (v 1) = pt := by
        unfold ssnd; exact dite_eq_right h
      exact Or.inr ⟨h, heq.trans hval⟩

theorem DefFun.ssnd_apply {k : Nat} {P : (Fin k → V) → V} (hP : DefFun k P) :
    DefFun k fun env => ssnd (P env) :=
  DefFun.comp1 (ssnd_base (V := V)) hP

theorem DefFun.sigmaSet_apply {k : Nat} (w : Nat)
    {A : (Fin k → V) → V} {B : (Fin (k + 1) → V) → V}
    {h : ∀ env, HasSigmaPairs (A env) (fun x => B (fcons x env))}
    (hA : DefFun k A) (hB : DefFun (k + 1) B) :
    DefFun k fun env => sigmaSet w (A env) (fun x => B (fcons x env)) (h env) := by
  by_cases hw : w = 0
  · subst hw
    have hrel : DefRel k fun env => ∃ x, x ∈ˢ A env ∧ ∃ y, y ∈ˢ B (fcons x env) :=
      (DefRel.bExists hA (DefRel.exists_ (DefRel.mem_apply (DefFun.proj 0) hB.weaken))).congr
        fun env => by simp only [fcons_zero, ftail_fcons]
    refine (DefFun.truthVal_apply hrel).congr fun env => ?_
    exact (sigmaSet_zero (h := h env)).symm
  · refine (DefFun.sigmaPairs_apply hA hB (h := h)).congr fun env => ?_
    exact (sigmaSet_pos hw (h := h env)).symm

theorem DefFun.sigmaSet_apply_curry {k : Nat} (w : Nat)
    {A : (Fin k → V) → V} {B : V → (Fin k → V) → V}
    {h : ∀ env, HasSigmaPairs (A env) (fun x => B x env)}
    (hA : DefFun k A) (hB : DefFun (k + 1) fun v => B (v 0) (ftail v)) :
    DefFun k fun env => sigmaSet w (A env) (fun x => B x env) (h env) :=
  DefFun.sigmaSet_apply w (B := fun v => B (v 0) (ftail v)) hA hB

theorem DefFun.unitSetAt_const {k : Nat} (w : Nat) :
    DefFun k fun _ => (unitSetAt w : V) :=
  DefFun.const (unitSetAt w)

theorem DefFun.unitAt_const {k : Nat} (w : Nat) :
    DefFun k fun _ => (unitAt w : V) :=
  DefFun.const (unitAt w)

attribute [irreducible] sigmaSet spair sfst ssnd

end ConLeche.SetTheory
