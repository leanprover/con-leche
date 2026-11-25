module

public import ConLeche.SetTheory.Derive.Univ

@[expose] public section

/-!
# Quotients

`quotSet u A R` is, for `u ≠ 0`, the set of equivalence classes of the
first-order equivalence closure `QuotRel A R` of "`app (app R a) b` is
inhabited" on `A` (defined as the bounded intersection of all equivalence
relations `E ∈ˢ power (prod A A)` containing the base relation on `A`;
classes by proof-carrying `sep`, the class set by proof-carrying `image`),
each class **tagged** as the pair `kpair ∅ (qclass A R a)` (task #342:
a raw class can be the point, see the end of the file; a tagged one is a
pair, so the quotient is strict); for `u = 0` the base lives in `Prop`,
everything collapses to the proof point, and the quotient is
`image (fun _ => pt) A h` — the truth value `[A inhabited]`.

`qrep` is retired: downstream lifts (`quotLiftR`, `SetModel/Value.lean`)
use a choice-free bounded separation graph over the quotient and `B`.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- An equivalence relation `E ⊆ A × A` on `A`. -/
def IsEquivRelOn (A E : V) : Prop :=
  E ⊆ˢ prod A A ∧
  (∀ x, x ∈ˢ A → kpair x x ∈ˢ E) ∧
  (∀ x y, x ∈ˢ A → y ∈ˢ A → kpair x y ∈ˢ E → kpair y x ∈ˢ E) ∧
  (∀ x y z, x ∈ˢ A → y ∈ˢ A → z ∈ˢ A →
    kpair x y ∈ˢ E → kpair y z ∈ˢ E → kpair x z ∈ˢ E)

theorem defRel_isEquivRelOn_apply {k : Nat} {A E : (Fin k → V) → V}
    (hA : DefFun k A) (hE : DefFun k E) :
    DefRel k fun env => IsEquivRelOn (A env) (E env) := by
  unfold IsEquivRelOn
  refine DefRel.and ?_ (DefRel.and ?_ (DefRel.and ?_ ?_))
  · exact DefRel.subset_apply hE (DefFun.prod_apply hA hA)
  · exact DefRel.bForall_curry hA
      (DefRel.mem_apply (DefFun.kpair_apply (DefFun.proj 0) (DefFun.proj 0)) hE.weaken)
  · refine DefRel.forall_curry (DefRel.forall_curry
      (DefRel.imp (DefRel.mem_apply (DefFun.proj 1) hA.weaken.weaken)
        (DefRel.imp (DefRel.mem_apply (DefFun.proj 0) hA.weaken.weaken)
          (DefRel.imp ?_ ?_))))
    · exact DefRel.mem_apply
        (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0)) hE.weaken.weaken
    · exact DefRel.mem_apply
        (DefFun.kpair_apply (DefFun.proj 0) (DefFun.proj 1)) hE.weaken.weaken
  · refine DefRel.forall_curry (DefRel.forall_curry (DefRel.forall_curry
      (DefRel.imp (DefRel.mem_apply (DefFun.proj 2) hA.weaken.weaken.weaken)
        (DefRel.imp (DefRel.mem_apply (DefFun.proj 1) hA.weaken.weaken.weaken)
          (DefRel.imp (DefRel.mem_apply (DefFun.proj 0) hA.weaken.weaken.weaken)
            (DefRel.imp ?_ (DefRel.imp ?_ ?_)))))))
    · exact DefRel.mem_apply
        (DefFun.kpair_apply (DefFun.proj 2) (DefFun.proj 1)) hE.weaken.weaken.weaken
    · exact DefRel.mem_apply
        (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0)) hE.weaken.weaken.weaken
    · exact DefRel.mem_apply
        (DefFun.kpair_apply (DefFun.proj 2) (DefFun.proj 0)) hE.weaken.weaken.weaken

theorem DefRel.isEquivRelOn_apply {k : Nat} {A E : (Fin k → V) → V}
    (hA : DefFun k A) (hE : DefFun k E) :
    DefRel k fun env => IsEquivRelOn (A env) (E env) :=
  defRel_isEquivRelOn_apply hA hE

/-- The equivalence closure, on `A`, of "`app (app R a) b` is
inhabited", defined by bounded intersection over `power (prod A A)`. -/
def QuotRel (A R a b : V) : Prop :=
  a ∈ˢ A ∧ b ∈ˢ A ∧
  ∀ E, E ∈ˢ power (prod A A) → IsEquivRelOn A E →
    (∀ x y, x ∈ˢ A → y ∈ˢ A → (∃ w, w ∈ˢ app (app R x) y) → kpair x y ∈ˢ E) →
    kpair a b ∈ˢ E

theorem defRel_quotRel_apply {k : Nat} {A R a b : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) (ha : DefFun k a) (hb : DefFun k b) :
    DefRel k fun env => QuotRel (A env) (R env) (a env) (b env) := by
  unfold QuotRel
  refine DefRel.and (DefRel.mem_apply ha hA)
    (DefRel.and (DefRel.mem_apply hb hA) ?_)
  refine DefRel.bForall_curry (DefFun.power_apply (DefFun.prod_apply hA hA))
    (DefRel.imp (defRel_isEquivRelOn_apply hA.weaken (DefFun.proj 0))
      (DefRel.imp ?_ ?_))
  · refine DefRel.forall_curry (DefRel.forall_curry
      (DefRel.imp (DefRel.mem_apply (DefFun.proj 1) hA.weaken.weaken.weaken)
        (DefRel.imp (DefRel.mem_apply (DefFun.proj 0) hA.weaken.weaken.weaken)
          (DefRel.imp ?_ ?_))))
    · refine DefRel.exists_curry (DefRel.mem_apply (DefFun.proj 0) ?_)
      exact DefFun.app_apply
        (DefFun.app_apply hR.weaken.weaken.weaken.weaken (DefFun.proj 2))
        (DefFun.proj 1)
    · exact DefRel.mem_apply
        (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0))
        (DefFun.proj 2)
  · exact DefRel.mem_apply
      (DefFun.kpair_apply ha.weaken hb.weaken)
      (DefFun.proj 0)

theorem DefRel.quotRel_apply {k : Nat} {A R a b : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) (ha : DefFun k a) (hb : DefFun k b) :
    DefRel k fun env => QuotRel (A env) (R env) (a env) (b env) :=
  defRel_quotRel_apply hA hR ha hb

theorem QuotRel.mem_left {A R a b : V} (h : QuotRel A R a b) : a ∈ˢ A := h.1

theorem QuotRel.mem_right {A R a b : V} (h : QuotRel A R a b) : b ∈ˢ A := h.2.1

theorem QuotRel.base {A R a b : V} (ha : a ∈ˢ A) (hb : b ∈ˢ A)
    (hw : ∃ w, w ∈ˢ app (app R a) b) : QuotRel A R a b :=
  ⟨ha, hb, fun _ _ _ hbase => hbase a b ha hb hw⟩

theorem QuotRel.refl {A R a : V} (ha : a ∈ˢ A) : QuotRel A R a a :=
  ⟨ha, ha, fun _ _ heq _ => heq.2.1 a ha⟩

theorem QuotRel.symm {A R a b : V} (h : QuotRel A R a b) : QuotRel A R b a :=
  ⟨h.2.1, h.1, fun E hE heq hbase =>
    heq.2.2.1 a b h.1 h.2.1 (h.2.2 E hE heq hbase)⟩

theorem QuotRel.trans {A R a b c : V} (h₁ : QuotRel A R a b)
    (h₂ : QuotRel A R b c) : QuotRel A R a c :=
  ⟨h₁.1, h₂.2.1, fun E hE heq hbase =>
    heq.2.2.2 a b c h₁.1 h₁.2.1 h₂.2.1
      (h₁.2.2 E hE heq hbase) (h₂.2.2 E hE heq hbase)⟩

theorem hasSep_qclass (A R a : V) : HasSep A (fun b => QuotRel A R a b) :=
  hasSep_of_defPred
    (defRel_quotRel_apply (DefFun.const A) (DefFun.const R) (DefFun.const a) (DefFun.proj 0))

/-- The `QuotRel`-class of `a` in `A`. -/
noncomputable def qclass (A R a : V) : V :=
  sep A (fun b => QuotRel A R a b) (hasSep_qclass A R a)

theorem defFun_qclass_apply {k : Nat} {A R a : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) (ha : DefFun k a) :
    DefFun k fun env => qclass (A env) (R env) (a env) := by
  unfold qclass
  exact DefFun.sep_apply_curry hA
    (defRel_quotRel_apply hA.weaken hR.weaken ha.weaken (DefFun.proj 0))

theorem DefFun.qclass_apply {k : Nat} {A R a : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) (ha : DefFun k a) :
    DefFun k fun env => qclass (A env) (R env) (a env) :=
  defFun_qclass_apply hA hR ha

theorem mem_qclass {A R a b : V} :
    b ∈ˢ qclass A R a ↔ b ∈ˢ A ∧ QuotRel A R a b := mem_sep

theorem qclass_subset {A R a : V} : qclass A R a ⊆ˢ A := sep_subset

theorem qclass_mem_tg {u : Nat} {A R a : V} (hA : A ∈ˢ tg u) :
    qclass A R a ∈ˢ tg u := by
  by_cases hu : u = 0
  · subst hu
    rw [tg_zero] at hA ⊢
    exact mem_univZero.mpr (qclass_subset.trans (mem_univZero.mp hA))
  · exact (tg_isGrothendieck hu).mem_of_subset_mem hA qclass_subset

theorem self_mem_qclass {A R a : V} (ha : a ∈ˢ A) : a ∈ˢ qclass A R a :=
  mem_qclass.mpr ⟨ha, QuotRel.refl ha⟩

theorem qclass_eq_of_rel {A R a b : V} (h : QuotRel A R a b) :
    qclass A R a = qclass A R b :=
  ext fun z => by
    rw [mem_qclass, mem_qclass]
    exact ⟨fun ⟨hz, hr⟩ => ⟨hz, (h.symm).trans hr⟩,
           fun ⟨hz, hr⟩ => ⟨hz, h.trans hr⟩⟩

theorem rel_of_qclass_eq {A R a b : V} (ha : a ∈ˢ A) (_hb : b ∈ˢ A)
    (h : qclass A R a = qclass A R b) : QuotRel A R a b :=
  (mem_qclass.mp (h ▸ self_mem_qclass ha)).2.symm

theorem hasImage_const_pt (A : V) : HasImage (fun _ => (pt : V)) A :=
  hasImage_of_defFun1 DefFun.pt A

theorem hasImage_quotClass_pos (A R : V) :
    HasImage (fun a => kpair empty (qclass A R a)) A :=
  hasImage_of_defFun1 (f := fun a => kpair empty (qclass A R a))
    (DefFun.kpair_apply DefFun.empty
      (defFun_qclass_apply (DefFun.const A) (DefFun.const R) (DefFun.proj 0)))
    A

open Classical in
/-- The quotient (see module docs). -/
noncomputable def quotSet (u : Nat) (A R : V) : V :=
  if u = 0 then image (fun _ => pt) A (hasImage_const_pt A)
  else image (fun a => kpair empty (qclass A R a)) A (hasImage_quotClass_pos A R)

open Classical in
/-- The class of `a` in the quotient: at `u ≠ 0` the `QuotRel`-class,
tagged as a pair (`kpair ∅ ·`; `sing` would not do, as the class can be
`ptTag` itself and `sing ptTag = pt`). -/
noncomputable def quotClass (u : Nat) (A R a : V) : V :=
  if u = 0 then pt else kpair empty (qclass A R a)

theorem defFun_quotClass_apply {k : Nat} (u : Nat) {A R a : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) (ha : DefFun k a) :
    DefFun k fun env => quotClass u (A env) (R env) (a env) := by
  unfold quotClass
  by_cases hu : u = 0
  · simp only [hu, ↓reduceIte]
    exact DefFun.pt
  · simp only [hu, ↓reduceIte]
    exact DefFun.kpair_apply DefFun.empty (defFun_qclass_apply hA hR ha)

theorem DefFun.quotClass_apply {k : Nat} (u : Nat) {A R a : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) (ha : DefFun k a) :
    DefFun k fun env => quotClass u (A env) (R env) (a env) :=
  defFun_quotClass_apply u hA hR ha

theorem defFun_quotSet_apply {k : Nat} (u : Nat) {A R : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) :
    DefFun k fun env => quotSet u (A env) (R env) := by
  unfold quotSet
  by_cases hu : u = 0
  · simp only [hu, ↓reduceIte]
    exact DefFun.image_apply DefFun.pt hA
  · simp only [hu, ↓reduceIte]
    exact DefFun.image_apply
      (DefFun.kpair_apply DefFun.empty
        (defFun_qclass_apply hA.weaken hR.weaken (DefFun.proj 0)))
      hA

theorem DefFun.quotSet_apply {k : Nat} (u : Nat) {A R : (Fin k → V) → V}
    (hA : DefFun k A) (hR : DefFun k R) :
    DefFun k fun env => quotSet u (A env) (R env) :=
  defFun_quotSet_apply u hA hR

theorem quotClass_mem {u : Nat} {A R a : V} (ha : a ∈ˢ A) :
    quotClass u A R a ∈ˢ quotSet u A R := by
  unfold quotClass quotSet
  split
  · exact mem_image.mpr ⟨a, ha, rfl⟩
  · exact mem_image.mpr ⟨a, ha, rfl⟩

theorem quotClass_surj {u : Nat} {A R q : V} (hq : q ∈ˢ quotSet u A R) :
    ∃ a, a ∈ˢ A ∧ q = quotClass u A R a := by
  unfold quotSet at hq
  unfold quotClass
  split at hq
  · next h =>
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    exact ⟨a, ha, (ite_eq_left h).symm⟩
  · next h =>
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    exact ⟨a, ha, (ite_eq_right h).symm⟩

/-- A class formed at ONE pair of parameters that lands in the quotient
of ANOTHER: its representative lies in the second parameter's carrier,
and the class is the second quotient's class of that same
representative.  Nothing relates the two parameter pairs — at a positive
level the first (tagged) class is a (tagged) `qclass` of the second's,
and at level zero
both classes are the point and the second carrier is inhabited because
the quotient is. -/
theorem quotClass_of_mem_quotSet {u : Nat} {Aset R A' R' a : V}
    (hAset : Aset ∈ˢ (univ u : V)) (hA' : A' ∈ˢ (univ u : V)) (ha : a ∈ˢ A')
    (hmem : quotClass u A' R' a ∈ˢ quotSet u Aset R) :
    a ∈ˢ Aset ∧ quotClass u A' R' a = quotClass u Aset R a := by
  obtain ⟨b, hb, hcls⟩ := quotClass_surj hmem
  by_cases hu : u = 0
  · subst hu
    refine ⟨?_, by unfold quotClass; rw [ite_eq_left rfl, ite_eq_left rfl]⟩
    rw [univ_zero] at hA' hAset
    rw [eq_pt_of_mem_univZero hA' ha, ← eq_pt_of_mem_univZero hAset hb]
    exact hb
  · unfold quotClass at hcls ⊢
    rw [ite_eq_right hu, ite_eq_right hu] at hcls
    rw [ite_eq_right hu, ite_eq_right hu]
    have hcls' := (kpair_inj hcls).2
    have hab : a ∈ˢ qclass Aset R b := by rw [← hcls']; exact self_mem_qclass ha
    obtain ⟨haA, hrel⟩ := mem_qclass.mp hab
    exact ⟨haA, hcls.trans (congrArg (kpair empty) (qclass_eq_of_rel hrel))⟩

/-- **`quotClass_of_mem_quotSet` across two positive levels**: a class
formed at one positive level and one pair of parameters that lands in
the quotient of another positive level and pair is, there, the class of
the same representative.  Above `Prop` the class reads no level. -/
theorem quotClass_of_mem_quotSet_pos {u u' : Nat} (hu : u ≠ 0) (hu' : u' ≠ 0)
    {Aset R A' R' a : V} (ha : a ∈ˢ A')
    (hmem : quotClass u' A' R' a ∈ˢ quotSet u Aset R) :
    a ∈ˢ Aset ∧ quotClass u' A' R' a = quotClass u Aset R a := by
  have hl : quotClass u' A' R' a = quotClass u A' R' a := by
    unfold quotClass; rw [ite_eq_right hu, ite_eq_right hu']
  rw [hl] at hmem ⊢
  obtain ⟨b, _hb, hcls⟩ := quotClass_surj hmem
  unfold quotClass at hcls ⊢
  rw [ite_eq_right hu, ite_eq_right hu] at hcls
  rw [ite_eq_right hu, ite_eq_right hu]
  have hcls' := (kpair_inj hcls).2
  have hab : a ∈ˢ qclass Aset R b := by rw [← hcls']; exact self_mem_qclass ha
  obtain ⟨haA, hrel⟩ := mem_qclass.mp hab
  exact ⟨haA, hcls.trans (congrArg (kpair empty) (qclass_eq_of_rel hrel))⟩

theorem quotSound {u : Nat} {A R a b w : V} (ha : a ∈ˢ A) (hb : b ∈ˢ A)
    (hw : w ∈ˢ app (app R a) b) : quotClass u A R a = quotClass u A R b := by
  unfold quotClass
  split
  · rfl
  · exact congrArg (kpair empty) (qclass_eq_of_rel (QuotRel.base ha hb ⟨w, hw⟩))

/-- The invariance premise extends from the base relation to its
equivalence closure, by instantiating `QuotRel` with the kernel
`E = {⟨x, y⟩ ∈ A × A : app f x = app f y}`. -/
theorem app_eq_of_rel {A R f a b : V}
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') →
      app f a' = app f b')
    (h : QuotRel A R a b) : app f a = app f b := by
  have hdef : DefPred (V := V) fun p => ∃ x y, p = kpair x y ∧ app f x = app f y := by
    refine DefRel.exists_curry (DefRel.exists_curry (DefRel.and ?_ ?_))
    · exact DefRel.eq_apply (DefFun.proj 2) (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0))
    · exact DefRel.eq_apply
        (DefFun.app_apply (DefFun.const f) (DefFun.proj 1))
        (DefFun.app_apply (DefFun.const f) (DefFun.proj 0))
  have hsep : HasSep (prod A A) fun p => ∃ x y, p = kpair x y ∧ app f x = app f y :=
    hasSep_of_defPred hdef
  let E := sep (prod A A) (fun p => ∃ x y, p = kpair x y ∧ app f x = app f y) hsep
  have hE_pow : E ∈ˢ power (prod A A) := mem_power_iff_subset.mpr sep_subset
  have hE_equiv : IsEquivRelOn A E := by
    refine ⟨sep_subset, ?_, ?_, ?_⟩
    · intro x hx
      exact mem_sep.mpr ⟨mem_prod.mpr ⟨x, hx, x, hx, rfl⟩, x, x, rfl, rfl⟩
    · intro x y hx hy hxy
      obtain ⟨_, x', y', heq, happ⟩ := mem_sep.mp hxy
      obtain ⟨rfl, rfl⟩ := kpair_inj heq
      exact mem_sep.mpr ⟨mem_prod.mpr ⟨y, hy, x, hx, rfl⟩, y, x, rfl, happ.symm⟩
    · intro x y z hx hy hz hxy hyz
      obtain ⟨_, x1, y1, heq1, happ1⟩ := mem_sep.mp hxy
      obtain ⟨rfl, rfl⟩ := kpair_inj heq1
      obtain ⟨_, x2, y2, heq2, happ2⟩ := mem_sep.mp hyz
      obtain ⟨rfl, rfl⟩ := kpair_inj heq2
      exact mem_sep.mpr ⟨mem_prod.mpr ⟨x, hx, z, hz, rfl⟩, x, z, rfl, happ1.trans happ2⟩
  have hE_base : ∀ x y, x ∈ˢ A → y ∈ˢ A → (∃ w, w ∈ˢ app (app R x) y) → kpair x y ∈ˢ E :=
    fun x y hx hy hw =>
      mem_sep.mpr ⟨mem_prod.mpr ⟨x, hx, y, hy, rfl⟩, x, y, rfl, hinv x y hx hy hw⟩
  obtain ⟨_, x, y, heq, happ⟩ := mem_sep.mp (h.2.2 E hE_pow hE_equiv hE_base)
  obtain ⟨rfl, rfl⟩ := kpair_inj heq
  exact happ

/-- Equal classes have equal `f`-values: by closure invariance at
`u ≠ 0`, and by the `A ⊆ {pt}` collapse at `u = 0`. -/
theorem app_eq_of_quotClass_eq {u : Nat} {A R f a b : V}
    (hA : A ∈ˢ (univ u : V)) (ha : a ∈ˢ A) (hb : b ∈ˢ A)
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') →
      app f a' = app f b')
    (hq : quotClass u A R a = quotClass u A R b) : app f a = app f b := by
  unfold quotClass at hq
  split at hq
  · next h =>
    subst h
    rw [univ_zero] at hA
    rw [eq_pt_of_mem_univZero hA ha, eq_pt_of_mem_univZero hA hb]
  · exact app_eq_of_rel hinv (rel_of_qclass_eq ha hb (kpair_inj hq).2)

/-! ## The class is never the point above `Prop` (tasks #109, #342)

Raw classes are arbitrary nonempty subsets of the base, so with base
`ptTag` itself and a total relation the one class is `ptTag` and the
untagged class set is exactly `{ptTag} = pt` — for *any* singleton
proof point.  The base `ptTag`
is not the interpretation of any *writable* type; the obstruction is
semantic, in the ∀-A-R quantification of the model lemmas.  Up to task
#342 the classes were raw and this was the quotient itself; since then
a class above `Prop` is the pair `kpair ∅ (qclass A R a)`, so it is
never the point, and the quotient never is nor
contains it (`strict_quotSet`). -/

/-- Above `Prop` the quotient is strict: its members are pairs. -/
theorem strict_quotSet {u : Nat} (hu : u ≠ 0) (A R : V) : Strict (quotSet u A R) :=
  strict_of_kpairs fun z hz => by
    unfold quotSet at hz; rw [ite_eq_right hu] at hz
    obtain ⟨a, -, rfl⟩ := mem_image.mp hz
    exact ⟨_, _, rfl⟩

attribute [irreducible] quotSet quotClass

theorem quotSet_mem_univ {u : Nat} {A R : V} (hA : A ∈ˢ (univ u : V)) :
    quotSet u A R ∈ˢ (univ u : V) := by
  by_cases h : u = 0
  · subst h
    unfold quotSet
    rw [ite_eq_left rfl, univ_zero]
    refine mem_univZero.mpr fun z hz => ?_
    obtain ⟨-, -, rfl⟩ := mem_image.mp hz
    exact pt_mem_unitSet
  · refine mem_univ_of_tg_strict ?_ (strict_quotSet h A R)
    have hA' := mem_tg_of_mem_univ hA
    have hU := tg_isGrothendieck (V := V) h
    unfold quotSet
    rw [ite_eq_right h]
    refine hU.image_mem_of_def hA'
      (fun a _ => hU.kpair_mem (hU.empty_mem hA') (hU.mem_of_subset_mem hA' qclass_subset))
      (hasImage_quotClass_pos A R) ?_
    exact DefFunOn.of_defFun1 (F := fun a => kpair empty (qclass A R a))
      (DefFun.kpair_apply DefFun.empty
        (defFun_qclass_apply (DefFun.const A) (DefFun.const R) (DefFun.proj 0)))

end ConLeche.SetTheory
