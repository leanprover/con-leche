import Setlec.SetTheory.Derive.Univ

/-!
# Quotients

`quotSet u A R` is, for `u ≠ 0`, the set of equivalence classes of the
equivalence closure of "`app (app R a) b` is inhabited" on `A` (classes
by separation, the class set by replacement); for `u = 0` the base
lives in `Prop`, everything collapses to the proof point, and the
quotient is `image (fun _ => pt) A` — the truth value `[A inhabited]`.

`quotLift` lifts `f` to the quotient as the graph of
`q ↦ app f (representative of q)` (representatives by choice) — except
when `f` is the proof point, where the lift is the proof point too.
That tag is what makes the beta law `app (quotLift …) (quotClass … a) =
app f a` hold with *no typing premise on `f`* (matching the interface):
a `pt`-tagged `f` beta-reduces to `pt` on both sides, any other `f`
goes through the representative and the invariance premise, with the
`u = 0` collapse handled by `A ⊆ {pt}` (from `A ∈ univ 0`).
-/

namespace Setlec.TG

universe u

variable {V : Type u} [TG V]

/-- The equivalence closure, on `A`, of "`app (app R a) b` is
inhabited". -/
inductive QuotRel (A R : V) : V → V → Prop where
  | base {a b : V} : a ∈ᵗ A → b ∈ᵗ A → (∃ w, w ∈ᵗ app (app R a) b) →
      QuotRel A R a b
  | refl {a : V} : a ∈ᵗ A → QuotRel A R a a
  | symm {a b : V} : QuotRel A R a b → QuotRel A R b a
  | trans {a b c : V} : QuotRel A R a b → QuotRel A R b c → QuotRel A R a c

theorem QuotRel.mem {A R a b : V} (h : QuotRel A R a b) : a ∈ᵗ A ∧ b ∈ᵗ A := by
  induction h with
  | base ha hb _ => exact ⟨ha, hb⟩
  | refl ha => exact ⟨ha, ha⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

/-- The `QuotRel`-class of `a` in `A`. -/
noncomputable def qclass (A R a : V) : V := sep A (fun b => QuotRel A R a b)

theorem mem_qclass {A R a b : V} :
    b ∈ᵗ qclass A R a ↔ b ∈ᵗ A ∧ QuotRel A R a b := mem_sep

theorem self_mem_qclass {A R a : V} (ha : a ∈ᵗ A) : a ∈ᵗ qclass A R a :=
  mem_qclass.mpr ⟨ha, QuotRel.refl ha⟩

theorem qclass_eq_of_rel {A R a b : V} (h : QuotRel A R a b) :
    qclass A R a = qclass A R b :=
  ext fun z => by
    rw [mem_qclass, mem_qclass]
    exact ⟨fun ⟨hz, hr⟩ => ⟨hz, (h.symm).trans hr⟩,
           fun ⟨hz, hr⟩ => ⟨hz, h.trans hr⟩⟩

theorem rel_of_qclass_eq {A R a b : V} (ha : a ∈ᵗ A) (_hb : b ∈ᵗ A)
    (h : qclass A R a = qclass A R b) : QuotRel A R a b :=
  (mem_qclass.mp (h ▸ self_mem_qclass ha)).2.symm

open Classical in
/-- The quotient (see module docs). -/
noncomputable def quotSet (u : Nat) (A R : V) : V :=
  if u = 0 then image (fun _ => pt) A else image (fun a => qclass A R a) A

open Classical in
/-- The class of `a` in the quotient. -/
noncomputable def quotClass (u : Nat) (A R a : V) : V :=
  if u = 0 then pt else qclass A R a

theorem quotClass_mem {u : Nat} {A R a : V} (ha : a ∈ᵗ A) :
    quotClass u A R a ∈ᵗ quotSet u A R := by
  unfold quotClass quotSet
  split
  · exact mem_image.mpr ⟨a, ha, rfl⟩
  · exact mem_image.mpr ⟨a, ha, rfl⟩

theorem quotClass_surj {u : Nat} {A R q : V} (hq : q ∈ᵗ quotSet u A R) :
    ∃ a, a ∈ᵗ A ∧ q = quotClass u A R a := by
  unfold quotSet at hq
  unfold quotClass
  split at hq
  · next h =>
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    exact ⟨a, ha, (if_pos h).symm⟩
  · next h =>
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    exact ⟨a, ha, (if_neg h).symm⟩

theorem quotSound {u : Nat} {A R a b w : V} (ha : a ∈ᵗ A) (hb : b ∈ᵗ A)
    (hw : w ∈ᵗ app (app R a) b) : quotClass u A R a = quotClass u A R b := by
  unfold quotClass
  split
  · rfl
  · exact qclass_eq_of_rel (QuotRel.base ha hb ⟨w, hw⟩)

theorem quotSet_mem_univ {u : Nat} {A R : V} (hA : A ∈ᵗ (univ u : V)) :
    quotSet u A R ∈ᵗ (univ u : V) := by
  unfold quotSet
  split
  · next h =>
    subst h
    refine mem_univZero.mpr fun z hz => ?_
    obtain ⟨-, -, rfl⟩ := mem_image.mp hz
    exact pt_mem_unitSet
  · next h =>
    refine (univ_isTGUniverse h).mem_of_subset_mem
      ((univ_isTGUniverse h).power_mem hA) fun z hz => ?_
    obtain ⟨a, -, rfl⟩ := mem_image.mp hz
    exact mem_power.mpr fun w hw => (mem_qclass.mp hw).1

open Classical in
/-- A representative of a quotient class, by choice. -/
noncomputable def qrep (u : Nat) (A R q : V) : V :=
  if h : ∃ a, a ∈ᵗ A ∧ q = quotClass u A R a then Classical.choose h else empty

theorem qrep_spec {u : Nat} {A R q : V} (hq : q ∈ᵗ quotSet u A R) :
    qrep u A R q ∈ᵗ A ∧ q = quotClass u A R (qrep u A R q) := by
  unfold qrep
  rw [dif_pos (quotClass_surj hq)]
  exact Classical.choose_spec (quotClass_surj hq)

open Classical in
/-- The lift of `f` to the quotient (see module docs on the `pt` tag). -/
noncomputable def quotLift (u : Nat) (_v : Nat) (A R f : V) : V :=
  if f = pt then pt
  else graph (fun q => app f (qrep u A R q)) (quotSet u A R)

/-- The invariance premise extends from the base relation to its
equivalence closure. -/
theorem app_eq_of_rel {A R f a b : V}
    (hinv : ∀ a' b', a' ∈ᵗ A → b' ∈ᵗ A → (∃ w, w ∈ᵗ app (app R a') b') →
      app f a' = app f b')
    (h : QuotRel A R a b) : app f a = app f b := by
  induction h with
  | base ha hb hw => exact hinv _ _ ha hb hw
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Equal classes have equal `f`-values: by closure invariance at
`u ≠ 0`, and by the `A ⊆ {pt}` collapse at `u = 0`. -/
theorem app_eq_of_quotClass_eq {u : Nat} {A R f a b : V}
    (hA : A ∈ᵗ (univ u : V)) (ha : a ∈ᵗ A) (hb : b ∈ᵗ A)
    (hinv : ∀ a' b', a' ∈ᵗ A → b' ∈ᵗ A → (∃ w, w ∈ᵗ app (app R a') b') →
      app f a' = app f b')
    (hq : quotClass u A R a = quotClass u A R b) : app f a = app f b := by
  unfold quotClass at hq
  split at hq
  · next h =>
    subst h
    rw [univ_zero] at hA
    rw [eq_pt_of_mem_univZero hA ha, eq_pt_of_mem_univZero hA hb]
  · exact app_eq_of_rel hinv (rel_of_qclass_eq ha hb hq)

theorem quotLift_beta {u v : Nat} {A R f a : V} (hA : A ∈ᵗ (univ u : V))
    (ha : a ∈ᵗ A)
    (hinv : ∀ a' b', a' ∈ᵗ A → b' ∈ᵗ A → (∃ w, w ∈ᵗ app (app R a') b') →
      app f a' = app f b') :
    app (quotLift u v A R f) (quotClass u A R a) = app f a := by
  unfold quotLift
  split
  · next h => rw [h, app_pt, app_pt]
  · rw [app_graph (quotClass_mem ha)]
    obtain ⟨hrep, hcls⟩ := qrep_spec (quotClass_mem (u := u) (R := R) ha)
    exact app_eq_of_quotClass_eq hA hrep ha hinv hcls.symm

theorem quotLift_mem {u v : Nat} {A R f B : V} (_hA : A ∈ᵗ (univ u : V))
    (hf : f ∈ᵗ pi v A (fun _ => B))
    (_hinv : ∀ a b, a ∈ᵗ A → b ∈ᵗ A → (∃ w, w ∈ᵗ app (app R a) b) →
      app f a = app f b) :
    quotLift u v A R f ∈ᵗ pi v (quotSet u A R) (fun _ => B) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · -- `f` is the proof point; the lifted product is the truth value
    -- `[∀ q ∈ quotSet, B inhabited]`, true via representatives.
    have hfp : f = pt := mem_pi_zero hf
    rw [pi_zero] at hf ⊢
    have hlift : quotLift u 0 A R f = pt := by
      unfold quotLift; exact if_pos hfp
    rw [hlift]
    refine pt_mem_truthVal fun q hq => ?_
    exact of_mem_truthVal hf _ (qrep_spec hq).1
  · have hv' : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
    rw [pi_pos hv'] at hf ⊢
    have hfp : f ≠ pt := ne_pt_of_mem_piSet hf
    have hlift : quotLift u v A R f =
        graph (fun q => app f (qrep u A R q)) (quotSet u A R) := by
      unfold quotLift; exact if_neg hfp
    rw [hlift]
    exact graph_mem_piSet fun q hq => app_mem_of_mem_piSet hf (qrep_spec hq).1

end Setlec.TG
