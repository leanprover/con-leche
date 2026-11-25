module

public import ConLeche.SetTheory.Definable

@[expose] public section

/-!
# Separation, derived from first-order replacement

Proof-carrying, zero-junk separation `sep a p h`, where `h : HasSep a p`
witnesses that `{x ∈ a : p x}` exists as a set in `V`.  For any
first-order definable predicate (`DefPredOn a p`), `hasSep_of_def` builds
`HasSep a p` using the classical trick: either `∃ x ∈ a, p x` (with
witness `w₀`), in which case `x ↦ if p x then x else w₀` is `DefFun1`
and `SetTheory.replacement` yields its image, or `empty` suffices.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- Proof-carrying predicate asserting that `{x ∈ a : p x}` exists as
a set in `V`. -/
def HasSep (a : V) (p : V → Prop) : Prop :=
  ∃ b : V, ∀ z, z ∈ˢ b ↔ z ∈ˢ a ∧ p z

/-- Proof-carrying, zero-junk separation `{x ∈ a : p x}`. -/
noncomputable def sep (a : V) (p : V → Prop) (h : HasSep a p) : V :=
  Classical.choose h

theorem mem_sep {a z : V} {p : V → Prop} {h : HasSep a p} :
    z ∈ˢ sep a p h ↔ z ∈ˢ a ∧ p z :=
  Classical.choose_spec h z

attribute [irreducible] sep

theorem sep_subset {a : V} {p : V → Prop} {h : HasSep a p} : sep a p h ⊆ˢ a :=
  fun _ hz => (mem_sep.mp hz).1

theorem HasSep.congr {a : V} {p q : V → Prop}
    (hpq : ∀ x, x ∈ˢ a → (p x ↔ q x)) (hp : HasSep a p) : HasSep a q := by
  obtain ⟨b, hb⟩ := hp
  exact ⟨b, fun z => (hb z).trans (and_congr_right fun hz => hpq z hz)⟩

theorem HasSep.ext {a b : V} {p q : V → Prop} (hab : a = b)
    (hpq : ∀ x, x ∈ˢ a → (p x ↔ q x)) (hp : HasSep a p) : HasSep b q :=
  hab ▸ hp.congr hpq

theorem sep_congr {a : V} {p q : V → Prop} (hp : HasSep a p) (hq : HasSep a q)
    (h : ∀ x, x ∈ˢ a → (p x ↔ q x)) : sep a p hp = sep a q hq :=
  ext fun z => by
    rw [mem_sep (h := hp), mem_sep (h := hq)]
    exact and_congr_right fun hz => h z hz

theorem sep_ext {a b : V} {p q : V → Prop} (hab : a = b)
    (hp : HasSep a p) (hq : HasSep b q)
    (h : ∀ x, x ∈ˢ a → (p x ↔ q x)) : sep a p hp = sep b q hq := by
  subst hab
  exact sep_congr hp hq h

theorem hasSep_empty (p : V → Prop) : HasSep empty p :=
  ⟨empty, fun z =>
    ⟨fun hz => absurd hz (not_mem_empty z),
     fun ⟨hz, _⟩ => absurd hz (not_mem_empty z)⟩⟩

open Classical in
/-- Any globally `DefPred` predicate separates every set `a`. -/
theorem hasSep_of_defPred {a : V} {p : V → Prop} (hp : DefPred p) : HasSep a p := by
  by_cases h : ∃ x, x ∈ˢ a ∧ p x
  · let w₀ := Classical.choose h
    have hw₀ : w₀ ∈ˢ a ∧ p w₀ := Classical.choose_spec h
    have hfun : DefFun 1 fun v => if p (v 0) then v 0 else w₀ :=
      DefFun.ite hp (DefFun.proj 0) (DefFun.const w₀)
    have himg : HasImage (fun x => if p x then x else w₀) a :=
      hasImage_of_defFun1 hfun a
    refine ⟨image (fun x => if p x then x else w₀) a himg, fun z => ?_⟩
    rw [mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hpw : p w
      · simp [hpw, hw]
      · simp [hpw, hw₀.1, hw₀.2]
    · rintro ⟨hz, hpz⟩
      exact ⟨z, hz, by simp [hpz]⟩
  · refine ⟨empty, fun z => ?_⟩
    exact ⟨fun hz => absurd hz (not_mem_empty z),
      fun ⟨hz, hpz⟩ => absurd ⟨z, hz, hpz⟩ h⟩

/-- Any predicate definable *on* `a` separates `a`. -/
theorem hasSep_of_def {a : V} {p : V → Prop} (hp : DefPredOn a p) : HasSep a p := by
  obtain ⟨q, hq, hpq⟩ := hp
  exact (hasSep_of_defPred hq).congr fun x hx => (hpq x hx).symm

/-- `DefFun` closure for `sep`. -/
theorem DefFun.sep_apply {k : Nat}
    {A : (Fin k → V) → V} {P : (Fin (k + 1) → V) → Prop}
    {h : ∀ env, HasSep (A env) (fun x => P (fcons x env))}
    (hA : DefFun k A) (hP : DefRel (k + 1) P) :
    DefFun k fun env => sep (A env) (fun x => P (fcons x env)) (h env) := by
  let reP : Fin (k + 1) → Fin (k + 2)
    | ⟨0, _⟩ => 0
    | ⟨i + 1, hi⟩ => ⟨i + 2, by omega⟩
  have hP' : DefRel (k + 2) fun w => P (fcons (w 0) (ftail (ftail w))) :=
    (hP.reIndex reP).congr fun w => by
      have heqv : (fun i => w (reP i)) = fcons (w 0) (ftail (ftail w)) := by
        funext ⟨j, hj⟩
        cases j with
        | zero => rfl
        | succ j => rfl
      rw [heqv]
  have hrel : DefRel (k + 1) fun v =>
      ∀ z, z ∈ˢ v 0 ↔ z ∈ˢ A (ftail v) ∧ P (fcons z (ftail v)) :=
    DefRel.forall_curry
      ((DefRel.mem_apply (DefFun.proj 0) (DefFun.proj 1)).iff
        ((DefRel.mem_apply (DefFun.proj 0) hA.weaken.weaken).and hP'))
  refine hrel.congr fun v => ?_
  exact ⟨fun hz => ext fun z => (hz z).trans (mem_sep (h := h (ftail v))).symm,
    fun heq z => by rw [heq, mem_sep]⟩

theorem DefFun.sep_apply_curry {k : Nat}
    {A : (Fin k → V) → V} {P : V → (Fin k → V) → Prop}
    {h : ∀ env, HasSep (A env) (fun x => P x env)}
    (hA : DefFun k A) (hP : DefRel (k + 1) fun v => P (v 0) (ftail v)) :
    DefFun k fun env => sep (A env) (fun x => P x env) (h env) :=
  DefFun.sep_apply (P := fun v => P (v 0) (ftail v)) hA hP

end ConLeche.SetTheory
