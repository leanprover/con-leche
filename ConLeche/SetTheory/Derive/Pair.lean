module

public import ConLeche.SetTheory.Derive.Sep

@[expose] public section

/-!
# Singletons, binary unions, and Kuratowski ordered pairs

Singleton and ordered pair are derived from the unordered pair — the
Kuratowski pair `⟨a, b⟩ := {{a}, {a, b}}` (Kuratowski, Fund. Math. 2
(1921)); binary union is the union of an unordered pair.  The payoff
lemmas are the injectivity of the Kuratowski pair, the fact that an
ordered pair is never `{∅}` — the tag that keeps the proof point `pt`
apart from function graphs (`Derive/Pt.lean`, `Derive/Graphs.lean`) —
and the bridge to the relational predicates `IsUpair`/`IsKPair` in
`Core.lean`, plus `DefFun` closure.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The singleton `{a}`. -/
noncomputable def sing (a : V) : V := upair a a

theorem mem_sing {z a : V} : z ∈ˢ sing a ↔ z = a := by
  rw [sing, mem_upair]; exact ⟨fun h => h.elim id id, Or.inl⟩

theorem sing_inj {a b : V} (h : sing a = sing b) : a = b :=
  mem_sing.mp (h ▸ mem_sing.mpr rfl)

theorem sUnion_sing (a : V) : sUnion (sing a) = a :=
  ext fun z => by
    rw [mem_sUnion]
    constructor
    · rintro ⟨y, hy, hz⟩; rwa [mem_sing.mp hy] at hz
    · exact fun hz => ⟨a, mem_sing.mpr rfl, hz⟩

/-- Binary union `a ∪ b := ⋃ {a, b}`. -/
noncomputable def binUnion (a b : V) : V := sUnion (upair a b)

theorem mem_binUnion {z a b : V} : z ∈ˢ binUnion a b ↔ z ∈ˢ a ∨ z ∈ˢ b := by
  rw [binUnion, mem_sUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    rcases mem_upair.mp hy with h | h <;> subst h
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact ⟨a, mem_upair.mpr (Or.inl rfl), hz⟩
    · exact ⟨b, mem_upair.mpr (Or.inr rfl), hz⟩

/-- The Kuratowski ordered pair `⟨a, b⟩ = {{a}, {a, b}}`. -/
noncomputable def kpair (a b : V) : V := upair (sing a) (upair a b)

theorem upair_eq_sing {a b c : V} (h : upair a b = sing c) : a = c ∧ b = c := by
  constructor
  · exact mem_sing.mp (h ▸ mem_upair.mpr (Or.inl rfl))
  · exact mem_sing.mp (h ▸ mem_upair.mpr (Or.inr rfl))

theorem mem_upair_left (a b : V) : a ∈ˢ upair a b := mem_upair.mpr (Or.inl rfl)
theorem mem_upair_right (a b : V) : b ∈ˢ upair a b := mem_upair.mpr (Or.inr rfl)

/-- First-component injectivity of the Kuratowski pair. -/
theorem kpair_inj_left {a b c d : V} (h : kpair a b = kpair c d) : a = c := by
  have hac : sing a ∈ˢ kpair c d := h ▸ mem_upair_left (sing a) (upair a b)
  rcases mem_upair.mp hac with h1 | h1
  · exact sing_inj h1
  · -- `{a} = {c, d}`, so `c = a` (and `d = a`).
    obtain ⟨hc, -⟩ := upair_eq_sing (h1.symm)
    exact hc.symm

theorem kpair_inj {a b c d : V} (h : kpair a b = kpair c d) : a = c ∧ b = d := by
  obtain rfl : a = c := kpair_inj_left h
  refine ⟨rfl, ?_⟩
  -- `{a, b} ∈ {{a}, {a, d}}` and `{a, d} ∈ {{a}, {a, b}}`.
  have hb : upair a b ∈ˢ kpair a d := by
    rw [← h]; exact mem_upair_right _ _
  have hd : upair a d ∈ˢ kpair a b := by
    rw [h]; exact mem_upair_right _ _
  rcases mem_upair.mp hb with h1 | h1
  · -- `{a, b} = {a}`, so `b = a`; then `{a, d}` collapses too, so `d = a = b`.
    obtain ⟨-, hba⟩ := upair_eq_sing h1
    rcases mem_upair.mp hd with h2 | h2
    · obtain ⟨-, hda⟩ := upair_eq_sing h2
      exact hba.trans hda.symm
    · -- `{a, d} = {a, b}`: `d` is `a` or `b`, and `b = a` closes both.
      rcases mem_upair.mp (h2 ▸ mem_upair_right a d) with hda | hdb
      · exact hba.trans hda.symm
      · exact hdb.symm
  · -- `{a, b} = {a, d}`: `b` is `a` or `d`.
    rcases mem_upair.mp (h1 ▸ mem_upair_right a b) with hba | hbd
    · -- `b = a`; then `d ∈ {a, d} = {a, b} = {a, a}`, so `d = a = b`.
      rcases mem_upair.mp (h1.symm ▸ mem_upair_right a d) with hda | hdb
      · exact hba.trans hda.symm
      · exact hdb.symm
    · exact hbd

/-- Every member of a Kuratowski pair is nonempty — the fact that keeps
`{∅}` (the proof point) out of the pair/graph world. -/
theorem mem_kpair_nonempty {a b z : V} (hz : z ∈ˢ kpair a b) : ∃ w, w ∈ˢ z := by
  rcases mem_upair.mp hz with h | h <;> subst h
  · exact ⟨a, mem_sing.mpr rfl⟩
  · exact ⟨a, mem_upair_left a b⟩

/-! ### Bridges to relational `IsUpair` / `IsKPair` -/

theorem isUpair_upair (a b : V) : IsUpair (Mem (V := V)) (upair a b) a b :=
  fun _ => mem_upair

theorem isUpair_iff {p a b : V} : IsUpair (Mem (V := V)) p a b ↔ p = upair a b :=
  ⟨fun h => ext fun z => (h z).trans mem_upair.symm,
   fun h => h ▸ isUpair_upair a b⟩

theorem isKPair_kpair (a b : V) : IsKPair (Mem (V := V)) (kpair a b) a b :=
  ⟨sing a, upair a b, isUpair_upair a a, isUpair_upair a b, isUpair_upair _ _⟩

theorem isKPair_iff {p a b : V} : IsKPair (Mem (V := V)) p a b ↔ p = kpair a b := by
  constructor
  · rintro ⟨s, t, hs, ht, hp⟩
    rw [isUpair_iff] at hs ht hp
    subst hs; subst ht; exact hp
  · rintro rfl
    exact isKPair_kpair a b

/-! ### First-order definability closure -/

theorem DefFun.sing_apply {k : Nat} {A : (Fin k → V) → V} (hA : DefFun k A) :
    DefFun k fun env => sing (A env) :=
  DefFun.upair_apply hA hA

theorem DefFun.binUnion_apply {k : Nat} {A B : (Fin k → V) → V}
    (hA : DefFun k A) (hB : DefFun k B) :
    DefFun k fun env => binUnion (A env) (B env) :=
  DefFun.sUnion_apply (DefFun.upair_apply hA hB)

theorem DefFun.kpair_apply {k : Nat} {A B : (Fin k → V) → V}
    (hA : DefFun k A) (hB : DefFun k B) :
    DefFun k fun env => kpair (A env) (B env) :=
  DefFun.upair_apply (DefFun.sing_apply hA) (DefFun.upair_apply hA hB)

theorem hasImage_kpair {F : V → V} {A : V} (hF : DefFunOn A F) :
    HasImage (fun x => kpair x (F x)) A := by
  obtain ⟨G, hG, heq⟩ := hF
  have hdef : DefFun 1 fun v => kpair (v 0) (G (v 0)) :=
    DefFun.kpair_apply (DefFun.proj 0) hG
  exact (hasImage_of_defFun1 hdef A).congr fun x hx => by rw [heq x hx]

theorem DefFun.image_kpair {k : Nat} {F : V → (Fin k → V) → V} {A : (Fin k → V) → V}
    {h : ∀ env, HasImage (fun x => kpair x (F x env)) (A env)}
    (hF : DefFun (k + 1) fun v => F (v 0) (ftail v)) (hA : DefFun k A) :
    DefFun k fun env => image (fun x => kpair x (F x env)) (A env) (h env) :=
  DefFun.image_apply_curry (DefFun.kpair_apply (DefFun.proj 0) hF) hA

end ConLeche.SetTheory
