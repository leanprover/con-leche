module

public import ConLeche.IsModel
public import ConLeche.Cached.Justify
import ConLeche.Verify.Cached.IndWalksC

/-!
# A model of the records a fold with a sidecar checks is a model of the input

With a sidecar, the fold reads a definition, theorem or opaque constant whose value uses
`sorryAx` as the axiom of its statement (`sideRecord`).  `IsModel` reads such a definition, and
every theorem and opaque constant, by its statement already (`Declaration.constants`), so the two
streams have the same models (`isModel_sideRecords`): a theorem's constant and an axiom's constant
of one statement say the same (`Satisfies` reads neither's kind), and no record of a
constructor moves.
-/

public section

namespace ConLeche

open ConLeche.Cached

universe w

/-- **A record read by its statement**: the same constants, or a theorem's statement read as an
axiom's. -/
theorem constants_sideRecord (d : Declaration) :
    (sideRecord d).constants = d.constants ∨
      ∃ cv v, d = .thmDecl cv v ∧ (sideRecord d).constants = [.axiomInfo cv] := by
  have hax : ∀ cv : ConstantVal, builtinAxiomName cv.name = false →
      (Declaration.axiomDecl cv).constants = [.axiomInfo cv] := fun cv hb => by
    have h1 : cv.name ≠ quotSoundName := fun e => by simp [builtinAxiomName, e] at hb
    have h2 : cv.name ≠ sorryAxName := fun e => by simp [builtinAxiomName, e] at hb
    simp [Declaration.constants, h1, h2]
  cases d with
  | defnDecl cv v hint =>
    left
    by_cases hc : (!builtinAxiomName cv.name && Expr.mentionsAnyConstC [sorryAxName] v) = true
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      have hs : usesSorry v = true := by
        rw [usesSorry, ← Expr.mentionsAnyConstC_spec]; exact hc.2
      rw [show sideRecord (.defnDecl cv v hint) = .axiomDecl cv by
        simp only [sideRecord, hc.1, hc.2, Bool.not_false, Bool.and_self, ↓reduceIte], hax cv hc.1]
      simp only [Declaration.constants, hs, ↓reduceIte]
    · simp only [sideRecord, hc, Bool.false_eq_true, ↓reduceIte]
  | thmDecl cv v =>
    by_cases hc : (!builtinAxiomName cv.name && Expr.mentionsAnyConstC [sorryAxName] v) = true
    · right
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      refine ⟨cv, v, rfl, ?_⟩
      rw [show sideRecord (.thmDecl cv v) = .axiomDecl cv by
        simp only [sideRecord, hc.1, hc.2, Bool.not_false, Bool.and_self, ↓reduceIte], hax cv hc.1]
    · left; simp only [sideRecord, hc, Bool.false_eq_true, ↓reduceIte]
  | opaqueDecl cv v =>
    left
    by_cases hc : (!builtinAxiomName cv.name && Expr.mentionsAnyConstC [sorryAxName] v) = true
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      rw [show sideRecord (.opaqueDecl cv v) = .axiomDecl cv by
        simp only [sideRecord, hc.1, hc.2, Bool.not_false, Bool.and_self, ↓reduceIte], hax cv hc.1]
      rfl
    · simp only [sideRecord, hc, Bool.false_eq_true, ↓reduceIte]
  | _ => left; rfl

/-- No constructor constant moves. -/
theorem ctor_mem_sideRecord {d : Declaration} {cvj : ConstantVal} {cnP nF : Nat} {T : Name} :
    ConstantInfo.ctorInfo cvj cnP nF T ∈ (sideRecord d).constants ↔
      ConstantInfo.ctorInfo cvj cnP nF T ∈ d.constants := by
  rcases constants_sideRecord d with h | ⟨cv, v, rfl, h⟩
  · rw [h]
  · rw [h]
    simp [Declaration.constants]

theorem ctor_mem_constantsOf_side {ds : List Declaration} {cvj : ConstantVal} {cnP nF : Nat}
    {T : Name} :
    ConstantInfo.ctorInfo cvj cnP nF T ∈ constantsOf (ds.map sideRecord) ↔
      ConstantInfo.ctorInfo cvj cnP nF T ∈ constantsOf ds := by
  simp only [constantsOf, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, hc⟩; exact ⟨d, hd, ctor_mem_sideRecord.1 hc⟩
  · rintro ⟨d, hd, hc⟩; exact ⟨_, ⟨d, hd, rfl⟩, ctor_mem_sideRecord.2 hc⟩

variable {V : Type w} [SetTheory V]

theorem ruleHolds_side (model : Name → List Nat → V) (ds : List Declaration)
    (φ : LevelParam → Nat) (cv : ConstantVal) (mI rP : Nat) (rl : RecRule) :
    RuleHolds V model (· ∈ constantsOf (ds.map sideRecord)) φ cv mI rP rl ↔
      RuleHolds V model (· ∈ constantsOf ds) φ cv mI rP rl := by
  unfold RuleHolds
  refine forall_congr' fun cvj => forall_congr' fun cnP => forall_congr' fun nF =>
    forall_congr' fun T => ?_
  exact imp_congr_left ctor_mem_constantsOf_side

theorem satisfies_side (model : Name → List Nat → V) (ds : List Declaration) (c : ConstantInfo) :
    Satisfies V model (· ∈ constantsOf (ds.map sideRecord)) c ↔
      Satisfies V model (· ∈ constantsOf ds) c := by
  unfold Satisfies
  refine forall_congr' fun vals => imp_congr_right fun _ => and_congr_right fun _ => ?_
  cases c with
  | recInfo cv mI rP isK rules =>
    exact forall_congr' fun rl => imp_congr_right fun _ => ruleHolds_side model ds _ cv mI rP rl
  | _ => exact Iff.rfl

/-- **The fold's records and the input have the same models.** -/
theorem isModel_sideRecords (model : Name → List Nat → V) (j : Option Env)
    (ds : Array Declaration) :
    IsModel V model (· ∈ constantsOf (sideRecords j ds).toList) ↔
      IsModel V model (· ∈ constantsOf ds.toList) := by
  cases j with
  | none => exact Iff.rfl
  | some e =>
    simp only [sideRecords, Array.toList_map]
    unfold IsModel
    simp only [satisfies_side]
    have hthm : ∀ cv : ConstantVal,
        Satisfies V model (· ∈ constantsOf ds.toList) (.axiomInfo cv) ↔
          Satisfies V model (· ∈ constantsOf ds.toList) (.thmInfo cv) := fun _ => Iff.rfl
    simp only [constantsOf, List.mem_flatMap, List.mem_map]
    constructor
    · rintro h c ⟨d, hd, hc⟩
      rcases constants_sideRecord d with h' | ⟨cv, v, rfl, h'⟩
      · exact h c ⟨_, ⟨d, hd, rfl⟩, h' ▸ hc⟩
      · simp only [Declaration.constants, List.mem_singleton] at hc
        subst hc
        exact (hthm cv).1 (h _ ⟨_, ⟨_, hd, rfl⟩, by rw [h']; exact List.mem_singleton_self _⟩)
    · rintro h c ⟨_, ⟨d, hd, rfl⟩, hc⟩
      rcases constants_sideRecord d with h' | ⟨cv, v, rfl, h'⟩
      · exact h c ⟨d, hd, h' ▸ hc⟩
      · rw [h', List.mem_singleton] at hc
        subst hc
        exact (hthm cv).2 (h _ ⟨_, hd, List.mem_singleton_self _⟩)

end ConLeche
