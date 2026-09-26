module

public import ConLeche.Verify.Inductives.StructRec
import ConLeche.Kernel.Inductives.SumInstall

public section

/-!
# The generated recursor at a constructor list (task #175 sum-types)

`ConLeche/Verify/Inductives/StructRec.lean`'s syntactic kit at one
constructor, generalized to the list the generators fold over
(`structMinorsPis`/`structMinorsLams`): the unfoldings of
`structRecTy`/`structRecRhs`, the minor premise's telescope under any
number of earlier binders (`instSeq_minorBody_at`: the motive is the
first extra, the earlier minors follow), the rule body under the
motive and all minors (`instSeq_ruleBody_at`: minor `j` is extra
`j + 1`), and the `.proj`-freeness of the generated forms.
-/

namespace ConLeche

open Expr

end ConLeche

namespace ConLeche

open Expr

/-! ## The elimination restriction's readout -/

/-- `Level.isNeverZero` is sound: such a level evaluates to a nonzero
number at every assignment. -/
theorem Level.isNeverZero_sound (φ : Name → Nat) :
    ∀ l : Level, l.isNeverZero = true → Level.eval φ l ≠ 0
  | .zero, h => by simp [Level.isNeverZero] at h
  | .param _, h => by simp [Level.isNeverZero] at h
  | .succ _, _ => by simp [Level.eval]
  | .max l r, h => by
    simp only [Level.isNeverZero, Bool.or_eq_true] at h
    simp only [Level.eval]
    rcases h with h | h
    · have := Level.isNeverZero_sound φ l h; omega
    · have := Level.isNeverZero_sound φ r h; omega
  | .imax l r, h => by
    simp only [Level.isNeverZero] at h
    have := Level.isNeverZero_sound φ r h
    simp only [Level.eval, if_neg this]
    omega

/-! ## The stored rules, positionally -/

/-- A stored rule is constructor `j`'s rule at right-hand side `j`. -/
theorem sumRules_getElem? {find? : Name → Option ConstantInfo}
    {recName : Name} {nP mI rP : Nat} {recTy : Expr} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {r : RecRule},
      r ∈ sumRules find? recName nP mI rP recTy ctorsA rhss →
      ∃ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        ctorsA[j]? = some cA ∧ rhss[j]? = some rhs ∧
        r = recRuleBits find? recName
          { ctor := cA.1.name, nfields := cA.2, ctorParams := nP,
            fire := if Expr.recRulePlain recTy mI rP nP then .plain
              else .inert,
            rhs := rhs, paramsBlind := true }
  | [], _, r, h => by simp [sumRules] at h
  | _ :: _, [], r, h => by simp [sumRules] at h
  | c :: cs, rhs :: rhss, r, h => by
    simp only [sumRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, c, rhs, rfl, rfl, rfl⟩
    · obtain ⟨j, cA, rhs', hc, hr, rfl⟩ := sumRules_getElem? h
      exact ⟨j + 1, cA, rhs', by simpa using hc, by simpa using hr, rfl⟩

/-! ## Instantiation under a mid-cutoff lift -/


end ConLeche
