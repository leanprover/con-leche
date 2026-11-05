module

import ConLeche.Kernel.Checker
public import ConLeche.Verify.OfReducePin

public section

/-!
# The standard axioms' pinned families, extracted (task #148)

`stdAxiomOk`'s two branches, inverted.  Both are pure `Env`/`Bool`
reasoning — no valuation, no typing judgement — so they belong in the
shared tier by task #123's criterion, and both soundness routes read
them.

**The shape statements track the pin exactly.**  Six conclusions
here read `cv.type = pinA.type`: `ConstantVal.matchesPin` is plain
equality (binders carry no datum, task #342).
-/

namespace ConLeche.Verify

variable {mode : CheckMode}

/-- The pinned `Iff` family, extracted. -/
theorem iff_shapes {env : Env} {cv : ConstantVal}
    (h : stdAxiomOk env cv = true) (hp : cv.name = propextName) :
    (env.find? eqName).isSome = true ∧
    (∃ cvI caps, env.find? iffName = some (.indInfo cvI caps) ∧
      cvI.levelParams = [] ∧
      cvI.type = iffA.toConstantVal.type) ∧
    (∃ cvIi, env.find? iffIntroName = some (.ctorInfo cvIi 2 2) ∧
      cvIi.levelParams = [] ∧
      cvIi.type = iffIntroA.toConstantVal.type) ∧
    (∃ cvIr mI rP isK rules,
      env.find? iffRecName = some (.recInfo cvIr mI rP isK rules) ∧
      cvIr.levelParams = iffRecA.toConstantVal.levelParams ∧
      cvIr.type = iffRecA.toConstantVal.type) ∧
    ConstantVal.matchesPin cv propextA = true := by
  rw [stdAxiomOk, ite_eq_left hp] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hEq, hI⟩, hIi⟩, hIr⟩, hA⟩ := h
  refine ⟨hEq, ?_, ?_, ?_, hA⟩
  · cases hf : env.find? iffName with
    | none => rw [hf] at hI; exact nomatch hI
    | some ci =>
      rw [hf] at hI
      cases ci with
      | indInfo cvI caps =>
        refine ⟨cvI, caps, rfl, ?_, ?_⟩
        · exact (matchesPin_invT hI).2
        · simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            beq_iff_eq] at hI
          exact hI.2
      | _ => exact nomatch hI
  · cases hf : env.find? iffIntroName with
    | none => rw [hf] at hIi; exact nomatch hIi
    | some ci =>
      rw [hf] at hIi
      cases ci with
      | ctorInfo cvIi nP nF =>
        match nP, nF, hIi with
        | 2, 2, hIi =>
          refine ⟨cvIi, rfl, (matchesPin_invT hIi).2, ?_⟩
          simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            beq_iff_eq] at hIi
          exact hIi.2
      | _ => exact nomatch hIi
  · cases hf : env.find? iffRecName with
    | none => rw [hf] at hIr; exact nomatch hIr
    | some ci =>
      rw [hf] at hIr
      cases ci with
      | recInfo cvIr mI rP isK rules =>
        match mI, rP, hIr with
        | 4, 4, hIr =>
          refine ⟨cvIr, 4, 4, isK, rules, rfl, (matchesPin_invT hIr).2, ?_⟩
          simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            beq_iff_eq] at hIr
          exact hIr.2
      | _ => exact nomatch hIr

/-- The pinned `Nonempty` family, extracted. -/
theorem nonempty_shapes {env : Env} {cv : ConstantVal}
    (h : stdAxiomOk env cv = true) (hc : cv.name = choiceName) :
    (∃ cvN caps, env.find? nonemptyName = some (.indInfo cvN caps) ∧
      cvN.levelParams = nonemptyA.toConstantVal.levelParams ∧
      cvN.type = nonemptyA.toConstantVal.type) ∧
    (∃ cvNi, env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1) ∧
      cvNi.levelParams = nonemptyIntroA.toConstantVal.levelParams ∧
      cvNi.type = nonemptyIntroA.toConstantVal.type) ∧
    (∃ cvNr mI rP isK rules,
      env.find? nonemptyRecName = some (.recInfo cvNr mI rP isK rules) ∧
      cvNr.levelParams = nonemptyRecA.toConstantVal.levelParams ∧
      cvNr.type = nonemptyRecA.toConstantVal.type) ∧
    ConstantVal.matchesPin cv choiceA = true := by
  rw [stdAxiomOk, ite_eq_right (by rw [hc]; decide), ite_eq_left hc] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hN, hNi⟩, hNr⟩, hA⟩ := h
  refine ⟨?_, ?_, ?_, hA⟩
  · cases hf : env.find? nonemptyName with
    | none => rw [hf] at hN; exact nomatch hN
    | some ci =>
      rw [hf] at hN
      cases ci with
      | indInfo cvN caps =>
        refine ⟨cvN, caps, rfl, (matchesPin_invT hN).2, ?_⟩
        simp only [ConstantVal.matchesPin, Bool.and_eq_true,
          beq_iff_eq] at hN
        exact hN.2
      | _ => exact nomatch hN
  · cases hf : env.find? nonemptyIntroName with
    | none => rw [hf] at hNi; exact nomatch hNi
    | some ci =>
      rw [hf] at hNi
      cases ci with
      | ctorInfo cvNi nP nF =>
        match nP, nF, hNi with
        | 1, 1, hNi =>
          refine ⟨cvNi, rfl, (matchesPin_invT hNi).2, ?_⟩
          simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            beq_iff_eq] at hNi
          exact hNi.2
      | _ => exact nomatch hNi
  · cases hf : env.find? nonemptyRecName with
    | none => rw [hf] at hNr; exact nomatch hNr
    | some ci =>
      rw [hf] at hNr
      cases ci with
      | recInfo cvNr mI rP isK rules =>
        match mI, rP, hNr with
        | 3, 3, hNr =>
          refine ⟨cvNr, 3, 3, isK, rules, rfl, (matchesPin_invT hNr).2, ?_⟩
          simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            beq_iff_eq] at hNr
          exact hNr.2
      | _ => exact nomatch hNr
end ConLeche.Verify
