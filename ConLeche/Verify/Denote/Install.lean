module

import ConLeche.Verify.Denote
import ConLeche.Verify.EnvWF
public import ConLeche.Verify.EnvGuards
import ConLeche.Verify.EnvPreds
public import ConLeche.Verify.Denote.Pinned

public section

/-!
# Denotations survive environment extension — the install transport core

Relocated verbatim from `ConLeche/TTVerify/Extend.lean` (task #148,
T5): the environment-extension transports that are `V`-free and
lane-independent.  The namespace stays `ConLeche.Verify` so no call
site moves.

Contents: the literal-guard monotonicity family
(`natLitSupported_cons`, `strLitSupported_cons`, `natOpGuard_cons`) and
the projection-table transport (`findProj?_cons_of_base_none`,
`ProjOkT.cons`).
-/

set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.Term

/-- A fresh cons that is not a projection table cannot create a table
lookup where none existed. -/
theorem findProj?_cons_of_base_none {env : Env} {c₀ : ConstantInfo}
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl) :
    ∀ (sn : Name) (i : Nat),
      env.findProj? sn i = none →
      Env.findProj? ⟨c₀ :: env.consts⟩ sn i = none := by
  intro sn i h0
  by_cases hn : c₀.name = projTableName sn
  · have hf : (⟨c₀ :: env.consts⟩ : Env).find? (projTableName sn) = some c₀ := by
      rw [Env.find?_cons, if_pos hn]
    unfold Env.findProj?
    rw [hf]
    cases c₀ <;> first | rfl | exact absurd rfl (hntc _)
  · rw [Env.findProj?_cons_ne hn]; exact h0


/-! ## The guards are monotone, not merely congruent

A guard's transport across a cons needs the new constant's name to
differ from each slot's.  At an install those distinctness facts have
to come from somewhere, and there is a cheaper source than freshness
plus a case analysis: **the guard itself**.  A
guard that holds has already found every slot it reads, so each slot is
`isSome` in the *small* environment, and freshness then supplies the
distinctness for free.

The resulting monotonicity lemmas take a single hypothesis and
discharge the `hguardN`/`hguardS` obligations of `denote_mono`,
`denote_install` and `has_type_cons` at every ordinary install. -/

/-- The `Nat`-literal guard is monotone under a fresh install. -/
theorem natLitSupported_cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) (h : natLitSupported env = true) :
    natLitSupported ⟨c₀ :: env.consts⟩ = true := by
  simp only [natLitSupported, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have i1 : (env.find? natName).isSome = true := by
    revert h1; cases env.find? natName <;> simp [natIndOk]
  have i2 : (env.find? natZeroName).isSome = true := by
    revert h2; cases env.find? natZeroName <;> simp [natZeroOk]
  have i3 : (env.find? natSuccName).isSome = true := by
    revert h3; cases env.find? natSuccName <;> simp [natSuccOk]
  rw [Env.find?_cons_of_isSome hfresh i1, Env.find?_cons_of_isSome hfresh i2,
    Env.find?_cons_of_isSome hfresh i3]
  exact ⟨⟨h1, h2⟩, h3⟩

/-- The `String`-literal guard is monotone under a fresh install. -/
theorem strLitSupported_cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) (h : strLitSupported env = true) :
    strLitSupported ⟨c₀ :: env.consts⟩ = true := by
  simp only [strLitSupported, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  have i1 : (env.find? stringName).isSome = true := by
    revert h1; cases env.find? stringName <;> simp [stringTyOk]
  have i2 : (env.find? stringOfListName).isSome = true := by
    revert h2; cases env.find? stringOfListName <;> simp [stringOfListTyOk]
  have i3 : (env.find? listName).isSome = true := by
    revert h3; cases env.find? listName <;> simp [listTyOk]
  have i4 : (env.find? listNilName).isSome = true := by
    revert h4; cases env.find? listNilName <;> simp [listNilTyOk]
  have i5 : (env.find? listConsName).isSome = true := by
    revert h5; cases env.find? listConsName <;> simp [listConsTyOk]
  have i6 : (env.find? charName).isSome = true := by
    revert h6; cases env.find? charName <;> simp [charTyOk]
  have i7 : (env.find? charOfNatName).isSome = true := by
    revert h7; cases env.find? charOfNatName <;> simp [charOfNatTyOk]
  rw [Env.find?_cons_of_isSome hfresh i1, Env.find?_cons_of_isSome hfresh i2,
    Env.find?_cons_of_isSome hfresh i3, Env.find?_cons_of_isSome hfresh i4,
    Env.find?_cons_of_isSome hfresh i5, Env.find?_cons_of_isSome hfresh i6,
    Env.find?_cons_of_isSome hfresh i7]
  exact ⟨⟨⟨⟨⟨⟨⟨natLitSupported_cons hfresh h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

/-- The `Nat`-operation guard is monotone under a fresh install. -/
theorem natOpGuard_cons {env : Env} {c₀ : ConstantInfo} {c : Name}
    (hfresh : env.find? c₀.name = none) (h : natOpGuard env c = true) :
    natOpGuard ⟨c₀ :: env.consts⟩ c = true := by
  simp only [natOpGuard, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨h0, hdeps⟩, hbool⟩ := h
  refine ⟨⟨natLitSupported_cons hfresh h0, ?_⟩, ?_⟩
  · rw [List.all_eq_true] at hdeps ⊢
    intro n hn
    have hn' := hdeps n hn
    have i : (env.find? n).isSome = true := by
      revert hn'; cases env.find? n <;> simp
    rw [Env.find?_cons_of_isSome hfresh i]
    exact hn'
  · split at hbool
    · next hc =>
      rw [if_pos hc]
      simp only [Bool.and_eq_true] at hbool ⊢
      obtain ⟨hT, hF⟩ := hbool
      have iT : (env.find? boolTrueName).isSome = true := by
        revert hT; cases env.find? boolTrueName <;> simp
      have iF : (env.find? boolFalseName).isSome = true := by
        revert hF; cases env.find? boolFalseName <;> simp
      rw [Env.find?_cons_of_isSome hfresh iT,
        Env.find?_cons_of_isSome hfresh iF]
      exact ⟨hT, hF⟩
    · next hc => rw [if_neg hc]


/-! ## The projection-table transport

The head case is a hypothesis (the install must establish its own
constant's law), and everything else transports. -/

/-- The projection-table discipline survives an install.  A head that
is a table supplies its own head data (task #175 wiring W5); the
stored tables' head data survives by freshness. -/
theorem ProjOkT.cons {env : Env} {c₀ : ConstantInfo} (h : ProjOkT env)
    (hfresh : env.find? c₀.name = none)
    (hheadTower : ∀ tbl, c₀ = .projInfo tbl →
      ∀ i, i < tbl.numFields → TowerHead ⟨c₀ :: env.consts⟩ (tbl.entry i)) :
    ProjOkT ⟨c₀ :: env.consts⟩ := by
  have hkeep : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env.find? n = some ci → (⟨c₀ :: env.consts⟩ : Env).find? n = some ci := by
    intro n ci _ hf
    rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]; exact hf
  intro n tbl hf i hi
  by_cases hn : c₀.name = n
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    exact hheadTower tbl (Option.some.inj hf) i hi
  · rw [Env.find?_cons, if_neg hn] at hf
    exact TowerHead.mono hkeep (h n tbl hf i hi)

end ConLeche.Verify
