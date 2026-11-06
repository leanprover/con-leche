module

import ConLeche.Verify.Denote
import ConLeche.Verify.EnvWF
public import ConLeche.Verify.EnvGuards
import ConLeche.Verify.EnvPreds
public import ConLeche.Verify.Denote.Pinned

public section

/-!
# Denotations survive environment extension — the install transport core

The environment-extension transports that are `V`-free (task #148).

Contents: the literal-guard monotonicity family
(`natLitSupported_cons`, `strLitSupported_cons`, `natOpGuard_cons`) and
the projection-table transport (`findProj?_cons_of_base_none`,
`ProjOkT.cons`, `ProjOkT.pushTable`).
-/

set_option linter.unusedVariables false

namespace ConLeche.Verify

open ConLeche.Term

/-- A fresh cons cannot create a table lookup where none existed: a
stored table's structure is stored (`EnvWF`), so no table waits for the
fresh name (task #362). -/
theorem findProj?_cons_of_base_none {env : Env} {c₀ : ConstantInfo} (hwf : EnvWF env)
    (hfresh : env.find? c₀.name = none) :
    ∀ (sn : Name) (i : Nat),
      env.findProj? sn i = none →
      Env.findProj? ⟨c₀ :: env.consts, env.tables⟩ sn i = none := by
  intro sn i h0
  rw [hwf.findProj?_cons hfresh]
  exact h0


/-! ## The guards are monotone, not merely congruent

A guard's transport across a cons needs the new constant's name to
differ from each slot's.  At an install those distinctness facts have
to come from somewhere, and there is a cheaper source than freshness
plus a case analysis: **the guard itself**.  A
guard that holds has already found every slot it reads, so each slot is
`isSome` in the *small* environment, and freshness then supplies the
distinctness for free.

The resulting monotonicity lemmas take a single hypothesis
(`litGuardsMono_cons` packs them for the fold's harvests). -/

/-- The `Nat`-literal guard is monotone under a fresh install. -/
theorem natLitSupported_cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) (h : natLitSupported env = true) :
    natLitSupported ⟨c₀ :: env.consts, env.tables⟩ = true := by
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
    strLitSupported ⟨c₀ :: env.consts, env.tables⟩ = true := by
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
    natOpGuard ⟨c₀ :: env.consts, env.tables⟩ c = true := by
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
      rw [ite_eq_left hc]
      simp only [Bool.and_eq_true] at hbool ⊢
      obtain ⟨hT, hF⟩ := hbool
      have iT : (env.find? boolTrueName).isSome = true := by
        revert hT; cases env.find? boolTrueName <;> simp
      have iF : (env.find? boolFalseName).isSome = true := by
        revert hF; cases env.find? boolFalseName <;> simp
      rw [Env.find?_cons_of_isSome hfresh iT,
        Env.find?_cons_of_isSome hfresh iF]
      exact ⟨hT, hF⟩
    · next hc => rw [ite_eq_right hc]


/-- A pinned operation codomain survives any environment change that keeps
the stored `Bool` entry's constant value. -/
theorem natOpCod_of_find {env env' : Env} {c : Name} {e : Expr}
    (hb : ∀ ci, env.find? boolName = some ci →
      ∃ ci', env'.find? boolName = some ci' ∧ ci'.toConstantVal = ci.toConstantVal)
    (h : natOpCod env c e = true) : natOpCod env' c e = true := by
  unfold natOpCod at h ⊢
  split at h
  · next hc =>
    rw [ite_eq_left hc]
    simp only [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    revert h2
    cases hf : env.find? boolName with
    | none => intro h2; exact absurd h2 (by simp)
    | some ci =>
      intro h2
      obtain ⟨ci', hf', hcv⟩ := hb ci hf
      rw [hf']; dsimp only; rw [hcv]; exact h2
  · next hc => rw [ite_eq_right hc]; exact h

/-- A pinned operation type survives any environment change that keeps
the stored `Bool` entry's constant value. -/
theorem natOpTyPinned_of_find {env env' : Env} {c : Name} {ty : Expr}
    (hb : ∀ ci, env.find? boolName = some ci →
      ∃ ci', env'.find? boolName = some ci' ∧ ci'.toConstantVal = ci.toConstantVal)
    (h : natOpTyPinned env c ty = true) : natOpTyPinned env' c ty = true := by
  unfold natOpTyPinned at h ⊢
  split at h
  · next hc =>
    rw [ite_eq_left hc]
    split at h
    · simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, natOpCod_of_find hb h.2⟩
    · exact nomatch h
  · next hc =>
    rw [ite_eq_right hc]
    split at h
    · simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, natOpCod_of_find hb h.2⟩
    · exact nomatch h

/-- The pinned operation type is monotone under a fresh install. -/
theorem natOpTyPinned_cons {env : Env} {c₀ : ConstantInfo} {c : Name} {ty : Expr}
    (hfresh : env.find? c₀.name = none) (h : natOpTyPinned env c ty = true) :
    natOpTyPinned ⟨c₀ :: env.consts, env.tables⟩ c ty = true :=
  natOpTyPinned_of_find (fun ci hf =>
    ⟨ci, by rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]; exact hf, rfl⟩) h

/-! ## The projection-table transport

The head case is a hypothesis (the install must establish its own
constant's law), and everything else transports. -/

/-- The projection-table discipline survives a fresh constant's
install: the stored tables stay (`EnvWF.findTable?_cons`) and so does
their head data. -/
theorem ProjOkT.cons {env : Env} {c₀ : ConstantInfo} (h : ProjOkT env) (hwf : EnvWF env)
    (hfresh : env.find? c₀.name = none) :
    ProjOkT ⟨c₀ :: env.consts, env.tables⟩ := by
  have hkeep : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) →
      env.find? n = some ci → (⟨c₀ :: env.consts, env.tables⟩ : Env).find? n = some ci := by
    intro n ci _ hf
    rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]; exact hf
  intro T tbl hf i hi
  rw [hwf.findTable?_cons hfresh] at hf
  exact TowerHead.mono hkeep (h T tbl hf i hi)

/-- **The projection-table discipline survives a table's install**
(task #362): the new table supplies its own head data, the others keep
theirs (a table install leaves the constants alone). -/
theorem ProjOkT.pushTable {env : Env} {t : ProjTable} (h : ProjOkT env)
    (hhead : ∀ i, i < t.numFields → TowerHead env (t.entry i)) :
    ProjOkT ⟨env.consts, t :: env.tables⟩ := by
  intro T tbl hf i hi
  rw [Env.findTable?_pushTable] at hf
  split at hf
  · cases hf
    exact hhead i hi
  · exact h T tbl hf i hi

/-! ## The one-name update -/

/-- Extend a canonical constant reading at one name. -/
@[expose] def acvalWith (acval : Name → (Name → Nat) → Term) (n : Name)
    (A : (Name → Nat) → Term) : Name → (Name → Nat) → Term :=
  fun c ψ => if c = n then A ψ else acval c ψ

theorem acvalWith_ne {acval : Name → (Name → Nat) → Term}
    {n : Name} {A : (Name → Nat) → Term} {c : Name} (h : c ≠ n) :
    acvalWith acval n A c = acval c := by
  funext ψ; simp [acvalWith, h]

theorem acvalWith_self {acval : Name → (Name → Nat) → Term}
    {n : Name} {A : (Name → Nat) → Term} :
    acvalWith acval n A n = A := by
  funext ψ; simp [acvalWith]

/-! ## The syntactic fields, transported

`acval_params` is a condition on an install-fixed object with no
`interp` in it, so it extends by a case split on the updated name and
nothing else. -/

/-- `acval_params` extends across a `cons`: the stored entries are the
old ones plus the installed one, and the new leaf answers for itself.

Note the environment moves here — the field
is indexed by `env.find?`.  Freshness is **not** needed: the `cons`
shadows, so the installed entry answers first either way. -/
theorem acvalWith_params {acval : Name → (Name → Nat) → Term}
    {env : Env} {c₀ : ConLeche.ConstantInfo}
    {A : (Name → Nat) → Term}
    (h : ∀ (m : Name) (ci : ConLeche.ConstantInfo),
      env.find? m = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acval m ψ₁ = acval m ψ₂)
    (hA : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂) :
    ∀ (m : Name) (ci : ConLeche.ConstantInfo),
      (⟨c₀ :: env.consts, env.tables⟩ : Env).find? m = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acvalWith acval c₀.name A m ψ₁
          = acvalWith acval c₀.name A m ψ₂ := by
  intro m ci hf ψ₁ ψ₂ hp
  rw [Env.find?_cons] at hf
  by_cases hm : c₀.name = m
  · rw [ite_eq_left hm] at hf
    obtain rfl := Option.some.inj hf
    subst hm
    rw [acvalWith_self]
    exact hA ψ₁ ψ₂ hp
  · rw [ite_eq_right hm] at hf
    rw [acvalWith_ne (fun hh => hm hh.symm)]
    exact h m ci hf ψ₁ ψ₂ hp

end ConLeche.Verify
