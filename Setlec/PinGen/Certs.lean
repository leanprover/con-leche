module
/-!
# Certificate theorems for the pin-certified Nat operations (elab-time)

The characterization certificates of the pin-certified WF-recursive
`Nat` operations, elaborated against the ambient *toolchain* prelude,
where `Nat.div`/`Nat.mod`/… are the real operations.  The *statements*
fix the pinned spellings: guards via the already-certified `Nat.ble`
(never the `Nat.le`/`Nat.lt` `Prop` inductives), numerals via
`Nat.succ`/`Nat.zero` (never `OfNat`), so the model-side consumption
rides the existing `NatOpsOk` literal semantics.

The proofs are written with *controlled* dependencies: no `simp`, no
`decide` — the core lemmas (`Nat.mod_eq` …) are proved with simp steps
whose terms mention `eq_true`/`and_self` and hence `Iff`/`propext`,
which do not exist in the export stream before `Nat.mod`.  Everything
below reduces to `Eq`-rewriting, `Nat`/`Decidable` case analysis, and
prefix-present arithmetic lemmas.  (Constants that are *definitions*
outside the stream prefix are inlined by the generator; a non-prefix
*inductive* aborts the build.)

This module is part of the elab-time pin generator
(`Setlec/PinGen.lean`); nothing in it is used by the checker at
runtime.
-/

public section

namespace Setlec.PinGen

/-! ## Support lemmas for `Nat.div`/`Nat.mod` -/

/-- One-step unfolding of the fuel-recursive worker (the auto-generated
`eq_def`, coerced through the definitional match reduction at `succ`). -/
private theorem divGoStep (y : Nat) (hy : 0 < y) (f x : Nat)
    (h : x < Nat.succ f) :
    Nat.div.go y hy (Nat.succ f) x h =
      dite (y ≤ x)
        (fun hle => Nat.succ (Nat.div.go y hy f (x - y)
          (Nat.div_rec_fuel_lemma hy hle h)))
        (fun _ => 0) :=
  Nat.div.go.eq_def y hy (Nat.succ f) x h

private theorem modGoStep (y : Nat) (hy : 0 < y) (f x : Nat)
    (h : x < Nat.succ f) :
    Nat.modCore.go y hy (Nat.succ f) x h =
      dite (y ≤ x)
        (fun hle => Nat.modCore.go y hy f (x - y)
          (Nat.div_rec_fuel_lemma hy hle h))
        (fun _ => x) :=
  Nat.modCore.go.eq_def y hy (Nat.succ f) x h

private theorem divGoFuelCongr (y : Nat) (hy : 0 < y) :
    ∀ (f1 x : Nat) (h1 : x < f1) (f2 : Nat) (h2 : x < f2),
      Nat.div.go y hy f1 x h1 = Nat.div.go y hy f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro x h1 f2 h2; exact absurd h1 (Nat.not_succ_le_zero x)
  | succ f1 ih =>
    intro x h1 f2 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_succ_le_zero x)
    | succ f2 =>
      rw [divGoStep, divGoStep]
      match Nat.decLe y x with
      | .isTrue hle =>
        rw [dif_pos hle, dif_pos hle]
        exact congrArg Nat.succ (ih _ _ _ _)
      | .isFalse hnle => rw [dif_neg hnle, dif_neg hnle]

private theorem modGoFuelCongr (y : Nat) (hy : 0 < y) :
    ∀ (f1 x : Nat) (h1 : x < f1) (f2 : Nat) (h2 : x < f2),
      Nat.modCore.go y hy f1 x h1 = Nat.modCore.go y hy f2 x h2 := by
  intro f1
  induction f1 with
  | zero => intro x h1 f2 h2; exact absurd h1 (Nat.not_succ_le_zero x)
  | succ f1 ih =>
    intro x h1 f2 h2
    cases f2 with
    | zero => exact absurd h2 (Nat.not_succ_le_zero x)
    | succ f2 =>
      rw [modGoStep, modGoStep]
      match Nat.decLe y x with
      | .isTrue hle =>
        rw [dif_pos hle, dif_pos hle]
        exact ih _ _ _ _
      | .isFalse hnle => rw [dif_neg hnle, dif_neg hnle]

/-- The dispatcher, unfolded (the auto-generated `eq_def`). -/
private theorem divUnfold (x y : Nat) :
    Nat.div x y =
      dite (0 < y)
        (fun hy => Nat.div.go y hy (Nat.succ x) x (Nat.lt_succ_self x))
        (fun _ => Nat.zero) :=
  Nat.div.eq_def x y

private theorem modCoreUnfold (x y : Nat) :
    Nat.modCore x y =
      dite (0 < y)
        (fun hy => Nat.modCore.go y hy (Nat.succ x) x (Nat.lt_succ_self x))
        (fun _ => x) :=
  Nat.modCore.eq_def x y

/-- `Nat.mod` agrees with `Nat.modCore` (the dispatcher's `x`-match and
`≤`-test collapse against `modCore`'s own tests). -/
private theorem modEqModCore (x y : Nat) (hy : 0 < y) :
    Nat.mod x y = Nat.modCore x y := by
  cases x with
  | zero =>
    show Nat.zero = Nat.modCore Nat.zero y
    rw [modCoreUnfold, dif_pos hy, modGoStep,
      dif_neg (fun hle => absurd (Nat.lt_of_lt_of_le hy hle) (Nat.lt_irrefl Nat.zero))]
  | succ n =>
    show ite (y ≤ Nat.succ n) (Nat.modCore (Nat.succ n) y) (Nat.succ n) = _
    match Nat.decLe y (Nat.succ n) with
    | .isTrue hle => rw [if_pos hle]
    | .isFalse hnle =>
      rw [if_neg hnle, modCoreUnfold, dif_pos hy, modGoStep, dif_neg hnle]

/-! ## The `Nat.div`/`Nat.mod` certificate theorems -/

theorem modRecCert : ∀ (x y : Nat), Nat.ble y x = Bool.true →
    Nat.ble (Nat.succ Nat.zero) y = Bool.true →
    Nat.mod x y = Nat.mod (Nat.sub x y) y := by
  intro x y hyx h1y
  have hy : 0 < y := Nat.le_of_ble_eq_true h1y
  have hxy : y ≤ x := Nat.le_of_ble_eq_true hyx
  rw [modEqModCore x y hy, modEqModCore (Nat.sub x y) y hy,
    modCoreUnfold, modCoreUnfold, dif_pos hy, dif_pos hy,
    modGoStep, dif_pos hxy]
  exact modGoFuelCongr y hy _ _ _ _ _

theorem modBaseGtCert : ∀ (x y : Nat), Nat.ble y x = Bool.false →
    Nat.mod x y = x := by
  intro x y hf
  have hnle : ¬ (y ≤ x) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  cases x with
  | zero => rfl
  | succ n =>
    show ite (y ≤ Nat.succ n) (Nat.modCore (Nat.succ n) y) (Nat.succ n) = _
    rw [if_neg hnle]

theorem modBaseZeroCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.false →
    Nat.mod x y = x := by
  intro x y hf
  have hny : ¬ (0 < y) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  cases x with
  | zero => rfl
  | succ n =>
    show ite (y ≤ Nat.succ n) (Nat.modCore (Nat.succ n) y) (Nat.succ n) = _
    match Nat.decLe y (Nat.succ n) with
    | .isTrue hle => rw [if_pos hle, modCoreUnfold, dif_neg hny]
    | .isFalse hnle => rw [if_neg hnle]

theorem divRecCert : ∀ (x y : Nat), Nat.ble y x = Bool.true →
    Nat.ble (Nat.succ Nat.zero) y = Bool.true →
    Nat.div x y = Nat.succ (Nat.div (Nat.sub x y) y) := by
  intro x y hyx h1y
  have hy : 0 < y := Nat.le_of_ble_eq_true h1y
  have hxy : y ≤ x := Nat.le_of_ble_eq_true hyx
  rw [divUnfold, divUnfold, dif_pos hy, dif_pos hy, divGoStep, dif_pos hxy]
  exact congrArg Nat.succ (divGoFuelCongr y hy _ _ _ _ _)

theorem divBaseGtCert : ∀ (x y : Nat), Nat.ble y x = Bool.false →
    Nat.div x y = Nat.zero := by
  intro x y hf
  have hnle : ¬ (y ≤ x) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  rw [divUnfold]
  match Nat.decLt 0 y with
  | .isTrue hy => rw [dif_pos hy, divGoStep, dif_neg hnle]
  | .isFalse hny => rw [dif_neg hny]

theorem divBaseZeroCert : ∀ (x y : Nat),
    Nat.ble (Nat.succ Nat.zero) y = Bool.false →
    Nat.div x y = Nat.zero := by
  intro x y hf
  have hny : ¬ (0 < y) := fun h =>
    Bool.noConfusion ((Nat.ble_eq_true_of_le h).symm.trans hf)
  rw [divUnfold, dif_neg hny]

end Setlec.PinGen
