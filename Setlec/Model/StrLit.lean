import Setlec.Model.NatLit

/-!
# The string-literal fragment of the model

`strLitSupported` pins the stored `String`/`String.ofList`/`List`/
`List.nil`/`List.cons`/`Char`/`Char.ofNat` declarations; here the model
consumes that guard:

* the interpretation of a string literal (`strLitVal`, the value-level
  reading of the reference kernels' `strLitToConstructor` form) agrees
  with the interpretation of that constructor form itself;
* in an environment with a model, the literal's value is a member of
  the `String` value (derived from `EnvModel.mem_type` and the guard's
  shape facts alone, mirroring `Setlec.Model.NatLit`);
* the constructor form carries truthful annotations (`AnnotOk`), so
  the checker may switch a literal for its unfolding mid-reduction.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

private theorem find?_name' {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  have := List.find?_some h
  simpa using this

/-- The character-list part of `strLitToConstructor`, as a standalone
recursion (the kernel function folds; this is its unfolding). -/
def strLitList : List Char → Expr
  | [] => .app (.const listNilName [.zero]) (.const charName [])
  | c :: cs =>
    .app (.app (.app (.const listConsName [.zero]) (.const charName []))
      (.app (.const charOfNatName []) (.lit (.natVal c.toNat))))
      (strLitList cs)

private theorem strLitList_foldr : ∀ cs : List Char,
    cs.foldr
      (fun c e =>
        .app (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e)
      (.app (.const listNilName [.zero]) (.const charName [])) =
    strLitList cs
  | [] => rfl
  | c :: cs => by rw [List.foldr_cons, strLitList_foldr cs, strLitList]

theorem strLitToConstructor_eq (s : String) :
    strLitToConstructor s =
      .app (.const stringOfListName []) (strLitList s.toList) := by
  unfold strLitToConstructor
  rw [strLitList_foldr s.toList]

/-! ## Interpretation equations for the pinned constants -/

/-- The interpretation of `String` (given the guard). -/
theorem interpExpr_const_string {cval : ConstVal V}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ (.const stringName []) =
      some (cval stringName φ) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, -⟩ :=
    strLitSupported_inv hs
  simp [interpExpr, hfS, hpS, Level.substFn_nil]

/-- The interpretation of `Char` (given the guard). -/
theorem interpExpr_const_char {cval : ConstVal V}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ (.const charName []) =
      some (cval charName φ) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, -⟩ :=
    strLitSupported_inv hs
  simp [interpExpr, hfH, hpH, Level.substFn_nil]

/-- The interpretation of `String.ofList` (given the guard). -/
theorem interpExpr_const_stringOfList {cval : ConstVal V}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ (.const stringOfListName []) =
      some (cval stringOfListName φ) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, -⟩ :=
    strLitSupported_inv hs
  simp [interpExpr, hfO, hpO, Level.substFn_nil]

/-- The interpretation of `Char.ofNat` (given the guard). -/
theorem interpExpr_const_charOfNat {cval : ConstVal V}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ (.const charOfNatName []) =
      some (cval charOfNatName φ) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, -⟩ :=
    strLitSupported_inv hs
  simp [interpExpr, hfF, hpF, Level.substFn_nil]

/-- The interpretation of `List.nil.{0} Char` (given the guard). -/
theorem interpExpr_listNilChar {cval : ConstVal V}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ
        (.app (.const listNilName [.zero]) (.const charName [])) =
      some (SetTheory.app
        (cval listNilName
          (Level.substFn φ (env.levelParamsAt listNilName) [.zero]))
        (cval charName φ)) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, -⟩ :=
    strLitSupported_inv hs
  have hlp : env.levelParamsAt listNilName = ciN.toConstantVal.levelParams := by
    simp [Env.levelParamsAt, hfN]
  rw [hlp]
  simp [interpExpr, hfN, hfH, hpH, hpN, Level.substFn_nil]

/-- The interpretation of `List.cons.{0} Char` (given the guard). -/
theorem interpExpr_listConsChar {cval : ConstVal V}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ
        (.app (.const listConsName [.zero]) (.const charName [])) =
      some (SetTheory.app
        (cval listConsName
          (Level.substFn φ (env.levelParamsAt listConsName) [.zero]))
        (cval charName φ)) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, -⟩ :=
    strLitSupported_inv hs
  have hlp : env.levelParamsAt listConsName = ciC.toConstantVal.levelParams := by
    simp [Env.levelParamsAt, hfC]
  rw [hlp]
  simp [interpExpr, hfC, hfH, hpH, hpC, Level.substFn_nil]

/-- The character-list expression interprets to `charListVal` (given
the guard). -/
theorem interpExpr_strLitList {cval : ConstVal V}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    ∀ cs : List Char,
      interpExpr V cval env φ d ρ (strLitList cs) =
        some (charListVal V
          (SetTheory.app
            (cval listNilName
              (Level.substFn φ (env.levelParamsAt listNilName) [.zero]))
            (cval charName φ))
          (SetTheory.app
            (cval listConsName
              (Level.substFn φ (env.levelParamsAt listConsName) [.zero]))
            (cval charName φ))
          (cval charOfNatName φ) (cval natZeroName φ) (cval natSuccName φ)
          cs)
  | [] => by
    rw [strLitList, charListVal]
    exact interpExpr_listNilChar hs
  | c :: cs => by
    obtain ⟨hnat, -⟩ := strLitSupported_inv hs
    rw [strLitList, charListVal]
    simp only [interpExpr, interpExpr_listConsChar hs,
      interpExpr_const_charOfNat hs, interpExpr_strLitList hs cs,
      interpExpr_lit hnat]

/-- The constructor form of a string literal interprets to the
literal's value (given the guard). -/
theorem interpExpr_strLitToConstructor {cval : ConstVal V}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} {s : String} :
    interpExpr V cval env φ d ρ (strLitToConstructor s) =
      interpExpr V cval env φ d ρ (.lit (.strVal s)) := by
  rw [strLitToConstructor_eq, interpExpr_strLit (V := V) hs]
  simp only [interpExpr, interpExpr_const_stringOfList hs,
    interpExpr_strLitList hs s.toList]
  rw [strLitVal]
  simp [Level.substFn_nil]

end Setlec
