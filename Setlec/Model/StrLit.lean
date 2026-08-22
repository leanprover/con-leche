import Setlec.Model.NatLit
import Setlec.Verify.StrLitExpr

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

/-- The `List.{0} Char` value the literal machinery types its character
lists with. -/
def listCharVal (cval : ConstVal V) (env : Env) (φ : Name → Nat) : V :=
  SetTheory.app
    (cval listName (Level.substFn φ (env.levelParamsAt listName) [.zero]))
    (cval charName φ)

/-- The interpretation of `List.{0} Char` (given the guard). -/
theorem interpExpr_listChar {cval : ConstVal V}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ
        (.app (.const listName [.zero]) (.const charName [])) =
      some (listCharVal cval env φ) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, -⟩ :=
    strLitSupported_inv hs
  have hlp : env.levelParamsAt listName = ciL.toConstantVal.levelParams := by
    simp [Env.levelParamsAt, hfL]
  rw [listCharVal, hlp]
  simp [interpExpr, hfL, hfH, hpH, hpL, Level.substFn_nil]

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

/-! ## Membership facts (environments with a model)

Derived from `EnvModel.mem_type` and the guard's shape facts alone, with
no `String`-specific model assumptions — mirroring the `Nat` facts in
`Setlec.Model.NatLit`. -/

/-- The `String` value lives in `univ 1`. -/
theorem stringVal_mem_univ (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) :
    m.val stringName φ ∈ˢ (univ 1 : V) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, htS, -⟩ :=
    strLitSupported_inv hs
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hfS) φ
  rw [htS] at ht
  rw [find?_name' hfS] at hmem
  simp only [interpClosed, interpExpr, Option.some.injEq] at ht
  subst ht
  simpa only [Level.eval] using hmem

/-- The `Char` value lives in `univ 1`. -/
theorem charVal_mem_univ (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) :
    m.val charName φ ∈ˢ (univ 1 : V) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, htS, htH, -⟩ :=
    strLitSupported_inv hs
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hfH) φ
  rw [htH] at ht
  rw [find?_name' hfH] at hmem
  simp only [interpClosed, interpExpr, Option.some.injEq] at ht
  subst ht
  simpa only [Level.eval] using hmem

/-- The `List` value (own parameter at `0`) is a function from `univ 1`
to `univ 1`. -/
theorem listVal_mem_pi (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) :
    m.val listName (Level.substFn φ (env.levelParamsAt listName) [.zero]) ∈ˢ
      pi 2 (univ 1 : V) (fun _ => univ 1) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, htS, htH, htO,
    htL, -⟩ := strLitSupported_inv hs
  obtain ⟨nm, mb, htyL, hcodL⟩ := htL
  have hlp : env.levelParamsAt listName = [pL] := by
    simp [Env.levelParamsAt, hfL, hpL]
  rw [hlp]
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hfL)
    (Level.substFn φ [pL] [.zero])
  rw [htyL] at ht
  rw [find?_name' hfL] at hmem
  rw [interpClosed, interpExpr] at ht
  rw [hcodL] at ht
  simp only [interpExpr, Option.getD_some, Option.some.injEq,
    show ((Expr.sort (.succ (.param pL))).instantiate1
      (.fvar 0 nm (.sort (.succ (.param pL))))) =
      .sort (.succ (.param pL)) from rfl] at ht
  subst ht
  simpa [Level.eval, Level.substFn] using hmem

/-- The `List.{0} Char` value lives in `univ 1`. -/
theorem listCharVal_mem_univ (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) :
    listCharVal m.val env φ ∈ˢ (univ 1 : V) := by
  rw [listCharVal]
  exact app_mem (listVal_mem_pi m hs φ) (charVal_mem_univ m hs φ)
    (fun x hx => univ_mem_univ 1)

/-- The `Char.ofNat` value is a member of the constant function space
from the `Nat` value to the `Char` value. -/
theorem charOfNatVal_mem_pi (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) :
    m.val charOfNatName φ ∈ˢ
      pi 1 (m.val natName φ) (fun _ => m.val charName φ) := by
  obtain ⟨hnat, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, htS, htH, htO,
    htL, htN, htC, htF⟩ := strLitSupported_inv hs
  obtain ⟨nm, mb, htyF, hcodF⟩ := htF
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hfF) φ
  rw [htyF] at ht
  rw [find?_name' hfF] at hmem
  rw [interpClosed, interpExpr] at ht
  rw [hcodF] at ht
  rw [interpExpr_const_nat hnat] at ht
  simp only [show ((Expr.const charName []).instantiate1
      (.fvar 0 nm (.const natName []))) = .const charName [] from rfl,
    interpExpr_const_char hs, Option.getD_some, Option.some.injEq,
    Level.eval] at ht
  subst ht
  exact hmem

/-- `Char.ofNat` of a numeral value is a member of the `Char` value. -/
theorem charOfNatVal_app_mem (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) {x : V}
    (hx : x ∈ˢ m.val natName φ) :
    SetTheory.app (m.val charOfNatName φ) x ∈ˢ m.val charName φ :=
  app_mem (charOfNatVal_mem_pi m hs φ) hx
    (fun _ _ => charVal_mem_univ m hs φ)

/-- Applying the `List` value keeps `univ 1`. -/
theorem listVal_app_mem_univ (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) {x : V}
    (hx : x ∈ˢ (univ 1 : V)) :
    SetTheory.app
      (m.val listName (Level.substFn φ (env.levelParamsAt listName) [.zero]))
      x ∈ˢ (univ 1 : V) :=
  app_mem (listVal_mem_pi m hs φ) hx (fun _ _ => univ_mem_univ 1)

/-- The `List.nil.{0} Char` value... helper: `List.nil` itself lives in
the dependent product over `univ 1` with the canonical `List` family. -/
theorem listNilVal_mem_pi (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) :
    m.val listNilName
        (Level.substFn φ (env.levelParamsAt listNilName) [.zero]) ∈ˢ
      pi 1 (univ 1 : V) (fun x => SetTheory.app
        (m.val listName
          (Level.substFn φ (env.levelParamsAt listName) [.zero])) x) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, htS, htH, htO,
    htL, htN, -⟩ := strLitSupported_inv hs
  obtain ⟨nm, mb, htyN, hcodN⟩ := htN
  have hlpN : env.levelParamsAt listNilName = [pN] := by
    simp [Env.levelParamsAt, hfN, hpN]
  have hlpL : env.levelParamsAt listName = [pL] := by
    simp [Env.levelParamsAt, hfL, hpL]
  rw [hlpN, hlpL]
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hfN)
    (Level.substFn φ [pN] [.zero])
  rw [htyN] at ht
  rw [find?_name' hfN] at hmem
  -- the stored type's interpretation, computed
  have hIN : interpClosed V m.val env (Level.substFn φ [pN] [Level.zero])
      (Expr.forallE nm (.sort (.succ (.param pN)))
        (.app (.const listName [.param pN]) (.bvar 0)) mb) =
      some (pi 1 (univ 1) (fun x =>
        SetTheory.app (m.val listName
          (Level.substFn (Level.substFn φ [pN] [Level.zero]) [pL]
            [.param pN])) x)) := by
    rw [interpClosed, interpExpr, hcodN]
    simp [interpExpr, instantiate1, hfL, hpL, updV, Level.eval,
      Level.substFn]
  rw [hIN] at ht
  obtain rfl := Option.some.inj ht
  -- canonicalize the family's `List` instantiation (both send `List`'s
  -- parameter to `0`)
  have hvals : m.val listName
      (Level.substFn (Level.substFn φ [pN] [Level.zero]) [pL] [.param pN]) =
      m.val listName (Level.substFn φ [pL] [Level.zero]) := by
    refine m.val_params _ _ hfL _ _ ?_
    rw [hpL]
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    simp [Level.substFn, Level.eval]
  rw [hvals] at hmem
  exact hmem

/-- The `List.nil.{0} Char` value is a member of the `List.{0} Char`
value. -/
theorem listNilCharVal_mem (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) :
    SetTheory.app
        (m.val listNilName
          (Level.substFn φ (env.levelParamsAt listNilName) [.zero]))
        (m.val charName φ) ∈ˢ
      listCharVal m.val env φ := by
  rw [listCharVal]
  exact app_mem (listNilVal_mem_pi m hs φ) (charVal_mem_univ m hs φ)
    (fun x hx => listVal_app_mem_univ m hs φ hx)

/-- The `List.cons.{0} Char` machinery, step one: `List.cons` itself
lives in the dependent product over `univ 1` with the canonical
families. -/
theorem listConsVal_mem_pi (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) :
    m.val listConsName
        (Level.substFn φ (env.levelParamsAt listConsName) [.zero]) ∈ˢ
      pi 1 (univ 1 : V) (fun x => pi 1 x (fun _ =>
        pi 1 (SetTheory.app (m.val listName
            (Level.substFn φ (env.levelParamsAt listName) [.zero])) x)
          (fun _ => SetTheory.app (m.val listName
            (Level.substFn φ (env.levelParamsAt listName) [.zero])) x))) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, htS, htH, htO,
    htL, htN, htC, -⟩ := strLitSupported_inv hs
  obtain ⟨nm1, nm2, nm3, mb1, mb2, mb3, htyC, hcod3, hcod2, hcod1⟩ := htC
  have hlpC : env.levelParamsAt listConsName = [pC] := by
    simp [Env.levelParamsAt, hfC, hpC]
  have hlpL : env.levelParamsAt listName = [pL] := by
    simp [Env.levelParamsAt, hfL, hpL]
  rw [hlpC, hlpL]
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hfC)
    (Level.substFn φ [pC] [.zero])
  rw [htyC] at ht
  rw [find?_name' hfC] at hmem
  -- the family's `List` instantiation agrees with the canonical one
  have hvals : m.val listName
      (Level.substFn (Level.substFn φ [pC] [Level.zero]) [pL] [.param pC]) =
      m.val listName (Level.substFn φ [pL] [Level.zero]) := by
    refine m.val_params _ _ hfL _ _ ?_
    rw [hpL]
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    simp [Level.substFn, Level.eval]
  -- the stored type's interpretation, computed
  have hIC : interpClosed V m.val env (Level.substFn φ [pC] [Level.zero])
      (Expr.forallE nm1 (.sort (.succ (.param pC)))
        (.forallE nm2 (.bvar 0)
          (.forallE nm3 (.app (.const listName [.param pC]) (.bvar 1))
            (.app (.const listName [.param pC]) (.bvar 2)) mb3) mb2) mb1) =
      some (pi 1 (univ 1) (fun x => pi 1 x (fun _ =>
        pi 1 (SetTheory.app (m.val listName
            (Level.substFn (Level.substFn φ [pC] [Level.zero]) [pL]
              [.param pC])) x)
          (fun _ => SetTheory.app (m.val listName
            (Level.substFn (Level.substFn φ [pC] [Level.zero]) [pL]
              [.param pC])) x)))) := by
    rw [interpClosed, interpExpr, hcod1]
    simp [interpExpr, instantiate1, hcod2, hcod3, hfL, hpL, updV,
      Level.eval, Level.substFn]
  rw [hIC] at ht
  obtain rfl := Option.some.inj ht
  rw [hvals] at hmem
  exact hmem

/-- The `List.cons.{0} Char` value is a member of the function space
`Char → List Char → List Char` (constant families over the canonical
values). -/
theorem listConsCharVal_mem_pi (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) :
    SetTheory.app
        (m.val listConsName
          (Level.substFn φ (env.levelParamsAt listConsName) [.zero]))
        (m.val charName φ) ∈ˢ
      pi 1 (m.val charName φ)
        (fun _ => pi 1 (listCharVal m.val env φ)
          (fun _ => listCharVal m.val env φ)) := by
  have happ := app_mem (listConsVal_mem_pi m hs φ) (charVal_mem_univ m hs φ)
    (fun x hx => by
      have hLx : SetTheory.app (m.val listName
          (Level.substFn φ (env.levelParamsAt listName) [.zero])) x ∈ˢ
          (univ 1 : V) := listVal_app_mem_univ m hs φ hx
      have h1 : pi 1 (SetTheory.app (m.val listName
          (Level.substFn φ (env.levelParamsAt listName) [.zero])) x)
          (fun _ => SetTheory.app (m.val listName
            (Level.substFn φ (env.levelParamsAt listName) [.zero])) x) ∈ˢ
          (univ 1 : V) := by
        simpa using pi_mem_univ (u := 1) (v := 1) hLx (fun _ _ => hLx)
      simpa using pi_mem_univ (u := 1) (v := 1) hx (fun _ _ => h1))
  rw [listCharVal]
  exact happ

/-- Every character-list value is a member of the `List.{0} Char`
value. -/
theorem charListVal_mem (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) :
    ∀ cs : List Char,
      charListVal V
        (SetTheory.app
          (m.val listNilName
            (Level.substFn φ (env.levelParamsAt listNilName) [.zero]))
          (m.val charName φ))
        (SetTheory.app
          (m.val listConsName
            (Level.substFn φ (env.levelParamsAt listConsName) [.zero]))
          (m.val charName φ))
        (m.val charOfNatName φ) (m.val natZeroName φ) (m.val natSuccName φ)
        cs ∈ˢ listCharVal m.val env φ
  | [] => by
    rw [charListVal]
    exact listNilCharVal_mem m hs φ
  | c :: cs => by
    obtain ⟨hnat, -⟩ := strLitSupported_inv hs
    rw [charListVal]
    have hchar : SetTheory.app (m.val charOfNatName φ)
        (natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) c.toNat) ∈ˢ
        m.val charName φ :=
      charOfNatVal_app_mem m hs φ (natLitVal_mem_nat m hnat φ c.toNat)
    have hlist : pi 1 (listCharVal m.val env φ)
        (fun _ => listCharVal m.val env φ) ∈ˢ (univ 1 : V) := by
      simpa using pi_mem_univ (u := 1) (v := 1)
        (listCharVal_mem_univ m hs φ) (fun _ _ => listCharVal_mem_univ m hs φ)
    have hcons := app_mem (listConsCharVal_mem_pi m hs φ) hchar
      (fun _ _ => hlist)
    exact app_mem hcons (charListVal_mem m hs φ cs)
      (fun _ _ => listCharVal_mem_univ m hs φ)

/-- The `String.ofList` value is a member of the constant function
space from the `List.{0} Char` value to the `String` value. -/
theorem stringOfListVal_mem_pi (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) :
    m.val stringOfListName φ ∈ˢ
      pi 1 (listCharVal m.val env φ) (fun _ => m.val stringName φ) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, htS, htH, htO,
    -⟩ := strLitSupported_inv hs
  obtain ⟨nm, mb, htyO, hcodO⟩ := htO
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hfO) φ
  rw [htyO] at ht
  rw [find?_name' hfO] at hmem
  have hIO : interpClosed V m.val env φ
      (Expr.forallE nm
        (.app (.const listName [Level.zero]) (.const charName []))
        (.const stringName []) mb) =
      some (pi 1 (listCharVal m.val env φ)
        (fun _ => m.val stringName φ)) := by
    rw [interpClosed, interpExpr, hcodO]
    rw [interpExpr_listChar hs]
    simp only [instantiate1, interpExpr_const_string hs, Option.getD_some,
      Level.eval]
  rw [hIO] at ht
  obtain rfl := Option.some.inj ht
  exact hmem

/-- The value of a string literal is a member of the `String` value —
the membership fact behind the literal's inference rule. -/
theorem strLitVal_mem_string (m : EnvModel V env)
    (hs : strLitSupported env = true) (φ : Name → Nat) (s : String) :
    strLitVal V m.val env φ s ∈ˢ m.val stringName φ := by
  rw [strLitVal]
  simp only [Level.substFn_nil]
  exact app_mem (stringOfListVal_mem_pi m hs φ)
    (charListVal_mem m hs φ s.toList)
    (fun _ _ => stringVal_mem_univ m hs φ)

/-! ## Truthful annotations on the constructor form -/

/-- The interpretation of the bare `List.nil.{0}` constant (given the
guard). -/
theorem interpExpr_const_listNil {cval : ConstVal V}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ (.const listNilName [.zero]) =
      some (cval listNilName
        (Level.substFn φ (env.levelParamsAt listNilName) [.zero])) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, -⟩ :=
    strLitSupported_inv hs
  have hlp : env.levelParamsAt listNilName = ciN.toConstantVal.levelParams := by
    simp [Env.levelParamsAt, hfN]
  rw [hlp]
  simp [interpExpr, hfN, hpN]

/-- The interpretation of the bare `List.cons.{0}` constant (given the
guard). -/
theorem interpExpr_const_listCons {cval : ConstVal V}
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ (.const listConsName [.zero]) =
      some (cval listConsName
        (Level.substFn φ (env.levelParamsAt listConsName) [.zero])) := by
  obtain ⟨-, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO, hfL,
    hfN, hfC, hfH, hfF, hpS, hpO, hpL, hpN, hpC, hpH, hpF, -⟩ :=
    strLitSupported_inv hs
  have hlp : env.levelParamsAt listConsName = ciC.toConstantVal.levelParams := by
    simp [Env.levelParamsAt, hfC]
  rw [hlp]
  simp [interpExpr, hfC, hpC]

/-- The character-list expression carries truthful annotations: every
application spine slot is semantically well-typed. -/
theorem annotOk_strLitList (m : EnvModel V env)
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    ∀ cs : List Char, AnnotOk V m.val env φ d ρ (strLitList cs)
  | [] => by
    rw [strLitList]
    simp only [AnnotOk]
    exact ⟨trivial, trivial,
      m.val listNilName
        (Level.substFn φ (env.levelParamsAt listNilName) [.zero]),
      m.val charName φ, 1, univ 1,
      fun x => SetTheory.app
        (m.val listName
          (Level.substFn φ (env.levelParamsAt listName) [.zero])) x,
      interpExpr_const_listNil hs, interpExpr_const_char hs,
      listNilVal_mem_pi m hs φ, charVal_mem_univ m hs φ,
      fun x hx => listVal_app_mem_univ m hs φ hx⟩
  | c :: cs => by
    obtain ⟨hnat, -⟩ := strLitSupported_inv hs
    -- shared values
    have hchar : SetTheory.app (m.val charOfNatName φ)
        (natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) c.toNat) ∈ˢ
        m.val charName φ :=
      charOfNatVal_app_mem m hs φ (natLitVal_mem_nat m hnat φ c.toNat)
    have hLCV : listCharVal m.val env φ ∈ˢ (univ 1 : V) :=
      listCharVal_mem_univ m hs φ
    have hpiLCV : pi 1 (listCharVal m.val env φ)
        (fun _ => listCharVal m.val env φ) ∈ˢ (univ 1 : V) := by
      simpa using pi_mem_univ (u := 1) (v := 1) hLCV (fun _ _ => hLCV)
    -- interp of `Char.ofNat (lit c)`
    have hIofNat : interpExpr V m.val env φ d ρ
        (.app (.const charOfNatName []) (.lit (.natVal c.toNat))) =
        some (SetTheory.app (m.val charOfNatName φ)
          (natLitVal V (m.val natZeroName φ) (m.val natSuccName φ)
            c.toNat)) := by
      simp only [interpExpr, interpExpr_const_charOfNat hs,
        interpExpr_lit hnat]
    -- interp of `List.cons.{0} Char (Char.ofNat (lit c))`
    have hIcons2 : interpExpr V m.val env φ d ρ
        (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) =
        some (SetTheory.app (SetTheory.app
          (m.val listConsName
            (Level.substFn φ (env.levelParamsAt listConsName) [.zero]))
          (m.val charName φ))
          (SetTheory.app (m.val charOfNatName φ)
            (natLitVal V (m.val natZeroName φ) (m.val natSuccName φ)
              c.toNat))) := by
      simp only [interpExpr, interpExpr_listConsChar hs, hIofNat]
    rw [strLitList]
    simp only [AnnotOk]
    refine ⟨⟨?_, ?_, ?_⟩, annotOk_strLitList m hs cs, ?_⟩
    · -- `List.cons.{0} Char` node
      exact ⟨trivial, trivial,
        m.val listConsName
          (Level.substFn φ (env.levelParamsAt listConsName) [.zero]),
        m.val charName φ, 1, univ 1,
        fun x => pi 1 x (fun _ =>
          pi 1 (SetTheory.app (m.val listName
              (Level.substFn φ (env.levelParamsAt listName) [.zero])) x)
            (fun _ => SetTheory.app (m.val listName
              (Level.substFn φ (env.levelParamsAt listName) [.zero])) x)),
        interpExpr_const_listCons hs, interpExpr_const_char hs,
        listConsVal_mem_pi m hs φ, charVal_mem_univ m hs φ,
        fun x hx => by
          have hLx := listVal_app_mem_univ m hs φ hx
          have h1 : pi 1 (SetTheory.app (m.val listName
              (Level.substFn φ (env.levelParamsAt listName) [.zero])) x)
              (fun _ => SetTheory.app (m.val listName
                (Level.substFn φ (env.levelParamsAt listName) [.zero])) x)
              ∈ˢ (univ 1 : V) := by
            simpa using pi_mem_univ (u := 1) (v := 1) hLx (fun _ _ => hLx)
          simpa using pi_mem_univ (u := 1) (v := 1) hx (fun _ _ => h1)⟩
    · -- `Char.ofNat (lit c)` node
      exact ⟨trivial, trivial, m.val charOfNatName φ,
        natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) c.toNat,
        1, m.val natName φ, fun _ => m.val charName φ,
        interpExpr_const_charOfNat hs, interpExpr_lit hnat,
        charOfNatVal_mem_pi m hs φ, natLitVal_mem_nat m hnat φ c.toNat,
        fun _ _ => charVal_mem_univ m hs φ⟩
    · -- `(cons Char) (ofNat c)` application facts
      exact ⟨SetTheory.app
          (m.val listConsName
            (Level.substFn φ (env.levelParamsAt listConsName) [.zero]))
          (m.val charName φ),
        SetTheory.app (m.val charOfNatName φ)
          (natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) c.toNat),
        1, m.val charName φ,
        fun _ => pi 1 (listCharVal m.val env φ)
          (fun _ => listCharVal m.val env φ),
        interpExpr_listConsChar hs, hIofNat,
        listConsCharVal_mem_pi m hs φ, hchar, fun _ _ => hpiLCV⟩
    · -- top application onto the tail
      exact ⟨SetTheory.app (SetTheory.app
          (m.val listConsName
            (Level.substFn φ (env.levelParamsAt listConsName) [.zero]))
          (m.val charName φ))
          (SetTheory.app (m.val charOfNatName φ)
            (natLitVal V (m.val natZeroName φ) (m.val natSuccName φ)
              c.toNat)),
        charListVal V
          (SetTheory.app (m.val listNilName
            (Level.substFn φ (env.levelParamsAt listNilName) [.zero]))
            (m.val charName φ))
          (SetTheory.app (m.val listConsName
            (Level.substFn φ (env.levelParamsAt listConsName) [.zero]))
            (m.val charName φ))
          (m.val charOfNatName φ) (m.val natZeroName φ)
          (m.val natSuccName φ) cs,
        1, listCharVal m.val env φ, fun _ => listCharVal m.val env φ,
        hIcons2, interpExpr_strLitList hs cs,
        app_mem (listConsCharVal_mem_pi m hs φ) hchar
          (fun _ _ => hpiLCV),
        charListVal_mem m hs φ cs, fun _ _ => hLCV⟩

/-- The constructor form of a string literal carries truthful
annotations. -/
theorem annotOk_strLitToConstructor (m : EnvModel V env)
    (hs : strLitSupported env = true) {d : Nat} {ρ : Nat → V} {s : String} :
    AnnotOk V m.val env φ d ρ (strLitToConstructor s) := by
  rw [strLitToConstructor_eq]
  simp only [AnnotOk]
  exact ⟨trivial, annotOk_strLitList m hs s.toList,
    m.val stringOfListName φ,
    charListVal V
      (SetTheory.app (m.val listNilName
        (Level.substFn φ (env.levelParamsAt listNilName) [.zero]))
        (m.val charName φ))
      (SetTheory.app (m.val listConsName
        (Level.substFn φ (env.levelParamsAt listConsName) [.zero]))
        (m.val charName φ))
      (m.val charOfNatName φ) (m.val natZeroName φ) (m.val natSuccName φ)
      s.toList,
    1, listCharVal m.val env φ, fun _ => m.val stringName φ,
    interpExpr_const_stringOfList hs, interpExpr_strLitList hs s.toList,
    stringOfListVal_mem_pi m hs φ, charListVal_mem m hs φ s.toList,
    fun _ _ => stringVal_mem_univ m hs φ⟩

end Setlec
