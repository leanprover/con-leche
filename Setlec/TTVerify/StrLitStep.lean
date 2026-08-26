import Setlec.TTVerify.InferStep

/-!
# The string-literal clause

`InferStrLitStepTT`: a `String` literal is typed at `String`.

The shape of the work is the `Nat` one over again, and the reason is
§8.4: `strLitSupported` pins the **exact stored type** of each of the
ten support constants, so `EnvTT.has_type` at one of them yields a
typing at a type the bridge can compute.  Nothing here inspects a
value; every step is "the guard says the type is *this*, so the
environment's typing is at *this*".

The chain, read outwards from a character:

```
⌜k⌝ : Nat                    numerals (Setlec/TT/Nat/*)
Char.ofNat ⌜k⌝ : Char        the pinned `Nat → Char`
List.cons.{0} Char … : List.{0} Char
String.ofList … : String     the pinned `List.{0} Char → String`
```
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The workhorse

Every clause below is this lemma at a different constant: the guard
says what the stored type is, the environment says the valuation is
derivably of it. -/

/-- A stored constant is derivably of its stored type, in any context,
at any level assignment. -/
theorem cval_hasType {env : Env} (m : EnvTT env) {c : Name}
    {ci : ConstantInfo} {t : VExpr} (hf : env.find? c = some ci)
    (ψ : Name → Nat)
    (ht : denoteClosed m.cval env ψ ci.toConstantVal.type = some t)
    {Δ : List VExpr} : HasType Δ (m.cval c ψ) t := by
  obtain ⟨t', ht', hd⟩ := m.has_type ci (find?_mem hf) ψ
  obtain rfl : t' = t := by rw [ht'] at ht; exact Option.some.inj ht
  obtain rfl : ci.name = c := by
    rw [Env.find?] at hf
    have := List.find?_some hf
    simpa using this
  exact HasType.weakenNil hd Δ

/-! ## The pinned shapes

Each guard component is a `match` on the stored declaration, so
extracting the shape is a `split` and a `simp`.  They are separated
from the typings below because the *shape* facts are about `Env` alone
and would move to `Setlec/Verify/*` with the rest of the stranded
guard machinery. -/

/-- `Char : Type`. -/
theorem char_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci, env.find? charName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type = .sort (.succ .zero) := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, h6⟩, -⟩ := hg
  cases hf : env.find? charName with
  | none => rw [hf] at h6; exact nomatch h6
  | some ci =>
    rw [hf] at h6
    simp only [charTyOk, Bool.and_eq_true, beq_iff_eq] at h6
    exact ⟨ci, rfl, by simpa [List.isEmpty_iff] using h6.1, h6.2⟩

/-- `String : Type`. -/
theorem string_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci, env.find? stringName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type = .sort (.succ .zero) := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, h1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg
  cases hf : env.find? stringName with
  | none => rw [hf] at h1; exact nomatch h1
  | some ci =>
    rw [hf] at h1
    simp only [stringTyOk, Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨ci, rfl, by simpa [List.isEmpty_iff] using h1.1, h1.2⟩

/-- `Char.ofNat : Nat → Char`. -/
theorem charOfNat_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci nm mb, env.find? charOfNatName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type =
        .forallE nm (.const natName []) (.const charName []) mb := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, h7⟩ := hg
  cases hf : env.find? charOfNatName with
  | none => rw [hf] at h7; exact nomatch h7
  | some ci =>
    rw [hf] at h7
    simp only [charOfNatTyOk, Bool.and_eq_true] at h7
    obtain ⟨he, hty⟩ := h7
    split at hty
    · next nm c1 c2 mb hsh =>
      simp only [beq_iff_eq, Bool.and_eq_true] at hty
      obtain ⟨rfl, rfl⟩ := hty
      exact ⟨ci, nm, mb, rfl, by simpa [List.isEmpty_iff] using he, hsh⟩
    · exact nomatch hty

/-- `String.ofList : List.{0} Char → String`. -/
theorem stringOfList_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci nm mb, env.find? stringOfListName = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type =
        .forallE nm (.app (.const listName [.zero]) (.const charName []))
          (.const stringName []) mb := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hg
  cases hf : env.find? stringOfListName with
  | none => rw [hf] at h2; exact nomatch h2
  | some ci =>
    rw [hf] at h2
    simp only [stringOfListTyOk, Bool.and_eq_true] at h2
    obtain ⟨he, hty⟩ := h2
    split at hty
    · next nm l1 us1 c1 c2 mb hsh =>
      simp only [beq_iff_eq, Bool.and_eq_true] at hty
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hty
      exact ⟨ci, nm, mb, rfl, by simpa [List.isEmpty_iff] using he, hsh⟩
    · exact nomatch hty

/-! ## The typings

Each is `cval_hasType` at a shape, with the stored type denoted.  The
`Nat`-literal machinery supplies the one non-constant piece
(`natLitT_eq_numeral`), and `strLitSupported` contains
`natLitSupported`, so the two guards never have to be carried
separately. -/

/-- `Char` is a type. -/
theorem hasType_charT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) {Δ : List VExpr} :
    HasType Δ (m.cval charName φ) (.sort 1) := by
  obtain ⟨ci, hf, -, hty⟩ := char_shape hg
  refine cval_hasType m hf φ ?_
  rw [denoteClosed, hty, denote_sort]
  rfl

/-- `Char.ofNat` takes a `Nat` to a `Char`. -/
theorem hasType_charOfNat {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) {Δ : List VExpr} :
    HasType Δ (m.cval charOfNatName φ)
      (.pi natT (m.cval charName φ)) := by
  have hnat : natLitSupported env = true := by
    simp only [strLitSupported, Bool.and_eq_true] at hg
    exact hg.1.1.1.1.1.1.1
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  obtain ⟨ci, nm, mb, hf, -, hty⟩ := charOfNat_shape hg
  refine cval_hasType m hf φ ?_
  rw [denoteClosed, hty, denote_forallE, denote_natT_const m φ hnat,
    show ((Expr.const charName []).instantiate1
      (.fvar 0 nm (.const natName []))) = .const charName [] from rfl,
    denote_const_nolevels m φ hfC hlpC 1]

/-- `String.ofList` takes a `List.{0} Char` to a `String`. -/
theorem hasType_stringOfList {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) {Δ : List VExpr}
    {listChar : VExpr}
    (hlc : denote m.cval env φ 0
      (.app (.const listName [.zero]) (.const charName [])) = some listChar) :
    HasType Δ (m.cval stringOfListName φ)
      (.pi listChar (m.cval stringName φ)) := by
  obtain ⟨ciS, hfS, hlpS, -⟩ := string_shape hg
  obtain ⟨ci, nm, mb, hf, -, hty⟩ := stringOfList_shape hg
  refine cval_hasType m hf φ ?_
  rw [denoteClosed, hty, denote_forallE, hlc,
    show ((Expr.const stringName []).instantiate1
      (.fvar 0 nm (.app (.const listName [.zero]) (.const charName [])))) =
      .const stringName [] from rfl,
    denote_const_nolevels m φ hfS hlpS 1]

/-! ## The list constructors

`List.nil` and `List.cons` are the two support constants with a level
parameter, and `strLitT` instantiates it at `Level.zero`.  Their types
therefore have to be denoted at the *substituted* assignment, which is
where `EnvTT.val_params` earns its keep: the assignment `strLitT` uses
and the one the stored type is denoted at differ only away from the
constant's own parameters, so the valuation cannot tell them apart. -/

/-- `List.nil.{p} : ∀ (α : Sort (p+1)), List.{p} α`. -/
theorem listNil_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci p nm mb, env.find? listNilName = some ci ∧
      ci.toConstantVal.levelParams = [p] ∧
      ci.toConstantVal.type =
        .forallE nm (.sort (.succ (.param p)))
          (.app (.const listName [.param p]) (.bvar 0)) mb := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h4⟩, -⟩, -⟩, -⟩ := hg
  cases hf : env.find? listNilName with
  | none => rw [hf] at h4; exact nomatch h4
  | some ci =>
    rw [hf] at h4
    simp only [listNilTyOk] at h4
    split at h4
    · next p hlp =>
      split at h4
      · next nm u1 l1 us1 mb hsh =>
        simp only [beq_iff_eq, Bool.and_eq_true] at h4
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
        exact ⟨ci, p, nm, mb, rfl, hlp, hsh⟩
      · exact nomatch h4
    · exact nomatch h4

/-- `List.cons.{p} : ∀ (α : Sort (p+1)) (_ : α) (_ : List.{p} α),
List.{p} α`. -/
theorem listCons_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci p nm₁ nm₂ nm₃ mb₁ mb₂ mb₃, env.find? listConsName = some ci ∧
      ci.toConstantVal.levelParams = [p] ∧
      ci.toConstantVal.type =
        .forallE nm₁ (.sort (.succ (.param p)))
          (.forallE nm₂ (.bvar 0)
            (.forallE nm₃ (.app (.const listName [.param p]) (.bvar 1))
              (.app (.const listName [.param p]) (.bvar 2)) mb₃) mb₂) mb₁ := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, h5⟩, -⟩, -⟩ := hg
  cases hf : env.find? listConsName with
  | none => rw [hf] at h5; exact nomatch h5
  | some ci =>
    rw [hf] at h5
    simp only [listConsTyOk] at h5
    split at h5
    · next p hlp =>
      split at h5
      · next nm₁ u1 nm₂ nm₃ l1 us1 l2 us2 mb₃ mb₂ mb₁ hsh =>
        simp only [beq_iff_eq, Bool.and_eq_true] at h5
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h5
        exact ⟨ci, p, nm₁, nm₂, nm₃, mb₁, mb₂, mb₃, rfl, hlp, hsh⟩
      · exact nomatch h5
    · exact nomatch h5

/-- `List.{p} : Sort (p+1) → Sort (p+1)`; only the parameter count is
used below. -/
theorem list_shape {env : Env} (hg : strLitSupported env = true) :
    ∃ ci p, env.find? listName = some ci ∧
      ci.toConstantVal.levelParams = [p] := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h3⟩, -⟩, -⟩, -⟩, -⟩ := hg
  cases hf : env.find? listName with
  | none => rw [hf] at h3; exact nomatch h3
  | some ci =>
    rw [hf] at h3
    simp only [listTyOk] at h3
    split at h3
    · next p hlp => exact ⟨ci, p, rfl, hlp⟩
    · exact nomatch h3

/-- The `List Char` type as `strLitT` builds it. -/
def listCharT {env : Env} (m : EnvTT env) (φ : Name → Nat) : VExpr :=
  .app (m.cval listName
    (Level.substFn φ (levelParamsAt env listName) [.zero]))
    (m.cval charName φ)

/-- The valuation `List`'s own type is denoted at, and the one
`strLitT` reads it at, agree on `List`'s parameters — so the valuation
cannot tell them apart (`EnvTT.val_params`). -/
theorem cval_list_eq {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) {p : Name} (ψ : Name → Nat)
    (hψ : ψ p = 0) :
    m.cval listName (Level.substFn ψ (levelParamsAt env listName)
        [.param p])
      = m.cval listName
        (Level.substFn φ (levelParamsAt env listName) [.zero]) := by
  obtain ⟨ci, q, hf, hlp⟩ := list_shape hg
  have hlpa : levelParamsAt env listName = [q] := by
    simp [levelParamsAt, hf, hlp]
  refine m.val_params listName ci hf _ _ ?_
  intro r hr
  rw [hlp] at hr
  obtain rfl : r = q := by simpa using hr
  rw [hlpa]
  simp [Level.substFn, hψ, Level.eval]

/-- The empty character list is a `List Char`. -/
theorem hasType_nilTerm {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) {Δ : List VExpr} :
    HasType Δ (.app (m.cval listNilName
        (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
      (m.cval charName φ)) (listCharT m φ) := by
  obtain ⟨ci, p, nm, mb, hf, hlp, hty⟩ := listNil_shape hg
  have hlpa : levelParamsAt env listNilName = [p] := by
    simp [levelParamsAt, hf, hlp]
  have hψ : (Level.substFn φ (levelParamsAt env listNilName) [.zero]) p
      = 0 := by simp [hlpa, Level.substFn, Level.eval]
  have hnil := cval_hasType m hf
    (Level.substFn φ (levelParamsAt env listNilName) [.zero])
    (t := .pi (.sort 1) (.app (m.cval listName
      (Level.substFn φ (levelParamsAt env listName) [.zero])) (.bvar 0)))
    (Δ := Δ) ?_
  · have := HasType.app hnil (hasType_charT m φ hg (Δ := Δ))
    simpa [listCharT, VExpr.inst,
      VExpr.inst_eq_self_of_closed (m.cval_closed listName _),
      VExpr.liftN_eq_self_of_closed (m.cval_closed charName _)] using this
  · obtain ⟨ciL, q, hfL, hlpL⟩ := list_shape hg
    have hlpaL : ciL.toConstantVal.levelParams
        = levelParamsAt env listName := by simp [levelParamsAt, hfL]
    rw [denoteClosed, hty, denote_forallE, denote_sort,
      show ((Expr.app (.const listName [.param p]) (.bvar 0)).instantiate1
        (.fvar 0 nm (.sort (.succ (.param p))))) =
        .app (.const listName [.param p])
          (.fvar 0 nm (.sort (.succ (.param p)))) from rfl,
      denote_app, denote_fvar, denote_const, hfL]
    dsimp only
    rw [hlpaL, if_pos (by rw [← hlpaL]; simp [hlpL]),
      cval_list_eq m φ hg _ hψ]
    simp [Level.eval, hψ]

/-- `List.cons` at `Char` takes a head and a tail. -/
theorem hasType_consTerm {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) {Δ : List VExpr} :
    HasType Δ (.app (m.cval listConsName
        (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
      (m.cval charName φ))
      (.pi (m.cval charName φ)
        (.pi (listCharT m φ) (listCharT m φ))) := by
  obtain ⟨ci, p, nm₁, nm₂, nm₃, mb₁, mb₂, mb₃, hf, hlp, hty⟩ :=
    listCons_shape hg
  have hlpa : levelParamsAt env listConsName = [p] := by
    simp [levelParamsAt, hf, hlp]
  have hψ : (Level.substFn φ (levelParamsAt env listConsName) [.zero]) p
      = 0 := by simp [hlpa, Level.substFn, Level.eval]
  have hcons := cval_hasType m hf
    (Level.substFn φ (levelParamsAt env listConsName) [.zero])
    (t := .pi (.sort 1) (.pi (.bvar 0)
      (.pi (.app (m.cval listName
          (Level.substFn φ (levelParamsAt env listName) [.zero])) (.bvar 1))
        (.app (m.cval listName
          (Level.substFn φ (levelParamsAt env listName) [.zero]))
          (.bvar 2)))))
    (Δ := Δ) ?_
  · have := HasType.app hcons (hasType_charT m φ hg (Δ := Δ))
    simpa [listCharT, VExpr.inst,
      VExpr.inst_eq_self_of_closed (m.cval_closed listName _),
      VExpr.liftN_eq_self_of_closed (m.cval_closed charName _)] using this
  · obtain ⟨ciL, q, hfL, hlpL⟩ := list_shape hg
    have hlpaL : ciL.toConstantVal.levelParams
        = levelParamsAt env listName := by simp [levelParamsAt, hfL]
    rw [denoteClosed, hty, denote_forallE, denote_sort]
    rw [show ((Expr.forallE nm₂ (.bvar 0)
        (.forallE nm₃ (.app (.const listName [.param p]) (.bvar 1))
          (.app (.const listName [.param p]) (.bvar 2)) mb₃)
        mb₂).instantiate1 (.fvar 0 nm₁ (.sort (.succ (.param p))))) =
      .forallE nm₂ (.fvar 0 nm₁ (.sort (.succ (.param p))))
        (.forallE nm₃ (.app (.const listName [.param p])
            (.fvar 0 nm₁ (.sort (.succ (.param p)))))
          (.app (.const listName [.param p])
            (.fvar 0 nm₁ (.sort (.succ (.param p))))) mb₃) mb₂ from rfl]
    rw [denote_forallE, denote_fvar]
    rw [show ((Expr.forallE nm₃ (.app (.const listName [.param p])
          (.fvar 0 nm₁ (.sort (.succ (.param p)))))
        (.app (.const listName [.param p])
          (.fvar 0 nm₁ (.sort (.succ (.param p))))) mb₃).instantiate1
        (.fvar 1 nm₂ (.fvar 0 nm₁ (.sort (.succ (.param p)))))) =
      .forallE nm₃ (.app (.const listName [.param p])
          (.fvar 0 nm₁ (.sort (.succ (.param p)))))
        (.app (.const listName [.param p])
          (.fvar 0 nm₁ (.sort (.succ (.param p))))) mb₃ from rfl]
    rw [denote_forallE, denote_app, denote_fvar, denote_const, hfL]
    dsimp only
    rw [hlpaL, if_pos (by rw [← hlpaL]; simp [hlpL]),
      cval_list_eq m φ hg _ hψ]
    rw [show ((Expr.app (.const listName [.param p])
        (.fvar 0 nm₁ (.sort (.succ (.param p))))).instantiate1
        (.fvar 2 nm₃ (.app (.const listName [.param p])
          (.fvar 0 nm₁ (.sort (.succ (.param p))))))) =
      .app (.const listName [.param p])
        (.fvar 0 nm₁ (.sort (.succ (.param p)))) from rfl]
    rw [denote_app, denote_fvar, denote_const, hfL]
    dsimp only
    rw [hlpaL, if_pos (by rw [← hlpaL]; simp [hlpL]),
      cval_list_eq m φ hg _ hψ]
    simp [Level.eval, hψ]

/-! ## The chain

Everything above is per-constant; this is the induction that strings
them together, and it is the only recursion in the module — over the
*meta-level* character list, exactly as the `Nat` families recurse over
the meta-level numeral. -/

/-- The `List Char` type, denoted. -/
theorem denote_listCharT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) (d : Nat) :
    denote m.cval env φ d
        (.app (.const listName [.zero]) (.const charName []))
      = some (listCharT m φ) := by
  obtain ⟨ciL, q, hfL, hlpL⟩ := list_shape hg
  obtain ⟨ciC, hfC, hlpC, -⟩ := char_shape hg
  have hlpaL : ciL.toConstantVal.levelParams
      = levelParamsAt env listName := by simp [levelParamsAt, hfL]
  rw [denote_app, denote_const, hfL]
  dsimp only
  rw [hlpaL, if_pos (by rw [← hlpaL]; simp [hlpL]),
    denote_const_nolevels m φ hfC hlpC d]
  rfl

/-- A character's term is a `Char`. -/
theorem hasType_charTerm {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) {Δ : List VExpr} (k : Nat) :
    HasType Δ (.app (m.cval charOfNatName φ) (numeral k))
      (m.cval charName φ) := by
  have := HasType.app (hasType_charOfNat m φ hg (Δ := Δ))
    (hasType_numeral (Γ := Δ) k)
  simpa [VExpr.inst_eq_self_of_closed (m.cval_closed charName φ)] using this

/-- A character list's term is a `List Char`. -/
theorem hasType_charListT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) {Δ : List VExpr} :
    ∀ cs : List Char,
      HasType Δ (charListT
        (.app (m.cval listNilName
          (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
          (m.cval charName φ))
        (.app (m.cval listConsName
          (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
          (m.cval charName φ))
        (m.cval charOfNatName φ) (m.cval natZeroName φ)
        (m.cval natSuccName φ) cs)
        (listCharT m φ) := by
  have hnat : natLitSupported env = true := by
    simp only [strLitSupported, Bool.and_eq_true] at hg
    exact hg.1.1.1.1.1.1.1
  intro cs
  induction cs with
  | nil => exact hasType_nilTerm m φ hg
  | cons c cs ih =>
    rw [charListT, natLitT_eq_numeral m hnat φ]
    have h1 := HasType.app (hasType_consTerm m φ hg (Δ := Δ))
      (hasType_charTerm m φ hg c.toNat)
    have h2 := HasType.app
      (show HasType Δ _ (.pi (listCharT m φ) (listCharT m φ)) from by
        simpa [VExpr.inst,
          VExpr.inst_eq_self_of_closed (m.cval_closed listName _),
          VExpr.inst_eq_self_of_closed (m.cval_closed charName _),
          listCharT] using h1) ih
    simpa [VExpr.inst, substFn_nil,
      VExpr.inst_eq_self_of_closed (m.cval_closed listName _),
      VExpr.inst_eq_self_of_closed (m.cval_closed charName _),
      listCharT] using h2

/-- **A string literal's term is a `String`.** -/
theorem hasType_strLitT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) {Δ : List VExpr} (s : String) :
    HasType Δ (strLitT m.cval env φ s) (m.cval stringName φ) := by
  simp only [strLitT, substFn_nil]
  have := HasType.app
    (hasType_stringOfList m φ hg (Δ := Δ) (denote_listCharT m φ hg 0))
    (hasType_charListT m φ hg s.toList)
  simpa [substFn_nil,
    VExpr.inst_eq_self_of_closed (m.cval_closed stringName φ)] using this

/-- **`InferStrLitStepTT`, discharged.** -/
theorem infer_strLit_step {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} : InferStrLitStepTT m φ fuel := by
  intro d Δ str t h
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · next hg =>
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨ciS, hfS, hlpS, -⟩ := string_shape hg
    refine ⟨strLitT m.cval env φ str, m.cval stringName φ, ?_, ?_, ?_⟩
    · rw [denote_strLit, if_pos hg]
    · exact denote_const_nolevels m φ hfS hlpS d
    · exact hasType_strLitT m φ hg str
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `InferClaimsTT` at `fuel + 1` with the string-literal obligation
discharged; only the projection clause remains. -/
theorem infer_claimsTT_strLit {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hproj : InferProjStepTT m φ fuel)
    (ihw : WhnfClaimsTT m φ fuel) (ihd : DefEqClaimsTT m φ fuel)
    (ihi : InferClaimsTT m φ fuel) :
    InferClaimsTT m φ (fuel + 1) :=
  infer_claimsTT m φ hcl (infer_strLit_step m φ) hproj ihw ihd ihi

end Setlec.TTVerify
