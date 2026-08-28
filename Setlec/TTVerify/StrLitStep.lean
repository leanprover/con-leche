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

/- Task #147: stated at the TT-lane mode; the seven gated checks
reduce definitionally at `.ttModel`. -/
private abbrev mode : CheckMode := .ttModel

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

/-! ## The constructor form, denoted

The stuck block compares a `String` literal against a unary
`String.ofList` application by *expanding* the literal
(`tryStringLitExpansion` in the reference kernels), so the bridge owes
the expansion's denotation.  It is `strLitT` — which is how `strLitT`
was defined in the first place (`Setlec/Verify/Denote.lean`), so the
lemma is the definition read forwards, once per constant the guard
pins. -/

/-- `List.nil.{0} Char`, denoted (the `EnvTT` specialization of
`denote_nilTermV`). -/
theorem denote_nilTerm {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) (d : Nat) :
    denote m.cval env φ d
        (.app (.const listNilName [.zero]) (.const charName []))
      = some (.app (m.cval listNilName
          (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
        (m.cval charName φ)) :=
  denote_nilTermV φ hg d

/-- `List.cons.{0} Char`, denoted (the `EnvTT` specialization of
`denote_consTermV`). -/
theorem denote_consTerm {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) (d : Nat) :
    denote m.cval env φ d
        (.app (.const listConsName [.zero]) (.const charName []))
      = some (.app (m.cval listConsName
          (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
        (m.cval charName φ)) :=
  denote_consTermV φ hg d

/-- **The character-list expression denotes to `charListT`** (the
`EnvTT` specialization of `denote_strLitListV`). -/
theorem denote_strLitList {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hg : strLitSupported env = true) (d : Nat) :
    ∀ cs : List Char,
      denote m.cval env φ d (strLitList cs) = some (charListT
        (.app (m.cval listNilName
          (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
          (m.cval charName φ))
        (.app (m.cval listConsName
          (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
          (m.cval charName φ))
        (m.cval charOfNatName φ) (m.cval natZeroName φ)
        (m.cval natSuccName φ) cs) :=
  denote_strLitListV φ hg d

/-- **A string literal's constructor form denotes to the literal** (the
`EnvTT` specialization of `denote_strLitToConstructorV`). -/
theorem denote_strLitToConstructor {env : Env} (m : EnvTT env)
    (φ : Name → Nat) (hg : strLitSupported env = true) (d : Nat)
    (s : String) :
    denote m.cval env φ d (strLitToConstructor s)
      = denote m.cval env φ d (.lit (.strVal s)) :=
  denote_strLitToConstructorV φ hg d s

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
    (ihw : WhnfClaimsTT mode m φ fuel) (ihd : DefEqClaimsTT mode m φ fuel)
    (ihi : InferClaimsTT mode m φ fuel) :
    InferClaimsTT mode m φ (fuel + 1) :=
  infer_claimsTT m φ hcl (infer_strLit_step m φ) hproj ihw ihd ihi

end Setlec.TTVerify
