module

import ConLeche.Verify.InstLevels
import ConLeche.Verify.Denote
public import ConLeche.Model.Env.EnvModel

public section

/-!
# The level crossing for `denote`: algebra, outright (task #161, P3)

The crossing **is** algebra: `denote` runs no checker function, its
binders read no level datum, and the sort and constant clauses read the
instantiated levels through `Level.eval` of the composed valuation.  So
the theorem below is

* **unconditional** — no checker residue, no `EnvWF`, and
* an **equality** — there is no fuel, and no run that instantiation
  could make succeed or fail asymmetrically.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}

/-! ### The literal-support slot lemmas

Each reads the `acval_params` field of `EnvModel` and nothing else. -/

/-- A parameter-free slot is valued independently of the assignment. -/
theorem acval_isEmpty (m : EnvModel V env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (he : ci.toConstantVal.levelParams.isEmpty = true)
    (ψ₁ ψ₂ : Name → Nat) : m.acval n ψ₁ = m.acval n ψ₂ := by
  refine m.acval_params n ci hf ψ₁ ψ₂ fun p hpm => ?_
  rw [List.isEmpty_iff] at he
  rw [he] at hpm
  exact nomatch hpm

/-- A one-parameter slot substituted at `Level.zero` is valued
independently of the assignment. -/
theorem acval_oneParam (m : EnvModel V env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hlen : ci.toConstantVal.levelParams.length = 1)
    (ψ₁ ψ₂ : Name → Nat) :
    m.acval n (Level.substFn ψ₁ ci.toConstantVal.levelParams [.zero])
      = m.acval n
        (Level.substFn ψ₂ ci.toConstantVal.levelParams [.zero]) := by
  refine m.acval_params n ci hf _ _ ?_
  intro p hpm
  refine Level.substFn_ext (ps := []) (fun q hq => nomatch hq) ?_ ?_ p
    hpm
  · intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    rfl
  · simp [hlen]

/-- The scalar literal-support slots, read off their shape guards. -/
theorem acval_scalar (m : EnvModel V env) (nm : Name)
    (f : Option ConstantInfo → Bool) (hfok : f (env.find? nm) = true)
    (hnone : f none = false)
    (hshape : ∀ ci, f (some ci) = true →
      ci.toConstantVal.levelParams.isEmpty = true)
    (ψ₁ ψ₂ : Name → Nat) : m.acval nm ψ₁ = m.acval nm ψ₂ := by
  cases hx : env.find? nm with
  | none => rw [hx, hnone] at hfok; exact nomatch hfok
  | some ci =>
    rw [hx] at hfok
    exact acval_isEmpty m hx (hshape ci hfok) _ _

/-- The two one-parameter literal-support slots. -/
theorem acval_one (m : EnvModel V env) (nm : Name)
    (f : Option ConstantInfo → Bool) (hfok : f (env.find? nm) = true)
    (hnone : f none = false)
    (hshape : ∀ ci, f (some ci) = true →
      ci.toConstantVal.levelParams.length = 1)
    (ψ₁ ψ₂ : Name → Nat) :
    m.acval nm (Level.substFn ψ₁ (levelParamsAt env nm) [.zero])
      = m.acval nm
        (Level.substFn ψ₂ (levelParamsAt env nm) [.zero]) := by
  cases hx : env.find? nm with
  | none => rw [hx, hnone] at hfok; exact nomatch hfok
  | some ci =>
    have hlp : levelParamsAt env nm = ci.toConstantVal.levelParams := by
      simp [levelParamsAt, hx]
    rw [hx] at hfok
    rw [hlp]
    exact acval_oneParam m hx (hshape ci hfok) _ _

/-- The `Nat`-literal leaves are assignment-independent. -/
theorem acval_natPair (m : EnvModel V env)
    (hg : ConLeche.natLitSupported env = true) (ψ₁ ψ₂ : Name → Nat) :
    m.acval natZeroName ψ₁ = m.acval natZeroName ψ₂ ∧
      m.acval natSuccName ψ₁ = m.acval natSuccName ψ₂ := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, hz⟩, hs⟩ := hg
  refine ⟨acval_scalar m natZeroName natZeroOk hz rfl ?_ _ _,
    acval_scalar m natSuccName natSuccOk hs rfl ?_ _ _⟩
  · intro ci h
    cases ci with
    | ctorInfo cv a b =>
      simp only [natZeroOk, Bool.and_eq_true] at h
      simpa [ConstantInfo.toConstantVal] using h.1
    | _ => simp [natZeroOk] at h
  · intro ci h
    cases ci with
    | ctorInfo cv a b =>
      simp only [natSuccOk, Bool.and_eq_true] at h
      simpa [ConstantInfo.toConstantVal] using h.1
    | _ => simp [natSuccOk] at h

/-- **The level crossing for `denote`, unconditional and exact**:
reading an instantiated term at `φ` is reading the term at the
composed valuation `Level.substFn φ ks us`.  The binder steps are the
induction hypotheses; the constant step is `EnvModel.acval_params` +
`Level.substFn_map_subst`. -/
theorem denotePInstLevels (m : EnvModel V env)
    (φ : Name → Nat) (ks : List Name) (us : List Level) :
    ∀ (d : Nat) (e : Expr),
      denote m.acval env φ d (e.instantiateLevelParams ks us)
        = denote m.acval env (Level.substFn φ ks us) d e := by
  intro d e
  induction d, e using denote.induct (env := env) with
  | case1 d u =>
    rw [Expr.instantiateLevelParams, denote, denote, Level.eval_subst]
  | case2 d idx ty =>
    rw [Expr.instantiateLevelParams, denote, denote]
  | case3 d n vs ci hf hlen =>
    rw [Expr.instantiateLevelParams, denote, denote, hf]
    dsimp only
    rw [ite_eq_left hlen, ite_eq_left (by simpa using hlen)]
    exact congrArg some
      (m.acval_params n ci hf _ _ fun p hp =>
        Level.substFn_map_subst hlen hp)
  | case4 d n vs ci hf hlen =>
    rw [Expr.instantiateLevelParams, denote, denote, hf]
    dsimp only
    rw [ite_eq_right hlen, ite_eq_right (by simpa using hlen)]
  | case5 d n vs hf =>
    rw [Expr.instantiateLevelParams, denote, denote, hf]
  | case6 d ty body ihty ihbody =>
    rw [Expr.instantiateLevelParams, denote, denote,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      ihty, ihbody]
  | case7 d ty body ihty ihbody =>
    rw [Expr.instantiateLevelParams, denote, denote,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      ihty, ihbody]
  | case8 d fe a ihf iha =>
    rw [Expr.instantiateLevelParams, denote, denote, ihf, iha]
  | case9 d ty val body ihty ihv ihbody =>
    rw [Expr.instantiateLevelParams, denote, denote,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      ihty, ihv, ihbody]
  | case10 d sn i e ihe =>
    rw [Expr.instantiateLevelParams, denote, denote, ihe]
  | case11 d k hsup =>
    rw [Expr.instantiateLevelParams, denote, denote,
      ite_eq_left hsup, ite_eq_left hsup]
    obtain ⟨ez, es⟩ := acval_natPair m hsup
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    rw [ez, es]
  | case12 d k hsup =>
    rw [Expr.instantiateLevelParams, denote, denote,
      ite_eq_right hsup, ite_eq_right hsup]
  | case13 d s hsup =>
    rw [Expr.instantiateLevelParams, denote, denote,
      ite_eq_left hsup, ite_eq_left hsup]
    have hg := hsup
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    obtain ⟨ez, es⟩ := acval_natPair m h0
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have esol := acval_scalar m stringOfListName stringOfListTyOk h2 rfl
      (by intro ci hh
          simp only [stringOfListTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have echar := acval_scalar m charName charTyOk h6 rfl
      (by intro ci hh
          simp only [charTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have eofn := acval_scalar m charOfNatName charOfNatTyOk h7 rfl
      (by intro ci hh
          simp only [charOfNatTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have enil := acval_one m listNilName listNilTyOk h4 rfl
      (by intro ci hh
          simp only [listNilTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      (Level.substFn φ ks us) φ
    have econs := acval_one m listConsName listConsTyOk h5 rfl
      (by intro ci hh
          simp only [listConsTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      (Level.substFn φ ks us) φ
    rw [ez, es, esol, echar, eofn, enil, econs]
  | case14 d s hsup =>
    rw [Expr.instantiateLevelParams, denote, denote,
      ite_eq_right hsup, ite_eq_right hsup]
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    cases x with
    | bvar i =>
      rw [Expr.instantiateLevelParams, denote.eq_def, denote.eq_def]
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

/-- **The reading's φ-congruence at the expression's own parameters**
(the harvest layer's `hAparams` supplier). -/
theorem denote_params_ext (m : EnvModel V env)
    {ps : List Name} {φ₁ φ₂ : Name → Nat}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ (d : Nat) (e : Expr), e.allLevelParamsDefined ps = true →
      denote m.acval env φ₁ d e = denote m.acval env φ₂ d e := by
  intro d e
  induction d, e using denote.induct (env := env) with
  | case1 d u =>
    intro hd
    rw [denote, denote,
      Level.eval_ext (by simpa [Expr.allLevelParamsDefined] using hd) hφ]
  | case2 d idx ty => intro _; rw [denote, denote]
  | case3 d n us ci h1 h2 =>
    intro hd
    rw [denote, denote, h1]
    dsimp only
    rw [ite_eq_left h2, ite_eq_left h2]
    refine congrArg _ (m.acval_params n ci h1 _ _ fun p hpm => ?_)
    refine Level.substFn_ext hφ ?_ h2 p hpm
    intro u hu
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at hd
    exact hd u hu
  | case4 d n us ci h1 h2 =>
    intro _
    rw [denote, denote, h1]
    dsimp only
    rw [ite_eq_right h2, ite_eq_right h2]
  | case5 d n us h1 => intro _; rw [denote, denote, h1]
  | case6 d ty body ihty ihbody =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote, denote, ← ihty hd.1,
      ← ihbody (ConLeche.Expr.allLevelParamsDefined_instantiate1 hd.1 0
        hd.2)]
  | case7 d ty body ihty ihbody =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote, denote, ← ihty hd.1,
      ← ihbody (ConLeche.Expr.allLevelParamsDefined_instantiate1 hd.1 0
        hd.2)]
  | case8 d fe a ihf iha =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote, denote, ← ihf hd.1, ← iha hd.2]
  | case9 d ty val body ihty ihv ihbody =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote, denote, ← ihty hd.1.1, ← ihv hd.1.2,
      ← ihbody (ConLeche.Expr.allLevelParamsDefined_instantiate1 hd.1.1 0
        hd.2)]
  | case10 d sn i e ihe =>
    intro hd
    rw [denote, denote,
      ← ihe (by simpa [Expr.allLevelParamsDefined] using hd)]
  | case11 d k hsup =>
    intro _
    rw [denote, denote, ite_eq_left hsup, ite_eq_left hsup]
    obtain ⟨ez, es⟩ := acval_natPair m hsup
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    rw [ez, es]
  | case12 d k hsup =>
    intro _
    rw [denote, denote, ite_eq_right hsup, ite_eq_right hsup]
  | case13 d s hsup =>
    intro _
    rw [denote, denote, ite_eq_left hsup, ite_eq_left hsup]
    have hg := hsup
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    obtain ⟨ez, es⟩ := acval_natPair m h0
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have esol := acval_scalar m stringOfListName stringOfListTyOk h2 rfl
      (by intro ci hh
          simp only [stringOfListTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have echar := acval_scalar m charName charTyOk h6 rfl
      (by intro ci hh
          simp only [charTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have eofn := acval_scalar m charOfNatName charOfNatTyOk h7 rfl
      (by intro ci hh
          simp only [charOfNatTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have enil := acval_one m listNilName listNilTyOk h4 rfl
      (by intro ci hh
          simp only [listNilTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ₁ φ₂
    have econs := acval_one m listConsName listConsTyOk h5 rfl
      (by intro ci hh
          simp only [listConsTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ₁ φ₂
    rw [ez, es, esol, echar, eofn, enil, econs]
  | case14 d s hsup =>
    intro _
    rw [denote, denote, ite_eq_right hsup, ite_eq_right hsup]
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denote.eq_def, denote.eq_def]
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

end ConLeche.Model
