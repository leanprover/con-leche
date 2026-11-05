module

public import ConLeche.Model.Cover
public import ConLeche.Verify.PinRen
import ConLeche.Model.Reading.Levels

public section

/-!
# The invariant across different copies of the pins

`EnvModelM.rename` carries the model's invariant from one environment to
another that differs only in the level-parameter names of its pinned
constants (`RenEnv`).  The new valuation reads a constant at the assignment
that gives the old parameter `ks[i]` the new parameter `ps[i]`'s value
(`renAcval`), so every term reads alike on both sides (`denote_ren`).
-/

namespace ConLeche.Model

open ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule IndCaps
  reservedBasisNames pinnedInfo)

universe w

variable {V : Type w} [SetTheory V]

/-- The old assignment a new constant is read at. -/
@[expose] def renTr (env env' : Env) (n : Name) (ψ : Name → Nat) : Name → Nat :=
  match env.find? n, env'.find? n with
  | some c, some c' =>
    Level.substFn ψ c.toConstantVal.levelParams (c'.toConstantVal.levelParams.map Level.param)
  | _, _ => ψ

/-- The new leaf valuation. -/
@[expose] def renAcval (acval : Name → (Name → Nat) → Term) (env env' : Env) :
    Name → (Name → Nat) → Term :=
  fun n ψ => acval n (renTr env env' n ψ)

section

variable {env env' : Env} (h : RenEnv env env') {acval : Name → (Name → Nat) → Term}
  (hparams : ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      acval n ψ₁ = acval n ψ₂)

include h

/-- **The new leaf at an instantiation is the old one**, parameter by
parameter. -/
theorem renAcval_inst (hparams : ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acval n ψ₁ = acval n ψ₂)
    {n : Name} {c c' : ConstantInfo} (hf : env.find? n = some c) (hf' : env'.find? n = some c')
    (hr : ConstRen c c') (φ : Name → Nat) {us : List Level}
    (hus : us.length = c.toConstantVal.levelParams.length) :
    renAcval acval env env' n (Level.substFn φ c'.toConstantVal.levelParams us)
      = acval n (Level.substFn φ c.toConstantVal.levelParams us) := by
  unfold renAcval renTr
  rw [hf, hf']
  dsimp only
  rcases hr with rfl | ⟨-, h1, h2⟩
  · rw [Level.substFn_param_self]
  · refine hparams n c hf _ _ fun p hp => ?_
    have hl : c.toConstantVal.levelParams.length = c'.toConstantVal.levelParams.length := by
      rw [h1.2.2, h2.2.2]
    exact substFn_ren h2.2.1 hl (hus.trans hl) (fun _ _ => rfl) p hp

omit h in
/-- A name with the same lookup keeps its leaf. -/
theorem renAcval_same {n : Name} (he : env'.find? n = env.find? n) :
    renAcval acval env env' n = acval n := by
  funext ψ
  unfold renAcval renTr
  rw [he]
  cases env.find? n with
  | none => rfl
  | some c =>
    dsimp only
    rw [Level.substFn_param_self]

omit h in
theorem levelParamsAt_ren {n : Name} (he : env'.find? n = env.find? n) :
    levelParamsAt env' n = levelParamsAt env n := by
  unfold levelParamsAt
  rw [he]

/-- **Every term reads alike on both sides.** -/
theorem denote_ren (hparams : ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acval n ψ₁ = acval n ψ₂)
    (φ : Name → Nat) :
    ∀ (d : Nat) (e : Expr),
      denote (renAcval acval env env') env' φ d e = denote acval env φ d e := by
  have hlen : ∀ {n c c'}, env.find? n = some c → env'.find? n = some c' → ConstRen c c' →
      c.toConstantVal.levelParams.length = c'.toConstantVal.levelParams.length := by
    intro n c c' _ _ hr
    rcases hr with rfl | ⟨-, h1, h2⟩
    · rfl
    · rw [h1.2.2, h2.2.2]
  have hnat : ConLeche.natLitSupported env = ConLeche.natLitSupported env' := h.natLit.symm
  have hstr : ConLeche.strLitSupported env = ConLeche.strLitSupported env' := h.strLit.symm
  have hproj : ∀ (sn : Name) (i : Nat), env.findProj? sn i = env'.findProj? sn i :=
    fun sn i => (h.findProj sn i).symm
  intro d e
  induction d, e using denote.induct (env := env) with
  | case1 d u => rw [denote, denote]
  | case2 d idx ty => rw [denote, denote]
  | case3 d n us ci hf hl =>
    rcases h.find n with ⟨h1, -⟩ | ⟨c, c', h1, h2, hr⟩
    · rw [h1] at hf; exact nomatch hf
    · rw [h1] at hf
      obtain rfl := Option.some.inj hf
      have hl' := hlen h1 h2 hr
      rw [denote, h2, denote, h1]
      dsimp only
      rw [ite_eq_left (hl' ▸ hl), ite_eq_left hl]
      exact congrArg some (renAcval_inst h hparams h1 h2 hr φ hl)
  | case4 d n us ci hf hl =>
    rcases h.find n with ⟨h1, -⟩ | ⟨c, c', h1, h2, hr⟩
    · rw [h1] at hf; exact nomatch hf
    · rw [h1] at hf
      obtain rfl := Option.some.inj hf
      have hl' := hlen h1 h2 hr
      rw [denote, h2, denote, h1]
      dsimp only
      rw [ite_eq_right (fun hh => hl (hh.trans hl'.symm)), ite_eq_right hl]
  | case5 d n us hf =>
    rcases h.find n with ⟨-, h2⟩ | ⟨c, c', h1, h2, hr⟩
    · rw [denote, h2, denote, hf]
    · rw [h1] at hf; exact nomatch hf
  | case6 d ty body ihty ihbody =>
    rw [denote, denote, ihty, ihbody]
  | case7 d ty body ihty ihbody =>
    rw [denote, denote, ihty, ihbody]
  | case8 d f a ihf iha => rw [denote, denote, ihf, iha]
  | case9 d ty val body ihty ihv ihbody =>
    rw [denote, denote, ihty, ihv, ihbody]
  | case10 d sn i e ihe =>
    rw [denote, denote, ihe, hproj sn i]
  | case11 d n hsup =>
    rw [denote, ite_eq_left (hnat ▸ hsup), denote, ite_eq_left hsup,
      renAcval_same (h.find_noLps rfl), renAcval_same (h.find_noLps rfl)]
  | case12 d n hsup =>
    rw [denote, ite_eq_right (fun h => hsup (hnat.trans h)), denote, ite_eq_right hsup]
  | case13 d s hsup =>
    rw [denote, ite_eq_left (hstr ▸ hsup), denote, ite_eq_left hsup,
      renAcval_same (n := ConLeche.natZeroName) (h.find_noLps rfl),
      renAcval_same (n := ConLeche.natSuccName) (h.find_noLps rfl),
      renAcval_same (n := ConLeche.stringOfListName) (h.find_nonres (by decide)),
      renAcval_same (n := ConLeche.listNilName) (h.find_nonres (by decide)),
      renAcval_same (n := ConLeche.listConsName) (h.find_nonres (by decide)),
      renAcval_same (n := ConLeche.charName) (h.find_nonres (by decide)),
      renAcval_same (n := ConLeche.charOfNatName) (h.find_nonres (by decide)),
      levelParamsAt_ren (h.find_nonres (by decide)), levelParamsAt_ren (h.find_nonres (by decide))]
  | case14 d s hsup =>
    rw [denote, ite_eq_right (fun h => hsup (hstr.trans h)), denote, ite_eq_right hsup]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat' hstr' =>
    cases x with
    | bvar i => rw [denote.eq_def, denote.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat' n)
      | strVal s => exact absurd rfl (hstr' s)

end

end ConLeche.Model
