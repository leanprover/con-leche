module

public import ConLeche.Verify.Inductives.CopyTypes
public import ConLeche.Verify.Mono

public section

/-!
# The two lemmas behind `AuxFormersAnnot` (task #300)

placeholder
-/

namespace ConLeche

open Expr

variable {mode : CheckMode}

/-! ## A conservative environment extension -/

/-- **`env'` extends `env` conservatively**: every constant stored in
`env` is stored in `env'`, unchanged.  This is the checker's own shape
of extension (a cons over a freshness check) and the only thing the
lemmas below need.

`ConLeche/Verify/Denote/Install.lean` states the same relation as
`Verify.EnvExtends` for the denotation transports; that spelling sits
in a plain `public section`, so its body does not unfold outside its
own module and it cannot be *applied* here.  Restating it (four tokens)
is the module system's own answer — the alternative would be to
`@[expose]` a definition the Denote tier deliberately keeps opaque. -/
@[expose] def EnvExt (env env' : Env) : Prop :=
  ∀ n ci, env.find? n = some ci → env'.find? n = some ci

theorem EnvExt.refl (env : Env) : EnvExt env env := fun _ _ h => h

theorem EnvExt.trans {e₁ e₂ e₃ : Env} (h₁ : EnvExt e₁ e₂) (h₂ : EnvExt e₂ e₃) :
    EnvExt e₁ e₃ := fun n ci h => h₂ n ci (h₁ n ci h)

/-- A cons over a fresh name is a conservative extension. -/
theorem EnvExt.cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) : EnvExt env ⟨c₀ :: env.consts⟩ := by
  intro n ci h
  rw [Env.find?_cons]
  split
  · next hn => rw [← hn, hfresh] at h; exact nomatch h
  · exact h

/-! ## The head readers under a conservative environment extension -/

/-- A shape predicate on a stored constant is monotone along an
extension: it rejects `none`, so a `true` reading had to have found the
constant, and the extension stores the same one. -/
private theorem constShapeOk_envExt {env env' : Env} (hext : EnvExt env env')
    (P : Option ConstantInfo → Bool) (hnone : P none = false) (n : Name)
    (h : P (env.find? n) = true) : P (env'.find? n) = true := by
  cases hf : env.find? n with
  | none => rw [hf, hnone] at h; exact nomatch h
  | some ci => rw [hext n ci hf]; rwa [hf] at h

/-- **The head reader's answers survive an extension.**  Every lookup
the reader makes is on the `some` branch of its own answer, so the
extension returns the same constant and the same datum. -/
theorem headTypePW_envExt {env env' : Env} (hext : EnvExt env env')
    {h : Expr} {n : Nat} {pw : PropWhen}
    (hr : headTypePW env.find? h n = some pw) :
    headTypePW env'.find? h n = some pw := by
  cases h with
  | const I us =>
    simp only [headTypePW] at hr ⊢
    cases hf : env.find? I with
    | none => rw [hf] at hr; exact nomatch hr
    | some ci => rw [hext I ci hf]; rwa [hf] at hr
  | _ => exact hr

/-- `typeSortPW`'s answers survive an extension. -/
theorem typeSortPW_envExt {env env' : Env} (hext : EnvExt env env')
    {T : Expr} {pw : PropWhen} (hr : typeSortPW env.find? T = some pw) :
    typeSortPW env'.find? T = some pw := by
  cases T with
  | forallE ty b m => exact hr
  | sort u => exact hr
  | _ =>
    simp only [typeSortPW] at hr ⊢
    exact headTypePW_envExt hext hr

/-- `headProofPW`'s answers survive an extension (through
`typeSortPW`'s, which it reads off the head's stored type). -/
theorem headProofPW_envExt {env env' : Env} (hext : EnvExt env env')
    {h : Expr} {pw : PropWhen} (hr : headProofPW env.find? h = some pw) :
    headProofPW env'.find? h = some pw := by
  cases h with
  | const c us =>
    simp only [headProofPW] at hr ⊢
    cases hf : env.find? c with
    | none => rw [hf] at hr; exact nomatch hr
    | some ci =>
      rw [hext c ci hf]
      rw [hf] at hr
      dsimp only at hr ⊢
      cases hts : typeSortPW env.find? ci.toConstantVal.type with
      | none => rw [hts] at hr; simp at hr
      | some pw0 =>
        rw [hts] at hr
        rw [typeSortPW_envExt hext hts]
        exact hr
  | fvar idx ty => exact typeSortPW_envExt hext hr
  | _ => exact hr

/-- `proofPW`'s answers survive an extension. -/
theorem proofPW_envExt {env env' : Env} (hext : EnvExt env env')
    {a : Expr} {pw : PropWhen} (hr : proofPW env.find? a = some pw) :
    proofPW env'.find? a = some pw := by
  cases a with
  | lam ty b m => exact hr
  | _ =>
    simp only [proofPW] at hr ⊢
    exact headProofPW_envExt hext hr

/-! ## The literal-support guards under an extension -/

theorem natLitSupported_envExt {env env' : Env} (hext : EnvExt env env')
    (h : natLitSupported env = true) : natLitSupported env' = true := by
  simp only [natLitSupported, Bool.and_eq_true] at h ⊢
  exact ⟨⟨constShapeOk_envExt hext natIndOk rfl _ h.1.1,
    constShapeOk_envExt hext natZeroOk rfl _ h.1.2⟩,
    constShapeOk_envExt hext natSuccOk rfl _ h.2⟩

theorem strLitSupported_envExt {env env' : Env} (hext : EnvExt env env')
    (h : strLitSupported env = true) : strLitSupported env' = true := by
  simp only [strLitSupported, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, hs⟩, hsl⟩, hl⟩, hnil⟩, hcons⟩, hc⟩, hco⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨natLitSupported_envExt hext hn,
    constShapeOk_envExt hext stringTyOk rfl _ hs⟩,
    constShapeOk_envExt hext stringOfListTyOk rfl _ hsl⟩,
    constShapeOk_envExt hext listTyOk rfl _ hl⟩,
    constShapeOk_envExt hext listNilTyOk rfl _ hnil⟩,
    constShapeOk_envExt hext listConsTyOk rfl _ hcons⟩,
    constShapeOk_envExt hext charTyOk rfl _ hc⟩,
    constShapeOk_envExt hext charOfNatTyOk rfl _ hco⟩

end ConLeche
