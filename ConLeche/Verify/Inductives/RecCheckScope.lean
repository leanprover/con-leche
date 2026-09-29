module

public import ConLeche.Kernel.Inductives.RecCheck
public import ConLeche.Verify.Shift
public import ConLeche.Rules.Rel

public section

/-!
# The target check's terms are scoped by the rule's frame

The residue's context (`walkCtx_targetEntry`) takes, at every `ih`
variable, the SCOPING of its type `∀ a⃗ : A⃗, c x⃗ e⃗ (f a⃗)` and of the
call's λ: every free-variable leaf is an entry of the rule's frame (the
prefix and the fields), and neither has a loose bound variable.  The
parts are the frame's own variables, the call's index arguments (sub-
terms of the opened rule body, `targetAbstract`), the recursor's closed
stored type, and the field's telescope — the member-abstracted field
type read through whnf (`targetWhnfPis`), whose holes the check excluded
(`targetHoleFree`).  This file proves the leaf and bound facts of each
part; `targetIh_scope` assembles them.
-/

namespace ConLeche

open Expr

variable {mode : CheckMode}

/-! ## A recorded instantiation moved to a class's openers -/

/-- **Moving the parameters to scoped openers scopes the term**: every
free variable of `e` lies below `|pfvs|` and is replaced by its opener. -/
theorem targetCanonParams_WScoped {pfvs : List Expr} {D : Nat} (hp : ∀ x ∈ pfvs, WScoped D x) :
    ∀ (e : Expr), e.fvarsBelow pfvs.length → WScoped D (targetCanonParams pfvs e) := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro h
    simp only [Expr.fvarsBelow] at h
    simp only [targetCanonParams, Expr.replaceFVars, List.getElem?_eq_getElem h, Option.getD_some]
    exact hp _ (List.getElem_mem h)
  | app f a ihf iha =>
    intro h
    simp only [Expr.fvarsBelow] at h
    have h1 := ihf h.1
    have h2 := iha h.2
    simp only [targetCanonParams] at h1 h2 ⊢
    simp only [Expr.replaceFVars, WScoped]
    exact ⟨h1, h2⟩
  | lam t b m iht ihb =>
    intro h
    simp only [Expr.fvarsBelow] at h
    have h1 := iht h.1
    have h2 := ihb h.2
    simp only [targetCanonParams] at h1 h2 ⊢
    simp only [Expr.replaceFVars, WScoped]
    exact ⟨h1, h2⟩
  | forallE t b m iht ihb =>
    intro h
    simp only [Expr.fvarsBelow] at h
    have h1 := iht h.1
    have h2 := ihb h.2
    simp only [targetCanonParams] at h1 h2 ⊢
    simp only [Expr.replaceFVars, WScoped]
    exact ⟨h1, h2⟩
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.fvarsBelow] at h
    have h1 := iht h.1
    have h2 := ihv h.2.1
    have h3 := ihb h.2.2
    simp only [targetCanonParams] at h1 h2 h3 ⊢
    simp only [Expr.replaceFVars, WScoped]
    exact ⟨h1, h2, h3⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.fvarsBelow] at h
    have h1 := ih h
    simp only [targetCanonParams] at h1 ⊢
    simp only [Expr.replaceFVars, WScoped]
    exact h1
  | bvar _ => intro _; simp [targetCanonParams, Expr.replaceFVars, WScoped]
  | sort _ => intro _; simp [targetCanonParams, Expr.replaceFVars, WScoped]
  | const _ _ => intro _; simp [targetCanonParams, Expr.replaceFVars, WScoped]
  | lit _ => intro _; simp [targetCanonParams, Expr.replaceFVars, WScoped]

/-! ## The parts, one by one -/

/-- The member abstraction adds only the holes' leaves. -/
theorem targetAbs_fvarLeaves {names : List Name} {lvls : List Level} {holes : List Expr} :
    ∀ (e : Expr) (l : Nat × Expr), l ∈ (targetAbs names lvls holes e).fvarLeaves →
      l ∈ e.fvarLeaves ∨ ∃ h ∈ holes, l ∈ h.fvarLeaves := by
  intro e
  induction e with
  | bvar i => intro l hl; simp [targetAbs, fvarLeaves] at hl
  | sort u => intro l hl; simp [targetAbs, fvarLeaves] at hl
  | lit v => intro l hl; simp [targetAbs, fvarLeaves] at hl
  | fvar i ty _ => intro l hl; exact Or.inl (by simpa [targetAbs] using hl)
  | const n us =>
    intro l hl
    simp only [targetAbs] at hl
    split at hl
    · split at hl
      · rename_i t _
        rcases Nat.lt_or_ge t holes.length with ht | ht
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some] at hl
          exact Or.inr ⟨_, List.getElem_mem ht, hl⟩
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ht, Option.getD_none] at hl
          simp [fvarLeaves] at hl
      · simp [fvarLeaves] at hl
    · simp [fvarLeaves] at hl
  | app a b iha ihb =>
    intro l hl
    simp only [targetAbs, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases iha l hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihb l hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | lam ty b m iht ihb =>
    intro l hl
    simp only [targetAbs, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases iht l hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihb l hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | forallE ty b m iht ihb =>
    intro l hl
    simp only [targetAbs, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases iht l hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihb l hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | letE ty v b iht ihv ihb =>
    intro l hl
    simp only [targetAbs, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · rcases iht l hl with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
    · rcases ihv l hl with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
    · rcases ihb l hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | proj s i sub ih =>
    intro l hl
    simp only [targetAbs, fvarLeaves] at hl ⊢
    exact ih l hl

/-- The member abstraction keeps the scope, holes included. -/
theorem targetAbs_WScoped {names : List Name} {lvls : List Level} {holes : List Expr} {D : Nat}
    (hh : ∀ h ∈ holes, WScoped D h) :
    ∀ (e : Expr), WScoped D e → WScoped D (targetAbs names lvls holes e) := by
  intro e
  induction e with
  | const n us =>
    intro _
    simp only [targetAbs]
    split
    · split
      · rename_i t _
        rcases Nat.lt_or_ge t holes.length with ht | ht
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
          exact hh _ (List.getElem_mem ht)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ht, Option.getD_none]
          unfold WScoped; trivial
      · unfold WScoped; trivial
    · unfold WScoped; trivial
  | app a b iha ihb =>
    intro hw; unfold WScoped at hw ⊢; exact ⟨iha hw.1, ihb hw.2⟩
  | lam ty b m iht ihb =>
    intro hw; unfold WScoped at hw ⊢; exact ⟨iht hw.1, ihb hw.2⟩
  | forallE ty b m iht ihb =>
    intro hw; unfold WScoped at hw ⊢; exact ⟨iht hw.1, ihb hw.2⟩
  | letE ty v b iht ihv ihb =>
    intro hw; unfold WScoped at hw ⊢; exact ⟨iht hw.1, ihv hw.2.1, ihb hw.2.2⟩
  | proj s i sub ih =>
    intro hw; unfold WScoped at hw ⊢; exact ih hw
  | _ => intro hw; simpa [targetAbs] using hw

/-! ## The abstract frame (`targetMoveF`, `targetAbsFields`) -/

/-- Replacing free variables by scoped terms keeps the scope. -/
theorem replaceFVars_WScoped {g : Nat → Option Expr} {d : Nat}
    (hg : ∀ i r, g i = some r → WScoped d r) :
    ∀ (e : Expr), WScoped d e → WScoped d (e.replaceFVars g) := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro hw
    simp only [Expr.replaceFVars]
    cases hgi : g i with
    | none => exact hw
    | some r => exact hg i r hgi
  | app a b iha ihb =>
    intro hw; unfold WScoped at hw; simp only [Expr.replaceFVars]; unfold WScoped
    exact ⟨iha hw.1, ihb hw.2⟩
  | lam ty b m iht ihb =>
    intro hw; unfold WScoped at hw; simp only [Expr.replaceFVars]; unfold WScoped
    exact ⟨iht hw.1, ihb hw.2⟩
  | forallE ty b m iht ihb =>
    intro hw; unfold WScoped at hw; simp only [Expr.replaceFVars]; unfold WScoped
    exact ⟨iht hw.1, ihb hw.2⟩
  | letE ty v b iht ihv ihb =>
    intro hw; unfold WScoped at hw; simp only [Expr.replaceFVars]; unfold WScoped
    exact ⟨iht hw.1, ihv hw.2.1, ihb hw.2.2⟩
  | proj s i sub ih =>
    intro hw; unfold WScoped at hw; simp only [Expr.replaceFVars]; unfold WScoped; exact ih hw
  | _ => intro hw; simpa [Expr.replaceFVars] using hw

/-- Closing a binder body back: an opened body without loose bound
variables past `k` had none past `k + 1`. -/
theorem looseBVarsBounded_of_instantiate1_fvar {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), (e.instantiate1 (.fvar d ty) k).looseBVarsBounded k = true →
      e.looseBVarsBounded (k + 1) = true := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.instantiate1, Expr.looseBVarsBounded]
  case bvar i =>
    by_cases h1 : i = k
    · omega
    · by_cases h2 : i > k
      · simp [h1, h2, Expr.looseBVarsBounded] at hb; omega
      · omega

/-- `infer_full_bvarClosed` at any grade that is the certified one. -/
theorem infer_bvarClosed_of_full {env : Env} :
    ∀ {g : Rules.Grade} {d : Nat} {e t : Expr}, Rules.Infer env g d e t → g = .full →
      e.looseBVarsBounded 0 = true
  | _, _, _, _, .sort, _ => rfl
  | _, _, _, _, .fvar _, _ => rfl
  | _, _, _, _, .const .., _ => rfl
  | _, _, _, _, .natLit _, _ => rfl
  | _, _, _, _, .strLit _, _ => rfl
  | _, _, _, _, .forallE hs _ hbs _ _, hg => by
    simp only [looseBVarsBounded, Bool.and_eq_true]
    exact ⟨infer_bvarClosed_of_full hs hg,
      looseBVarsBounded_of_instantiate1_fvar _ 0 (infer_bvarClosed_of_full hbs hg)⟩
  | _, _, _, _, .lam hs _ hbt _ _ _ _, hg => by
    simp only [looseBVarsBounded, Bool.and_eq_true]
    exact ⟨infer_bvarClosed_of_full (hs hg) rfl,
      looseBVarsBounded_of_instantiate1_fvar _ 0 (infer_bvarClosed_of_full hbt hg)⟩
  | _, _, _, _, .app hf _ ha _, hg => by
    simp only [looseBVarsBounded, Bool.and_eq_true]
    exact ⟨infer_bvarClosed_of_full hf hg, infer_bvarClosed_of_full ha hg⟩
  | _, _, _, _, .appSkip .., hg => nomatch hg
  | _, _, _, _, .proj hp .., hg => by
    simp only [looseBVarsBounded]
    exact infer_bvarClosed_of_full hp hg

/-- **A term the checker infers at the certified grade has no loose
bound variable**: inference opens every binder it passes and throws at a
loose one (`Infer`'s `.full` rules visit every sub-term). -/
theorem infer_full_bvarClosed {env : Env} {d : Nat} {e t : Expr}
    (h : Rules.Infer env .full d e t) : e.looseBVarsBounded 0 = true :=
  infer_bvarClosed_of_full h rfl

end ConLeche
