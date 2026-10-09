module

public import ConLeche.Frontend.ExportC
import ConLeche.Verify.ExceptBind
import Std.Data.HashSet.Lemmas

public section

/-!
# Builders over growing lookups (task #329)

A builder's result depends on its lookups' answers alone: if every
answer `f` gives is one `g` gives too (`Mono f g`), a build through `f`
that succeeds is the build through `g`.  The lazy check builds through
lookups that answer built entries only; the serial parse's answer every
bound entry.
-/

namespace ConLeche.Frontend

open ConLeche

/-- Every answer of `f` is `g`'s. -/
@[expose] def Mono {ε α : Type} (f g : Nat → Except ε α) : Prop := ∀ k a, f k = .ok a → g k = .ok a

theorem Mono.refl {ε α : Type} (f : Nat → Except ε α) : Mono f f := fun _ _ h => h

theorem bindM {ε α β : Type} {x x' : Except ε α} {f f' : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) (hx : ∀ a, x = .ok a → x' = .ok a)
    (hf : ∀ a, f a = .ok b → f' a = .ok b) : (x' >>= f') = .ok b := by
  obtain ⟨a, ha, h⟩ := exceptBind_ok h
  rw [hx a ha]; exact hf a h

theorem mapM_mono {ε α : Type} {f g : Nat → Except ε α} (h : Mono f g) :
    ∀ {l : List Nat} {r : List α}, l.mapM f = .ok r → l.mapM g = .ok r
  | [], r, hl => hl
  | k :: l, r, hl => by
    simp only [List.mapM_cons] at hl ⊢
    exact bindM hl (h k) fun a hl => bindM hl (fun _ => mapM_mono h) fun _ hl => hl

theorem pwOfF_mono {ε : Type} {nm nm' : Nat → Except ε Name} {lv lv' : Nat → Except ε Level}
    {ex ex' : Nat → Except ε Expr} (hn : Mono nm nm') {x : PwRec} {v : PropWhen}
    (h : pwOfF nm lv ex x = .ok v) : pwOfF nm' lv' ex' x = .ok v := by
  cases x with
  | never => exact h
  | ifAllZero ns =>
    simp only [pwOfF] at h ⊢
    exact bindM h (fun _ => mapM_mono hn) fun _ h => h

theorem exprOfF_mono {ε : Type} {nm nm' : Nat → Except ε Name} {lv lv' : Nat → Except ε Level}
    {ex ex' : Nat → Except ε Expr} (hn : Mono nm nm') (hl : Mono lv lv') (he : Mono ex ex')
    {x : ExprRec} {v : Expr} (h : exprOfF nm lv ex x = .ok v) : exprOfF nm' lv' ex' x = .ok v := by
  cases x with
  | bvar k => exact h
  | sort u => exact bindM h (hl _) fun _ h => h
  | const n us => exact bindM h (hn _) fun _ h => bindM h (fun _ => mapM_mono hl) fun _ h => h
  | app f a => exact bindM h (he _) fun _ h => bindM h (he _) fun _ h => h
  | lam ty bd pw =>
    exact bindM h (he _) fun _ h => bindM h (he _) fun _ h =>
      bindM h (fun _ => pwOfF_mono hn) fun _ h => h
  | forallE ty bd pw =>
    exact bindM h (he _) fun _ h => bindM h (he _) fun _ h =>
      bindM h (fun _ => pwOfF_mono hn) fun _ h => h
  | letE ty vl bd =>
    exact bindM h (he _) fun _ h => bindM h (he _) fun _ h => bindM h (he _) fun _ h => h
  | proj tn ix s => exact bindM h (hn _) fun _ h => bindM h (he _) fun _ h => h
  | natVal n => exact h
  | strVal s => exact h

theorem cvOfF_mono {nm nm' : Nat → M Name} {lv lv' : Nat → M Level}
    {ex ex' : Nat → M Expr} (hn : Mono nm nm') (he : Mono ex ex')
    {x : CVRec} {v : ConstantVal} (h : cvOfF nm lv ex x = .ok v) : cvOfF nm' lv' ex' x = .ok v := by
  simp only [cvOfF] at h ⊢
  exact bindM h (hn _) fun _ h => bindM h (he _) fun _ h =>
    bindM h (fun _ => mapM_mono hn) fun _ h => h

/-- A non-inductive record's build over growing expression lookups. -/
theorem declOfF_mono {nm : Nat → M Name} {lv : Nat → M Level}
    {ex ex' : Nat → M Expr} (he : Mono ex ex') {d : DeclRec}
    (hd : ∀ tys cts rcs, d ≠ .ind tys cts rcs)
    {v : Declaration ⊕ RecordVerdict} (h : declOfF nm lv ex d = .ok v) :
    declOfF nm lv ex' d = .ok v := by
  cases d with
  | ax cvr u =>
    simp only [declOfF] at h ⊢
    exact bindM h (fun _ => cvOfF_mono (Mono.refl _) he) fun _ h => h
  | defn cvr vl hints safety =>
    simp only [declOfF] at h ⊢
    refine bindM h (fun _ => cvOfF_mono (Mono.refl _) he) fun _ h => ?_
    revert h; split
    · intro h; exact bindM h (he _) fun _ h => h
    · intro h; exact h
  | thm cvr vl =>
    simp only [declOfF] at h ⊢
    exact bindM h (fun _ => cvOfF_mono (Mono.refl _) he) fun _ h => bindM h (he _) fun _ h => h
  | opaq cvr vl u =>
    simp only [declOfF] at h ⊢
    refine bindM h (fun _ => cvOfF_mono (Mono.refl _) he) fun _ h => ?_
    revert h; split
    · intro h; exact h
    · intro h; exact bindM h (he _) fun _ h => h
  | quot cvr k =>
    simp only [declOfF] at h ⊢
    exact bindM h (fun _ => cvOfF_mono (Mono.refl _) he) fun _ h => h
  | ind tys cts rcs => exact absurd rfl (hd tys cts rcs)

/-- An inductive record reads its own indices only: through two lookups
that agree there, it is the same. -/
theorem declOfF_ind_congr {nm : Nat → M Name} {lv : Nat → M Level}
    {ex ex' : Nat → M Expr} {tys : List IndTypeRec} {cts : List IndCtorRec}
    {rcs : List IndRecRec} (he : ∀ j ∈ indExprIds tys cts rcs, ex j = ex' j) :
    declOfF nm lv ex (.ind tys cts rcs) = declOfF nm lv ex' (.ind tys cts rcs) := by
  have : restrictEx (Std.HashSet.ofList (indExprIds tys cts rcs)) ex =
      restrictEx (Std.HashSet.ofList (indExprIds tys cts rcs)) ex' := by
    funext j
    simp only [restrictEx, Std.HashSet.contains_ofList]
    split
    · rename_i hj
      exact he j (List.contains_iff_mem.mp hj)
    · rfl
  simp only [declOfF, this]

end ConLeche.Frontend
