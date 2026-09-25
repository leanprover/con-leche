module

public import ConLeche.Verify.Inductives.PosCompleteFrame

public section

/-!
# The elimination link (lane COMPLETE-4, (A))

Official's `elimNested` (`OfficialNested.lean`) replaces nested
occurrences with a GROWING auxiliary map, one constructor at a time, and
reads "mentions a type of the declaration" over the GROWING list of its
types.  The completeness proof reads the result against the FINAL map,
over the members only (`sigmaAll`).  This module relates the two:

* on a term free of auxiliary names (every term official replaces is: a
  replaced occurrence is not descended into), official's
  `isNestedApp` over its type list agrees with the one over the members
  (`isNestedApp_congr`);
* `sigmaAll` is stable under extending the map (`sigmaAll_compat`);
* `replaceAll` from a state computes `sigmaAll` against every map that
  extends the one it ends with (`replaceAll_spec`).
-/

namespace ConLeche

open Expr

section Elim

variable {c : Official.ElimCtx}

/-! ## Occurrences off the auxiliary names -/

theorem nestOcc_congr_noAux {G : Name → Bool} {mem mem' : List Name}
    (h : ∀ n, G n = false → mem.contains n = mem'.contains n) :
    ∀ (x : Expr), NoAux G x → x.nestOcc mem 0 0 = x.nestOcc mem' 0 0 := by
  intro x
  induction x with
  | const n us => intro hx; simp only [NoAux] at hx; simp only [Expr.nestOcc, h n hx]
  | app f a ihf iha => intro hx; simp only [NoAux] at hx; simp only [Expr.nestOcc, ihf hx.1, iha hx.2]
  | lam t b m iht ihb => intro hx; simp only [NoAux] at hx; simp only [Expr.nestOcc, iht hx.1, ihb hx.2]
  | forallE t b m iht ihb =>
    intro hx; simp only [NoAux] at hx; simp only [Expr.nestOcc, iht hx.1, ihb hx.2]
  | letE t v b iht ihv ihb =>
    intro hx; simp only [NoAux] at hx
    simp only [Expr.nestOcc, iht hx.1, ihv hx.2.1, ihb hx.2.2]
  | proj s i x ih => intro hx; simp only [NoAux] at hx; simp only [Expr.nestOcc, ih hx]
  | _ => intro _; rfl

theorem noAux_getAppArgs {G : Name → Bool} : ∀ (e : Expr), NoAux G e → ∀ x ∈ e.getAppArgs, NoAux G x := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h x hx
    simp only [NoAux] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ihf h.1 x hx
    · exact h.2
  | _ => intro _ x hx; simp [Expr.getAppArgs] at hx

theorem noAux_getAppFn {G : Name → Bool} : ∀ (e : Expr), NoAux G e → NoAux G e.getAppFn := by
  intro e
  induction e with
  | app f a ihf _ => intro h; simp only [NoAux] at h; simpa [Expr.getAppFn] using ihf h.1
  | _ => intro h; simpa [Expr.getAppFn] using h

theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.any_cons]
    rw [h y List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **Official's nested-occurrence test off the auxiliary names**: on a
term free of them, it reads the same over any two lists of declared
names that agree off them. -/
theorem isNestedApp_congr {G : Name → Bool} {mem mem' : List Name}
    (h : ∀ n, G n = false → mem.contains n = mem'.contains n) {e : Expr} (he : NoAux G e) :
    Official.isNestedApp c mem e = Official.isNestedApp c mem' e := by
  have hargs := noAux_getAppArgs e he
  cases e with
  | app f a =>
    simp only [Official.isNestedApp]
    split
    · split
      · rename_i caps _
        rw [any_congr_mem (l := ((Expr.app f a).getAppArgs.take caps.nparams))
          (fun x hx => nestOcc_congr_noAux h x (hargs x (List.mem_of_mem_take hx)))]
      · rfl
    · rfl
  | _ => rfl

/-! ## `sigmaAll` against a growing map -/

/-- `M` extends `A` as a lookup table. -/
@[expose] def Compat (A M : List (Expr × Name)) : Prop :=
  ∀ k x, A.lookup k = some x → M.lookup k = some x

theorem Compat.refl (A : List (Expr × Name)) : Compat A A := fun _ _ h => h

theorem Compat.trans {A B C : List (Expr × Name)} (h₁ : Compat A B) (h₂ : Compat B C) :
    Compat A C := fun k x h => h₂ k x (h₁ k x h)

theorem Compat.append (A B : List (Expr × Name)) : Compat A (A ++ B) := by
  intro k x h
  induction A with
  | nil => simp at h
  | cons p A ih =>
    obtain ⟨k', x'⟩ := p
    by_cases hk : (k == k') = true
    · simp only [List.lookup, List.cons_append, hk] at h ⊢; exact h
    · simp only [Bool.not_eq_true] at hk
      simp only [List.lookup, List.cons_append, hk] at h ⊢
      exact ih h

/-- **`sigmaAll` is stable under extending the map.** -/
theorem sigmaAll_compat {mem : List Name} {A M : List (Expr × Name)} (hAM : Compat A M) :
    ∀ (e : Expr), SigOk c mem A e → SigOk c mem M e ∧ sigmaAll c mem M e = sigmaAll c mem A e := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro h
    rcases hN : Official.isNestedApp c mem (.app f a) with err | (_ | ⟨I, us, np, args⟩)
    · simp only [SigOk, hN] at h
    · simp only [SigOk, hN] at h
      obtain ⟨hf', ef⟩ := ihf h.1
      obtain ⟨ha', ea⟩ := iha h.2
      simp only [SigOk, sigmaAll, hN, ef, ea]
      exact ⟨⟨hf', ha'⟩, trivial⟩
    · simp only [SigOk, hN] at h
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
      simp only [SigOk, sigmaAll, hN, hAM _ _ hx, hx, Option.isSome_some, and_self]
  | lam t b m iht ihb =>
    intro h; simp only [SigOk] at h
    obtain ⟨h1, e1⟩ := iht h.1; obtain ⟨h2, e2⟩ := ihb h.2
    exact ⟨⟨h1, h2⟩, by simp only [sigmaAll, e1, e2]⟩
  | forallE t b m iht ihb =>
    intro h; simp only [SigOk] at h
    obtain ⟨h1, e1⟩ := iht h.1; obtain ⟨h2, e2⟩ := ihb h.2
    exact ⟨⟨h1, h2⟩, by simp only [sigmaAll, e1, e2]⟩
  | letE t v b iht ihv ihb =>
    intro h; simp only [SigOk] at h
    obtain ⟨h1, e1⟩ := iht h.1; obtain ⟨h2, e2⟩ := ihv h.2.1; obtain ⟨h3, e3⟩ := ihb h.2.2
    exact ⟨⟨h1, h2, h3⟩, by simp only [sigmaAll, e1, e2, e3]⟩
  | proj s i x ih =>
    intro h; simp only [SigOk] at h
    obtain ⟨h1, e1⟩ := ih h
    exact ⟨h1, by simp only [sigmaAll, e1]⟩
  | _ => intro h; exact ⟨h, rfl⟩

end Elim

end ConLeche
