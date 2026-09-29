module

public import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Verify.Inductives.NestScope

public section

/-!
# A generated minor premise, as syntax (G1-syn, `hminor`)

The generated recursor stage generates, per minor slot `s` of class `c`
and constructor `x`, the minor premise's type

    minorTy c x (nP + s) = Π (f⃗ : fields) (ih⃗ : Π a⃗, motive_t e⃗ (f a⃗)), motive_c es (C p⃗ f⃗)

(`ClassGen.minorTy`, `Kernel/Inductives/GenRec.lean`) and places it
in the shared prefix at position `nP + s` (`ClassGen.prefixBinders`).
What the model's reading of it (`Model/Inductives/ClassGenMinor.lean`)
needs, as pure syntax:

* **the spelled-out shape** (`ClassGen.minorTy_spec`): a telescope over
  the fields and the `ih`s, closed at `nP + s`, whose conclusion is the
  class's motive variable applied to a nonempty spine, and whose `ih`
  domains are telescopes over the callee's motive variable applied to a
  nonempty spine;
* **the `ih` domains name no `ih` variable** (`fvarsBelow (nP + s + nF)`):
  an `ih`'s own telescope is opened at `nP + s + nF + l` and closed again
  there, so what is left names only the parameters, the motives and the
  fields — the gap `[nP + s + nF, nP + s + nF + l)` is never used
  (`Expr.FvGap`, a shallow "no variable in the gap" predicate that every
  step of the construction keeps);
* **a tighter scope** (`WScoped.of_leaves_below`): a term whose closure
  leaves lie below `lo` is scoped at `lo`.
-/

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-! ## No variable in a gap -/

/-! ## A tighter scope -/

/-- A term scoped at `d` whose closure leaves all lie below `lo` is
scoped at `lo`. -/
theorem WScoped.of_leaves_below {lo : Nat} :
    ∀ {e : Expr} {d : Nat}, WScoped d e → (∀ l ∈ e.fvarLeaves, l.1 < lo) → WScoped lo e := by
  intro e
  induction e with
  | fvar i ty _ =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨hl (i, ty) (by simp [fvarLeaves]), hw.2⟩
  | app f a ihf iha =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨ihf hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      iha hw.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | lam ty b m iht ihb =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨iht hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihb hw.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | forallE ty b m iht ihb =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨iht hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihb hw.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | letE ty v b iht ihv ihb =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ⟨iht hw.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihv hw.2.1 fun l h => hl l (by simp [fvarLeaves, h]),
      ihb hw.2.2 fun l h => hl l (by simp [fvarLeaves, h])⟩
  | proj s i x ih =>
    intro d hw hl
    simp only [WScoped] at hw ⊢
    exact ih hw fun l h => hl l (by simpa [fvarLeaves] using h)
  | _ => intro _ _ _; simp [WScoped]

/-! ## The minor premise, spelled out -/

/-- The recursive fields a constructor's minor premise walks: field
index, landing class, telescope length. -/
@[expose] def ClassCtor.recs (x : ClassCtor) : List (Nat × Nat × Nat) :=
  (List.range x.nF).filterMap fun i =>
    match x.kinds.getD i .ordinary with
    | .recursive t tele => some (i, t, tele)
    | .ordinary => none

/-- **The prefix binder at a minor slot** is the minor premise's type of
the slot's constructor. -/
theorem ClassGen.prefixBinders_minor {g : ClassGen} (hg : ClassGenScoped g) {s c : Nat}
    {C : Name} {ihs0 : List (Nat × Nat)} (hs : g.slots[s]? = some (.minor c C ihs0)) :
    ∃ x T, (g.ctors.getD c []).find? (·.cv.name == C) = some x ∧
      g.minorTy c x (g.nP + s) = some T ∧ g.pre[g.nP + s]? = some (T, g.bm) := by
  have hpre := hg.pre
  unfold ClassGen.prefixBinders at hpre
  obtain ⟨slotBs, hsl, hpre⟩ := Option.bind_eq_some_iff.mp hpre
  simp only [Option.pure_def, Option.some.injEq] at hpre
  have hslen : s < g.slots.length := (List.getElem?_eq_some_iff.mp hs).1
  obtain ⟨y, hy, hyb⟩ := option_mapM_getElem? hsl s s (List.getElem?_range hslen)
  have hslot : g.slots.getD s default = .minor c C ihs0 := by
    rw [List.getD_eq_getElem?_getD, hs, Option.getD_some]
  simp only at hy
  rw [hslot] at hy
  simp only at hy
  obtain ⟨x, hxf, hy⟩ := Option.bind_eq_some_iff.mp hy
  obtain ⟨T, hT, hy⟩ := Option.bind_eq_some_iff.mp hy
  simp only [Option.pure_def, Option.some.injEq] at hy
  subst hy
  refine ⟨x, T, hxf, hT, ?_⟩
  rw [← hpre, List.getElem?_append_right (by simp [hg.params_len])]
  simpa [hg.params_len] using hyb

end ConLeche
