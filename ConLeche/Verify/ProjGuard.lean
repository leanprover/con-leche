module

public import ConLeche.Kernel.CoreDefs
public import ConLeche.Verify.Shift
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The rows of a projection's guard (task #480)

What `projGuardRows` hands the checker is scoped: each row's term at its
own depth.  The cached walk needs it for its callees' preconditions, the
model for its frames.
-/

namespace ConLeche

/-- A row list whose terms are scoped at their own depths. -/
@[expose] def GuardRowsWS (rows : List (Nat × Expr)) : Prop :=
  ∀ p ∈ rows, Expr.WScoped p.1 p.2

theorem GuardRowsWS.nil : GuardRowsWS [] := fun _ h => nomatch h

theorem GuardRowsWS.head {d : Nat} {dom : Expr} {rest : List (Nat × Expr)}
    (h : GuardRowsWS ((d, dom) :: rest)) : Expr.WScoped d dom :=
  h (d, dom) List.mem_cons_self

theorem GuardRowsWS.tail {p : Nat × Expr} {rest : List (Nat × Expr)}
    (h : GuardRowsWS (p :: rest)) : GuardRowsWS rest :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- A row of `projGuardRowsAt` is a binder of the telescope. -/
theorem mem_projGuardRowsAt {cty : Expr} {nP idx : Nat} {fvs : List Expr} {p : Nat × Expr}
    (h : p ∈ projGuardRowsAt cty nP idx fvs) :
    ∃ j x, j ≤ idx ∧ (j = idx ∨ structUsedLater cty nP j = true) ∧
      fvs[nP + j]? = some x ∧ p = (nP + j, x.fvarTypeD) := by
  unfold projGuardRowsAt at h
  obtain ⟨j, hj, hp⟩ := List.mem_filterMap.mp h
  have hle : j ≤ idx := Nat.le_of_lt_succ (List.mem_range.mp hj)
  split at hp
  next hc =>
    cases hx : fvs[nP + j]? with
    | none => rw [hx] at hp; exact nomatch hp
    | some x =>
      rw [hx] at hp
      simp only [Option.map_some, Option.some.injEq] at hp
      exact ⟨j, x, hle, hc, hx, hp.symm⟩
  next => exact nomatch hp

/-- The rows at an opened closed telescope are scoped. -/
theorem projGuardRowsAt_ws {cty e o : Expr} {nP idx k : Nat} {fvs : List Expr}
    (hop : openPisAtFvars k e 0 = some (fvs, o)) (hw : Expr.WScoped 0 e) :
    GuardRowsWS (projGuardRowsAt cty nP idx fvs) := by
  intro p hp
  obtain ⟨j, x, -, -, hx, rfl⟩ := mem_projGuardRowsAt hp
  have := openPisAtFvars_typeWScoped k hop hw (nP + j) x hx
  simpa using this

end ConLeche
