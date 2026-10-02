module

public import Fragment.Rules
public import Fragment.Scope

public section

/-!
# Scope from typing

Of the three scope facts the environment section reads off a
definition's type and value (`Expr.Scoped`, `Decl.lean`) — closed,
mentioning only stored constants, using only the declared level
parameters — the first two are not checks: they follow from the two
typing derivations being in the empty context.  A typed term is
**closed** below its context's length (`Infer.closedAt`: no rule
types a variable beyond the context), and every constant it
**mentions** is stored (`Infer.consts`: the constant rule
looks the name up).  Only the third is a condition beyond typing,
because the sort rule accepts `Sort u` at any level `u`; the
definition check (`DefOk`, `Decl.lean`) states it alone.

Both are structural inductions over `Infer` alone: the reduction and
equality premises of the inference rules concern the inferred
*types*, not the subject, so the mutual induction with `Red` and
`DefEq` (`Sound.lean`) is not needed here.
-/

namespace Fragment

variable [LevelOracle] {env : Env}

/-- **A typed term is closed below its context**: the variable rule
reads an entry of the context, and the binder rules type the body
under the context extended by the domain. -/
theorem Infer.closedAt : ∀ {Γ : List Expr} {e T : Expr}, Infer env Γ e T →
    e.closedAt Γ.length = true
  | _, _, _, .bvar h => by
    simp only [Expr.closedAt, decide_eq_true_eq]
    exact (List.getElem?_eq_some_iff.mp h).1
  | _, _, _, .sort => rfl
  | _, _, _, .const _ _ => rfl
  | _, _, _, .pi hA _ hB _ _ => by
    simp only [Expr.closedAt, Bool.and_eq_true]
    exact ⟨Infer.closedAt hA, Infer.closedAt hB⟩
  | _, _, _, .lam hA _ hb _ _ _ => by
    simp only [Expr.closedAt, Bool.and_eq_true]
    exact ⟨Infer.closedAt hA, Infer.closedAt hb⟩
  | _, _, _, .app hf _ ha _ => by
    simp only [Expr.closedAt, Bool.and_eq_true]
    exact ⟨Infer.closedAt hf, Infer.closedAt ha⟩

/-- **Every constant a typed term mentions is stored**: the constant
rule looks the name up in the environment. -/
theorem Infer.consts : ∀ {Γ : List Expr} {e T : Expr}, Infer env Γ e T →
    ∀ c ∈ e.consts, (env.find? c).isSome
  | _, _, _, .bvar _ => fun _ hc => by simp [Expr.consts] at hc
  | _, _, _, .sort => fun _ hc => by simp [Expr.consts] at hc
  | _, _, _, .const hfind _ => fun _ hc => by
    simp only [Expr.consts, List.mem_singleton] at hc
    subst hc
    rw [hfind]
    rfl
  | _, _, _, .pi hA _ hB _ _ => fun c hc => by
    simp only [Expr.consts, List.mem_append] at hc
    exact hc.elim (Infer.consts hA c) (Infer.consts hB c)
  | _, _, _, .lam hA _ hb _ _ _ => fun c hc => by
    simp only [Expr.consts, List.mem_append] at hc
    exact hc.elim (Infer.consts hA c) (Infer.consts hb c)
  | _, _, _, .app hf _ ha _ => fun c hc => by
    simp only [Expr.consts, List.mem_append] at hc
    exact hc.elim (Infer.consts hf c) (Infer.consts ha c)

end Fragment
