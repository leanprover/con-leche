module

public import ConLeche.Model.Inductives.FixRecRead
public import ConLeche.Model.Inductives.FixCtorReads
public import ConLeche.Verify.Inductives.SumInv
public import ConLeche.Verify.Inductives.FixParts
public import ConLeche.Kernel.Inductives.NativeInstall
public import ConLeche.Verify.Inductives.SumWF
public import ConLeche.Model.Inductives.SumRecFrames
public import ConLeche.Model.Inductives.SumStageCtor
public import ConLeche.Model.IndPointKit
public import ConLeche.Model.Annot.BitLevels
public section

/-!
# The recursive rules' readings at the recursor's cons (task #188)

A recursive rule's right-hand side mentions the recursor, so it reads
only at an environment holding it: the constructors' reading
premises cross the recursor's cons (`CtorReadsR.cross` — the
constructor types and their index expressions, instantiated at the
opening's variables, resolve at the pre-recursor environment), and
`denoteMeta_structRecRhsR` reads rule `j` there, with the recursor's leaf
the stored valuation.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  NativeParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Boundness through openings -/

omit [SetTheory V] in
/-- A bounded application's arguments are bounded. -/
theorem constsBound_getAppArgs {env₀ : Env} :
    ∀ (e : Expr), ConstsBound env₀ e → ∀ a ∈ e.getAppArgs, ConstsBound env₀ a
  | .app f a, he, x, hx => by
    rw [constsBound_app] at he
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact constsBound_getAppArgs f he.1 x hx
    · exact he.2
  | .bvar _, _, _, hx => nomatch hx
  | .fvar _ _, _, _, hx => nomatch hx
  | .sort _, _, _, hx => nomatch hx
  | .const _ _, _, _, hx => nomatch hx
  | .lam _ _ _, _, _, hx => nomatch hx
  | .forallE _ _ _, _, _, hx => nomatch hx
  | .letE _ _ _, _, _, hx => nomatch hx
  | .lit _, _, _, hx => nomatch hx
  | .proj _ _ _, _, _, hx => nomatch hx

omit [SetTheory V] in
/-- An opening's variables (their types) and residual are bounded when
the opened term is. -/
theorem openPisAtFvars_constsBound {env₀ : Env} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      ConstsBound env₀ e → openPisAtFvars n e d = some (fvs, o) →
      (∀ x ∈ fvs, ConstsBound env₀ x) ∧ ConstsBound env₀ o
  | 0, e, d, fvs, o, he, hop => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun x hx => nomatch hx), he⟩
  | n + 1, e, d, fvs, o, he, hop => by
    match e, he, hop with
    | .forallE dom bd mb, he, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        rw [constsBound_forallE] at he
        have hfv : ConstsBound env₀ (Expr.fvar d dom) := by
          rw [constsBound_fvar]; exact he.1
        obtain ⟨hfvs, ho⟩ := openPisAtFvars_constsBound n
          (ConstsBound.instantiate1 hfv bd 0 he.2) h₁
        refine ⟨fun x hx => ?_, ho⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hfv
        · exact hfvs x hx
      · exact nomatch hop

end ConLeche.Model
