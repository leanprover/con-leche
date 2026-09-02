import Setlec.Cached.CoreC
import Setlec.Verify.Cached.SimCEff
import Setlec.Verify.Disc

/-!
# Cached body walks, part 1: list helpers and small twins (task #163)

Per-helper simulation walks: each cached twin
(`Setlec/Cached/CoreC.lean`) is `SimC`-related to its `Expr` original
at the fueled record, on `WFc`, well-scoped inputs.  Ports of
`Setlec/Verify/DiscI1.lean`'s walks under the recipe (DESIGN.md,
task #163): `SimAt → SimC`, denotation hypotheses → `RelC`/`RelCL`,
no `Ext`, node inversion by the `WFc.*_inv` lemmas instead of
`denoteNode` unpacking.  The pure comparand side of every statement is
byte-identical to the interned original's.
-/

namespace Setlec.Cached

open Setlec.Cached.ExprC

variable {mode : CheckMode}

/-- The cached conditional simulation at fuel `f` (the `SSimI` mirror):
every cached entry point simulates the corresponding fueled family on
`WFc`, well-scoped inputs.  Declared here so the per-body walks can
take it as their induction hypothesis; the knot batch proves it at
every fuel. -/
structure SSimC (mode : CheckMode) (env : Env) (f : Nat) : Prop where
  whnfCore : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).whnfCore d i)
      ((fueledFns mode env).whnfCore d e)
  whnf : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).whnf d i)
      ((fueledFns mode env).whnf d e)
  infer : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).infer d i)
      ((fueledFns mode env).infer d e)
  defeq : ∀ {s₀ : CState} {d : Nat} {i j : ExprC} {a b : Expr},
    CSOK mode env s₀ → RelC i a → RelC j b →
    Expr.WScoped d a → Expr.WScoped d b →
    SimC mode env s₀ RelVC
      ((coreKnotI mode (mkFEnv env) f).defeq d i j)
      ((fueledFns mode env).defeq d a b)
  annotate : ∀ {s₀ : CState} {d : Nat} {i : ExprC} {e : Expr},
    CSOK mode env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode env s₀ (RelEC d)
      ((coreKnotI mode (mkFEnv env) f).annotate d i)
      ((fueledFns mode env).annotate d e)

/-- The base case: fuel `0` throws everywhere. -/
theorem ssimC_zero (env : Env) : SSimC mode env 0 :=
  { whnfCore := fun _ _ _ => SimC.throw
    whnf := fun _ _ _ => SimC.throw
    infer := fun _ _ _ => SimC.throw
    defeq := fun _ _ _ _ _ => SimC.throw
    annotate := fun _ _ _ => SimC.throw }

section Walks

variable {env : Env} {f : Nat}

/-- Port of `defEqListI_sim`: the pairwise definitional-equality
helper simulates its fueled original on related, well-scoped lists. -/
theorem defEqListC_sim (ih : SSimC mode env f) {d : Nat} :
    ∀ {args : List ExprC} {xs : List Expr} {brgs : List ExprC}
      {ys : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      RelCL args xs → RelCL brgs ys →
      (∀ x ∈ xs, Expr.WScoped d x) → (∀ y ∈ ys, Expr.WScoped d y) →
      SimC mode env s₀ RelVC
        (defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d args brgs)
        (defEqList (fueledFns mode env) env d xs ys) := by
  intro args
  induction args with
  | nil =>
    intro xs brgs ys s₀ hs hargs hbrgs _ _
    obtain rfl := hargs.nil_inv
    match brgs, ys, hbrgs.length with
    | [], [], _ => exact SimC.pure hs rfl
    | b :: bs, y :: ys, _ => exact SimC.pure hs rfl
  | cons a as iha =>
    intro xs brgs ys s₀ hs hargs hbrgs hwx hwy
    obtain ⟨x, xs, rfl, hax, hasxs⟩ := hargs.cons_inv
    match brgs, ys, hbrgs.length with
    | [], [], _ => exact SimC.pure hs rfl
    | b :: bs, ys', hlen =>
      obtain ⟨y, ys, rfl, hby, hbsys⟩ := hbrgs.cons_inv
      show SimC mode env s₀ RelVC
        ((coreKnotI mode (mkFEnv env) f).defeq d a b >>= fun r =>
          if r then defEqListI (coreKnotI mode (mkFEnv env) f)
            (mkFEnv env) d as bs
          else pure false)
        ((fueledFns mode env).defeq d x y >>= fun r =>
          if r then defEqList (fueledFns mode env) env d xs ys
          else pure false)
      refine SimC.bind (ih.defeq hs hax hby
        (hwx x (List.mem_cons_self ..)) (hwy y (List.mem_cons_self ..)))
        (fun s₁ rb r hs₁ hP => ?_)
      obtain rfl : rb = r := hP
      cases rb with
      | true =>
        simp only [↓reduceIte]
        exact iha hs₁ hasxs hbsys
          (fun x hx => hwx x (List.mem_cons_of_mem _ hx))
          (fun y hy => hwy y (List.mem_cons_of_mem _ hy))
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.pure hs₁ rfl

end Walks

end Setlec.Cached
