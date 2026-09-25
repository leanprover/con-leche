module

public import ConLeche.Kernel.Inductives.StructInstallF
public import ConLeche.Verify.InstList

public section

/-!
# The one-pass structure-install operations equal their sequential specs

The direct simple-structure install's hot loops run the `*A`
variants (`domsMatchAuxA`, `checkStructDomsAtFA`, and
`checkStructFieldUnivFA`) and the threaded `structProjResid`; every
lemma here identifies one of them **unconditionally** with the
sequential function the Model/Verify layers keep seeing.  The one-pass
telescope openers (`instPisAtF`, `instLamsAtF`, `openPisAtFvarsF`) are
not here: their equalities are `@[csimp]`s beside the definitions
(`ConLeche/Kernel/ExprOps.lean`, `ConLeche/Kernel/CheckerBase.lean`),
so every caller runs them.
-/

namespace ConLeche

theorem domsMatchAuxA_eq (g : Nat → Expr → Expr)
    (bs₁ bs₂ : List (Expr × BinderMeta)) (o₁ o₂ n : Nat) :
    domsMatchAuxA g bs₁.toArray bs₂.toArray o₁ o₂ n
      = domsMatchAux g bs₁ bs₂ o₁ o₂ n := by
  simp only [domsMatchAuxA, domsMatchAux, List.getElem?_toArray]

section
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

theorem checkStructDomsAtFA_eq (ops : CheckerOps m) (fe : FEnv)
    (off : Nat) (fvs doms : List Expr) :
    ∀ j, checkStructDomsAtFA ops fe off fvs.toArray doms.toArray j
      = checkStructDomsAtF ops fe off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructDomsAtFA, checkStructDomsAtF,
      List.getElem?_toArray, checkStructDomsAtFA_eq ops fe off fvs doms j]

end

open Expr in
theorem instPisAtLift_append :
    ∀ (xs ys : List Expr) (e : Expr),
      instPisAtLift (xs ++ ys) e = (instPisAtLift xs e).bind (instPisAtLift ys)
  | [], ys, e => by simp only [List.nil_append, instPisAtLift, Option.bind_some]
  | x :: xs, ys, .forallE dom body bi => by
    simp only [List.cons_append, instPisAtLift,
      instPisAtLift_append xs ys (body.instantiate1Lift x)]
  | x :: xs, ys, .bvar _ | x :: xs, ys, .fvar _ _ | x :: xs, ys, .sort _
  | x :: xs, ys, .const _ _ | x :: xs, ys, .app _ _ | x :: xs, ys, .lam _ _ _
  | x :: xs, ys, .letE _ _ _ | x :: xs, ys, .lit _
  | x :: xs, ys, .proj _ _ _ => rfl
