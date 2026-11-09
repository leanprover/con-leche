module

public import ConLeche.Kernel.Inductives.StructInstallF

public section

/-!
# Instantiating a telescope at lifted arguments, in two steps

`instPisAtLift` at an appended argument list is the instantiation at
the first part, then at the second (`instPisAtLift_append`).
-/

namespace ConLeche

open Expr in
theorem instPisAtLift_append :
    ∀ (xs ys : List Expr) (e : Expr),
      instPisAtLift (xs ++ ys) e = (instPisAtLift xs e).bind (instPisAtLift ys)
  | [], ys, e => by simp only [List.nil_append, instPisAtLift, Option.bind_some]
  | x :: xs, ys, .forallE dom body => by
    simp only [List.cons_append, instPisAtLift,
      instPisAtLift_append xs ys (body.instantiate1Lift x)]
  | x :: xs, ys, .bvar _ | x :: xs, ys, .fvar _ _ | x :: xs, ys, .sort _
  | x :: xs, ys, .const _ _ | x :: xs, ys, .app _ _ | x :: xs, ys, .lam _ _
  | x :: xs, ys, .letE _ _ _ | x :: xs, ys, .lit _
  | x :: xs, ys, .proj _ _ _ => rfl
