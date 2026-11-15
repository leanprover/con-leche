--#export t
/- End-to-end fixture (task #592): the constructor shortcut in the eager
   tower (official's `m_eager_reduce`, task #353).  `t` checks
   `@id (f (x * 0 + 3) = some 2) (eagerReduce (Eq.refl (some 2)))` under the
   binder `x : Nat`; the argument's type is compared with the domain in
   eager mode, where the shortcut head-normalises `f (x * 0 + 3)` although
   it has a free variable, reaches `some (x * 0 + 2)` and continues on that
   normal form.  Outside the eager tower the free `x` keeps the shortcut off
   and the lazy path decides.  Official accepts; con-leche accepts (the
   target verdict).

   `hint_eager` builds the term without the elaborator deciding the
   equation; `debug.skipKernelTC` keeps the elaborator's own kernel off
   it. -/
import Lean

open Lean Elab Term Meta in
elab "hint_eager" : term <= T => do
  let T ← instantiateMVars T
  let some (α, _, rhs) := T.eq? | throwError "hint_eager: expected an equation"
  let u ← getLevel α
  let refl := mkApp2 (mkConst ``Eq.refl [u]) α rhs
  let arg := mkApp2 (mkConst ``eagerReduce [levelZero]) (mkApp3 (mkConst ``Eq [u]) α rhs rhs) refl
  return mkApp2 (mkConst ``id [levelZero]) T arg

noncomputable def f (n : Nat) : Option Nat :=
  Nat.rec (motive := fun _ => Option Nat) none (fun k _ => some k) n

set_option debug.skipKernelTC true in
theorem t (x : Nat) : f (x * 0 + 3) = some 2 := hint_eager
