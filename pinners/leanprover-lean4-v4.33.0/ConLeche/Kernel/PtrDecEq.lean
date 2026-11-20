module

public import Init.Util
/- This toolchain's `withPtrEq` is `implemented_by`, its body `k ()` not
exposed; `withPtrEq_eq` below is that body. -/
import all Init.Util

/-!
# FORK of `ConLeche/Kernel/PtrDecEq.lean` for this pinner

This pinner's toolchain predates lean4's `withPtrEq` change of 2026-11:
its `withPtrEqDecEq` takes `a b k` alone (the pointer test is built in),
and its `withPtrEq` hides its body.  This copy has the shared file's two
names and statements: `withPtrEq_eq` is proved by that body, under
`import all`, and `ptrDecEq` drops the pointer test it is passed and
calls this toolchain's `withPtrEqDecEq`.  The same copy serves the
v4.33.0, v4.34.0-rc2 and nightly-2026-09-10 pinners; see this pinner's
`lakefile.lean` for how the fork is wired in.
-/

@[expose] public section

namespace ConLeche

/-- `withPtrEq` is `k ()`.  `by rfl`: a term-mode `rfl` elaborates in
the public view, which does not see the body. -/
theorem withPtrEq_eq {α : Type u} (a b : α) (k : Unit → Bool) (h : a = b → k () = true) :
    withPtrEq a b k h = k () := by rfl

/-- `withPtrEqDecEq a b k`: this toolchain's pointer test, then `k ()`. -/
@[inline] def ptrDecEq {α : Type u}
    (_ptrEq : (a b : α) → (k : Unit → Bool) → (a = b → k () = true) → Bool)
    (_hw : ∀ a b k h, _ptrEq a b k h = k ()) (a b : α) (k : Unit → Decidable (a = b)) :
    Decidable (a = b) :=
  withPtrEqDecEq a b k

end ConLeche
