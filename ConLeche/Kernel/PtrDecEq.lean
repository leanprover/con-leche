module

public import Init.Util

/-!
# The pointer-first decision, behind one name

`Name`, `Level`, `Literal` and `Expr` equality are pointer first
(`Name.decEqPtr` and its siblings): `Init.Util`'s `withPtrEqDecEq`
answers `isTrue` on one object at runtime and is `k ()` in the pure
model.  Its calling convention differs between the toolchains that
build this file: on the repository toolchain it takes `a b k`; on
lean4 master since 2026-10 it takes the pointer test and that test's
equation first (`withPtrEqDecEq withPtrEq (fun _ _ _ _ => rfl) a b k`).

Every call site goes through `ptrDecEq` below, so the difference is
this one definition.  The repository builds this copy; the pinner of a
toolchain with the new convention forks this file and nothing else
(`pinners/README.md`).  `@[inline]`: the compiled code is the call to
`withPtrEqDecEq` itself.
-/

@[expose] public section

namespace ConLeche

/-- `withPtrEqDecEq a b k`: the pointer test, then `k ()`. -/
@[inline] def ptrDecEq {α : Type u} (a b : α) (k : Unit → Decidable (a = b)) :
    Decidable (a = b) :=
  withPtrEqDecEq a b k

end ConLeche
