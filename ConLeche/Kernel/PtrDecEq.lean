module

public import Init.Util

/-!
# The pointer-first decision, behind one name

`Name`, `Level`, `Literal` and `Expr` equality are pointer first
(`Name.decEqPtr` and its siblings): `Init.Util`'s `withPtrEqDecEq`
answers `isTrue` on one object at runtime and is `k ()` in the pure
model.  It takes the pointer test as an argument, `withPtrEq`, because
the compiler accepts `withPtrEq` only at a type it can check (one whose
values hold no types or type formers), never at a type variable.  So
every call site is at a concrete type and passes `withPtrEq` and its
equation `withPtrEq_eq` itself:
`ConLeche.ptrDecEq withPtrEq ConLeche.withPtrEq_eq a b k`.

Every call site goes through `ptrDecEq` and `withPtrEq_eq` below, so
these two are all a toolchain with another calling convention must
replace.  The pinners of the toolchains before 2026-11 (an
`implemented_by` `withPtrEq`, accepted at every type, and a
`withPtrEqDecEq a b k` without the test) fork this file and nothing
else (`pinners/README.md`).  `@[inline]`: the compiled code is the call
to `withPtrEqDecEq` itself.
-/

@[expose] public section

namespace ConLeche

/-- `withPtrEq` is `k ()`: the equation `withPtrEqDecEq` asks for, and
what a proof about a `withPtrEq` call rewrites with. -/
theorem withPtrEq_eq {α : Type u} (a b : α) (k : Unit → Bool) (h : a = b → k () = true) :
    withPtrEq a b k h = k () := rfl

/-- `withPtrEqDecEq ptrEq hw a b k`: the pointer test `ptrEq`, then `k ()`. -/
@[inline] def ptrDecEq {α : Type u}
    (ptrEq : (a b : α) → (k : Unit → Bool) → (a = b → k () = true) → Bool)
    (hw : ∀ a b k h, ptrEq a b k h = k ()) (a b : α) (k : Unit → Decidable (a = b)) :
    Decidable (a = b) :=
  withPtrEqDecEq ptrEq hw a b k

end ConLeche
