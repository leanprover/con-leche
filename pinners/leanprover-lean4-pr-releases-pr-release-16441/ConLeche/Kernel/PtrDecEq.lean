module

public import Init.Util

/-!
# FORK of `ConLeche/Kernel/PtrDecEq.lean` for this pinner

This pinner's toolchain (lean4 master, 2026-11) changed
`withPtrEqDecEq`'s calling convention and accepts `withPtrEq` only at
types the compiler can check, never polymorphically, so the shared
`ptrDecEq` does not compile here.  This copy decides by `k ()` alone —
the pure meaning of the shared one, without the pointer shortcut,
which a one-shot dump generator does not need.  See this pinner's `lakefile.toml`
for how the fork is wired in.
-/

@[expose] public section

namespace ConLeche

/-- `k ()`: the shared definition's pure meaning. -/
@[inline] def ptrDecEq {α : Type u} (a b : α) (k : Unit → Decidable (a = b)) :
    Decidable (a = b) :=
  k ()

end ConLeche
