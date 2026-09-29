prelude
--#export f

/- Corner case (lane PUNIT, 2026-09-29): `PUnit` is not pinned.  This
   stream (a `prelude` module, so nothing else is in scope) declares its
   OWN `PUnit` — `Type`-valued, two constructors, nothing like the
   toolchain's — and uses it.  While `PUnit` was a pinned basis block
   the checker rejected the block at the reserved-name check (a basis
   redefinition, exit 1); now it is an ordinary inductive and installs
   through the uniform route.  Official 0 (no pins).  Today 0. -/

inductive PUnit : Type where
  | unit : PUnit
  | other : PUnit

def f : PUnit := PUnit.other
