--#export t
/- End-to-end fixture (task #547; lean4#15686, fixed upstream by lean4#16146):
   ten thousand `Nat` literals that agree in their low 64 bits.

   `run n (2^64)` steps `n` times; each step matches its accumulator `a + 1`
   against a literal, so the kernel turns the literal `k * 2^64` into
   `Nat.succ (k * 2^64 - 1)` and continues with the literal `k * 2^64 - 1`,
   whose low 64 bits are all ones.  Every memo key that holds one of these
   literals differs from the others in that literal alone.  A literal hash of
   `n mod 2^64` (Lean's `Hashable Nat`, which `Literal.hash` was until
   lean4#16146) gives them all one hash, so each step's lookups walk a bucket
   of all the earlier steps' keys: quadratic in `n`.  With a hash of all the
   bits the check is linear.

   A performance fixture: accepted, in under a second (con-leche with the
   hash of all the words, 2026-11-09); con-leche with the `mod 2^64` hash took
   over 10 minutes.  `tests/arena.sh` runs it under a timeout of 10 s, so a
   hash that reads only the low bits fails it.

   The theorem is added with `addDecl` under `debug.skipKernelTC`: the
   elaborator would check `rfl` by its own unfolding, and its kernel has the
   same hash.  The stream is checked by the checkers that read it. -/
import Lean
open Lean Elab Command

def M : Nat := 2^64

def run : Nat → Nat → Nat
  | 0, a => a
  | _+1, 0 => 0
  | n+1, a+1 => run n (a + 1 + M)

/-- `Nat.beq (run n M) ((n + 1) * 2^64) = true`, by `Eq.refl true`. -/
def tDecl (n : Nat) : Declaration :=
  let ty := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Nat.beq) (mkApp2 (mkConst ``run) (mkRawNatLit n) (mkConst ``M))
      (mkRawNatLit ((n + 1) * 2 ^ 64))) (mkConst ``Bool.true)
  .thmDecl {
    name := Name.mkSimple "t"
    levelParams := []
    type := ty
    value := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true) }

elab "lit_hash_thm% " n:num : command => liftCoreM (addDecl (tDecl n.getNat))

set_option debug.skipKernelTC true
lit_hash_thm% 10000
