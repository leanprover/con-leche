module

public import ConLeche.Kernel.Expr
public import Std.Data.HashSet
/- The `#guard`s are EVALUATED, so the module is needed at the meta level
too. -/
meta import ConLeche.Kernel.Expr
meta import Std.Data.HashSet

public section

/-!
# The node hash along a chain

A node combines its children's 32-bit hashes with `mixHash32`
(`Expr.data`; tasks #634, #638, lean4#16107), a bijection in each argument
when the other is fixed.  So two applications to the same argument share a
hash only if their functions do, two applications of the same function
share one only if their arguments do, and on a chain `acc ↦ acc + 1`, which
is `app (app P acc) 1`, the hash step is a bijection: the hashes repeat only
by returning to the start's (after about 2³¹ steps on average).  The old
64-bit `mixHash` truncated to 32 bits lost information in the argument slot
once per step, and such a chain's hashes ran into a cycle after about 82k
steps.

The checks: 2^18 variables, whose own hashes collide a little, applied to one
argument, and one function applied to them; the applications have exactly
as many distinct hashes as the variables.  And an `acc + 1` chain of 2^18
steps has no repeated hash.  And `mixHash32` agrees with upstream's C on a
few values.
-/

namespace ConLecheTests.ExprHash

open ConLeche

-- `mixHash32` is upstream's `lean_uint32_mix_hash` (lean4#16107): values
-- computed from that C.
#guard mixHash32 0 0 == 3864292196
#guard mixHash32 1 2 == 3704777237
#guard mixHash32 29 0xdeadbeef == 3395699167
#guard mixHash32 0xffffffff 0xffffffff == 1284620446
#guard mixHash32 0x12345678 0x9abcdef0 == 733402588

#guard
  let xs := (List.range 262144).map Expr.bvar
  let a := Expr.lit (.natVal 1)
  (Std.HashSet.ofList (xs.map fun x => (Expr.app x a).hash)).size ==
    (Std.HashSet.ofList (xs.map Expr.hash)).size

#guard
  let xs := (List.range 262144).map Expr.bvar
  let f := Expr.const (.str .anonymous "f") []
  (Std.HashSet.ofList (xs.map fun x => (Expr.app f x).hash)).size ==
    (Std.HashSet.ofList (xs.map Expr.hash)).size

/-- `acc + 1` as the elaborator writes it, over `Nat`. -/
def addOne (acc : Expr) : Expr :=
  let nat := Expr.const (.str .anonymous "Nat") []
  let p := Expr.app (Expr.app (Expr.app (Expr.app
    (Expr.const (.str (.str .anonymous "HAdd") "hAdd") [.zero, .zero, .zero]) nat) nat) nat)
    (Expr.const (.str .anonymous "instHAdd") [.zero])
  Expr.app (Expr.app p acc) (Expr.lit (.natVal 1))

#guard Id.run do
  let mut e := Expr.lit (.natVal 0)
  let mut seen : Std.HashSet UInt64 := {}
  for _ in [0:262144] do
    if seen.contains e.hash then return false
    seen := seen.insert e.hash
    e := addOne e
  return true

end ConLecheTests.ExprHash
