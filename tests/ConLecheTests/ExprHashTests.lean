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

An application's 32-bit hash is a bijection in its function's hash
(`Expr.data`; task #634): two applications to the same argument share a
hash only if their functions do.  So on a chain `acc ↦ acc + 1`, which is
`app (app P acc) 1`, only the inner application's argument slot loses
information, once per step, as in official's `Lean.Expr` hash; the hash
orbit then closes after about 82k steps on average instead of the 58k of
a hash that mixed every node's hash through a lossy slot once more.

The check: 2^18 variables, whose own hashes collide a little, applied to
one argument; the applications have exactly as many distinct hashes as
the variables.  (The earlier hash lost 6 of them.)
-/

namespace ConLecheTests.ExprHash

open ConLeche

#guard
  let xs := (List.range 262144).map Expr.bvar
  let a := Expr.lit (.natVal 1)
  (Std.HashSet.ofList (xs.map fun x => (Expr.app x a).hash)).size ==
    (Std.HashSet.ofList (xs.map Expr.hash)).size

end ConLecheTests.ExprHash
