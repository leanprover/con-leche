import Setlec.TT.Nat.Numeral
import Setlec.TT.Nat.Ops
import Setlec.TT.Nat.WfOps
import Setlec.TT.Nat.Examples

/-!
# Literal `Nat` computation in the declarative layer (task #119, split)

`Setlec/TT/DESIGN.md` §7.  The checker accepts `Nat.add 12345 67890 =
80235` through certified GMP fast paths; this directory shows that
every such acceptance is *derivable* in the layer, without built-in
literal rules and without building a 12345-step derivation object.

The modules are checker-free: they import only `Setlec/TT/*`, and no
lemma mentions a particular operation term.
-/
