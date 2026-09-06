module
public import Setlec.Kernel.Expr
meta import Setlec.PinGen

/-!
# Pinned compiler-trust opaque values (generated, task #95)

The `#gen_trust_pins` command reads the toolchain prelude's
`Lean.reduceNat` / `Lean.reduceBool` opaque values and splices their
pinned defining expressions (`reduceNatDeclPin` / `reduceBoolDeclPin`
`: Expr`; the `have := trustCompiler` wrapper is zeta-expanded by the
conversion, leaving the plain identity function).  At install
(`checkReducePin` in `Setlec/Kernel/Checker.lean`) the stream's stored
opaque value is compared against the pin by definitional equality —
toolchain drift surfaces as a decline, never silently.

These two pins stay *generated at elaboration time*: `#gen_trust_pins`
reads only the toolchain's own `Init`, which is always built, so it
never had the build-ordering defect that moved the Nat-operation pins
to a committed file at task #176 (see `Setlec/Kernel/NatOpPins.lean`).

Rebuild caveat: Lake sees no dependency edge to the toolchain prelude;
`touch` this file to force regeneration after a toolchain bump.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

#gen_trust_pins
