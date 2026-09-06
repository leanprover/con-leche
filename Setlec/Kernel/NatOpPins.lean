module
public import Setlec.Kernel.Expr
meta import Setlec.PinGen.Dump

/-!
# Pinned Nat-operation declarations and certificate proofs (generated)

`#load_natop_pins` below splices, per pin-certified operation
(`Nat.div`, `Nat.mod`, …), the pinned defining expression
(`nat…DeclPin : Expr`) and the certificate proof blobs
(`nat…CertProofs : List Expr`) out of the **committed dump**
`NatOpPins/leanprover-lean4-v4.33.0.json`, embedded below with
`include_str`.  The hand-pinned certificate *statements* the proofs are
checked against stay in `Setlec/Kernel/Checker.lean`.

## Why a committed file (task #176, 2026-09-06)

Until now the pins were *computed* while this module elaborated: the
`#gen_natop_pins` command of `Setlec/PinGen.lean` loaded
`Setlec/PinGen/Certs.olean` **by name** (`importModules` at
`OLeanLevel.private`, the only way to see the certificate theorems'
proof bodies from a `module`).  Loading an olean by name is not an
import edge, so Lake never ordered the two, and the `extraDepTargets`
that stood in for the edge did not reach this module when it was built
through the executable's import graph.  On a cold tree

    $ lake build setlec
    error: Setlec/Kernel/NatOpPins.lean:33:0: object file
    '…/.lake/build/lib/lean/Setlec/PinGen/Certs.olean' of module
    Setlec.PinGen.Certs does not exist

The user's ruling: *"committing the pin as a file is fine — as soon as
we want to support multiple toolchains we have to do that.  CI can keep
the export up to date.  So let's just do that.  `lake build setlec`
should work out of the box."*

So this module is now an ordinary one.  Its only elaboration-time
dependency is `Setlec/PinGen/Dump.lean` — the interchange format,
`Lean` plus `Setlec.Kernel.Expr` and nothing else, reached by an
ordinary import edge.  Nothing in the checker's build depends on the
certificate library any more.

## Where the trust still comes from

The certificates are still **kernel-checked theorems**
(`Setlec/PinGen/Certs.lean`, the `SetlecPinCerts` library, still built
by `lake build`): the dump carries their proof *terms*, and the
statements those terms inhabit are re-checked by this checker at
install time against the hand-pinned `divModCertStmts`.  The
committed file is a cache of a computation, not a new axiom.

## Regenerating

    lake exe natop-pins-export            # rewrites the committed dump

`tests/pindump.sh` (run from `tests/arena.sh`) regenerates into a
scratch directory and `diff -q`s, so a stale dump fails the battery
loudly.  A toolchain bump writes a *new* file named after the new
toolchain: regenerate, add the file, and point the `include_str` below
at it — the loader refuses a dump whose `leanVersion` is not the
running one, so a forgotten bump is an error, never a silent wrong pin.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

#load_natop_pins include_str "NatOpPins/leanprover-lean4-v4.33.0.json"
