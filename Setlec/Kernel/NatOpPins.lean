module
public import Setlec.Kernel.Expr
meta import Setlec.PinGen

/-!
# Pinned Nat-operation declarations and certificate proofs (generated)

The `#gen_natop_pins` command below reads the pin-certified operations
(`Nat.div`, `Nat.mod`, …) from this module's *compiling environment* —
the toolchain prelude — and splices, per operation, the pinned
defining expression (`nat…DeclPin : Expr`) and the certificate proof
blobs (`nat…CertProofs : List Expr`).  See `Setlec/PinGen.lean` for
the generator and `Setlec/Kernel/Checker.lean` for the hand-pinned
certificate *statements* the proofs are checked against.

An out-of-prefix dependency in a pin or proof is a hard build error
here, at `lake build` time.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

#gen_natop_pins
