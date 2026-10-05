module
public import ConLeche.Kernel.NatOpPinSet
meta import ConLeche.PinGen.Dump

/-!
# Pinned Nat-operation declarations and certificate proofs (generated)

`#load_natop_pins` below splices, per **committed dump** listed —
`pins/<toolchain>.json`, the repository's top-level `pins/` directory,
see `pins/README.md` — one **pin variant** `natOpPinSet_v<i> :
NatOpPinSet` (`ConLeche/Kernel/NatOpPinSet.lean`): per pin-certified
operation (`Nat.div`, `Nat.mod`, …) that toolchain's pinned defining
expression and certificate proof blobs, as constants
`nat…DeclPin_v<i> : Expr` / `nat…CertProofs_v<i> : List Expr`.  The
variants are listed in `natOpPinSets` in the order below.  That list is
what the shipped binary hands the fold as its PIN-LIST PARAMETER (task
#304), and the order is the order the install gate tries them in
(`checkDivModPinLoop`, `ConLeche/Kernel/Checker.lean`): the first
whose guards pass, whose pin is definitionally equal to the stream's
stored value and whose certificates check enables the operation's fast
path.  The hand-pinned certificate *statements* the proofs are checked against
stay in `ConLeche/Kernel/Checker.lean` and are shared by every variant.

## Why a committed file (task #176, 2026-09-06)

Until then the pins were *computed* while this module elaborated, out
of an olean loaded BY NAME, which Lake never ordered — on a cold tree
`lake build con-leche` failed.  The user's ruling: *"committing the pin
as a file is fine — as soon as we want to support multiple toolchains
we have to do that.  CI can keep the export up to date."*  So this
module is an ordinary one whose only elaboration-time dependency is
`ConLeche/PinGen/Dump.lean` (the interchange format); nothing in the
checker's build depends on the certificate library.

## Why several files (task #273, 2026-09-10)

A pin describes one toolchain's definition.  When lean4 master
rewrote `Decidable` into a structure the v4.33.0 pins stopped
describing its `Nat.mod`, and a con-leche bundled with a Lean release
must accept that release's own exports — so the binary now embeds the
dumps of every supported toolchain and tries them in order.  The
dump MATCHING the repository's own toolchain (`lean-toolchain`) comes
FIRST: on its streams the first attempt matches and the loop costs
nothing extra.

A dump is named after the toolchain that FIRST needed it, not after
the repository toolchain: a toolchain bump whose Init a committed pin set
still matches adds nothing (maintainer's ruling, task #328:
*"if the previous works with the new Init we should not add one"*) —
it only moves that dump to the front.  Today the repository toolchain
is v4.35.0-rc3 and its dump is the nightly-2026-09-10 one.  "Matches"
is the install gate's own criterion — the stored values definitionally
equal to a variant's pins, its certificates checking — so it is
decided by the checker: `tests/pindump.sh` exports the pinned
operations' cone out of the repository toolchain's `Init`
(`scripts/natop-matrix.sh`) and fails unless the binary accepts it.  A
new dump is added (recipe in `pins/README.md`) only when it declines
("no pin variant matched").  The loader accepts dumps from any Lean
version.

## Where the trust still comes from

The certificates are **kernel-checked theorems**
(`ConLeche/PinGen/Certs.lean`, the `ConLechePinCerts` library, built by
`lake build`): a dump carries their proof *terms*, and the statements
those terms inhabit are re-checked by this checker at install time
against the hand-pinned `divModCertStmts`.  The committed files are a
cache of a computation, not a new axiom; a corrupted dump fails its
certificate check and the stream declines.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

#load_natop_pins
  include_str "../../pins/leanprover-lean4-nightly-nightly-2026-09-10.json",
  include_str "../../pins/leanprover-lean4-v4.33.0.json",
  include_str "../../pins/leanprover-lean4-v4.34.0-rc2.json"
