# `pins/` — the Nat-operation pin certificates and the built-in prelude

Committed **generated data**: one pin dump per supported Lean
toolchain, and the built-in prelude of the repository's own toolchain:

    pins/leanprover-lean4-v4.33.0.json                        the repository toolchain's dump
    pins/leanprover-lean4-nightly-nightly-2026-09-10.json     a second toolchain's dump (a "pin variant")
    pins/leanprover-lean4-v4.33.0.prelude.ndjson              the built-in prelude

## The pin dump (`<toolchain>.json`)

Carries, for every pin-certified `Nat` operation — `Nat.div`,
`Nat.mod`, `Nat.gcd`, `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.land`,
`Nat.lor`, `Nat.xor` — two things:

* the **pinned defining expression**: that toolchain's own definition
  value with every local helper (`Nat.modCore`, `Nat.div.go`, matchers,
  `._f` functionals) delta-unfolded and every non-stream-prefix
  definition inlined, so the pin is one closed expression over ground
  constants the export stream declares.  At install the checker compares
  the stream's stored value against the pin by *definitional equality*;
  a mismatch declines (exit 2), never accepts silently.
* the **certificate proof terms**: the proofs of the characterization
  theorems in `ConLeche/PinGen/Certs.lean` — kernel-checked Lean
  theorems, elaborated against the real toolchain prelude and made
  self-contained (closed over each operation's own dependency cone, so
  they check against dependency-sliced streams too).

The encoding is described in `ConLeche/PinGen/Dump.lean`: JSON, and what
is stored per blob is the *share table* (`["a",123,124]`-style entries
referring to earlier entries by index), not the expression tree — the
pins share heavily, and the tree form would be three orders of
magnitude larger.

Since task #191 the dump also carries an index of the prelude beside
it: `preludeFile` (its basename), `preludeMembers` (the record owners
it holds beyond the pinned basis blocks — today `Bool`),
`preludeNames` (every name it declares, in order) and `orderResidual`
(per operation, the order-sensitive ground the prelude does NOT hold
because it is a stream-certified operation — `Nat.shiftLeft`'s
`Nat.ble`/`Nat.sub`, the bitwise operations' `Nat.mul`; the frontend
*hoists* those ahead of the operation instead, see
`ConLeche/Frontend/NatOpGround.lean`).

## The built-in prelude (`<toolchain>.prelude.ndjson`)

A **lean4export-format stream** — the six pinned basis blocks (`Eq`,
`Nat`, `PUnit`, `Empty`, `False`, `Quot` with `Quot.sound`) and the
toolchain's `Bool` block, exactly as the toolchain declares them,
serialised by `ConLeche/PinGen/Prelude.lean` (a port of lean4export's
writer).  `ConLeche/Frontend/Prelude.lean` embeds it with `include_str`,
parses it with the ordinary frontend parser, and every stream parse
PREPENDS its records: the fold installs them first, unconditionally,
by the routes it installs any stream's records by (the basis blocks
from their pins, `Bool` through the direct sum install).  A later
stream copy of a prelude declaration is dropped when it is the same
declaration (up to the basis-matching canonical form) and declines the
run when it differs.

Why: the pin-certified operations' certificate statements are spelled
over `Bool`, `Eq` and the structural operations, which the operation's
own value never reaches — an export that orders declarations by a DFS
from arbitrary roots (lean4export does) could emit the operation
first, and the install declined (user report, 2026-09-06).  The
prelude's membership is *computed*, not chosen: the generator
determines, per operation, every constant the pin, the certificates
and the guards need that the operation's own closure does not reach,
and the prelude is the part of that which is not a stream-certified
operation (see `ConLeche/PinGen/Prelude.lean` and DESIGN.md, task #191).

## One dump per toolchain — the pin variants

The names are the `lean-toolchain` string with everything outside
`[A-Za-z0-9._-]` turned into `-`.  A pin computed from one toolchain
describes only that toolchain's definitions, so supporting several
toolchains means storing their dumps side by side in this directory,
and `ConLeche/Kernel/NatOpPins.lean` embeds **all of them** with
`include_str` (paths there resolve relative to that source file's
directory, hence `"../../pins/…"`), one `#load_natop_pins` argument per
dump, in the order the install gate tries them: each dump becomes a
**pin variant** (`ConLeche.NatOpPinSet`, listed in
`ConLeche.natOpPinSets`), and at a pin-certified operation's install
the checker takes the FIRST variant whose ground constants the stream
declares, whose pin is definitionally equal to the stream's stored
value and whose certificates check; only when no variant matches does
the stream decline, naming what each variant failed on.  The
repository's own toolchain (`lean-toolchain`) is listed first, so on
its streams the first attempt matches and the loop costs nothing; the
others follow in the order they were added.

So one binary — built on the repository toolchain — accepts the
exports of every toolchain it carries a variant for (and of the
toolchains in between whose definitions did not drift: the v4.33.0
variant accepts v4.29.0 … v4.33.1 exports, the nightly variant the
lean4-master ones since the `Decidable` rewrite of v4.34.0-rc2).

**The prelude is one file**, the repository toolchain's.  It holds
only the pinned basis blocks and the `Bool`/`And` blocks, which have
not changed across the supported toolchains (the nightly's generated
prelude is byte-identical to v4.33.0's below its meta line); a stream
whose copy of a prelude declaration differs declines the run, naming
it, so a toolchain that does change them shows up loudly and would
need the prelude generalised the way the pins were.

### Adding a toolchain's variant

A dump is computed by the generator running ON its toolchain, so it
cannot be regenerated here; the cross-toolchain matrix lane
(`scripts/natop-matrix.sh`, run in CI over every supported toolchain)
is what tells you a new one is needed — its export declines at a
pin-certified operation with "no pin variant matched".  Then, in a
scratch worktree:

1. set `lean-toolchain` to the new toolchain and `lake build
   natop-pins-export` (if the certificate proofs in
   `ConLeche/PinGen/Certs.lean` or the generator's cone rule need a fix
   for the new prelude, make it — it must leave the OTHER dumps
   byte-identical when regenerated on their toolchains, or the
   difference is explained in the commit);
2. `lake exe natop-pins-export _tmp/newpins` and copy the `.json` here
   (the `.prelude.ndjson` it wrote beside it must equal the committed
   prelude below its meta line — `diff <(tail -n +2 a) <(tail -n +2
   b)`; if it does not, stop: that is a prelude drift, see above);
3. add the new file to `#load_natop_pins` in
   `ConLeche/Kernel/NatOpPins.lean` AFTER the existing entries;
4. restore `lean-toolchain`, rebuild, and run the matrix lane: the new
   toolchain's export must now accept, and every older one still.

Dropping a toolchain is the reverse: delete its dump and its
`#load_natop_pins` line.

## Regenerating

    lake exe natop-pins-export

writes `pins/<toolchain>.json` and `pins/<toolchain>.prelude.ndjson`
and prints both paths.  The generator lives in the certificate
library's world (`PinDump.lean`; its root imports
`ConLeche.PinGen.Certs`, so the proof bodies are visible to it and Lake
builds them first).  **Never edit a file here by hand** — regenerate.

## Staleness is a test failure

`tests/pindump.sh`, run from `tests/arena.sh` in the standard battery,
regenerates the CURRENT toolchain's dump and the prelude into a
scratch directory and `diff -q`s them against the committed ones.  A
difference fails the battery, and the only fix is to regenerate and
commit.  The gate also checks that a dump and a prelude exist for the
toolchain in `lean-toolchain`, that `ConLeche/Kernel/NatOpPins.lean`
and `ConLeche/Frontend/Prelude.lean` embed those basenames, that the
dump names the prelude, and that every committed dump is embedded and
every embedded dump committed.  The OTHER toolchains' dumps cannot be
regenerated on this toolchain; the matrix lane exercises them.

The loader accepts dumps from any Lean version (that is the point of
the variants), so a forgotten regeneration after a toolchain bump is
caught by this gate in the standard battery, not at build time.

## Trust does not rest on these files

They are a cache of a computation, not an axiom.  The certificates are
kernel-checked theorems (`ConLeche/PinGen/Certs.lean`, the
`ConLechePinCerts` library, still built by `lake build`); what is stored
here is their proof *terms*, and this checker re-checks those terms at
install time against the hand-pinned certificate statements in
`ConLeche/Kernel/Checker.lean`.  A corrupted or tampered dump therefore
fails its certificate check and the stream **declines** — it cannot
produce a wrong accept.  The prelude is checked by the fold like any
stream: a corrupted prelude is rejected or declined at the head of
every run, never installed unchecked (`tests/ConLecheTests` pins that the
committed one is accepted, at both modes, from the empty environment).
