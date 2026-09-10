# `pins/` — the Nat-operation pin certificates and the built-in prelude

Committed **generated data**: one pin dump per supported Lean
toolchain, and the built-in prelude of the repository's own toolchain:

    pins/leanprover-lean4-v4.33.0.json                        the repository toolchain's dump
    pins/leanprover-lean4-v4.34.0-rc2.json                    further toolchains' dumps ("pin variants")
    pins/leanprover-lean4-nightly-nightly-2026-09-10.json
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
variant accepts v4.29.0 … v4.33.1 exports; v4.34.0-rc2 renamed the
`if_pos`/`dif_pos`/`Nat.div_eq` family the certificate blobs cite and
needs its own; the nightly variant covers lean4 master since the
`Decidable` rewrite).

**The prelude is one file**, the repository toolchain's.  It holds
only the pinned basis blocks and the `Bool`/`And` blocks, which have
not changed across the supported toolchains (the nightly's generated
prelude is byte-identical to v4.33.0's below its meta line); a stream
whose copy of a prelude declaration differs declines the run, naming
it, so a toolchain that does change them shows up loudly and would
need the prelude generalised the way the pins were.

### Adding a toolchain's variant

A dump is computed by the generator running ON its toolchain, so every
committed dump has a **pinner** beside it — a self-contained Lake
project carrying that toolchain (`pinners/<toolchain>/`, see
`pinners/README.md`).  Adding a variant means adding a pinner.

What tells you a new one is needed is the cross-toolchain matrix lane
(`scripts/natop-matrix.sh`, run in CI over every supported toolchain):
its export declines at a pin-certified operation with "no pin variant
matched".  Then:

1. `cp -r pinners/leanprover-lean4-v4.33.0 pinners/<sanitised new
   toolchain>` and put the new toolchain in its `lean-toolchain`.  The
   directory name is the toolchain string with everything outside
   `[A-Za-z0-9._-]` turned into `-` — the same sanitisation the dump's
   filename gets, and the gate checks the two agree.
2. `cd pinners/<new> && lake build`.  If a shared source does not
   compile on that toolchain, fork it into the pinner as
   `pinners/README.md` describes — and if the fix belongs in
   `ConLeche/PinGen/Certs.lean` or the generator's cone rule instead,
   it must leave the OTHER dumps byte-identical when regenerated on
   their toolchains, or the difference is explained in the commit.
3. `lake exe natop-pins-export ../../pins` — from the pinner
   directory; that is what tells the generator which toolchain it is
   dumping.  It writes the new `.json` here, and a
   `.prelude.ndjson` beside it which must equal the committed prelude
   below its meta line (`diff <(tail -n +2 a) <(tail -n +2 b)`).  If it
   does not, stop: that is a prelude drift, see above.  Delete the
   regenerated prelude — only the repository toolchain's is committed.
4. add the new dump to `#load_natop_pins` in
   `ConLeche/Kernel/NatOpPins.lean` AFTER the existing entries;
5. `tests/pindump.sh` (it now reproduces the new dump too), then the
   matrix lane: the new toolchain's export must accept, and every older
   one still.

Commit the dump and its pinner together.  Dropping a toolchain is the
reverse: delete its dump, its pinner and its `#load_natop_pins` line.

## Regenerating

    lake exe natop-pins-export                                  # the repository toolchain's
    cd pinners/<toolchain> && lake exe natop-pins-export ../../pins   # any variant's

writes `pins/<toolchain>.json` and `pins/<toolchain>.prelude.ndjson`
and prints both paths.  Which toolchain it writes for is the Lake
project it is run in: the generator searches upward from the working
directory for `lean-toolchain` exactly as elan does when it picks the
Lean that is running, and refuses to run if that name disagrees with
`Lean.versionString`.  The two commands above are the same sources
built by two projects — `pinners/leanprover-lean4-v4.33.0/` is the
repository toolchain's pinner and produces the identical file.

The generator lives in the certificate library's world (`PinDump.lean`;
its root imports `ConLeche.PinGen.Certs`, so the proof bodies are
visible to it and Lake builds them first).  **Never edit a file here by
hand** — regenerate.

## Staleness is a test failure

`tests/pindump.sh`, run from `tests/arena.sh` in the standard battery,
walks `pinners/*/` and, for each pinner whose toolchain elan has,
builds it, regenerates into a scratch directory and `diff -q`s the
result against the committed dump.  A difference fails the battery, and
the only fix is to regenerate and commit.  A pinner whose toolchain is
not installed is a labelled SKIP; `PINDUMP_INSTALL=1` makes elan
install it first, which is how CI reproduces EVERY dump.  The
repository's own toolchain is always installed, so its pinner always
runs.

The gate also checks that a dump and a prelude exist for the toolchain
in `lean-toolchain`, that `ConLeche/Kernel/NatOpPins.lean` and
`ConLeche/Frontend/Prelude.lean` embed those basenames, that the dump
names the prelude, that every committed dump is embedded and every
embedded dump committed, and that every committed dump has a pinner
named after its own toolchain.  A foreign pinner's regenerated prelude
is checked against the committed one below its meta line — a difference
there is reported as PRELUDE DRIFT.

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
