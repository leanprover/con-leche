# `pins/` — the Nat-operation pin certificates and the built-in prelude

Committed **generated data**, two files per Lean toolchain:

    pins/leanprover-lean4-v4.33.0.json
    pins/leanprover-lean4-v4.33.0.prelude.ndjson

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
  theorems in `Lech/PinGen/Certs.lean` — kernel-checked Lean
  theorems, elaborated against the real toolchain prelude and made
  self-contained (closed over each operation's own dependency cone, so
  they check against dependency-sliced streams too).

The encoding is described in `Lech/PinGen/Dump.lean`: JSON, and what
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
`Lech/Frontend/NatOpGround.lean`).

## The built-in prelude (`<toolchain>.prelude.ndjson`)

A **lean4export-format stream** — the six pinned basis blocks (`Eq`,
`Nat`, `PUnit`, `Empty`, `False`, `Quot` with `Quot.sound`) and the
toolchain's `Bool` block, exactly as the toolchain declares them,
serialised by `Lech/PinGen/Prelude.lean` (a port of lean4export's
writer).  `Lech/Frontend/Prelude.lean` embeds it with `include_str`,
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
operation (see `Lech/PinGen/Prelude.lean` and DESIGN.md, task #191).

## One file pair per toolchain

The names are the `lean-toolchain` string with everything outside
`[A-Za-z0-9._-]` turned into `-`.  A pin computed from one toolchain
describes only that toolchain, so supporting a second means storing
both pairs, side by side in this directory.

`Lech/Kernel/NatOpPins.lean` embeds exactly one dump with
`include_str` (paths there resolve relative to that source file's
directory, hence `"../../pins/…"`) and splices it at elaboration time;
`Lech/Frontend/Prelude.lean` embeds the matching prelude the same
way.  A toolchain bump means: regenerate, add the new files here, and
re-point both `include_str`s.

## Regenerating

    lake exe natop-pins-export

writes `pins/<toolchain>.json` and `pins/<toolchain>.prelude.ndjson`
and prints both paths.  The generator lives in the certificate
library's world (`PinDump.lean`; its root imports
`Lech.PinGen.Certs`, so the proof bodies are visible to it and Lake
builds them first).  **Never edit a file here by hand** — regenerate.

## Staleness is a test failure

`tests/pindump.sh`, run from `tests/arena.sh` in the standard battery,
regenerates into a scratch directory and `diff -q`s both files against
the committed ones.  A difference fails the battery, and the only fix
is to regenerate and commit.  The gate also checks that a dump and a
prelude exist for the toolchain in `lean-toolchain`, that
`Lech/Kernel/NatOpPins.lean` and `Lech/Frontend/Prelude.lean` embed
those same basenames, and that the dump names the prelude.

Independently, the loader **refuses a dump generated by a different
Lean version** — a forgotten regeneration after a toolchain bump is a
build error naming the fix, never a silently wrong pin.

## Trust does not rest on these files

They are a cache of a computation, not an axiom.  The certificates are
kernel-checked theorems (`Lech/PinGen/Certs.lean`, the
`LechPinCerts` library, still built by `lake build`); what is stored
here is their proof *terms*, and this checker re-checks those terms at
install time against the hand-pinned certificate statements in
`Lech/Kernel/Checker.lean`.  A corrupted or tampered dump therefore
fails its certificate check and the stream **declines** — it cannot
produce a wrong accept.  The prelude is checked by the fold like any
stream: a corrupted prelude is rejected or declined at the head of
every run, never installed unchecked (`tests/LechTests` pins that the
committed one is accepted, at both modes, from the empty environment).
