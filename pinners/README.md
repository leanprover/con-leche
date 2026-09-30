# `pinners/` — one Lake project per committed pin dump

A pin dump (`pins/<toolchain>.json`, see `pins/README.md`) records one
toolchain's own definitions of the pin-certified `Nat` operations, and
it is computed by the generator **running on that toolchain**.  The
repository has one `lean-toolchain`, so until task #275 only the
repository toolchain's dump could be regenerated here and the others
were committed files with no recipe behind them.

A **pinner** is that recipe: a Lake project whose `lean-toolchain` is
the dump's toolchain.

    pinners/leanprover-lean4-v4.33.0/                    lean-toolchain, lakefile.toml
    pinners/leanprover-lean4-v4.34.0-rc2/                lean-toolchain, lakefile.toml
    pinners/leanprover-lean4-nightly-nightly-2026-09-10/ lean-toolchain, lakefile.toml

The directory name is the dump's basename without `.json` — the
toolchain string with everything outside `[A-Za-z0-9._-]` turned into
`-`, the generator's own sanitisation.  `tests/pindump.sh` checks that
correspondence in both directions: a dump without a pinner and a pinner
without a dump are both failures.

## Regenerating a dump

    cd pinners/<toolchain> && lake exe natop-pins-export ../../pins

elan reads the `lean-toolchain` beside the lakefile, so `lake` here
runs the Lean the dump is a dump of; the generator reads the same file
(searching upward from the working directory, as elan does) to label
and name its output, and refuses to run if that name disagrees with
`Lean.versionString`.  It writes `<toolchain>.json` and
`<toolchain>.prelude.ndjson` and prints both paths.

Only the repository toolchain's `.prelude.ndjson` is committed: the
prelude holds the pinned basis blocks and `Bool`/`And`, which have not
drifted across the supported toolchains.  A foreign pinner's regenerated
prelude must match the committed one below its meta line, and the gate
checks it.

## What is shared, and why it can be

Nothing is copied.  Both of a pinner's Lake targets take their sources
from the repository root with `srcDir = "../.."`, so the tree holds
exactly ONE generator — the one the repository's own
`lake exe natop-pins-export` builds.  The cone a pinner compiles is

    PinDump                                the executable root
    ConLeche.PinGen, .Dump, .Prelude       the generator
    ConLeche.PinGen.Certs                  the certificate theorems
    ConLeche.Kernel.{Name,PropWhen,Expr}   the checker's Expr datatypes

The last line is why the generator is not free-standing: a dump is an
encoding of `ConLeche.Expr`, and the splice back into
`ConLeche/Kernel/NatOpPins.lean` names that type's constructors.  So a
pinner does build three checker modules — the three that define the
term representation, none of the checking.

Those eight modules must therefore be written in the subset every
supported toolchain accepts.  That is not a hope: it is what the cold
build in `tests/pindump.sh` and in CI checks, on every toolchain, every
time.  A cold pinner build is eighteen jobs and a few seconds.

**If a toolchain cannot share a file**, fork it — but note how, because
the obvious way silently does nothing.  Lake resolves a module through
the first library whose ROOTS COVER it, and putting a `srcDir = "."`
library FIRST does not shadow a later library that also covers the
module: the shared copy still wins and the fork is dead code (measured,
task #275).  A fork is therefore a narrowing:

1. replace the shared library's `roots = ["ConLeche"]` with the
   explicit cone above, minus the module being forked;
2. add a `lean_lib` with `srcDir = "."` whose root is that module;
3. put the fixed copy in the pinner's own directory under its module
   path (say `ConLeche/PinGen/Certs.lean`), and say at its top why it
   is forked and how it differs.

No fork exists today — v4.34.0-rc2 and the nightly build the shared
sources with deprecation warnings only, and produce byte-identical
dumps.

## Adding or dropping a toolchain

The recipe is in `pins/README.md` ("Adding a toolchain's variant"):
copy a pinner directory, set its `lean-toolchain`, fork what breaks,
regenerate into `pins/`, add the new dump to `#load_natop_pins` in
`ConLeche/Kernel/NatOpPins.lean`, and commit dump and pinner together.
Dropping one is the reverse.
