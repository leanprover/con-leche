# `scripts/`

Instruments, not checker code: fixture generators (`mk_*.py`), the
census and slicing tools (`dead-census.*`, `slice-cone.py`,
`stream-census.py`), the perf-table renderer, `selfcheck.sh`, and the
pin-prefix recipe (`extract_natop_prefix.py`,
`diagnose_natop_prefix.py`, `natop_prefix.json`) and the pin-drift
probe (`natop-matrix.sh`).  Nothing here is on the build's critical
path; each file's header says who consumes it.

## `natop-matrix.sh` — the pin-drift probe (task #274)

    scripts/natop-matrix.sh v4.33.0
    scripts/natop-matrix.sh leanprover/lean4-nightly:nightly-2026-09-10

Exports the pinned `Nat` operations' and compiler-trust values'
dependency cone WITH THAT TOOLCHAIN'S exporter (the bundled
`leanexport` where the toolchain has one, otherwise a lean4export
built at the matching tag) and checks the result with the con-leche
binary in this tree.  One summary line on stdout, the checker's exit
code passed through.  `.github/workflows/natop-matrix.yml` runs it
over every release since v4.29.0 plus the newest rc and nightly; the
script is the whole of the per-toolchain logic, so a red matrix job
reproduces with one command here.

## Re-running `shake` (the unused-import minimizer) — tasks #223, #235

`shake` is no longer a Mathlib program: it was upstreamed into Lake
(`mathlib4#27632`, 2025-07-29) and our toolchain ships it as `lake
shake`, sources at
`$(lean --print-prefix)/src/lean/lake/Lake/CLI/Shake.lean`.  Task #223
could not use it as shipped — `Lake.Shake.run` throws ``  `lake shake`
only works with `module`s currently `` if *any* module in the closure
is a classic file, and 529 of 547 `.lean` files were classic then — so
`scripts/shake-setup.sh` vendors that one source file into a scratch
Lake project under `_tmp/shake-tool/` (gitignored; **no dependency is
ever added to this package's manifest**) and patches three
classic-file edges out of it.  **Since task #231 every file is a
`module` and the vendoring is unnecessary**: `lake shake` runs on the
tree as it stands.  `shake-setup.sh` is kept as the record of what the
patches were, and would be needed again only if a classic file
re-entered the closure.

The gate that runs the tool is `tests/shake.sh` (in `tests/arena.sh`
and CI); read its header first — it states the criterion, the
allowlist and what `--keep-implied` costs.  By hand, from a fully
built worktree:

    lake shake --keep-implied \
      ConLeche.MainTheorem ConLeche.Verify.Cached ConLeche.Model \
      ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche \
      ConLeche.PinGen.Certs Main

`PinDump.lean` and `tests/ProofDeps.lean` are still classic, so they
cannot be shaken (and `Main` and `PinDump` both define `main`, so they
could not share a run anyway).  Read the output against the **noise
floor** first: a run with `--only ConLeche.NoSuchModule` minimizes
nothing and still reports ~177 `add` lines, almost all of them `Std`
internals a `grind`/`omega` proof term mentions — those adds are false,
the tree builds without them.  A removal is safe when the run with
`--only <that module>` reports the noise floor and nothing more;
DESIGN.md tasks #223 and #235 record the three classes that criterion
still misses (a bare `open Namespace`, two individually-safe removals
that jointly orphan a third module, and a need arising inside an
elaboration-time splice), which is why the cold build is the arbiter.

`--only` is undocumented in `lake shake --help` but real
(`Lake/CLI/Main.lean`).

## The `public` keyword — `scripts/pub-import-plan.py`

Orthogonal to the above: `shake` decides import *lines*, this decides
whether a line needs `public`.  Run it over two dumps taken from the
built oleans (`tests/shake.sh` takes them; `PUBPLAN_DIR` says where):

    lake env lean --run scripts/dead-census.lean <every module> > $D/census.tsv
    lake env lean --run scripts/pub-iface.lean   <every module> > $D/pub.tsv
    PUBPLAN_DIR=$D scripts/pub-import-plan.py            # the plan
    PUBPLAN_DIR=$D scripts/pub-import-plan.py --check    # the gate

`--check` starts from the tree's actual `public` set and fails if any
edge is demotable on its own; the plan mode writes `plan.json` for
`scripts/pub-import-apply.py`.  The script's header has the four
constraints and the two dot-notation fallbacks.
