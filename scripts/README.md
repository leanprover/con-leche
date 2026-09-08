# `scripts/`

Instruments, not checker code: fixture generators (`mk_*.py`), the
census and slicing tools (`dead-census.*`, `slice-cone.py`,
`stream-census.py`), the perf-table renderer, `selfcheck.sh`, and the
pin-prefix recipe (`extract_natop_prefix.py`,
`diagnose_natop_prefix.py`, `natop_prefix.json`).  Nothing here is on
the build's critical path; each file's header says who consumes it.

## Re-running `shake` (the unused-import minimizer) — task #223

`shake` is no longer a Mathlib program: it was upstreamed into Lake
(`mathlib4#27632`, 2025-07-29) and our toolchain ships it as `lake
shake`, with sources at `$(lean --print-prefix)/src/lean/lake/Lake/CLI/Shake.lean`.
It cannot be used on this tree as shipped — `Lake.Shake.run` throws
`` `lake shake` only works with `module`s currently `` if *any* module
in the closure is a classic (non-`module`) file, and 529 of our 547
`.lean` files are classic — so `scripts/shake-setup.sh` vendors that
one source file into a scratch Lake project under `_tmp/shake-tool/`
(gitignored; **no dependency is ever added to this package's
manifest**) and applies three patches, all of them about classic files:
it drops the guard (a classic file's imports are recorded as
`isExported := true, importAll := false`, i.e. exactly `public import`,
which *is* classic re-export semantics, so the analysis core needs no
change), it teaches `decodeImport` to read a classic `import X` as
exported (upstream keys that off the `public` token, which a classic
header cannot carry, so without it `--fix` silently does nothing), and
it makes the `--fix` writer spell an added import in the file's own
dialect.  Run `scripts/shake-setup.sh`, then, from a fully built
worktree,

    SHAKE_SRC=.:tests LEAN_PATH=.lake/build/lib/lean \
      _tmp/shake-tool/.lake/build/bin/shaketool --keep-implied \
      ConLeche.MainTheorem ConLeche.Verify.Cached ConLeche.Model \
      ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche \
      ConLeche.PinGen.Certs Main

(`PinDump` needs its own run: it and `Main` both define `main`.)  Read
the output against the **noise floor** first: a run with `--only
ConLeche.NoSuchModule` minimizes nothing and still reports ~22 `add`
lines, because a classic file sees a `module` file's *private* imports
too and shake models only the public closure — those adds are false.
A removal is safe when the run with `--only <that module>` reports the
noise floor and nothing more; DESIGN.md task #223 records the two
classes that criterion still misses (a bare `open Namespace`, and two
individually-safe removals that jointly orphan a third module), which
is why the cold build is the arbiter.
