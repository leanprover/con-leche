import ConLeche.PinGen
import ConLeche.PinGen.Prelude
import ConLeche.PinGen.Certs

/- NOT a `module` (task #231): `main` here drives `ConLeche/PinGen/*`, which
is `meta` code (a `public meta section` there).  A `module` root cannot call
it from a non-`meta` definition, and making the root `meta` instead produced
an executable that segfaults on start — so this generator root stays
classic, which may import `module`s and may call their `meta` code. -/
/-!
# `natop-pins-export` — the pin dump generator (task #176)

Writes the pinned `Nat`-operation declarations and their certificate
proof blobs to `<outdir>/<toolchain>.json`, and — since task #191 —
the **built-in prelude** the pins' order-sensitive ground needs to
`<outdir>/<toolchain>.prelude.ndjson` beside it (a lean4export-format
stream the checker's frontend embeds and prepends to every input; see
`ConLeche/PinGen/Prelude.lean`).  Prints both paths.  The default
`<outdir>` is the repository's top-level `pins/`, where the dump is
COMMITTED (see `pins/README.md`); `tests/pindump.sh` regenerates into
a scratch directory and `diff -q`s both files, so a stale dump fails
the battery.

    lake exe natop-pins-export                 # regenerate in place
    lake exe natop-pins-export _tmp/scratch    # for the freshness gate

`import ConLeche.PinGen.Certs` above is the *build-order edge* the old
mechanism lacked: the certificate theorems are read out of their olean
at run time (`importModules` at `OLeanLevel.private`, so the proof
bodies are visible), and this import is what makes Lake build that
olean first.  Nothing in the checker's own build depends on it any
more.
-/

open ConLeche.PinGen

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let outDir : System.FilePath :=
    match args with
    | [] => "pins"
    | [d] => d
    | _ => "pins"
  if args.length > 1 then
    IO.eprintln "usage: natop-pins-export [output-directory]"
    return 1
  let (dump, prelude) ← computeDumpAndPrelude
  IO.FS.createDirAll outDir
  let path := outDir / toolchainFileName dump.toolchain
  IO.FS.withFile path .write fun h => do
    for line in dumpLines dump do
      h.putStrLn line
  let ppath := outDir / dump.preludeFile
  IO.FS.withFile ppath .write fun h => do
    for line in prelude do
      h.putStrLn line
  IO.println path
  IO.println ppath
  return 0
