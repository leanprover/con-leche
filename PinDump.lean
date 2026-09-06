import Setlec.PinGen
import Setlec.PinGen.Certs

/-!
# `natop-pins-export` — the pin dump generator (task #176)

Writes the pinned `Nat`-operation declarations and their certificate
proof blobs to `<outdir>/<toolchain>.json` and prints the path.  The
default `<outdir>` is `Setlec/Kernel/NatOpPins`, where the dump is
COMMITTED; `tests/pindump.sh` regenerates into a scratch directory and
`diff -q`s, so a stale dump fails the battery.

    lake exe natop-pins-export                 # regenerate in place
    lake exe natop-pins-export _tmp/scratch    # for the freshness gate

`import Setlec.PinGen.Certs` above is the *build-order edge* the old
mechanism lacked: the certificate theorems are read out of their olean
at run time (`importModules` at `OLeanLevel.private`, so the proof
bodies are visible), and this import is what makes Lake build that
olean first.  Nothing in the checker's own build depends on it any
more.
-/

open Setlec.PinGen

def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let outDir : System.FilePath :=
    match args with
    | [] => "Setlec" / "Kernel" / "NatOpPins"
    | [d] => d
    | _ => "Setlec" / "Kernel" / "NatOpPins"
  if args.length > 1 then
    IO.eprintln "usage: natop-pins-export [output-directory]"
    return 1
  let dump ← computeDump
  IO.FS.createDirAll outDir
  let path := outDir / toolchainFileName dump.toolchain
  IO.FS.withFile path .write fun h => do
    for line in dumpLines dump do
      h.putStrLn line
  IO.println path
  return 0
