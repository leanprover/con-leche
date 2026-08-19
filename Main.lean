import Setlec.Kernel.Checker
import Setlec.Frontend.Export

/-!
Command-line driver: `setlec FILE.ndjson` reads a lean4export NDJSON file
(the lean-inductive-models preprocessor will eventually be run transparently
first) and checks the declarations in order.

Exit codes follow the lean kernel arena convention:
* 0 — all declarations accepted
* 1 — a declaration was rejected as invalid
* 2 — the checker declined: it positively detected a feature it does not
  support (yet).  Never used for "something unexpectedly went wrong".
* 3 — bad usage, malformed input, or an internal failure of unclear cause
-/

open Setlec

def Setlec.CheckError.exitCode : CheckError → UInt32
  | .notImplemented _ => 2

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] =>
    let contents ← IO.FS.readFile file
    match Frontend.parseExport contents with
    | .error (.unsupported what) =>
      IO.eprintln s!"setlec: declined: {what}"
      return 2
    | .error (.parseError line msg) =>
      IO.eprintln s!"setlec: {file}:{line}: {msg}"
      return 3
    | .ok decls =>
      match checkDecls decls.toList with
      | .ok env =>
        IO.println s!"setlec: accepted {env.consts.length} declarations"
        return 0
      | .error e =>
        IO.eprintln s!"setlec: {e}"
        return e.exitCode
  | _ =>
    IO.eprintln "usage: setlec FILE.ndjson"
    return 3
