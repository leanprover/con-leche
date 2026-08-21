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
  | .invalid _ => 1
  | .internal _ => 3

/-- Locate the lean-inductive-models preprocessor: `$SETLEC_INDUCTIVE_MODELS`,
then `$PATH`, then the development checkout under `_tmp/`. -/
def findPreprocessor : IO (Option String) := do
  if let some p ← IO.getEnv "SETLEC_INDUCTIVE_MODELS" then
    return some p
  let dev := "_tmp/lean-inductive-models/.lake/build/bin/lean-inductive-models"
  if ← System.FilePath.pathExists dev then
    return some dev
  -- fall back to PATH resolution by just trying the bare name at spawn time
  return some "lean-inductive-models"

/-- Run the preprocessor over the input, reducing inductives to the
modelled basis.  On any failure to run it, fall back to the raw input
(the checker then declines at the first inductive). -/
def preprocess (file : String) (contents : String) : IO String := do
  unless ((contents.splitOn "\"inductive\"").length > 1 ||
      (contents.splitOn "\"quot\"").length > 1) do
    return contents
  let some tool ← findPreprocessor | return contents
  try
    let out ← IO.Process.output { cmd := tool, args := #["--quiet", "-o", "-", file] }
    if out.exitCode = 0 then
      return out.stdout
    else
      IO.eprintln s!"setlec: preprocessor exited {out.exitCode}; using raw input"
      return contents
  catch _ =>
    return contents

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] =>
    let contents ← preprocess file (← IO.FS.readFile file)
    match Frontend.parseExport contents (modeled := true) with
    | .error (.unsupported what) =>
      IO.eprintln s!"setlec: declined: {what}"
      return 2
    | .error (.parseError line msg) =>
      IO.eprintln s!"setlec: {file}:{line}: {msg}"
      return 3
    | .ok decls =>
      match checkDecls cachedOps decls.toList with
      | .ok env =>
        IO.println s!"setlec: accepted {env.consts.length} declarations"
        return 0
      | .error e =>
        -- Diagnostic second pass: the verdict above is the verified
        -- `checkDecls` run; this only locates the failing declaration
        -- for the message.
        let declName : Setlec.Declaration → String := fun d =>
          match d with
          | .defnDecl cv _ => s!"def {cv.name}"
          | .thmDecl cv _ => s!"theorem {cv.name}"
          | .opaqueDecl cv _ => s!"opaque {cv.name}"
          | .axiomDecl cv => s!"axiom {cv.name}"
          | .indDecl b => s!"inductive {(b.head?.map (·.name)).getD .anonymous}"
          | .basisDecl k => s!"basis block {repr k}"
        let ctx := Id.run do
          let mut env := Setlec.Env.empty
          for d in decls do
            match checkDecl cachedOps env d with
            | .ok env' => env := env'
            | .error _ => return s!" [at {declName d}]"
          return ""
        IO.eprintln s!"setlec: {e}{ctx}"
        return e.exitCode
  | _ =>
    IO.eprintln "usage: setlec FILE.ndjson"
    return 3
