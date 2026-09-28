module

public import ConLeche.Frontend.Prelude
public import ConLeche.Cached.ClassC
public import ConLeche.Cached.ParsedC

@[expose] public section

/-!
# `class-sweep`: the class checker on a stream (TEST DRIVER, not shipped)

`class-sweep [--both] FILE.ndjson` checks a raw export like `con-leche`
at `--verified`, one declaration after the other (no install/check
split, no worker pool), with every recognised inductive block installed
by the CLASS checker (`checkBlockClassKS`) instead of the default route.
Exit codes are the arena's.  `--both` also runs the default route at
every block from the same state and prints a `CLASSDIFF` line where the
two verdicts differ (the class checker's result is the one kept).
-/

open ConLeche ConLeche.Cached

def exitOf : CheckError → UInt32
  | .notImplemented _ => 2
  | .invalid _ => 1
  | .internal _ => 3

/-- The block's route decision, `checkDeclC`'s `.indDecl` arm. -/
def classBlock? (d : Declaration) : Option (List ConstantInfo × BlockParts) :=
  match d with
  | .indDecl block nP =>
    match basisPinHit block with
    | some _ => none
    | none => if indParamsOk nP block then (blockParts? nP block).map (block, ·) else none
  | _ => none

def declName : Declaration → String := declCLabel

def main (args : List String) : IO UInt32 := do
  let (both, file) := match args with
    | ["--both", f] => (true, f)
    | [f] => (false, f)
    | _ => (false, "")
  if file == "" then
    IO.eprintln "usage: class-sweep [--both] FILE.ndjson"
    return 3
  let .ok prelude := Frontend.builtinPreludeE
    | IO.eprintln "class-sweep: the built-in prelude does not parse"; return 3
  match ← Frontend.parseExportStreamD file with
  | .error (e, _) => IO.eprintln s!"class-sweep: parse: {e}"; return exitOf e
  | .ok ⟨parsed⟩ =>
    let ds := (Frontend.prepareD prelude parsed).decls
    let mut fe := mkFEnv Env.empty
    let mut s : CState := {}
    for d in ds do
      let stepNew : CheckCM FEnv := do
        flushC
        match classBlock? d with
        | some (block, p) => checkBlockClassKS .verified fe block p
        | none => checkDeclC .verified natOpPinSets fe d
      let rNew := stepNew.run s
      if both then
        if let some _ := classBlock? d then
          let rOld := (do flushC; checkDeclC .verified natOpPinSets fe d : CheckCM FEnv).run s
          let code : Except CheckError (FEnv × CState) → UInt32 := fun
            | .ok _ => 0
            | .error e => exitOf e
          if code rOld != code rNew then
            let msg : Except CheckError (FEnv × CState) → String := fun
              | .ok _ => "ok"
              | .error e => toString e
            IO.println s!"CLASSDIFF {declName d} old={code rOld} new={code rNew} :: \
              old: {msg rOld} :: new: {msg rNew}"
      match rNew with
      | .ok (fe', s') => fe := fe'; s := s'
      | .error e =>
        IO.eprintln s!"class-sweep: {e} [at {declName d}]"
        return exitOf e
    IO.println s!"class-sweep: accepted {parsed.size} declarations"
    return 0
