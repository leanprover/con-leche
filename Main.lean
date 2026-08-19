import Setlec

/-!
Command-line driver.  Eventually this will read declarations (lean4export
format, after running the lean-inductive-models preprocessor) and feed them
to `Setlec.checkDecls`.  For now it only reports the checker's state.
-/

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println "setlec: verified Lean checker (nothing implemented yet)"
    return 0
  | _ =>
    IO.eprintln "setlec: input processing not implemented yet"
    return 1
