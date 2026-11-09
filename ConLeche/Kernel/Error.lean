module

@[expose] public section

/-!
# The checker's verdict of a failure

A module of its own, importing nothing, so that a reader of untrusted
input (`ConLeche/Frontend/Olean/`) can report the checker's verdicts
without seeing the kernel.
-/

namespace ConLeche

/-- **The verdict of a failure, everywhere in the binary** — the one
error type the whole accept path reports (task #295): the kernel's
steps, the fold, and the frontend's parse and prelude alike.  The
three cases are the three verdicts the driver exits with
(`CheckError.exitCode`, `ConLeche/Driver/Run.lean`): 2 declined, 1 rejected, 3 an
error of unclear cause or a malformed input.

Where a failure has a POSITION the type is `CheckError × Nat`, and the
`Nat` is read in the step's own unit: the input's LINE number in the
frontend (`ConLeche/Frontend/Export.lean`; 0 where no line is meant,
as in the size guard, which refuses the input before reading it) and
the record's position in the list the fold folds
(`ConLeche.Cached.checkDecls`).  The two are in the same type because
the driver chains the steps, and the main corollary states that chain
(`ConLeche/MainTheorem.lean`). -/
inductive CheckError where
  | notImplemented (what : String)
  | invalid (msg : String)
  | internal (msg : String)
  deriving Repr

instance : ToString CheckError where
  toString
    | .notImplemented what => s!"not implemented yet: {what}"
    | .invalid msg => s!"invalid: {msg}"
    | .internal msg => s!"internal error: {msg}"

abbrev CheckM := Except CheckError

end ConLeche
