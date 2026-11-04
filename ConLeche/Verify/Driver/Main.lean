module

public import ConLeche.Driver.Cli

/-!
# `runArgs`, in the model, at the arguments `-- <file>` (task #450)

`runArgs_accept`: on every snapshot `fs`, every outcome of `runArgs
["--", file]` — the argument parse, the request run and the catch of
`IO` errors, all the real logic of `main`, whose exit takes the code
returned here — that is an exit 0 read the file's bytes off the
snapshot, and they parse as one chunk to records `checkDecls .verified`
accepts prepared with the built-in prelude.  No flag: the default mode
is `.verified` (`parseArgs_file`), the worker count the default (the
hardware's, which the statement does not depend on).  At these fixed
arguments nothing is said about `--help` or other flags.

The corollary is in `ConLeche/MainTheorem.lean`.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend

/-- The arguments `-- <file>`: that one file, whatever it is called, and
every setting at its default (the mode `.verified`). -/
theorem parseArgs_file (file : String) : parseArgs ["--", file] {} = { files := #[file] } := by
  simp [parseArgs]

/-- A `--help` after `--` is a file. -/
theorem helpWanted_file (file : String) : helpWanted ["--", file] = false := by
  simp [helpWanted]

/-- **`runArgs`, in the model** (task #450). -/
theorem runArgs_accept {file : String} {fs : FS}
    (h : (runArgs ["--", file] : ModelIO _) fs (.ok 0)) :
    ∃ pre b r env, builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
      parseChunks [b] = .ok r ∧
      Cached.checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env := by
  -- every value outcome `c` of the run: `c = 0` gives the chain
  suffices H : ModelIO.AllOk (runArgs ["--", file]) fs
      (fun c => c = 0 → ∃ pre b r env, builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
        parseChunks [b] = .ok r ∧
        Cached.checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env) from
    H 0 h rfl
  -- the code is the request's, or the handler's 3
  refine ModelIO.allOk_tryCatch ?_ fun _ _ => ?_
  · simp only [helpWanted_file, parseArgs_file]
    exact fun c hc _ => checkMainG_ndjson_accept (by subst_vars; exact hc)
  · simp

end ConLeche.Driver
