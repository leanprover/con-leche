module

public import ConLeche.Driver.Cli

/-!
# All of `main`, in the model, at the arguments `-- <file>` (task #450)

`mainG_accept`: on every snapshot `fs`, every outcome of `mainG ["--",
file]` — the argument parse, the abort variables, the request run, the
flush, everything `main` does but the exit, which takes
the code returned here — that is an exit 0 read the file's bytes off
the snapshot, and they parse as one chunk to records `checkDecls
.verified` accepts prepared with the built-in prelude.  No flag: the
default mode is `.verified` (`parseArgs_file`), the worker count the
default (the hardware's, which the statement does not depend on).  At
these fixed arguments nothing is said about `--help` or other flags.

The corollaries over `main` are in `ConLeche/MainTheorem.lean`.
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

/-- **`runArgs` at `-- <file>`**: the stream's request at the default
settings. -/
theorem runArgs_file (file : String) (fs : FS) (P : UInt8 → Prop)
    (h : ∀ jobs, ModelIO.AllOk (runReq (.stream file .verified 0 jobs false)) fs P) :
    ModelIO.AllOk (runArgs ["--", file]) fs P := by
  simp only [runArgs, helpWanted_file, parseArgs_file]
  exact h _

/-- **All of `main` but the exit, in the model** (task #450). -/
theorem mainG_accept {file : String} {fs : FS}
    (h : (mainG ["--", file] : ModelIO _) fs (.ok 0)) :
    ∃ pre b r env, builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
      parseChunks [b] = .ok r ∧
      Cached.checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env := by
  -- every value outcome `c` of the run: `c = 0` gives the chain
  suffices H : ModelIO.AllOk (mainG ["--", file]) fs
      (fun c => c = 0 → ∃ pre b r env, builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
        parseChunks [b] = .ok r ∧
        Cached.checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env) from
    H 0 h rfl
  simp only [mainG, ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_const, ModelIO.allOk_pure]
  intro code hrun _
  revert code
  -- the run: the code is the request's, or a handler's 3
  have hreq := runArgs_file file fs
    (fun c => c = 0 → ∃ pre b r env, builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
      parseChunks [b] = .ok r ∧
      Cached.checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env)
    (fun jobs c hc _ => checkMainG_ndjson_accept (by subst_vars; exact hc))
  refine ModelIO.allOk_tryCatch ?_ fun _ _ => ?_
  · simp only [ModelIO.allOk_bind, ModelIO.liftIO_iff, forall_const]
    refine ModelIO.allOk_tryCatch hreq fun _ _ => ?_
    simp
  · simp [eprintln]

end ConLeche.Driver
