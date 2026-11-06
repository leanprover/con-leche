module

public import ConLeche.Driver.Cli
public import ConLeche.Verify.Driver.Oleans

/-!
# `runArgs`, in the model

`runArgs_accept`: on every snapshot `fs`, every outcome of `runArgs
["--", file]` — the argument parse, the request run and the catch of
`IO` errors, all the real logic of `main`, whose exit takes the code
returned here — that is an exit 0 read the file's bytes off the
snapshot, and they parse as one chunk to records `checkDecls .verified`
accepts prepared with the built-in prelude.  No flag: the default mode
is `.verified` (`parseArgs_file`), the worker count the default (the
hardware's, which the statement does not depend on).  At these fixed
arguments nothing is said about `--help` or other flags.

`runArgs_olean_accept`: the same at the arguments `--olean --search-path=<dirs> -- <root>`
(`parseArgs_olean`): every outcome that is an exit 0 read records of that root's closure
(`Olean.readOleans`, whose values `Olean.readOleans_ok` unfolds) that `checkDecls .verified`
accepts prepared with the built-in prelude and with the theorems' values in place (`fillOf`,
`Olean.readOleans_filled`).  `runArgs_oleans_accept` is the step at any arguments
that ask for no help, parse without a usage error and ask for `--olean`.

The corollaries are in `ConLeche/MainTheorem.lean`.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend

/-- The arguments `-- <file>`: that one file, whatever it is called, and
every setting at its default (the mode `.verified`). -/
theorem parseArgs_file (file : String) : parseArgs ["--", file] {} = { files := #[file] } := by
  simp [parseArgs]

theorem flagValue_append (pre d : String) : flagValue pre (pre ++ d) = some d := by
  simp [flagValue]

/-- A flag that is no prefix of another's, and no longer, is no prefix of its values. -/
theorem flagValue_other {pre other : String} (d : String)
    (h : pre.toList.isPrefixOf other.toList = false) (hl : pre.toList.length ≤ other.toList.length) :
    flagValue pre (other ++ d) = none := by
  have hn : ¬ pre.toList <+: other.toList := by
    intro hp
    rw [List.isPrefixOf_iff_prefix.mpr hp] at h
    cases h
  have : ¬ pre.toList <+: other.toList ++ d.toList := fun hp =>
    hn (List.prefix_of_prefix_length_le hp (List.prefix_append _ _) hl)
  simp [flagValue, this]

/-- A flag spelled `<other><value>` is not a shorter or different literal. -/
theorem append_ne {other l : String} (d : String) (h : other.toList.isPrefixOf l.toList = false) :
    other ++ d ≠ l := by
  rintro rfl
  rw [String.toList_append, List.isPrefixOf_iff_prefix.mpr (List.prefix_append _ _)] at h
  cases h

/-- `parseArgs` past the literal flags. -/
theorem parseArgs_flag {s : String} (rest : List String) (a : Args) (h1 : s ≠ "--")
    (h2 : s ≠ "--verified") (h3 : s ≠ "--trusted") (h4 : s ≠ "--progress") (h5 : s ≠ "--olean") :
    parseArgs (s :: rest) a =
      if let some v := flagValue "--progress=" s then
        match progressPace v with
        | .ok n => parseArgs rest { a with progress := n }
        | .error msg => { a with bad := some msg }
      else if let some v := flagValue "--jobs=" s then
        match jobsCount v with
        | .ok n => parseArgs rest { a with jobs := some n }
        | .error msg => { a with bad := some msg }
      else if s == "--jobs" then
        { a with bad := some "--jobs takes a worker count: --jobs=<n>; omit the \
            flag for one worker per hardware thread" }
      else if let some v := flagValue "--constant=" s then
        parseArgs rest { a with constants := a.constants.push v }
      else if let some v := flagValue "--search-path=" s then
        parseArgs rest { a with searchPath := a.searchPath ++ searchPathOf v }
      else if s.startsWith "-" then
        { a with bad := some s!"unknown option {Display.str s}" }
      else parseArgs rest { a with files := a.files.push s } := by
  rw [parseArgs.eq_def]
  split <;> first | (rename_i heq; cases heq; rfl) | simp_all

/-- The arguments `--olean --search-path=<dirs> -- <root>`: that one root, those directories,
and every other setting at its default (the mode `.verified`, every constant). -/
theorem parseArgs_olean (dirs root : String) :
    parseArgs ["--olean", "--search-path=" ++ dirs, "--", root] {} =
      { olean := true, searchPath := searchPathOf dirs, files := #[root] } := by
  have hfst : parseArgs ["--olean", "--search-path=" ++ dirs, "--", root] {} =
      parseArgs ["--search-path=" ++ dirs, "--", root] { olean := true } := by
    rw [parseArgs.eq_def]
    rfl
  rw [hfst, parseArgs_flag _ _ (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide)),
    flagValue_other dirs (by decide) (by decide), flagValue_other dirs (by decide) (by decide),
    flagValue_other dirs (by decide) (by decide), flagValue_append]
  have hj : (("--search-path=" ++ dirs) == "--jobs") = false := by
    simp only [beq_eq_false_iff_ne]
    exact append_ne _ (by decide)
  simp only [hj, Bool.false_eq_true, ↓reduceIte]
  simp [parseArgs]

/-- A `--help` after `--` is a file. -/
theorem helpWanted_file (file : String) : helpWanted ["--", file] = false := by
  simp [helpWanted]

/-- **`runArgs` on `--olean` arguments, in the model**: at any arguments
that ask for no help, parse without a usage error and ask for `--olean`,
every outcome that is an exit 0 read records off the snapshot's `.olean`
files of the roots the arguments name, along the search path they name, and
`checkDecls` at the arguments' mode accepts them prepared with the built-in
prelude and with the theorems' values in place. -/
theorem runArgs_oleans_accept {args : List String} {fs : FS} {hs hs' : HS}
    (hh : helpWanted args = false) (hb : (parseArgs args {}).bad = none)
    (ho : (parseArgs args {}).olean = true)
    (h : (runArgs args : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre rd env, builtinPreludeE = .ok pre ∧
      ModelIO.CanGive (Olean.readOleans (parseArgs args {}).searchPath
        ((parseArgs args {}).files.filterMap Olean.parseModName) (parseArgs args {}).rootConstants)
          fs (.ok rd) ∧
      Cached.checkDecls (parseArgs args {}).mode natOpPinSets
        ((prepareD pre rd.decls (usedOf (some ((parseArgs args {}).searchPath, rd)))).decls.map
          (Cached.fillDecl (fillOf (parseArgs args {}).searchPath fs rd.values))) = .ok env := by
  suffices H : ModelIO.AllOk (runArgs args) fs hs
      (fun c => c = 0 → ∃ pre rd env, builtinPreludeE = .ok pre ∧
        ModelIO.CanGive (Olean.readOleans (parseArgs args {}).searchPath
          ((parseArgs args {}).files.filterMap Olean.parseModName) (parseArgs args {}).rootConstants)
          fs (.ok rd) ∧
        Cached.checkDecls (parseArgs args {}).mode natOpPinSets
          ((prepareD pre rd.decls (usedOf (some ((parseArgs args {}).searchPath, rd)))).decls.map
            (Cached.fillDecl (fillOf (parseArgs args {}).searchPath fs rd.values))) = .ok env) from
    H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · simp only [hh, hb, ho, Bool.false_eq_true, ite_false, ite_true]
    intro c _ hc h0
    subst h0
    split at hc
    · simp [eprintln] at hc
    · cases hf : (parseArgs args {}).files.find? (fun f => (Olean.parseModName f).isNone) with
      | some m => simp [hf, eprintln] at hc
      | none =>
        simp only [hf] at hc
        cases hg : (parseArgs args {}).constants.find? (fun c => (Olean.parseConstName c).isNone) with
        | some m => simp [hg, eprintln] at hc
        | none =>
          simp only [hg] at hc
          exact checkMainG_oleans_accept hc
  · simp

/-- The flags of `--olean --search-path=<dirs> -- <root>` ask for no help. -/
theorem helpWanted_olean (dirs root : String) :
    helpWanted ["--olean", "--search-path=" ++ dirs, "--", root] = false := by
  have h1 : "--search-path=" ++ dirs ≠ "--" := append_ne _ (by decide)
  have h2 : "--search-path=" ++ dirs ≠ "--help" := append_ne _ (by decide)
  simp [helpWanted, h1, h2.symm]

/-- **`runArgs` on `--olean --search-path=<dirs> -- <root>`, in the model**: every outcome that
is an exit 0 read records of that root's closure, every constant of it, that `checkDecls
.verified` accepts prepared with the built-in prelude and with the theorems' values in place. -/
theorem runArgs_olean_accept {dirs root : String} {fs : FS} {hs hs' : HS}
    (h : (runArgs ["--olean", "--search-path=" ++ dirs, "--", root] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre rd env, builtinPreludeE = .ok pre ∧
      ModelIO.CanGive (Olean.readOleans (searchPathOf dirs) (#[root].filterMap Olean.parseModName)
        none) fs (.ok rd) ∧
      Cached.checkDecls .verified natOpPinSets
        ((prepareD pre rd.decls (usedOf (some (searchPathOf dirs, rd)))).decls.map
          (Cached.fillDecl (fillOf (searchPathOf dirs) fs rd.values))) = .ok env := by
  have hp := parseArgs_olean dirs root
  obtain ⟨pre, rd, env, h1, h2, h3⟩ := runArgs_oleans_accept (helpWanted_olean dirs root)
    (by rw [hp]) (by rw [hp]) h
  rw [hp] at h2 h3
  exact ⟨pre, rd, env, h1, h2, h3⟩

/-- **`runArgs`, in the model** (task #450). -/
theorem runArgs_accept {file : String} {fs : FS} {hs hs' : HS}
    (h : (runArgs ["--", file] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre b r env, builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
      parseChunks [b] = .ok r ∧
      Cached.checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env := by
  -- every value outcome `c` of the run: `c = 0` gives the chain
  suffices H : ModelIO.AllOk (runArgs ["--", file]) fs hs
      (fun c => c = 0 → ∃ pre b r env, builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
        parseChunks [b] = .ok r ∧
        Cached.checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env) from
    H 0 hs' h rfl
  -- the code is the request's, or the handler's 3
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · simp only [helpWanted_file, parseArgs_file]
    exact fun c hs₁ hc _ =>
      checkMainG_ndjson_accept (hs := hs) (hs' := hs₁) (by subst_vars; exact hc)
  · simp

end ConLeche.Driver
