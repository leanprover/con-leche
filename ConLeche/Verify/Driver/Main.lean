module

public import ConLeche.Driver.Cli
public import ConLeche.Verify.Driver.Worker
import ConLeche.Verify.Driver.Modular
import ConLeche.Verify.Driver.Graph
public import ConLeche.Verify.Driver.CompareRun

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
(`Olean.readOleansAt`, whose values `Olean.readOleansAt_ok` unfolds) that `checkDecls .verified`
accepts prepared with the built-in prelude and with the theorems' values in place (`fillOf`,
`Olean.readOleansAt_filled`).  `runArgs_oleans_accept` is the step at any arguments
that ask for no help, parse without a usage error and ask for `--olean` without `--module`.

The corollaries are in `ConLeche/MainTheorem.lean`.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend

/-- The arguments `-- <file>`: that one file, whatever it is called, and
every setting at its default (the mode `.verified`). -/
theorem parseArgs_file (file : String) : parseArgs ["--", file] {} = { files := #[file] } := by
  simp [parseArgs, Args.closed]

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
    (h2 : s ≠ "--verified") (h3 : s ≠ "--trusted") (h4 : s ≠ "--progress") (h5 : s ≠ "--olean")
    (h6 : s ≠ "--check-graph") (h7 : s ≠ "--module") (h8 : s ≠ "--modular")
    (h9 : s ≠ "--compare") :
    parseArgs (s :: rest) a =
      if let some v := flagValue "--progress=" s then
        match progressPace v with
        | .ok n => parseArgs rest { a with progress := n }
        | .error msg => { a with bad := some msg }
      else if let some v := flagValue "--jobs=" s then
        match jobsCount v with
        | .ok n => parseArgs rest { a with jobs := some n }
        | .error msg => { a with bad := some msg }
      else if let some v := flagValue "--max-nat-size=" s then
        match maxNatSizeArg v with
        | .ok n => parseArgs rest { a with maxNatSize := n }
        | .error msg => { a with bad := some msg }
      else if s == "--jobs" then
        { a with bad := some "--jobs takes a worker count: --jobs=<n>; omit the \
            flag for one worker per hardware thread" }
      else if let some v := flagValue "--constant=" s then
        parseArgs rest { a with constants := a.constants.push v }
      else if let some v := flagValue "--search-path=" s then
        parseArgs rest { a with searchPath := a.searchPath ++ searchPathOf v }
      else if let some v := flagValue "--trusted-search-path=" s then
        parseArgs rest { a with trustedPath := a.trustedPath ++ searchPathOf v }
      else if let some v := flagValue "--schedule" s then
        parseArgs rest { a with schedule := a.schedule.push v, scheduled := true }
      else if let some v := flagValue "--worker-stack-size=" s then
        match Schedule.parseSize v with
        | some (n + 1) => parseArgs rest { a with workerStack := some (n + 1) }
        | _ => { a with bad := some s!"--worker-stack-size takes a size with a unit, K, M, G or T \
            (e.g. 8G), got {Display.str v}" }
      else if s.startsWith "-" then
        { a with bad := some s!"unknown option {Display.str s}" }
      else parseArgs rest { a with files := a.files.push s } := by
  rw [parseArgs.eq_def]
  split <;> first | (rename_i heq; cases heq; rfl) | simp_all

/-- `--max-nat-size=` is longer than `--search-path=`, and no prefix of its values. -/
theorem flagValue_natMax_searchPath (dirs : String) :
    flagValue "--max-nat-size=" ("--search-path=" ++ dirs) = none := by
  simp [flagValue, String.toList_append]

/-- **The two lookup flags** `--trusted-search-path=<T> --search-path=<D>` (task #608): each
directory list appended. -/
theorem parseArgs_paths (T D : String) (rest : List String) (a : Args) :
    parseArgs (("--trusted-search-path=" ++ T) :: ("--search-path=" ++ D) :: rest) a =
      parseArgs rest
        { a with trustedPath := a.trustedPath ++ searchPathOf T,
                 searchPath := a.searchPath ++ searchPathOf D } := by
  rw [parseArgs_flag _ _ (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)),
    flagValue_other T (by decide) (by decide), flagValue_other T (by decide) (by decide),
    flagValue_other T (by decide) (by decide)]
  have hj : (("--trusted-search-path=" ++ T) == "--jobs") = false := by
    simp only [beq_eq_false_iff_ne]
    exact append_ne _ (by decide)
  simp only [hj, Bool.false_eq_true, ↓reduceIte]
  rw [flagValue_other T (by decide) (by decide), flagValue_other T (by decide) (by decide),
    flagValue_append]
  simp only
  rw [parseArgs_flag _ _ (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)),
    flagValue_other D (by decide) (by decide), flagValue_other D (by decide) (by decide),
    flagValue_natMax_searchPath, flagValue_other D (by decide) (by decide),
    flagValue_append]
  have hj' : (("--search-path=" ++ D) == "--jobs") = false := by
    simp only [beq_eq_false_iff_ne]
    exact append_ne _ (by decide)
  simp only [hj', Bool.false_eq_true, ↓reduceIte]

/-- Flags spelled `--trusted-search-path=<T>` and `--search-path=<D>` end no option list and ask
for no help. -/
theorem paths_ne (T D : String) : "--search-path=" ++ D ≠ "--" ∧ "--search-path=" ++ D ≠ "--help" ∧
    "--trusted-search-path=" ++ T ≠ "--" ∧ "--trusted-search-path=" ++ T ≠ "--help" :=
  ⟨append_ne _ (by decide), append_ne _ (by decide), append_ne _ (by decide),
    append_ne _ (by decide)⟩

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
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)),
    flagValue_other dirs (by decide) (by decide), flagValue_other dirs (by decide) (by decide),
    flagValue_natMax_searchPath, flagValue_other dirs (by decide) (by decide),
    flagValue_append]
  have hj : (("--search-path=" ++ dirs) == "--jobs") = false := by
    simp only [beq_eq_false_iff_ne]
    exact append_ne _ (by decide)
  simp only [hj, Bool.false_eq_true, ↓reduceIte]
  simp [parseArgs, Args.closed]

/-- A `--help` after `--` is a file. -/
theorem helpWanted_file (file : String) : helpWanted ["--", file] = false := by
  simp [helpWanted]

/-- **`runArgs` on `--olean` arguments, in the model**: at any arguments
that ask for no help, parse without a usage error and ask for `--olean` (not `--module`),
every outcome that is an exit 0 read records off the snapshot's `.olean`
files of the roots the arguments name, along the search path they name, and
`checkDecls` at the arguments' mode accepts them prepared with the built-in
prelude and with the theorems' values in place. -/
theorem runArgs_oleans_accept {args : List String} {fs : FS} {hs hs' : HS}
    (hh : helpWanted args = false) (hb : (parseArgs args {}).bad = none)
    (ho : (parseArgs args {}).olean = true) (hcg : (parseArgs args {}).checkGraph = false)
    (hm : (parseArgs args {}).module = false) (hmd : (parseArgs args {}).modular = false)
    (hsc : (parseArgs args {}).scheduled = false) (hcmp : (parseArgs args {}).compare = false)
    (htp : (parseArgs args {}).trustedPath = [])
    (h : (runArgs args : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre rd env, builtinPreludeE = .ok pre ∧
      ModelIO.CanGive (Olean.readOleansAt (parseArgs args {}).searchPath
        ((parseArgs args {}).files.filterMap Olean.parseModName) (parseArgs args {}).rootConstants)
          fs (.ok rd) ∧
      Cached.checkDecls (parseArgs args {}).mode natOpPinSets (parseArgs args {}).maxNatSize
        ((prepareD pre rd.decls (usedOf (some ((parseArgs args {}).searchPath, rd)))).decls.map
          (Cached.fillDecl (fillOf (parseArgs args {}).searchPath fs rd.values))) = .ok env := by
  suffices H : ModelIO.AllOk (runArgs args) fs hs
      (fun c => c = 0 → ∃ pre rd env, builtinPreludeE = .ok pre ∧
        ModelIO.CanGive (Olean.readOleansAt (parseArgs args {}).searchPath
          ((parseArgs args {}).files.filterMap Olean.parseModName) (parseArgs args {}).rootConstants)
          fs (.ok rd) ∧
        Cached.checkDecls (parseArgs args {}).mode natOpPinSets (parseArgs args {}).maxNatSize
          ((prepareD pre rd.decls (usedOf (some ((parseArgs args {}).searchPath, rd)))).decls.map
            (Cached.fillDecl (fillOf (parseArgs args {}).searchPath fs rd.values))) = .ok env) from
    H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · simp only [hh, hb, ho, hcg, hm, hmd, hsc, hcmp, htp, List.isEmpty_nil, Bool.and_true,
      Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
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
      ModelIO.CanGive (Olean.readOleansAt (searchPathOf dirs) (#[root].filterMap Olean.parseModName)
        none) fs (.ok rd) ∧
      Cached.checkDecls .verified natOpPinSets Cached.maxNatSizeDefault
        ((prepareD pre rd.decls (usedOf (some (searchPathOf dirs, rd)))).decls.map
          (Cached.fillDecl (fillOf (searchPathOf dirs) fs rd.values))) = .ok env := by
  have hp := parseArgs_olean dirs root
  obtain ⟨pre, rd, env, h1, h2, h3⟩ := runArgs_oleans_accept (helpWanted_olean dirs root)
    (by rw [hp]) (by rw [hp]) (by rw [hp]) (by rw [hp]) (by rw [hp]) (by rw [hp]) (by rw [hp])
    (by rw [hp]) h
  rw [hp] at h2 h3
  exact ⟨pre, rd, env, h1, h2, h3⟩

/-- The arguments `--check-graph --search-path=<dirs> -- <root>`: that one root, those
directories, and every other setting at its default. -/
theorem parseArgs_graph (dirs root : String) :
    parseArgs ["--check-graph", "--search-path=" ++ dirs, "--", root] {} =
      { checkGraph := true, searchPath := searchPathOf dirs, files := #[root] } := by
  have hfst : parseArgs ["--check-graph", "--search-path=" ++ dirs, "--", root] {} =
      parseArgs ["--search-path=" ++ dirs, "--", root] { checkGraph := true } := by
    rw [parseArgs.eq_def]
    rfl
  rw [hfst, parseArgs_flag _ _ (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)),
    flagValue_other dirs (by decide) (by decide), flagValue_other dirs (by decide) (by decide),
    flagValue_natMax_searchPath, flagValue_other dirs (by decide) (by decide),
    flagValue_append]
  have hj : (("--search-path=" ++ dirs) == "--jobs") = false := by
    simp only [beq_eq_false_iff_ne]
    exact append_ne _ (by decide)
  simp only [hj, Bool.false_eq_true, ↓reduceIte]
  simp [parseArgs, Args.closed]

/-- The flags of `--check-graph --search-path=<dirs> -- <root>` ask for no help. -/
theorem helpWanted_graph (dirs root : String) :
    helpWanted ["--check-graph", "--search-path=" ++ dirs, "--", root] = false := by
  have h1 : "--search-path=" ++ dirs ≠ "--" := append_ne _ (by decide)
  have h2 : "--search-path=" ++ dirs ≠ "--help" := append_ne _ (by decide)
  simp [helpWanted, h1, h2.symm]

/-- **An exit 0 of a compared run's graph check** is one of the graph check of both closures
through the solution's lookup, the solution added to the challenge's header. -/
theorem checkGraphCmpG_accept {r : CmpReq} {jobs : Nat} {fs : FS}
    (h : ModelIO.CanGive (checkGraphCmpG r jobs) fs 0) :
    ModelIO.CanGive (Graph.checkGraphG r.solRoots [r.challenge] jobs
      (Graph.cmpExtra r.challenge r.solution)) fs 0 := by
  obtain ⟨hs, hs', h⟩ := h
  simp only [checkGraphCmpG, ModelIO.bind_ok] at h
  obtain ⟨x, hs₁, -, h⟩ := h
  rcases x with _ | e
  · exact ⟨_, _, h⟩
  · simp only [diagLine, ModelIO.bind_ok, ModelIO.liftIO_iff, ModelIO.pure_iff,
      Except.ok.injEq] at h
    obtain ⟨_, _, -, h, -⟩ := h
    exact absurd h.symm (CheckError.exitCode_ne_zero _)

/-- **`runArgs` on `--check-graph --search-path=<dirs> -- <root>`, in the model** (task #467):
every outcome that is an exit 0 is an exit 0 of the graph check of that root's closure, at some
worker count (`Graph.checkGraphG_ok` says what that means). -/
theorem runArgs_graph_accept {dirs root : String} {r : Name} {fs : FS} {hs hs' : HS}
    (hr : Frontend.Olean.parseModName root = some r)
    (h : (runArgs ["--check-graph", "--search-path=" ++ dirs, "--", root] : ModelIO _) fs hs
      (.ok 0) hs') :
    ∃ jobs, ModelIO.CanGive (Graph.checkGraphG (searchPathOf dirs) [r] jobs) fs 0 := by
  suffices H : ModelIO.AllOk (runArgs ["--check-graph", "--search-path=" ++ dirs, "--", root]) fs
      hs (fun c => c = 0 → ∃ jobs, ModelIO.CanGive (Graph.checkGraphG (searchPathOf dirs) [r] jobs)
        fs 0) from H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · simp only [helpWanted_graph, parseArgs_graph, Bool.false_eq_true, ite_false, ite_true]
    intro c _ hc h0
    subst h0
    have hf : (#[root].find? fun f => (Frontend.Olean.parseModName f).isNone) = none := by
      simp [hr]
    simp only [hf] at hc
    have hm : (#[root].filterMap Frontend.Olean.parseModName).toList = [r] := by simp [hr]
    simp only [hm, Bool.or_false, List.isEmpty_nil, Array.isEmpty_empty,
      Bool.not_true, Bool.and_true, runReq] at hc
    split at hc
    · simp [eprintln] at hc
    cases hE : (searchPathOf dirs).isEmpty
    · have h1 : (#[root] : Array String).isEmpty = false := rfl
      simp only [hE, h1, Bool.or_false, Bool.false_eq_true, ↓reduceIte] at hc
      exact ⟨_, _, _, hc⟩
    · simp [hE, eprintln] at hc
  · simp

/-- **`runArgs`, in the model** (task #450). -/
theorem runArgs_accept {file : String} {fs : FS} {hs hs' : HS}
    (h : (runArgs ["--", file] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ pre b r env, builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
      parseChunks [b] = .ok r ∧
      Cached.checkDecls .verified natOpPinSets Cached.maxNatSizeDefault (preparePrelude pre r.decls) = .ok env := by
  -- every value outcome `c` of the run: `c = 0` gives the chain
  suffices H : ModelIO.AllOk (runArgs ["--", file]) fs hs
      (fun c => c = 0 → ∃ pre b r env, builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
        parseChunks [b] = .ok r ∧
        Cached.checkDecls .verified natOpPinSets Cached.maxNatSizeDefault (preparePrelude pre r.decls) = .ok env) from
    H 0 hs' h rfl
  -- the code is the request's, or the handler's 3
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · simp only [helpWanted_file, parseArgs_file]
    exact fun c hs₁ hc _ =>
      checkMainG_ndjson_accept (hs := hs) (hs' := hs₁) (by subst_vars; exact hc)
  · simp

/-- The arguments `--olean --module --search-path=<dirs> -- <root>`: that one module, those
directories, every other setting at its default (the mode `.verified`). -/
theorem parseArgs_module (dirs root : String) :
    parseArgs ["--olean", "--module", "--search-path=" ++ dirs, "--", root] {} =
      { olean := true, module := true, searchPath := searchPathOf dirs, files := #[root] } := by
  have hfst : parseArgs ["--olean", "--module", "--search-path=" ++ dirs, "--", root] {} =
      parseArgs ["--search-path=" ++ dirs, "--", root] { olean := true, module := true } := by
    rw [parseArgs.eq_def]
    rfl
  rw [hfst, parseArgs_flag _ _ (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)),
    flagValue_other dirs (by decide) (by decide), flagValue_other dirs (by decide) (by decide),
    flagValue_natMax_searchPath, flagValue_other dirs (by decide) (by decide),
    flagValue_append]
  have hj : (("--search-path=" ++ dirs) == "--jobs") = false := by
    simp only [beq_eq_false_iff_ne]
    exact append_ne _ (by decide)
  simp only [hj, Bool.false_eq_true, ↓reduceIte]
  simp [parseArgs, Args.closed]

/-- The flags of `--olean --module --search-path=<dirs> -- <root>` ask for no help. -/
theorem helpWanted_module (dirs root : String) :
    helpWanted ["--olean", "--module", "--search-path=" ++ dirs, "--", root] = false := by
  have h1 : "--search-path=" ++ dirs ≠ "--" := append_ne _ (by decide)
  have h2 : "--search-path=" ++ dirs ≠ "--help" := append_ne _ (by decide)
  simp [helpWanted, h1, h2.symm]

/-- **`runArgs` on `--olean --module --search-path=<dirs> -- <root>`, in the model**: every
outcome that is an exit 0 names a module `m` and is an accepted worker at `m`
(`WorkerAccepted`, `ConLeche/Verify/Driver/Worker.lean`) at the mode `.verified`, on that
search path, at some worker count. -/
theorem runArgs_module_accept {dirs root : String} {fs : FS} {hs hs' : HS}
    (h : (runArgs ["--olean", "--module", "--search-path=" ++ dirs, "--", root] : ModelIO _) fs hs
      (.ok 0) hs') :
    ∃ m jobs, Olean.parseModName root = some m ∧
      WorkerAccepted .verified Cached.maxNatSizeDefault (searchPathOf dirs) fs m jobs := by
  suffices H : ModelIO.AllOk (runArgs ["--olean", "--module", "--search-path=" ++ dirs, "--", root])
      fs hs (fun c => c = 0 → ∃ m jobs, Olean.parseModName root = some m ∧
        WorkerAccepted .verified Cached.maxNatSizeDefault (searchPathOf dirs) fs m jobs) from H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · simp only [helpWanted_module, parseArgs_module, List.isEmpty_nil, Bool.and_true,
      Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    intro c _ hc h0
    subst h0
    split at hc
    · simp [eprintln] at hc
    · cases hf : (#[root] : Array String).find? (fun f => (Olean.parseModName f).isNone) with
      | some m => simp [hf, eprintln] at hc
      | none =>
        simp only [hf] at hc
        cases hr : Olean.parseModName root with
        | none => simp [hr] at hf
        | some m =>
          simp only [Array.find?_empty, List.filterMap_cons, hr, List.filterMap_nil,
            Array.isEmpty_empty] at hc
          simp only [runReq] at hc
          rcases hc with ⟨⟨R, T⟩, _, hT, hc⟩ | ⟨e, he, -⟩
          · obtain ⟨hR, hp, hT⟩ := workerTables_ok (CmpReq.solRoots_bare _) hT
            exact ⟨m, _, rfl, checkModuleG_accept (modTables_within hR hp hT) hR hp hc⟩
          · cases he
  · simp

/-- The arguments `--olean --modular --search-path=<dirs> -- <root>`: that one root, those
directories, every other setting at its default (the mode `.verified`). -/
theorem parseArgs_modular (dirs root : String) :
    parseArgs ["--olean", "--modular", "--search-path=" ++ dirs, "--", root] {} =
      { olean := true, modular := true, searchPath := searchPathOf dirs, files := #[root] } := by
  have hfst : parseArgs ["--olean", "--modular", "--search-path=" ++ dirs, "--", root] {} =
      parseArgs ["--search-path=" ++ dirs, "--", root] { olean := true, modular := true } := by
    rw [parseArgs.eq_def]
    rfl
  rw [hfst, parseArgs_flag _ _ (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)),
    flagValue_other dirs (by decide) (by decide), flagValue_other dirs (by decide) (by decide),
    flagValue_natMax_searchPath, flagValue_other dirs (by decide) (by decide),
    flagValue_append]
  have hj : (("--search-path=" ++ dirs) == "--jobs") = false := by
    simp only [beq_eq_false_iff_ne]
    exact append_ne _ (by decide)
  simp only [hj, Bool.false_eq_true, ↓reduceIte]
  simp [parseArgs, Args.closed]

/-- The flags of `--olean --modular --search-path=<dirs> -- <root>` ask for no help. -/
theorem helpWanted_modular (dirs root : String) :
    helpWanted ["--olean", "--modular", "--search-path=" ++ dirs, "--", root] = false := by
  have h1 : "--search-path=" ++ dirs ≠ "--" := append_ne _ (by decide)
  have h2 : "--search-path=" ++ dirs ≠ "--help" := append_ne _ (by decide)
  simp [helpWanted, h1, h2.symm]

/-- **`runArgs` on `--olean --modular --search-path=<dirs> -- <root>`, in the model**: every
outcome that is an exit 0 names a module `m`, and gives what an exit 0 of `--check-graph` at `m`
gives (`checkGraphG_ok`'s facts: the closure `C`, each module's imports its header's, closed
under imports, a rank decreasing along every import, one-to-one), and, at every module of `C`,
what an exit 0 of `--module` at that module gives (`WorkerAccepted` at the mode `.verified`). -/
theorem runArgs_modular_accept {dirs root : String} {fs : FS} {hs hs' : HS}
    (h : (runArgs ["--olean", "--modular", "--search-path=" ++ dirs, "--", root] : ModelIO _) fs hs
      (.ok 0) hs') :
    ∃ m, Olean.parseModName root = some m ∧ ∃ C : List Graph.Node, ∃ rk : Name → Nat,
      (∀ e ∈ C, ModelIO.CanGive (Olean.moduleImports (searchPathOf dirs) e.1) fs (.ok e.2)) ∧
      m ∈ C.map (·.1) ∧
      (∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1) ∧
      (C.map fun e => rk e.1).Nodup ∧
      ∀ e ∈ C, WorkerAccepted .verified Cached.maxNatSizeDefault (searchPathOf dirs) fs e.1 1 := by
  suffices H : ModelIO.AllOk (runArgs ["--olean", "--modular", "--search-path=" ++ dirs, "--", root])
      fs hs (fun c => c = 0 → ∃ m, Olean.parseModName root = some m ∧ ∃ C : List Graph.Node,
        ∃ rk : Name → Nat,
        (∀ e ∈ C, ModelIO.CanGive (Olean.moduleImports (searchPathOf dirs) e.1) fs (.ok e.2)) ∧
        m ∈ C.map (·.1) ∧
        (∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1) ∧
        (C.map fun e => rk e.1).Nodup ∧
        ∀ e ∈ C, WorkerAccepted .verified Cached.maxNatSizeDefault (searchPathOf dirs) fs e.1 1) from H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · simp only [helpWanted_modular, parseArgs_modular, List.isEmpty_nil, Bool.and_true,
      Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    intro c _ hc h0
    subst h0
    split at hc
    · simp [eprintln] at hc
    · cases hf : (#[root] : Array String).find? (fun f => (Olean.parseModName f).isNone) with
      | some m => simp [hf, eprintln] at hc
      | none =>
        simp only [hf] at hc
        cases hr : Olean.parseModName root with
        | none => simp [hr] at hf
        | some m =>
          simp only [Array.find?_empty, List.filterMap_cons, hr, List.filterMap_nil,
            Array.isEmpty_empty] at hc
          generalize (none : Option Nat).getD _ = j at hc
          simp only [runReq, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hc
          obtain ⟨C, T, ⟨_, _, hC⟩, hall⟩ := checkModularG_accept
            (sp := searchPathOf dirs) rfl hc
          obtain ⟨rk, h1, h2, h3, h4, -⟩ := Graph.graphOf_ok rfl hC
          exact ⟨m, rfl, C.toList, rk, fun e he => (h1 e he).plain, h2 m (by simp), h3, h4,
            fun e he => hall e he⟩
  · simp

/-- **`runArgs` on `--olean --compare` arguments, in the model**: at any arguments that ask for
no help, parse without a usage error and ask for `--olean --compare` (not `--check-graph`,
`--module`, `--modular` or `--schedule`), every outcome that is an exit 0 is one of `compareG` on
the two module names the arguments give, at the arguments' lookups and `--constant` names. -/
theorem runArgs_compares_accept {args : List String} {fs : FS} {hs hs' : HS}
    (hh : helpWanted args = false) (hb : (parseArgs args {}).bad = none)
    (ho : (parseArgs args {}).olean = true) (hcg : (parseArgs args {}).checkGraph = false)
    (hcmp : (parseArgs args {}).compare = true)
    (hmod : ((parseArgs args {}).module || (parseArgs args {}).modular ||
      (parseArgs args {}).scheduled) = false)
    (h : (runArgs args : ModelIO _) fs hs (.ok 0) hs') :
    ∃ C S jobs, (parseArgs args {}).files.toList.filterMap Olean.parseModName = [C, S] ∧
      ModelIO.CanGive (compareG ⟨C, S, (parseArgs args {}).trustedPath,
        (parseArgs args {}).searchPath, (parseArgs args {}).rootConstants⟩ (parseArgs args {}).mode
        (parseArgs args {}).maxNatSize (parseArgs args {}).progress jobs) fs 0 := by
  suffices H : ModelIO.AllOk (runArgs args) fs hs
      (fun c => c = 0 → ∃ C S jobs,
        (parseArgs args {}).files.toList.filterMap Olean.parseModName = [C, S] ∧
        ModelIO.CanGive (compareG ⟨C, S, (parseArgs args {}).trustedPath,
          (parseArgs args {}).searchPath, (parseArgs args {}).rootConstants⟩
          (parseArgs args {}).mode (parseArgs args {}).maxNatSize (parseArgs args {}).progress
          jobs) fs 0) from
    H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · simp only [hh, hb, ho, hcg, hcmp, hmod, Bool.false_eq_true, ite_false, ite_true]
    intro c hs₂ hc h0
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
          generalize hl : List.filterMap Olean.parseModName (parseArgs args {}).files.toList = l
            at hc
          rcases l with _ | ⟨C, _ | ⟨S, _ | ⟨_, _⟩⟩⟩ <;>
            simp only [eprintln, ModelIO.bind_ok, ModelIO.liftIO_iff, ModelIO.pure_iff,
              Except.ok.injEq, exists_eq_left] at hc
          all_goals try (obtain ⟨_, _, h3, -⟩ := hc; cases h3)
          split at hc
          · simp at hc
          · exact ⟨C, S, _, rfl, _, _, hc⟩
  · simp

/-- The arguments `--olean --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>`:
those two modules, those directories, and every other setting at its default (the mode
`.verified`, every constant). -/
theorem parseArgs_compare (T D c s : String) :
    parseArgs ["--olean", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--",
      c, s] {} =
      { olean := true, compare := true, trustedPath := searchPathOf T,
        searchPath := searchPathOf D, files := #[c, s] } := by
  have hfst : parseArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] {} =
      parseArgs ["--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]
        { olean := true, compare := true } := by
    rw [parseArgs.eq_def]
    rfl
  rw [hfst, parseArgs_flag _ _ (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)),
    flagValue_other T (by decide) (by decide), flagValue_other T (by decide) (by decide),
    flagValue_other T (by decide) (by decide)]
  have hj : (("--trusted-search-path=" ++ T) == "--jobs") = false := by
    simp only [beq_eq_false_iff_ne]
    exact append_ne _ (by decide)
  simp only [hj, Bool.false_eq_true, ↓reduceIte]
  rw [flagValue_other T (by decide) (by decide), flagValue_other T (by decide) (by decide),
    flagValue_append]
  simp only
  rw [parseArgs_flag _ _ (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)) (append_ne _ (by decide)) (append_ne _ (by decide))
      (append_ne _ (by decide)),
    flagValue_other D (by decide) (by decide), flagValue_other D (by decide) (by decide),
    flagValue_natMax_searchPath, flagValue_other D (by decide) (by decide),
    flagValue_append]
  have hj' : (("--search-path=" ++ D) == "--jobs") = false := by
    simp only [beq_eq_false_iff_ne]
    exact append_ne _ (by decide)
  simp only [hj', Bool.false_eq_true, ↓reduceIte]
  simp [parseArgs, Args.closed]

/-- The flags of the compare arguments ask for no help. -/
theorem helpWanted_compare (T D c s : String) :
    helpWanted ["--olean", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--",
      c, s] = false := by
  have h1 : "--search-path=" ++ D ≠ "--" := append_ne _ (by decide)
  have h2 : "--search-path=" ++ D ≠ "--help" := append_ne _ (by decide)
  have h3 : "--trusted-search-path=" ++ T ≠ "--" := append_ne _ (by decide)
  have h4 : "--trusted-search-path=" ++ T ≠ "--help" := append_ne _ (by decide)
  simp [helpWanted, h1, h2.symm, h3, h4.symm]

/-- **`runArgs` on `--olean --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>`,
in the model**: every outcome that is an exit 0 read the challenge `C` (`c`) through `T` alone
and the solution `S` (`s`) through `T`, then `D`, every constant of both closures;
`checkDecls .verified` accepts the solution's records prepared with the built-in prelude, with the
theorems' values in place, at the environment they denote, and the fold with that environment as
the solution has an accepting run over the challenge's records as its check reads them. -/
theorem runArgs_compare_accept {T D c s : String} {C S : Name} {fs : FS} {hs hs' : HS}
    (hc : Olean.parseModName c = some C) (hsol : Olean.parseModName s = some S)
    (h : (runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D,
      "--", c, s] : ModelIO _) fs hs (.ok 0) hs') :
    let r : CmpReq := ⟨C, S, searchPathOf T, searchPathOf D, none⟩
    ∃ pre rdC rdS n fe, builtinPreludeE = .ok pre ∧
      ModelIO.CanGive (Olean.readOleansAt r.chalRoots #[C] none (lenient := true)
        (homes := true)) fs (.ok rdC) ∧
      ModelIO.CanGive (Olean.readOleansAt r.solRoots #[S] none (lenient := true)) fs (.ok rdS) ∧
      Cached.checkDecls .verified natOpPinSets Cached.maxNatSizeDefault
        (solChecked pre r.solRoots fs rdS) = .ok (streamEnv (solChecked pre r.solRoots fs rdS).toList) ∧
      Cached.DeclsRun .verified natOpPinSets Cached.maxNatSizeDefault
        (Cached.solutionOf (some (streamEnv (solChecked pre r.solRoots fs rdS).toList))
          (chalChecked pre (streamEnv (solChecked pre r.solRoots fs rdS).toList) r.chalRoots fs rdC))
        (chalChecked pre (streamEnv (solChecked pre r.solRoots fs rdS).toList) r.chalRoots fs
          rdC).toList (0, mkFEnv Env.empty) (n, fe) := by
  have hp := parseArgs_compare T D c s
  obtain ⟨C', S', jobs, hf, _, _, hg⟩ := runArgs_compares_accept (helpWanted_compare T D c s)
    (by rw [hp]) (by rw [hp]) (by rw [hp]) (by rw [hp]) (by rw [hp]; rfl) h
  rw [hp] at hf hg
  simp only [List.filterMap_cons, List.filterMap_nil, hc, hsol] at hf
  obtain ⟨rfl, rfl⟩ : C = C' ∧ S = S' := by simpa using hf
  obtain ⟨pre, rdC, rdS, n, fe, h1, h2, -, h4, h5, h6⟩ := compareG_accept hg
  exact ⟨pre, rdC, rdS, n, fe, h1, h2, h4, h5, h6⟩

/-! ## The modular comparison with a trusted path (task #608) -/

/-- The arguments `--check-graph --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>`. -/
theorem parseArgs_graphCmpT (T D c s : String) :
    parseArgs ["--check-graph", "--compare", "--trusted-search-path=" ++ T, "--search-path=" ++ D,
      "--", c, s] {} =
      { checkGraph := true, compare := true, trustedPath := searchPathOf T,
        searchPath := searchPathOf D, files := #[c, s] } := by
  have hfst : parseArgs ["--check-graph", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] {} =
      parseArgs (("--trusted-search-path=" ++ T) :: ("--search-path=" ++ D) :: ["--", c, s])
        { checkGraph := true, compare := true } := by
    rw [parseArgs.eq_def]
    rfl
  rw [hfst, parseArgs_paths]
  simp [parseArgs, Args.closed]

/-- **`runArgs` on `--check-graph --compare --trusted-search-path=<T> --search-path=<D> -- <c>
<s>`, in the model**: every exit 0 is an exit 0 of the graph check of both closures through the
solution's lookup (`T`, then `D`), the solution added to the challenge's header. -/
theorem runArgs_graphCmpT_accept {T D c s : String} {C S : Name} {fs : FS} {hs hs' : HS}
    (hc : Frontend.Olean.parseModName c = some C) (hsol : Frontend.Olean.parseModName s = some S)
    (h : (runArgs ["--check-graph", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] : ModelIO _) fs hs (.ok 0) hs') :
    let r : CmpReq := ⟨C, S, searchPathOf T, searchPathOf D, none⟩
    ∃ jobs, ModelIO.CanGive (Graph.checkGraphG r.solRoots [C] jobs (Graph.cmpExtra C S)) fs 0 := by
  intro r
  obtain ⟨n1, n2, n3, n4⟩ := paths_ne T D
  suffices H : ModelIO.AllOk (runArgs ["--check-graph", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs hs (fun v => v = 0 → ∃ jobs, ModelIO.CanGive
        (Graph.checkGraphG r.solRoots [C] jobs (Graph.cmpExtra C S)) fs 0) from
    H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · have hhelp : helpWanted ["--check-graph", "--compare", "--trusted-search-path=" ++ T,
        "--search-path=" ++ D, "--", c, s] = false := by
      simp [helpWanted, n1, n2.symm, n3, n4.symm]
    simp only [hhelp, parseArgs_graphCmpT, Bool.false_eq_true, ite_false, ite_true]
    intro v _ hv h0
    subst h0
    have hf : (#[c, s].find? fun f => (Frontend.Olean.parseModName f).isNone) = none := by
      simp [hc, hsol]
    simp only [hf] at hv
    simp only [Bool.or_false, Array.isEmpty_empty, Bool.not_true,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hv
    simp only [List.filterMap_cons, hc, hsol, List.filterMap_nil] at hv
    simp only [runReq] at hv
    cases hE : ((searchPathOf D).isEmpty && (searchPathOf T).isEmpty)
    · have h1 : (#[c, s] : Array String).isEmpty = false := rfl
      simp only [hE, h1, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hv
      cases hCS : (C == S)
      · simp only [hCS, Bool.false_eq_true, ↓reduceIte] at hv
        exact ⟨_, checkGraphCmpG_accept ⟨_, _, hv⟩⟩
      · simp [hCS, eprintln] at hv
    · have h1 : (#[c, s] : Array String).isEmpty = false := rfl
      simp only [hE, h1, Bool.false_or, ↓reduceIte] at hv
      simp [eprintln] at hv
  · simp

/-- The arguments `--olean --module --trusted-search-path=<T> --search-path=<D> -- <root>`. -/
theorem parseArgs_moduleT (T D root : String) :
    parseArgs ["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--",
      root] {} =
      { olean := true, module := true, trustedPath := searchPathOf T,
        searchPath := searchPathOf D, files := #[root] } := by
  have hfst : parseArgs ["--olean", "--module", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", root] {} =
      parseArgs (("--trusted-search-path=" ++ T) :: ("--search-path=" ++ D) :: ["--", root])
        { olean := true, module := true } := by
    rw [parseArgs.eq_def]
    rfl
  rw [hfst, parseArgs_paths]
  simp [parseArgs, Args.closed]

/-- **`runArgs` on `--olean --module --trusted-search-path=<T> --search-path=<D> -- <root>`, in
the model**: every exit 0 names a module `m` and is an accepted worker at `m` through `T`, then
`D` (a compared run's solution side, `CmpReq.solRoots`). -/
theorem runArgs_moduleT_accept {T D root : String} {fs : FS} {hs hs' : HS}
    (h : (runArgs ["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D,
      "--", root] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ m jobs, Olean.parseModName root = some m ∧ ∀ C S : Name,
      WorkerAccepted .verified Cached.maxNatSizeDefault
        (⟨C, S, searchPathOf T, searchPathOf D, none⟩ : CmpReq).solRoots fs m jobs := by
  obtain ⟨n1, n2, n3, n4⟩ := paths_ne T D
  suffices H : ModelIO.AllOk (runArgs ["--olean", "--module", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", root]) fs hs (fun c => c = 0 → ∃ m jobs,
        Olean.parseModName root = some m ∧ ∀ C S : Name,
        WorkerAccepted .verified Cached.maxNatSizeDefault
          (⟨C, S, searchPathOf T, searchPathOf D, none⟩ : CmpReq).solRoots fs m jobs) from
    H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · have hhelp : helpWanted ["--olean", "--module", "--trusted-search-path=" ++ T,
        "--search-path=" ++ D, "--", root] = false := by
      simp [helpWanted, n1, n2.symm, n3, n4.symm]
    simp only [hhelp, parseArgs_moduleT, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    intro c _ hc h0
    subst h0
    split at hc
    · simp [eprintln] at hc
    · cases hf : (#[root] : Array String).find? (fun f => (Olean.parseModName f).isNone) with
      | some m => simp [hf, eprintln] at hc
      | none =>
        simp only [hf] at hc
        cases hr : Olean.parseModName root with
        | none => simp [hr] at hf
        | some m =>
          simp only [Array.find?_empty, List.filterMap_cons, hr, List.filterMap_nil,
            Array.isEmpty_empty, Bool.or_false, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte, runReq] at hc
          rcases hc with ⟨⟨R, Tb⟩, _, hT, hc⟩ | ⟨e, he, -⟩
          · obtain ⟨hR, hp, hT⟩ := workerTables_ok (CmpReq.solRoots_bare _) hT
            exact ⟨m, _, rfl, fun _ _ => checkModuleG_accept (modTables_within hR hp hT) hR hp hc⟩
          · cases he
  · simp

/-- The arguments `--olean --module --compare --trusted-search-path=<T> --search-path=<D> -- <c>
<s>`. -/
theorem parseArgs_cmpModuleT (T D c s : String) :
    parseArgs ["--olean", "--module", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] {} =
      { olean := true, module := true, compare := true, trustedPath := searchPathOf T,
        searchPath := searchPathOf D, files := #[c, s] } := by
  have hfst : parseArgs ["--olean", "--module", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] {} =
      parseArgs (("--trusted-search-path=" ++ T) :: ("--search-path=" ++ D) :: ["--", c, s])
        { olean := true, module := true, compare := true } := by
    rw [parseArgs.eq_def]
    rfl
  rw [hfst, parseArgs_paths]
  simp [parseArgs, Args.closed]

/-- **`runArgs` on `--olean --module --compare --trusted-search-path=<T> --search-path=<D> -- <c>
<s>`, in the model** (task #619): every exit 0 names a challenge `C` and a solution `S` and is an
accepted worker at `C` with `import all S` added to its header, every read through `T`, then
`D`. -/
theorem runArgs_cmpModuleT_accept {T D c s : String} {fs : FS} {hs hs' : HS}
    (h : (runArgs ["--olean", "--module", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ C S jobs, Olean.parseModName c = some C ∧ Olean.parseModName s = some S ∧
      WorkerAccepted .verified Cached.maxNatSizeDefault
        (⟨C, S, searchPathOf T, searchPathOf D, none⟩ : CmpReq).solRoots fs C jobs
        #[Graph.solutionImport S] := by
  obtain ⟨n1, n2, n3, n4⟩ := paths_ne T D
  suffices H : ModelIO.AllOk (runArgs ["--olean", "--module", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs hs
      (fun v => v = 0 → ∃ C S jobs, Olean.parseModName c = some C ∧
        Olean.parseModName s = some S ∧
        WorkerAccepted .verified Cached.maxNatSizeDefault
          (⟨C, S, searchPathOf T, searchPathOf D, none⟩ : CmpReq).solRoots fs C jobs
          #[Graph.solutionImport S]) from
    H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · have hhelp : helpWanted ["--olean", "--module", "--compare", "--trusted-search-path=" ++ T,
        "--search-path=" ++ D, "--", c, s] = false := by
      simp [helpWanted, n1, n2.symm, n3, n4.symm]
    simp only [hhelp, parseArgs_cmpModuleT, Bool.not_true, Bool.false_eq_true, ite_false,
      ite_true]
    intro v _ hv h0
    subst h0
    split at hv
    · simp [eprintln] at hv
    · cases hc : Olean.parseModName c with
      | none =>
        have : (#[c, s] : Array String).find? (fun f => (Olean.parseModName f).isNone) =
            some c := by simp [hc]
        simp [this, eprintln] at hv
      | some C =>
      cases hsn : Olean.parseModName s with
      | none =>
        have : (#[c, s] : Array String).find? (fun f => (Olean.parseModName f).isNone) =
            some s := by simp [hc, hsn]
        simp [this, eprintln] at hv
      | some S =>
        have : (#[c, s] : Array String).find? (fun f => (Olean.parseModName f).isNone) = none := by
          simp [hc, hsn]
        simp only [this, Array.find?_empty, List.filterMap_cons, hc, hsn, List.filterMap_nil,
          Array.isEmpty_empty] at hv
        split at hv
        · simp [eprintln] at hv
        · simp only [Bool.or_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Bool.and_false, Bool.false_and, Bool.or_self] at hv
          simp only [runReq, ModelIO.bind_ok] at hv
          obtain ⟨⟨R, Tb⟩, _, hT, hv⟩ := hv
          obtain ⟨hR, hp, hT⟩ := workerTables_ok (CmpReq.solRoots_bare _) hT
          simp only [checkCmpModuleG, ModelIO.bind_ok] at hv
          obtain ⟨w, _, -, hv⟩ := hv
          rcases w with _ | e
          · exact ⟨C, S, _, rfl, rfl, checkModuleG_accept (modTables_within hR hp hT) hR hp hv⟩
          · simp only [diagLine, ModelIO.bind_ok, ModelIO.liftIO_iff, ModelIO.pure_iff,
              Except.ok.injEq] at hv
            obtain ⟨_, _, -, hv, -⟩ := hv
            exact absurd hv.symm (CheckError.exitCode_ne_zero _)
  · simp

/-- The arguments `--olean --modular --compare --trusted-search-path=<T> --search-path=<D> -- <c>
<s>`. -/
theorem parseArgs_modularCmpT (T D c s : String) :
    parseArgs ["--olean", "--modular", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] {} =
      { olean := true, modular := true, compare := true, trustedPath := searchPathOf T,
        searchPath := searchPathOf D, files := #[c, s] } := by
  have hfst : parseArgs ["--olean", "--modular", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] {} =
      parseArgs (("--trusted-search-path=" ++ T) :: ("--search-path=" ++ D) :: ["--", c, s])
        { olean := true, modular := true, compare := true } := by
    rw [parseArgs.eq_def]
    rfl
  rw [hfst, parseArgs_paths]
  simp [parseArgs, Args.closed]

/-- **`runArgs` on `--olean --modular --compare --trusted-search-path=<T> --search-path=<D> --
<c> <s>`, in the model** (task #619): every exit 0 names a challenge `C` and a solution `S` and is
an accepting graph check of both closures through `T`, then `D` (`C`'s header with `import all S`
added), and an accepted worker at every module of it, `C`'s with that import added. -/
theorem runArgs_modularCmpT_accept {T D c s : String} {fs : FS} {hs hs' : HS}
    (h : (runArgs ["--olean", "--modular", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s] : ModelIO _) fs hs (.ok 0) hs') :
    ∃ C S, Olean.parseModName c = some C ∧ Olean.parseModName s = some S ∧
      let r : CmpReq := ⟨C, S, searchPathOf T, searchPathOf D, none⟩
      ∃ jobs Cg Tg, ModelIO.CanGive (Graph.graphOf r.solRoots [C] jobs
        (Graph.cmpExtra C S)) fs (.ok (Cg, Tg)) ∧
      ∀ e ∈ Cg.toList, WorkerAccepted .verified Cached.maxNatSizeDefault r.solRoots fs e.1 1
        (Graph.cmpExtra C S e.1) := by
  obtain ⟨n1, n2, n3, n4⟩ := paths_ne T D
  suffices H : ModelIO.AllOk (runArgs ["--olean", "--modular", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs hs (fun v => v = 0 →
        ∃ C S, Olean.parseModName c = some C ∧ Olean.parseModName s = some S ∧
        let r : CmpReq := ⟨C, S, searchPathOf T, searchPathOf D, none⟩
        ∃ jobs Cg Tg, ModelIO.CanGive (Graph.graphOf r.solRoots [C] jobs
          (Graph.cmpExtra C S)) fs (.ok (Cg, Tg)) ∧
        ∀ e ∈ Cg.toList, WorkerAccepted .verified Cached.maxNatSizeDefault r.solRoots fs e.1 1
          (Graph.cmpExtra C S e.1)) from H 0 hs' h rfl
  refine ModelIO.allOk_tryCatch ?_ fun _ _ _ => ?_
  · have hhelp : helpWanted ["--olean", "--modular", "--compare", "--trusted-search-path=" ++ T,
        "--search-path=" ++ D, "--", c, s] = false := by
      simp [helpWanted, n1, n2.symm, n3, n4.symm]
    simp only [hhelp, parseArgs_modularCmpT, Bool.not_true, Bool.false_eq_true, ite_false,
      ite_true]
    intro v _ hv h0
    subst h0
    split at hv
    · simp [eprintln] at hv
    · cases hc : Olean.parseModName c with
      | none =>
        have : (#[c, s] : Array String).find? (fun f => (Olean.parseModName f).isNone) =
            some c := by simp [hc]
        simp [this, eprintln] at hv
      | some C =>
      cases hsn : Olean.parseModName s with
      | none =>
        have : (#[c, s] : Array String).find? (fun f => (Olean.parseModName f).isNone) =
            some s := by simp [hc, hsn]
        simp [this, eprintln] at hv
      | some S =>
        have : (#[c, s] : Array String).find? (fun f => (Olean.parseModName f).isNone) = none := by
          simp [hc, hsn]
        simp only [this, Array.find?_empty, List.filterMap_cons, hc, hsn, List.filterMap_nil,
          Array.isEmpty_empty] at hv
        split at hv
        · simp [eprintln] at hv
        · simp only [Bool.or_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Bool.and_false, Bool.or_self] at hv
          generalize (none : Option Nat).getD _ = j at hv
          simp only [runReq, Bool.false_or, ↓reduceIte] at hv
          obtain ⟨Cg, Tg, hg, hall⟩ := checkModularG_accept (CmpReq.solRoots_bare _) hv
          exact ⟨C, S, rfl, rfl, _, Cg, Tg, hg, fun e he => hall e he⟩
  · simp

end ConLeche.Driver
