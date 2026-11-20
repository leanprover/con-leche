module

public import ConLeche.OleanInput
public import ConLeche.Driver.Cli
public import ConLeche.Cached.Decls
import ConLeche.Verify.OleanInput
import ConLeche.Verify.Driver.Main
import ConLeche.Verify.Driver.CompareJsonRun
import ConLeche.Verify.Frontend.Prepare

public section

/-!
# An accepted run's input, inside the stream it checked (task #624)

The no-`False` corollaries of the runs that check ONE stream — `-- <file>`, `--olean -- <root>`,
`--compare -- <c> <s>` — follow from the main theorem over that stream (`model_exists`,
`solution_model_exists`): the run's exit 0 is an accept of `checkDecls` (or `checkChallenge`) on
the input prepared with the built-in prelude, and every constant of the input is a constant of
that stream (a parsed file's, by `mem_preparePrelude`), or stored by one of the same statement
(an `.olean` closure's, `Olean.checkDecls_inputCovered`).  The stream, not the input alone: the
prelude's declarations the preparation adds are part of what was checked, and a crafted input
may read `False` from them.
-/

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend

/-- **An exit 0 of `-- <file>` accepted a stream holding every constant of the parsed file.** -/
theorem runArgs_stream {file : String} {fs : FS} {b : ByteArray} {r : ParseResultD}
    (h : ModelIO.CanGive (runArgs ["--", file]) fs 0) (hb : fs.file file = some b)
    (hp : parseChunks [b] = .ok r) :
    ∃ ds, (Cached.checkDecls .verified natOpPinSets Cached.maxNatSizeDefault ds).isOk ∧
      ∀ c ∈ constantsOf r.decls.toList, c ∈ constantsOf ds.toList := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨pre, b', r', env, -, hb', hp', hc⟩ := runArgs_accept h
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain rfl : r = r' := Except.ok.inj (hp.symm.trans hp')
  refine ⟨_, by rw [hc]; rfl, fun c hc => ?_⟩
  obtain ⟨d, hd, hcd⟩ := mem_constantsOf.1 hc
  exact mem_constantsOf.2 ⟨d, Array.mem_toList_iff.2
    (mem_preparePrelude (pre := pre) (Array.mem_toList_iff.1 hd)), hcd⟩

/-- **An exit 0 of `--olean -- <root>` accepted a stream storing every constant of the closure**
by a constant of the same statement. -/
theorem runArgs_olean_stream {dirs root : String} {r m : Name} {fs : FS} {c : ConstantInfo}
    (hr : Olean.parseModName root = some r)
    (h : ModelIO.CanGive (runArgs ["--olean", "--search-path=" ++ dirs, "--", root]) fs 0)
    (hm : Olean.InClosure (searchPathOf dirs) fs #[r] m)
    (hc : Olean.InModulePart (searchPathOf dirs) fs m .private c) :
    ∃ ds, (Cached.checkDecls .verified natOpPinSets Cached.maxNatSizeDefault ds).isOk ∧
      ∃ c' ∈ constantsOf ds.toList, c'.toConstantVal = c.toConstantVal := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨pre, rd, env, -, hrd, hchk⟩ := runArgs_olean_accept h
  have hroots : (#[root].filterMap Olean.parseModName) = #[r] := by simp [hr]
  rw [hroots] at hrd
  obtain ⟨_, _, hrd⟩ := hrd
  obtain ⟨c', hc', hst⟩ := Olean.checkDecls_inputCovered rfl hrd hchk ⟨m, hm, hc⟩
  exact ⟨_, by rw [hchk]; rfl, c', hc', hst.1⟩

/-- **An exit 0 of `--compare -- <c> <s>` accepted a solution stream, and a challenge stream
holding every constant of the parsed challenge file, checked with it.** -/
theorem runArgs_compare_json_stream {c s : String} {fs : FS} {bC : ByteArray} {rC : ParseResultD}
    (h : ModelIO.CanGive (runArgs ["--compare", "--", c, s]) fs 0)
    (hbC : fs.file c = some bC) (hp : parseChunks [bC] = .ok rC) :
    ∃ dsS ds, (Cached.checkDecls .verified natOpPinSets Cached.maxNatSizeDefault dsS).isOk ∧
      (Cached.checkChallenge .verified natOpPinSets Cached.maxNatSizeDefault dsS ds).isOk ∧
      ∀ k ∈ constantsOf rC.decls.toList, k ∈ constantsOf ds.toList := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨pre, bC', rC', bS, rS, env, -, h2, h3, -, -, hS, hC⟩ := runArgs_compare_json_accept h
  obtain rfl : bC = bC' := Option.some.inj (hbC.symm.trans h2)
  obtain rfl : rC = rC' := Except.ok.inj (hp.symm.trans h3)
  refine ⟨_, _, by rw [hS]; rfl, by rw [hC]; rfl, fun k hk => ?_⟩
  obtain ⟨d, hd, hkd⟩ := mem_constantsOf.1 hk
  exact mem_constantsOf.2 ⟨d, Array.mem_toList_iff.2
    (mem_preparePrelude (pre := pre) (Array.mem_toList_iff.1 hd)), hkd⟩

end ConLeche.Driver
