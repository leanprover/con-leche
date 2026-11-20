module

public import ConLeche.Driver.Cli
public import ConLeche.IsModel
public import ConLeche.Cached.Decls
import ConLeche.Verify.Driver.Main
import ConLeche.Verify.Frontend.Prepare
public import ConLeche.Accepts
import ConLeche.Verify.Frontend.FileFalse
import ConLeche.Verify.IsModelRecords

public section

/-!
# The plain run's theorem of type `False`, inside the stream it checked (task #624)

An exit 0 of `-- <file>` is an accept of `checkDecls` on the parsed records prepared with the
built-in prelude, which keeps every parsed record (`mem_preparePrelude`).  Where the file is a
`jsonWithTheoremFalse` file, the parse holds a theorem record of type `False`
(`parseChunks_jsonWithTheoremFalse`), so the checked stream has a constant of type `False`.  The
stream, not the file alone: the prelude's declarations the preparation adds are part of what was
checked.
-/

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend

/-- **An exit 0 of `-- <file>` on a `jsonWithTheoremFalse` file accepted a stream with a constant
of type `False`.** -/
theorem runArgs_json_false {file : String} {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (runArgs ["--", file]) fs 0) (hb : fs.file file = some b)
    (hF : jsonWithTheoremFalse [b]) :
    ∃ ds, (Cached.checkDecls .verified natOpPinSets Cached.maxNatSizeDefault ds).isOk ∧
      ∃ c ∈ constantsOf ds.toList, c.type = .const falseName [] := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨pre, b', r, env, -, hb', hp, hc⟩ := runArgs_accept h
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨cv, vl, hty, hmem⟩ := parseChunks_jsonWithTheoremFalse hF hp
  refine ⟨_, by rw [hc]; rfl, .thmInfo cv, mem_constantsOf.2 ⟨_, Array.mem_toList_iff.2
    (mem_preparePrelude (pre := pre) hmem), List.mem_singleton_self _⟩, hty⟩

end ConLeche.Driver
