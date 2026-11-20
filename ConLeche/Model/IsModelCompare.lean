module

import ConLeche.Model.IsModelBridge
import ConLeche.Model.Solution
import ConLeche.Model.Capstone
public import ConLeche.Verify.CompareInput

public section

/-!
# The `.olean` challenge checked with a solution has a model (task #619)

An exit 0 of `--olean --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>` checked
a solution stream and ran the fold with its environment as the solution over the challenge's
records, a run whose environment stores every constant of the closure of the challenge through
`T` (`Driver.runArgs_compare_stored`).  The run carries a model
(`Model.Solution.solution_envModel_run`), the bridge carries it to the closure's constants
(`isModel_of_envModelM`), and those are the same on every snapshot that agrees with the run's on
the paths the reader forms under `T` (`closureConstants_local`).
-/

namespace ConLeche

open Frontend

universe w

/-- **An accepted `.olean` comparison's challenge has a model, on every snapshot that agrees
under the trusted path**: the constants of the closure of `C` through `T`. -/
theorem compare_isModel (V : Type w) [SetTheory V] {T D c s : String} {C S : Name} {fs : FS}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0) :
    ∀ fs', FS.AgreeUnder (Driver.searchPathOf T) fs fs' →
      ∃ model, IsModel V model (Olean.closureConstants (Driver.searchPathOf T) fs' #[C]) := by
  intro fs' hag
  obtain ⟨_, _, h⟩ := h
  obtain ⟨_, _, _, _, fe, hS, hrun, hst⟩ := Driver.runArgs_compare_stored hc hs h
  obtain ⟨m⟩ := Model.Solution.solution_envModel_run (V := V) hS hrun
  rw [← closureConstants_local hag]
  exact ⟨_, isModel_of_envModelM m hst⟩

/-- **A challenge whose closure through the trusted path holds a theorem of type `False` has no
accepted `.olean` comparison.** -/
theorem compare_no_False (V : Type w) [SetTheory V] {T D c s : String} {C S m : Name} {fs : FS}
    {d : Olean.ModDecoded} {e : Olean.CEntryF Name Expr} {v : Expr} {all : List Name}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (hcl : Olean.InClosure (Driver.searchPathOf T) fs #[C] m)
    (hv : Olean.ViewOf (Driver.searchPathOf T) fs m d)
    (hmem : e ∈ d.constants) (hk : e.kind = .thm v all) (hty : e.type = .const falseName []) :
    ¬ ModelIO.CanGive (Driver.runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0 := by
  rintro ⟨_, _, h⟩
  obtain ⟨_, _, _, _, fe, hS, hrun, hst⟩ := Driver.runArgs_compare_stored hc hs h
  obtain ⟨mo⟩ := Model.Solution.solution_envModel_run (V := V) hS hrun
  obtain ⟨f, hf, hd⟩ := hv
  have hin : Olean.closureConstants (Driver.searchPathOf T) fs #[C] (.thmInfo e.cv) :=
    ⟨m, hcl, f, d, e, hf, hd, hmem, by simp [Olean.entryConstants, hk, Olean.declOfEntry,
      Declaration.constants]⟩
  obtain ⟨ci, hfi, hsa⟩ := hst _ hin
  exact Model.no_constant_of_False mo ci (Env.find?_mem hfi) (by rw [hsa.1]; exact hty)

end ConLeche
