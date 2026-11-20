module

import ConLeche.Model.IsModelBridge
import ConLeche.Model.Solution
import ConLeche.Model.Capstone
import ConLeche.Verify.CompareInput
public import ConLeche.OleanInput
public import ConLeche.Verify.Frontend.Olean.Local
public import ConLeche.Driver.Cli

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
    ∀ fs', FS.AgreeUnder (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs fs' →
      ∃ model, IsModel V model (Olean.closureConstants (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs' #[C]) := by
  intro fs' hag
  obtain ⟨_, _, h⟩ := h
  obtain ⟨_, _, _, _, fe, hS, hrun, hst⟩ := Driver.runArgs_compare_stored hc hs h
  obtain ⟨m⟩ := Model.Solution.solution_envModel_run (V := V) hS hrun
  rw [← closureConstants_local hag]
  exact ⟨_, isModel_of_envModelM m hst⟩

/-- **A challenge whose closure through the trusted path holds a constant of type `False` has no
accepted `.olean` comparison**: the run's environment stores the constant
(`Driver.runArgs_compare_stored`), and it has a model (`Model.no_constant_of_False`). -/
theorem compare_no_False (V : Type w) [SetTheory V] {T D c s : String} {C S m : Name} {fs : FS}
    {ci : ConstantInfo} (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0)
    (hm : Olean.InClosure (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs #[C] m)
    (hci : Olean.InModulePart (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs
      m .private ci)
    (hty : ci.type = .const falseName []) : False := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨_, _, _, _, fe, hS, hrun, hst⟩ := Driver.runArgs_compare_stored hc hs h
  obtain ⟨mo⟩ := Model.Solution.solution_envModel_run (V := V) hS hrun
  obtain ⟨ci', hfi, hsa, -⟩ := hst _ ⟨m, hm, hci⟩
  exact Model.no_constant_of_False mo ci' (Env.find?_mem hfi) (by rw [hsa.1]; exact hty)

end ConLeche
