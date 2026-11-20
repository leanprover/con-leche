module

public import ConLeche.Model.IsModelBridge
public import ConLeche.Verify.Frontend.Olean.Input
public import ConLeche.Verify.Driver.Main
import ConLeche.Verify.Cached.MainC

public section

/-!
# The `.olean` input has a model (task #618)

An exit 0 of `--olean -- <root>` checked the records the reader read off the closure of `root`,
prepared with the built-in prelude, with the theorems' values in place
(`Driver.runArgs_olean_accept`).  The fold's accept gives the proofs' model of the environment it
built (`Cached.checkDecls_sound`), every record of the closure's views is stored in it
(`Frontend.Olean.checkDecls_inputStored`), and the bridge carries the model to one of those
records (`isModel_of_envModelM`).
-/

namespace ConLeche

open Frontend

universe w

/-- **An accepted `.olean` run's input has a model**: every exit 0 of `runArgs` at
`--olean --search-path=<dirs> -- <root>` has a model of every record of every constant of the
private views of the closure of `root`'s module (`closureConstants`).  The prelude declarations the
preparation adds are checked with them, and the model is one of the closure's records alone. -/
theorem oleans_isModel (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : Olean.parseModName root = some r)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--search-path=" ++ dirs, "--", root]) fs 0) :
    ∃ model, IsModel V model (Olean.closureConstants (Driver.searchPathOf dirs) fs #[r]) := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨pre, rd, env, -, hrd, hchk⟩ := Driver.runArgs_olean_accept h
  have hroots : (#[root].filterMap Olean.parseModName) = #[r] := by simp [hr]
  rw [hroots] at hrd
  obtain ⟨_, _, hrd⟩ := hrd
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) hchk
  exact ⟨_, isModel_of_envModelM m (Olean.checkDecls_inputStored rfl hrd hchk)⟩

end ConLeche
