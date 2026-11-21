module

import ConLeche.Model.IsModelBridge
import ConLeche.Model.Solution
import ConLeche.Verify.Cached.MainC
public import ConLeche.Verify.FalseRuns
public import ConLeche.Verify.Driver.CompareJsonRun
import ConLeche.Semantics.NoFalse
import ConLeche.Verify.IsModelRecords
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Driver.Main

public section

/-!
# A lean4export file's records have a model

The proofs `ConLeche/MainTheorem.lean` cites for its theorems about lean4export files:

* `checkDecls_isModel`: the fold's accept gives the proofs' model of the environment it built
  (`Cached.checkDecls_sound`), every record is stored in it as it says
  (`Cached.checkDecls_recordsStored`), and the bridge carries the model to the records
  (`isModel_of_envModelM`);
* `json_isModel`: a run that accepts a file checked the parsed records prepared with the
  built-in prelude (`Driver.runArgs_accept`); they have a model, so the file's own records do;
* `json_no_False`: a run that accepts a `jsonWithTheoremFalse` file accepted a stream with a
  constant of type `False` (`Driver.runArgs_json_false`), whose model makes `False` empty;
* `compare_json_isModel`: an accepted `--compare` checked the solution file in full and the
  challenge file with its axioms justified by it (`Driver.runArgs_compare_json_accept`), and the
  challenge's prepared records have a model (`Model.Solution.challenge_isModel`), so its own
  records do.
-/

namespace ConLeche

open SetTheory Frontend

universe w

/-- **An accepted stream has a model.** -/
theorem checkDecls_isModel (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration)
    (accepted : (Cached.checkDecls .verified pins maxNatSize ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) := by
  cases h : Cached.checkDecls .verified pins maxNatSize ds with
  | error e => rw [h] at accepted; cases accepted
  | ok env =>
    obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) h
    exact ⟨_, isModel_of_envModelM m (Cached.checkDecls_recordsStored h)⟩

/-- The records of `ds` are among those of `ds` prepared with the built-in prelude. -/
theorem constantsOf_preparePrelude {pre : PreludeIx} {ds : Array Declaration} {c : ConstantInfo}
    (hc : c ∈ constantsOf ds.toList) : c ∈ constantsOf (preparePrelude pre ds).toList := by
  obtain ⟨d, hd, hc⟩ := mem_constantsOf.1 hc
  exact mem_constantsOf.2 ⟨d, Array.mem_toList_iff.2
    (Frontend.mem_preparePrelude (pre := pre) (Array.mem_toList_iff.1 hd)), hc⟩

/-- **An accepted file's records have a model.** -/
theorem json_isModel (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b) :
    ∃ r, parseChunks [b] = .ok r ∧ ∃ model, IsModel V model (· ∈ constantsOf r.decls.toList) := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨pre, b', r, env, -, hb', hp, hc⟩ := Driver.runArgs_accept h
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨model, hm⟩ := checkDecls_isModel V _ _ _ (by rw [hc]; rfl)
  exact ⟨r, hp, model, hm.anti fun _ => constantsOf_preparePrelude⟩

/-- **No exit 0 of `-- <file>` reads a `jsonWithTheoremFalse` file.** -/
theorem json_no_False (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b)
    (hF : jsonWithTheoremFalse [b]) : False := by
  obtain ⟨ds, ha, c, hc, hty⟩ := Driver.runArgs_json_false h hb hF
  exact IsModel.no_False_constant (checkDecls_isModel V _ _ ds ha)
    (checkDecls_declaresFalse_of_constant ha hc hty) hc hty

/-- **An accepted JSON comparison's challenge has a model.** -/
theorem compare_json_isModel (V : Type w) [SetTheory V] {c s : String} {fs : FS}
    (h : ModelIO.CanGive (Driver.runArgs ["--compare", "--", c, s]) fs 0) :
    ∃ bC rC, fs.file c = some bC ∧ parseChunks [bC] = .ok rC ∧
      ∃ model, IsModel V model (· ∈ constantsOf rC.decls.toList) := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨pre, bC, rC, bS, rS, env, -, hbC, hpC, -, -, hS, hC⟩ :=
    Driver.runArgs_compare_json_accept h
  obtain ⟨model, hm⟩ :=
    Model.Solution.challenge_isModel (V := V) (by rw [hS]; rfl) (by rw [hC]; rfl)
  exact ⟨bC, rC, hbC, hpC, model, hm.anti fun _ => constantsOf_preparePrelude⟩

end ConLeche
