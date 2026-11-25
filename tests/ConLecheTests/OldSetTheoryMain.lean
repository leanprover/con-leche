module

public import ConLeche.MainTheorem
public import ConLecheTests.SetTheoryFO

public section

/-!
# The main theorems, from the old second-order set theory

`setTheoryOfSecondOrder` (`tests/ConLecheTests/SetTheoryFO.lean`) turns an instance of the old
second-order class, `ConLecheOld.SetTheory` (`tests/ConLecheTests/OldSetTheory.lean`), into
one of the current first-order class.  The main theorems are stated for every instance of the
current class, so they hold at that one.  The two below say so for the lean4export run: from
any model of the old set theory, an accepted file has a model, and no accepted file declares a
theorem of type `False`.  The other runs' theorems instantiate the same way.
-/

namespace ConLecheTests.SetTheoryFO

open ConLeche ConLeche.Frontend

universe u

/-- **From a model of the old second-order set theory, an accepted file has a model**:
`main_json_model` at the first-order instance the old one induces. -/
theorem main_json_model_of_old {V : Type u} (S : ConLecheOld.SetTheory V) {file : String}
    {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b) :
    ∃ r, parseChunks [b] = .ok r ∧
      ∃ model, @IsModel V (setTheoryOfSecondOrder S) model (· ∈ constantsOf r.decls.toList) :=
  @main_json_model V (setTheoryOfSecondOrder S) file fs b h hb

/-- **From a model of the old second-order set theory, no accepted file declares a theorem of
type `False`**: the old model gives `ModelExists`, which is all `main_no_False` assumes. -/
theorem main_no_False_of_old {V : Type u} (S : ConLecheOld.SetTheory V) {file : String}
    {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b)
    (hF : jsonWithTheoremFalse [b]) : False :=
  main_no_False ⟨⟨V, setTheoryOfSecondOrder S⟩⟩ h hb hF

/--
info: 'ConLecheTests.SetTheoryFO.main_json_model_of_old' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms main_json_model_of_old

/--
info: 'ConLecheTests.SetTheoryFO.main_no_False_of_old' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms main_no_False_of_old

end ConLecheTests.SetTheoryFO
