module

public import ConLeche.IsModel
public import ConLeche.Cached.Decls
import ConLeche.Model.IsModelBridge
import ConLeche.Model.Solution
import ConLeche.Verify.Cached.MainC

public section

/-!
# The pure checker's main theorems

The checking function on parsed declarations, which every run of the binary calls: what
`checkDecls` accepts has a model in every set theory, and so has what `checkChallenge` accepts
with an accepted solution's declarations justifying the challenge's axioms.  The fold's accept
gives the proofs' model of the environment it built (`Cached.checkDecls_sound`), every record is
stored in it as it says (`Cached.checkDecls_recordsStored`), and the bridge carries the model to
the records (`isModel_of_envModelM`); with a solution, `Model.Solution.challenge_isModel`.
The theorems about the runs are in `ConLeche/MainTheorem.lean`.
-/

namespace ConLeche

open SetTheory
open ConLeche.Cached (checkDecls checkChallenge)

universe w

/-- **Every stream the checker accepts has a model in every set theory.** -/
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration)
    (accepted : (checkDecls .verified pins maxNatSize ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) := by
  cases h : checkDecls .verified pins maxNatSize ds with
  | error e => rw [h] at accepted; cases accepted
  | ok env =>
    obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) h
    exact ⟨_, isModel_of_envModelM m (Cached.checkDecls_recordsStored h)⟩

/-- **A challenge stream accepted with its axioms justified by an accepted solution stream has
a model in every set theory.** -/
theorem solution_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dsS ds : Array Declaration)
    (solution : (checkDecls .verified pins maxNatSize dsS).isOk)
    (challenge : (checkChallenge .verified pins maxNatSize dsS ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) :=
  Model.Solution.challenge_isModel solution challenge

end ConLeche
