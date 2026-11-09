module

public import ConLeche.Model.DeclsRun
import ConLeche.Model.Capstone
public section

/-!
# The capstone letters of the fold `checkDecls`

`checkDecls` (`ConLeche/Cached/Decls.lean`) is the declaration fold the binary's driver returns the
accept of (`checkDecls_of_jobs`) and the subject of the main theorem (`ConLeche.model_exists`,
`ConLeche/MainTheorem.lean`).  An accept of the fold is an accepting run, and the run carries the
graded model (`declsRun_model`, `ConLeche/Model/DeclsRun.lean`), so no constant of type `False` (or
`Empty`) is stored in what the fold accepts.  The letters are stated at `.verified`, the mode the model
covers.

**At every pin list** (task #304): the fold's pin-list parameter is
free in all three letters below (`checkDecls .verified pins maxNatSize ds`), because
nothing the model tier consumes reads which list the matched
`Nat.div`/`Nat.mod` variant came from.  The shipped binary's
statements are these at `pins := natOpPinSets`.
-/

namespace ConLeche.Cached

open ConLeche ConLeche.Semantics SetTheory ConLeche.SetModel
open ConLeche.Model (EnvModelM no_constant_of_Empty no_constant_of_False)

universe w
variable {V : Type w} [SetTheory V]
variable {pins : List NatOpPinSet}

/-- **Acceptance**: what the fold accepts carries the model. -/
theorem checkDecls_sound
    {ds : Array Declaration} {env' : Env}
    (h : checkDecls .verified pins maxNatSize ds = .ok env') :
    Nonempty (EnvModelM V env') := by
  obtain ⟨n, fe, r, rfl⟩ := checkDecls_run .verified h
  exact (declsRun_model (V := V) r rfl ConLeche.Model.EnvModelOk.empty).nonempty

/-- **The fold's letter about `Empty`**: the checker, running a
validating mode, never accepts a stream in which some stored constant
has type `Empty`.  Hypotheses are input-level only. -/
theorem no_proof_of_Empty_cached (V : Type w) [SetTheory V]
    {ds : Array Declaration} {env' : Env}
    (h : checkDecls .verified pins maxNatSize ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := checkDecls_sound (V := V) h
  exact fun c hc hty => no_constant_of_Empty mp c hc hty

/-- **The fold's letter about `False`** (task #181): the same letter at
the pinned `False` block — no hypothesis about how the stream declared
`False`.  The step the main corollary rests on is this at `.verified`. -/
theorem no_proof_of_False_cached (V : Type w) [SetTheory V]
    {ds : Array Declaration} {env' : Env}
    (h : checkDecls .verified pins maxNatSize ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := checkDecls_sound (V := V) h
  exact fun c hc hty => no_constant_of_False mp c hc hty

end ConLeche.Cached
