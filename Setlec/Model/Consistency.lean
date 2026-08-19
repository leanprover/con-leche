import Setlec.Verify.Checker
import Setlec.Model.Interp

/-!
# Consistency of the checker

The headline results:

* `accepted_env_has_model`: every environment accepted by `checkDecls` has a
  set-theoretic model (`EnvModel`).
* `consistency`: no accepted environment contains a constant at all — the
  strongest possible statement while the checker rejects everything.  As the
  checker grows, this will weaken to its final form: no accepted environment
  contains a proof of `Empty`.

Both are parametric in a model `V` of the target set theory.
-/

namespace Setlec

variable (V : Type u) [SetTheory V]

/-- Soundness: every accepted environment has a set-theoretic model. -/
theorem accepted_env_has_model {ds : List Declaration} {env : Env}
    (h : checkDecls ds = .ok env) : Nonempty (EnvModel V env) := by
  obtain ⟨-, rfl⟩ := checkDecls_ok h
  exact ⟨⟨fun _ => SetTheory.empty, by intro c hc; cases hc⟩⟩

/-- Consistency (current, syntactic form): an accepted environment is empty;
in particular it contains no constant of type `Empty`. -/
theorem consistency {ds : List Declaration} {env : Env}
    (h : checkDecls ds = .ok env) : env.consts = [] :=
  congrArg Env.consts (checkDecls_ok h).2

end Setlec
