import ConLeche.Verify.Cached.MainC

/-!
# The main theorem

If the checker, in its default `--verified` mode, accepts a stream of
declarations, then the resulting environment contains no constant of
type `False`.

* `checkDeclsSPCachedD` is the function the `con-leche` binary runs on the
  parsed export stream; `.verified` is the default mode.
* `DeclC` is a parsed declaration; `Env` is the environment the checker
  builds; `env.consts` are the constants it accepted.
* `False` is built in: the checker installs it from its own pin, and a
  stream that declares `False` or `False.rec` differently is rejected.
* `SetTheory V` is the set theory the model lives in; the proof works
  for any `V` implementing that interface.

The axioms used are exactly `propext`, `Classical.choice` and
`Quot.sound` (`tests/ConLecheTests/Axioms.lean`).
-/

namespace ConLeche

open ConLeche.Cached (DeclC checkDeclsSPCachedD)

theorem no_proof_of_False (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDeclsSPCachedD .verified ds = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const falseName [] :=
  fun ⟨c, hc, hty⟩ => Cached.no_proof_of_False_SPCD_P V rfl accepted c hc hty

end ConLeche
