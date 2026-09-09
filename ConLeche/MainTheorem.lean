module

public import ConLeche.Verify.Cached.MainC
public section

/-!
# The main theorem

What the checker accepts contains no constant of type `False`.

* `checkDecls` (`ConLeche/Cached/Installed.lean`) is the declaration
  fold: it installs every parsed declaration — a definition, theorem
  or opaque annotated and pushed with its check recorded, everything
  else checked in full as it is installed — and then checks every
  recorded declaration against the prefix of the environment it was
  installed at.  The binary's driver (`Main.lean`) runs this fold with a
  heartbeat between the steps and returns its environment together
  with the proof that `checkDecls` returns it
  (`Cached.fullyChecked_checkDecls`), so the success line is printed
  from an accept of `checkDecls` and from nothing else.
* `DeclC` is a parsed declaration; `Env` is the environment the checker
  builds; `env.consts` are the constants it accepted; `.verified` is the
  default mode.
* `False` is built in: the checker installs it from its own pin, and a
  stream that declares `False` or `False.rec` differently is rejected.
* `SetTheory V` is the set theory the model lives in; the proof works
  for any `V` implementing that interface.

The axioms used are exactly `propext`, `Classical.choice` and
`Quot.sound` (`tests/ConLecheTests/Axioms.lean`).
-/

namespace ConLeche

open ConLeche.Cached (DeclC checkDecls)

/-- **The main theorem**: if `checkDecls`, in the verified mode, accepts
the declarations `ds` with the environment `env`, then `env` contains
no constant of type `False`. -/
theorem no_proof_of_False (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDecls .verified ds = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const falseName [] :=
  fun ⟨c, hc, hty⟩ => Cached.no_proof_of_False_cached V rfl accepted c hc hty

end ConLeche
