module

public import ConLeche.Verify.Cached.InstalledC
public section

/-!
# The main theorem

A fully checked environment contains no constant of type `False`.

* `FullyChecked mode ds` (`ConLeche/Cached/Installed.lean`) is the type
  the binary's driver returns: an environment **properly installed**
  from the parsed declarations `ds` — the chain of accepting install
  steps that built it — in which **every recorded declaration has been
  checked** against the prefix of the environment it was installed at.
  Whoever holds a value of that type holds the evidence; the theorem is
  stated on the type and says nothing about the loop that produced the
  value — `Main.lean`'s loop, with or without its progress heartbeat,
  or any later one.
* `DeclC` is a parsed declaration; `Env` is the environment the checker
  builds; `env.consts` are the constants it accepted; `.verified` is the
  default mode.
* `False` is built in: the checker installs it from its own pin, and a
  stream that declares `False` or `False.rec` differently is rejected.
* `SetTheory V` is the set theory the model lives in; the proof works
  for any `V` implementing that interface.

The ordinary fold `checkDecls` (`ConLeche/Cached/ParsedC.lean`) — the
binary's driver until task #253, and still the pure reference fold the
agreement floor is stated about — keeps its own letter,
`no_proof_of_False_fold`.

The axioms used are exactly `propext`, `Classical.choice` and
`Quot.sound` (`tests/ConLecheTests/Axioms.lean`).
-/

namespace ConLeche

open ConLeche.Cached (DeclC checkDecls FullyChecked)

/-- **The main theorem**: a fully checked environment, in the verified
mode, contains no constant of type `False`. -/
theorem no_proof_of_False (V : Type w) [SetTheory V]
    (ds : List DeclC) (fc : FullyChecked .verified ds) :
    ¬ ∃ c ∈ fc.env.consts, c.toConstantVal.type = .const falseName [] :=
  fun ⟨c, hc, hty⟩ => Cached.no_proof_of_False_checked V rfl fc c hc hty

/-- The ordinary fold's letter: what `checkDecls` accepts contains no
constant of type `False`. -/
theorem no_proof_of_False_fold (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDecls .verified ds = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const falseName [] :=
  fun ⟨c, hc, hty⟩ => Cached.no_proof_of_False_cached V rfl accepted c hc hty

end ConLeche
