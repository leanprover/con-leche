import Lech.Cached.ParsedC
import Lech.Kernel.Basis.Names
import Lech.SetTheory.Core

/-!
# The advertised statement

Lech is a proof checker for Lean's export format: hand it the stream
of declarations `lean4export` writes for a Lean development and it
re-checks every one of them from scratch.  This module states the
theorem the project exists to prove and leaves it `sorry`; the proof
is in `Lech/MainTheorem.lean`.  Nothing imports this file.

> If the checker accepts a stream, the environment it built contains no
> constant whose type is `False`.

An accepted stream is therefore not a proof of a contradiction: the
checker cannot be talked into signing off on `theorem oops : False`.

* `checkDeclsSPCachedD` is the shipped checking function — the one the
  `lech` binary runs on the parsed stream; `.verified` is its
  default `--verified` mode.
* `ds : List DeclC` is the parsed stream, `Env` the environment the
  checker builds, `env.consts` the constants it accepted; `.ok env`
  says the checker accepted `ds` and this is what it accepted.
* `c.toConstantVal.type = .const falseName []` says `c` is a proof of
  `False`.  `False` is built in: the checker installs it from its own
  pin, and a stream that declares `False` or `False.rec` differently is
  rejected, so the conclusion needs no hypothesis about the input
  beyond its acceptance.
* `SetTheory V` is not a hypothesis about the input: the proof builds a
  set-theoretic model of the accepted environment in any `V`
  implementing that interface, and never fixes one.

The statement is about the checking function, not the process: reading
and parsing the bytes is outside it, as is the `--trusted` mode.  See
README.md.
-/

namespace Lech

open Lech.Cached (DeclC checkDeclsSPCachedD)

/-- **The main theorem.**  An accepted stream never yields a constant of
type `False`. -/
theorem no_proof_of_False (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDeclsSPCachedD .verified ds = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const falseName [] :=
  sorry

end Lech
