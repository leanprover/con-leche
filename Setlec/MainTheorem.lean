import Setlec.Verify.Cached.MainC

/-!
# The main theorem

The one statement this project exists to make, in its simplest form:

> If the checker, in its default `--verified` mode, accepts a stream of
> declarations, then the resulting environment contains no constant
> whose type is `False`.

Everything named in the statement is the shipped article:

* `checkDeclsSPCachedD` is the function `Main.lean` runs on the parsed
  export stream (`Setlec/Cached/ParsedC.lean`), and `cfgOf .verified`
  is the configuration the `--verified` mode (the default) runs it at.
* `DeclC` is a parsed declaration record; `Env` is the environment the
  checker builds; `env.consts` lists the constants it accepted.
* `False` is a pinned zero-constructor type (`Setlec/Kernel/Basis/
  False.lean`, task #181): the checker installs the toolchain's `False`
  block from its own pin and a stream cannot redefine the name, so the
  conclusion needs no hypothesis about the input beyond its acceptance.
  `Empty` (`Setlec/Kernel/Basis/Empty.lean`) is pinned the same way,
  and the second theorem is the same statement about it.

`SetTheory V` is the standing parametricity of the consistency
argument: the proof builds a set-theoretic model of the accepted
environment inside any `V` implementing that interface, and the
project's rule is that it never fixes a particular one.  It is not a
hypothesis about the input.

The theorems are corollaries of `Setlec.Cached.no_proof_of_False_SPCD_P`
and `no_proof_of_Empty_SPCD_P` (`Setlec/Verify/Cached/MainC.lean`),
which are stated for every validating mode at once; `no_proof_of_False_P`
and `no_proof_of_Empty_P` (`Setlec/SetP/FoldP.lean`) are the same
letters for the pure fuelled checker.  Their axioms are exactly
`propext`, `Classical.choice` and `Quot.sound` — checked by the pin in
`tests/SetlecTests/Axioms.lean`.
-/

namespace Setlec

open Setlec.Cached (DeclC checkDeclsSPCachedD)

/-- **The main theorem.**  An accepted stream never yields a constant of
type `False`. -/
theorem no_proof_of_False (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDeclsSPCachedD (cfgOf .verified) ds = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const falseName [] :=
  fun ⟨c, hc, hty⟩ => Cached.no_proof_of_False_SPCD_P V rfl accepted c hc hty

/-- The same statement about the pinned `Empty`. -/
theorem no_proof_of_Empty (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDeclsSPCachedD (cfgOf .verified) ds = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const emptyName [] :=
  fun ⟨c, hc, hty⟩ => Cached.no_proof_of_Empty_SPCD_P V rfl accepted c hc hty

end Setlec
