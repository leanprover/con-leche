import Setlec.Verify.Cached.MainC

/-!
# The main theorem

The one statement this project exists to make, in its simplest form:

> If the checker, in its default `--verified` mode, accepts a stream of
> declarations, then the resulting environment contains no constant
> whose type is `Empty`.

Everything named in the statement is the shipped article:

* `checkDeclsSPCachedD` is the function `Main.lean` runs on the parsed
  export stream (`Setlec/Cached/ParsedC.lean`), and `cfgOf .verified`
  is the configuration the `--verified` mode (the default) runs it at.
* `DeclC` is a parsed declaration record; `Env` is the environment the
  checker builds; `env.consts` lists the constants it accepted.
* `Empty` is the pinned zero-constructor type (`Setlec/Kernel/Basis/
  Empty.lean`); a stream cannot redefine it, so the conclusion needs no
  hypothesis about the input beyond its acceptance.

`SetTheory V` is the standing parametricity of the consistency
argument: the proof builds a set-theoretic model of the accepted
environment inside any `V` implementing that interface, and the
project's rule is that it never fixes a particular one.  It is not a
hypothesis about the input.

The theorem is a corollary of `Setlec.Cached.no_proof_of_Empty_SPCD_P`
(`Setlec/Verify/Cached/MainC.lean`), which is stated for every
validating mode at once; `no_proof_of_Empty_P` (`Setlec/SetP/FoldP.lean`)
is the same letter for the pure fuelled checker, and
`no_proof_of_Empty_IO` below says the same thing about the
callback-carrying `IO` loop the driver runs.  Its axioms are exactly
`propext`, `Classical.choice` and `Quot.sound` — checked by the pin in
`tests/SetlecTests/Axioms.lean`.
-/

namespace Setlec

open Setlec.Cached (DeclC checkDeclsSPCachedD Callbacks checkDeclsSPCachedM)

/-- **The main theorem.**  An accepted stream never yields a constant of
type `Empty`. -/
theorem no_proof_of_Empty (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDeclsSPCachedD (cfgOf .verified) ds = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const emptyName [] :=
  fun ⟨c, hc, hty⟩ => Cached.no_proof_of_Empty_SPCD_P V rfl accepted c hc hty

/-- **The main theorem, for the loop the binary actually runs.**  The
driver does not call the pure fold directly: it runs
`checkDeclsSPCachedM` in `IO`, which performs the same checks with two
callbacks around each declaration — the progress heartbeat, and
whatever else a lane wants.  A callback sees the fold position and the
declaration record, never the checker's state, and returns `Unit`, so
it cannot influence the verdict; it can only fail, in which case the
run returns no result.  Hence the same conclusion, for **any**
callbacks: an `IO` run that comes back with an accepted environment has
accepted no constant of type `Empty`.

(`Setlec.Cached.checkDeclsSPCachedM_run`: the loop's result *is*
`checkDeclsSPCachedD`'s.  In a lawful monad that is an instance of the
generic bridge `checkDeclsSPCachedM_eq`; `IO` is an `EST` and core
ships no `LawfulMonad` instance for it, so the `IO` case is proved by
the same induction directly.) -/
theorem no_proof_of_Empty_IO (V : Type w) [SetTheory V]
    (cb : Callbacks IO) (ds : List DeclC) (env : Env)
    (ω ω' : Void IO.RealWorld)
    (accepted : checkDeclsSPCachedM cb (cfgOf .verified) ds ω
      = .ok (.ok env) ω') :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const emptyName [] :=
  fun ⟨c, hc, hty⟩ =>
    Cached.no_proof_of_Empty_SPCD_IO V rfl cb accepted c hc hty

end Setlec
