import Setlec.Cached.ParsedC
import Setlec.SetTheory.Core

/-!
# The comparator challenge: setlec never accepts a proof of `Empty`

This file states the project's headline claim in the form
[leanprover/comparator](https://github.com/leanprover/comparator) judges:
a trusted *challenge* (this file, the statement with a `sorry`) and an
untrusted *solution* (`Solution.lean`, the same statement with a proof).
The comparator certifies that the solution proves exactly the statement
below, that its proof uses no axiom beyond `propext`, `Quot.sound` and
`Classical.choice`, and that the Lean kernel accepts it; the
configuration is `comparator.json`.  From the repository root:

    lake env comparator comparator.json

(with `landrun` and a `lean4export` built at this repository's toolchain
in `PATH`, or named by `COMPARATOR_LANDRUN` / `COMPARATOR_LEAN4EXPORT`).

## What this file asks the reader to trust

Only its transitive import closure — the comparator checks that every
constant the statement mentions is *the same* in the solution's
environment, so `Solution.lean` cannot redefine any of it:

* `Setlec.Cached.ParsedC` — **the shipped checker**, up to the driver
  `checkDeclsSPCachedD` that `Main.lean` runs on the parsed stream.  Its
  closure is `Setlec/Kernel/*` and `Setlec/Cached/*` (the term
  representation, the type checker, the basis pins and the direct
  structure install, the cached driver) plus `Setlec/PinGen/Dump.lean`,
  the reader of the committed `Nat`-operation pin file.  No verification
  module is reachable from here: `tests/layering.sh` fences the
  implementation off from `Setlec/{SetTheory,SetModel,Semantics,SetP,Verify}/*`.
* `Setlec.SetTheory.Core` — **the `SetTheory` interface**: ZF minus
  infinity and choice plus an ω-chain of Grothendieck universes, the one
  assumption the consistency proof is parametric in (its consistency
  strength is Lean's own; see the module's header and `README.md`).

Everything else in the repository — the set model, the graded model, the
capstone `Setlec.Cached.no_proof_of_Empty_SPCD_P` in
`Setlec/Verify/Cached/MainC.lean` — is what `Solution.lean` brings, and
is exactly what the comparator re-checks.
-/

universe w

namespace Setlec

set_option warn.sorry false in  -- the challenge states; `Solution.lean` proves
/-- **setlec never accepts a proof of `Empty`.**  If the shipped checker,
at the configuration `cfgP` — what `setlec --verified`, the default mode,
runs — accepts the declaration stream `ds` with resulting environment
`env'`, then no constant stored in `env'` has type `Empty`.

* `V` ranges over every model of the `SetTheory` interface, so the claim
  is consistency relative to ZF⁻ plus an ω-chain of Grothendieck
  universes.
* `emptyName` is the name `Empty`.  The checker installs a constant of
  that name only as its pinned basis block (`Setlec/Kernel/Basis/Empty.lean`),
  the inductive type with no constructors — so a stored constant of type
  `.const emptyName []` would be a proof of the empty type.
* Hypotheses are input-level only: the accepted run and the stored
  constant.  Nothing is assumed about the stream. -/
theorem no_proof_of_Empty (V : Type w) [SetTheory V]
    {ds : List Cached.DeclC} {env' : Env}
    (h : Cached.checkDeclsSPCachedD cfgP ds = .ok env') :
    ∀ c ∈ env'.consts, c.toConstantVal.type = .const emptyName [] → False :=
  sorry

end Setlec
