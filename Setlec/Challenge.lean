import Setlec.Cached.ParsedC
import Setlec.Kernel.Basis.Names
import Setlec.SetTheory.Core

/-!
# The advertised statement (Palomar / Comparator challenge module)

This module is the **small readable surface** a reader should audit
before believing anything else in this repository.  It states the one
theorem the project exists to prove, and proves it with `sorry`.  The
proof lives in `Setlec/MainTheorem.lean` (the Comparator *solution*
module), on top of the whole verification tower; nothing in the tree
imports this file, and it is not part of any default build target.

## What the theorem says, in words

Setlec is a **proof checker for Lean's export format**.  You hand it
the stream of declarations that `lean4export` writes out for a Lean
development, and it re-checks every one of them from scratch — types,
definitional unfolding, inductive types, recursors, the lot — and
either accepts the stream or rejects it.  The claim below is the
soundness claim you want from such a checker:

> **If the checker accepts a stream, the environment it built contains
> no constant whose type is `False`.**

That is, an accepted stream is not a proof of a contradiction: the
checker cannot be talked into signing off on `theorem oops : False`.

## What each name in the statement is

* `checkDeclsSPCachedD` is the *shipped* checking function — the very
  one `Main.lean` folds over the parsed export stream (it is defined in
  `Setlec/Cached/ParsedC.lean`, an implementation module, not a
  proof-friendly re-statement of one).  `cfgOf .verified` is the
  configuration it runs at in the binary's default `--verified` mode.
* `ds : List DeclC` is the parsed stream: `DeclC` is one parsed
  declaration record.  `Env` is the environment the checker builds as
  it goes, and `env.consts` lists the constants it has accepted.
  `.ok env` is therefore literally "the checker accepted `ds`, and this
  is what it accepted".
* `c.toConstantVal.type = .const falseName []` says the constant `c`
  is stated at the type `False` — i.e. `c` is a proof of `False`.
* `False` is a **pinned** zero-constructor type
  (`Setlec/Kernel/Basis/False.lean`): the checker installs the
  toolchain's `False` block from its own pin, and a stream that tries
  to declare `False` or `False.rec` any other way is rejected outright.
  So `falseName` really does denote falsehood here, and the conclusion
  needs no hypothesis about the input beyond the fact that it was
  accepted.
* `SetTheory V` is **not** a hypothesis about the input.  It is the
  standing parametricity of the consistency argument: the proof builds
  a set-theoretic model of the accepted environment inside an arbitrary
  type `V` implementing that interface (a ZF⁻-style set theory with an
  ω-chain of universes), and the project's rule is that it never fixes
  a particular one.  Instantiating `V` is what turns the theorem into a
  consistency statement relative to a concrete set theory.

## What it does not say

The statement is about the checking function, not about the process:
reading bytes off disk and parsing them into `List DeclC` is outside
it, as is the `--trusted` mode.  See `formalization.yaml` for the full
list of limitations.
-/

namespace Setlec

open Setlec.Cached (DeclC checkDeclsSPCachedD)

/-- **The main theorem.**  An accepted stream never yields a constant of
type `False`. -/
theorem no_proof_of_False (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDeclsSPCachedD (cfgOf .verified) ds = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const falseName [] :=
  sorry

end Setlec
