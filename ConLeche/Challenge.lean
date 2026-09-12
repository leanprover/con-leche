module

public import ConLeche.Cached.Installed
public import ConLeche.Denotes
public section

/-!
# The advertised statements

ConLeche is a proof checker for Lean's export format: hand it the stream
of declarations `lean4export` writes for a Lean development and it
re-checks every one of them from scratch.  This module states the
two theorems the project exists to prove and leaves them `sorry`; the
proofs are in `ConLeche/MainTheorem.lean`.  Nothing imports this file.

> **Main theorem.**  If the checker accepts a stream, the environment
> it built has a model in every set theory `V`: one set per constant
> under which every constant — every theorem included — is a member
> of its type, `False` is empty, and `Eq` is set equality.
>
> **Main corollary.**  Hence that environment contains no constant
> whose type is `False`.

The second is a corollary of the first: `False` denotes the empty set,
which has no members.  An accepted stream is therefore not a proof of
a contradiction, and more: every statement it proves is true in the
model.  Definitional equalities need no clause of their own — a reader
who cares that a definition unfolds as declared states that as a
theorem proved by `rfl`, and `Model`'s `eq_equality` field, which says
the built-in `Eq` denotes set equality, turns that theorem into the
equation of the two sides' denotations.

* `checkDecls` is the shipped checking function — the one the
  `con-leche` binary runs on the parsed stream; `.verified` is its
  default `--verified` mode.
* `ds : List DeclC` is the parsed stream, `Env` the environment the
  checker builds, `env.consts` the constants it accepted; `.ok env`
  says the checker accepted `ds` and this is what it accepted.
* `Model V env` (`ConLeche/Denotes.lean`) is a model of `env` in `V`,
  built on `Denotes`, the reading of a checker term as a set; that
  file is the whole of what the main theorem's meaning rests on beyond
  the checker's own data types.  It also proves `Denotes_functional`:
  a term has at most one denotation, so where `Model` says a stored
  constant is a member of *some* denotation of its type, it is saying
  so of *the* denotation.
* `SetTheory V` is not a hypothesis about the input: the proof works
  for every `V` implementing that interface and never fixes one.
* `c.toConstantVal.type = .const falseName []` says `c` is a proof of
  `False`.  `False` is built in: the checker installs it from its own
  pin, and a stream that declares `False` or `False.rec` differently is
  rejected, so the conclusion needs no hypothesis about the input
  beyond its acceptance.

The statements are about the checking function, not the process:
reading and parsing the bytes is outside them, as is the `--trusted`
mode.  See README.md.
-/

namespace ConLeche

open SetTheory
open ConLeche.Cached (DeclC ExprC checkDecls)

universe w

/-- **The main theorem.**  Every environment the checker accepts has a
model in every set theory. -/
theorem model_exists (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDecls .verified ds = .ok env) :
    Nonempty (Model V env) :=
  sorry

/-- **The main corollary.**  An accepted stream never yields a
constant of type `False`. -/
theorem no_proof_of_False (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDecls .verified ds = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const falseName [] :=
  sorry

/-- **The main corollary, at the stream.**  A stream that declares a
theorem of type `False` is never accepted. -/
theorem no_False_theorem_accepted (V : Type w) [SetTheory V]
    (ds : List DeclC) (cv : ConstantVal) (v : ExprC)
    (hmem : DeclC.thmDecl cv v ∈ ds) (hty : cv.type = .const falseName []) :
    ∀ env, checkDecls .verified ds ≠ .ok env :=
  sorry

end ConLeche
