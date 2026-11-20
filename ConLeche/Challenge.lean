module

public import ConLeche.Cached.Decls
public import ConLeche.IsModel
public import ConLeche.Denotes
public import ConLeche.Frontend.Prelude
public import ConLeche.Modular
public section

/-!
# The advertised statements

ConLeche is a proof checker for Lean's export format: hand it the stream
of declarations `lean4export` writes for a Lean development and it
re-checks every one of them from scratch.  This module states the
theorems the project exists to prove and leaves them `sorry`; the
proofs are in `ConLeche/MainTheorem.lean`.  Nothing imports this file.

> **Main theorem.**  If the checker accepts a stream of declarations,
> the stream has a model in every set theory `V`: one set per constant
> and list of universe levels, under which every declaration holds —
> every constant, every theorem included, is a member of what its type
> denotes, every definition is what its value denotes, and every
> recursor computes by its rules.
>
> **Main corollary.**  Hence an accepted stream holds no constant of
> type `False`.

The corollary follows from the theorem in two steps.  The constant —
a theorem, an axiom, an opaque constant, a definition, or a hole read
as the axiom of its statement — is stored by the checker under its
own name with its declared type, so its type's `False` is stored too,
and the checker stores at that name only the prelude's `False`: the
stream declares it.  In a model of such a stream `False` denotes the
empty set, which has no members, while the constant is a member of
what its type denotes.  An accepted stream is therefore not a proof of
a contradiction, and more: every statement it proves is true in the
model.  Definitional equalities need no
clause of their own — a reader who cares that a definition unfolds as
declared states that as a theorem proved by `rfl`, and `Eq`, declared
as the prelude's, denotes equality, which turns that theorem into the
equation of the two sides' denotations.

* `checkDecls` is the shipped checking function — the one the
  `con-leche` binary runs on the parsed stream; `.verified` is its
  default `--verified` mode.
* `ds : Array Declaration` is the parsed stream; `(checkDecls … ds).isOk`
  says the checker accepted it.
* `pins : List NatOpPinSet` is the list of pin variants the fold's
  `Nat.div`/`Nat.mod` install gate tries — the one large constant the
  checker carries, and the statements quantify over it: consistency
  holds at EVERY list, the empty one included (under which a stream
  that declares `Nat.div` simply declines).  The shipped `con-leche`
  binary runs the fold at `ConLeche.natOpPinSets`, the variants this
  toolchain committed.
* `maxNatSize : Nat` is the largest `Nat` numeral, in bytes, the fold
  takes in or computes; a larger one makes it reject, as the official
  kernel does.  The statements hold at every `maxNatSize`.  The shipped
  binary runs the fold at the official default, 128 MiB, unless
  `--max-nat-size` sets another.
* `IsModel V model C` (`ConLeche/IsModel.lean`) says that `model` is
  a model of the constants `C` in `V` — here `constantsOf ds`, every
  constant of every declaration of `ds`, as a membership predicate — :
  every constant holds, its terms read by `Expr.eval`, a total function
  from a checker term to a set.  `model : Name → List Nat → V` is the
  set a constant denotes at the values of its universe levels, given
  positionally.  That file is the whole of what the main theorem's
  meaning rests on beyond the checker's own data types; it reads the
  INPUT, nothing of the environment the checker builds.  Nothing in
  it treats `False` or `Eq` specially; the checker accepts a stream
  declaring them only as the prelude does, whose own clauses make
  `False` empty and `Eq` equality in every model — which is what the
  corollary uses.
* `SetTheory V` is not a hypothesis about the input: the proof works
  for every `V` implementing that interface and never fixes one.
* `c.type = .const falseName []` says the constant `c`'s type is the
  constant `False` (`ConstantInfo.type`, `ConLeche/IsModel.lean`).
* `False` is pinned: a stream that declares `False` or `False.rec`
  other than as the prelude's is rejected, so the corollary needs no
  hypothesis about the input beyond the constant.
* The modular statements below are still over `Model V env`
  (`ConLeche/Denotes.lean`), a model of the environment a module's
  checks build, read by the relation `Denotes`.

Both statements are about the checking function, not
the process, and `--trusted` mode is outside both.  See README.md.

> **Modular theorem.**  A development of modules every one of which
> passes the local checks has a compatible family of models of the
> modules' own environments: two modules that store a name under one
> key give it one value, and every proof the point.

* `dev : Nat → Modular.Module` is the development (`ConLeche/Modular.lean`):
  per module its context records, its own records, and for every name
  the module it is read from and its key (its home module, or for a
  proof its statement).  `LocalOk .verified pins maxNatSize dev j` are module `j`'s
  local checks: its interface presents its own records, and as an
  importer its context is made of presented records read as their
  homes read them, its own records are accepted from it by the fold's
  step, and its proof flags are proofs.

The statements about the binary's runs are in `ConLeche/MainTheorem.lean`, under the assumption
`ConLeche/Frontend/CheckerIO.lean` states: a run's file operations answer on one snapshot of the
files.  A statement about several runs (the import graph check, `--check-graph`, and the
per-module checks of the modules it numbers) assumes one snapshot for all of them: the files do
not change while the runs read them.
-/

namespace ConLeche

open SetTheory
open ConLeche.Cached (checkDecls checkChallenge)

universe w

/-- **The main theorem.**  Every stream the checker accepts has a
model in every set theory. -/
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration)
    (accepted : (checkDecls .verified pins maxNatSize ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) :=
  sorry

/-- **The main theorem, with a solution.**  A challenge stream the checker
accepts with its axioms justified by a solution stream (`checkChallenge`),
the solution itself accepted, has a model in every set theory. -/
theorem solution_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dsS ds : Array Declaration)
    (solution : (checkDecls .verified pins maxNatSize dsS).isOk)
    (challenge : (checkChallenge .verified pins maxNatSize dsS ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) :=
  sorry

/-- **The main corollary.**  An accepted stream holds no constant of type `False`. -/
theorem no_False_declaration (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration)
    (accepted : (checkDecls .verified pins maxNatSize ds).isOk) {c : ConstantInfo}
    (hc : c ∈ constantsOf ds.toList) (hty : c.type = .const falseName []) : False :=
  sorry

open Modular in
/-- **The modular theorem.** -/
theorem modular_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dev : Nat → Modular.Module) (i : Nat)
    (hok : ∀ j ≤ i, Modular.LocalOk .verified pins maxNatSize dev j) :
    ∃ model : Nat → Name → List Nat → V,
      (∀ j ≤ i, IsModel V (model j) (· ∈ constantsOf (dev j).decls)) ∧
      ∀ j ≤ i, ∀ n, ((dev j).context.find? n).isSome = true →
        (dev j).src n ≤ i ∧ model j n = model ((dev j).src n) n :=
  sorry

end ConLeche
