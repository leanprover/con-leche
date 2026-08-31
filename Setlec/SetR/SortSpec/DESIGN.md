# The sortSpec pilot

A reduction-free **structural** sort function, and the question of
whether its stability theorems can be proved without the fuel/run
apparatus. This file is the pilot's ledger. Seals append.

## Seal 0 — pre-registration, written BEFORE the definition

Three constraints were fixed by reading the existing ledger, not by
discovering them in a failed proof. Recording them here first so the
pilot cannot later claim them as its own findings.

### (P1) Every `Env`-quantified statement carries `EnvWF`

The ledger's bare-`Env` escape (seal 25, `Step2/LevelsInst.lean`;
repeated at seal 64 — *"this campaign has now built the same witness
twice"*). A stored constant with `levelParams = []` whose stored
expression mentions a level parameter anyway is legal input to a bare
`Env` and impossible for a checked one
(`ConstWF.allLevelParamsDefined`).

**This bites sortSpec harder than it bit its predecessors.** sortSpec
reads codomain sorts *through declared types, level-instantiated*.
That is precisely the operation the escape breaks: instantiation has
nothing to act on, and the escaped parameter is answered straight into
the result. So the semantic-soundness statement (2b) and every
level-eval statement is `EnvWF`-premised **from the start** — not
bare-`Env` first and repaired at the third seal.

### (P2) The δ clause must be stated at EVAL'd levels, never syntactically

The brief scopes the "currency lesson" to the conversion-leaf clause
(2d). **It applies to the δ clause (2c) as well**, and the ledger
already contains the falsifier.

The install cert certifies `Level.isEquiv`, **not** syntactic equality
(`Core.lean:1826` is the only sort-sort comparison in the checker and
it is `isEquiv`, never `≤`). So

    def f : Sort (max u v) := PUnit.{max v u}

installs — `isEquiv (max v u) (max u v) = true` is accepted — and the
stored value's structural sort is `max v u` while the declared
codomain is `max u v`. **Syntactically distinct.** The brief's
proposed δ fact, *"stored value's structural sort = declared
codomain"*, is therefore **false as an equation on level expressions**
and must be stated up to eval at ground `φ` (or up to `isEquiv`).

This is the seed that killed the (F) species (DESIGN "STOP: the
w-general (F) species are REFUTABLE — currency finding").

### (P3) …but the (F) species' *second* seed does NOT transfer

The (F) species died twice over: the `max u v` seed above, **and** a
non-sort seed — proof-irrelevance slack, `P x h₁` vs `P x h₂` — which
is why even the level-equivalence-weakened form
(`∃ w', LevelEq w w' ∧ …`) is false there.

**That second seed does not reach sortSpec, and the reason is
structural.** The (F) species transports a fixed witness expression
`w` through a step on an *arbitrary* subject, so it is sensitive to
the arguments. sortSpec reads the **head's declared codomain,
uniformly in arguments** — the no-cumulativity finding's own phrasing
— so `sortSpec (P x h₁)` and `sortSpec (P x h₂)` are equal *by
construction*: neither proof argument is ever inspected.

Argument-blindness is the pilot's structural advantage over the tier
it hopes to retire. It is also exactly what must be checked, not
assumed, at the ι clause, where the motive *is* an argument.

### (P4) Evidential grade — the inherited lesson is PAPER, not a tombstone

`TypeTransportDeltaF` / `TypeTransportCoreF`
(`Annot/SortCoh/Claims.lean:1193` and neighbours) are `def`s —
hypotheses. Their refutation is recorded in DESIGN as a described,
"arena-realizable" falsifier *checked against construction*. **It was
never mechanized.** There is no `not_typeTransportDeltaF` in the tree;
the `SortCoh/` directory holds no falsifier module.

So (P2) is inherited on a paper argument, at a different evidential
grade from this campaign's ninety-odd mechanized tombstones. The
argument is concrete and I believe it. But if the δ clause turns out
to be where sortSpec's wall stands, **mechanizing that falsifier is
part of the pilot's job** — converting inherited prose into a
tombstone is this campaign's standard, and the pilot should not spend
the paper claim as though it were already machine-checked.

### The enabling theorem, re-verified at current line numbers

DESIGN cites `Core.lean:1550`/`1816`; both had drifted. Re-checked on
the merged tree:

* `Core.lean:1560` — `| .sort u => pure (.sort (.succ u))`, `inferBody`'s
  sort clause.
* `Core.lean:1826` — `| .sort u, .sort v => Level.isEquiv u v`, the only
  sort-sort comparison anywhere. No `≤`. No cumulativity.

The set-theoretic side, by contrast, **is** cumulative
(`SetTheory.univ_mono : m ≤ n → univ m ⊆ˢ univ n`). The two sides
disagree about cumulativity, which is a live hazard for the semantic
clause (2b): membership in `univ` is upward-closed, so an *exact*
sort claim is strictly stronger than what the model forces, and a
`≤` claim would be too weak to feed a checker that compares with
`isEquiv`. The statement must land on the exact sort, and the proof
must not be allowed to leak through `univ_mono`.
