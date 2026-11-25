# The lean4lean-model bridge: Carneiro's hypothesis implies ConLeche's

A separate Lake package (task #204) proving, in Lean, that the
large-cardinal hypothesis of Mario Carneiro's
[lean4lean-model](https://github.com/digama0/lean4lean-model) implies
ConLeche's `SetTheory` interface (`ConLeche/SetTheory/Core.lean`).

It is a **separate package on purpose**: the ConLeche libraries never
acquire a Mathlib dependency (build time, trust surface, layering).  The
main repository's `lake build` and gates do not see this directory.

## Building

```sh
cd bridge/lean4lean-model
lake build          # `lake update` was already run; the manifest is committed.
```

The first build fetches Mathlib's oleans automatically (Mathlib's
post-update hook runs `cache get`; if it did not, run `lake exe cache
get` first).  `lean-toolchain` is a copy of the repository's; Mathlib is
pinned to the matching tag (`v4.36.0`).  The ConLeche modules the bridge
imports are built from `../..` by the path `require`.  Everything lands
in this directory's `.lake` (gitignored).

## Contents

`ConLecheBridge/Carneiro.lean`:

* `ConLecheBridge.OmegaInaccessibles` — **Carneiro's hypothesis, verbatim**
  from `Lean4LeanModel/Consistency.lean`:

  ```lean
  def OmegaInaccessibles : Prop :=
    ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible
  ```

  His file is internal to his repository (which also depends on
  lean4lean), so the definition is transcribed, not imported; the text
  and the Mathlib notions (`Cardinal.IsInaccessible`, `StrictMono`) are
  identical.  His theorem is
  `consistency (_ : OmegaInaccessibles.{u}) {env : VEnv} (_ : env.WF) (U : Nat) :
  ¬ ∃ e, env.HasType U [] e Term.false` (sorried there, pending his
  model construction).

* `isGrothendieck_vonNeumann : κ.IsInaccessible → ConLeche.IsGrothendieck (· ∈ ·) (V_ κ.ord)`
  — Mathlib's von Neumann stage at an inaccessible is an SGA4 Grothendieck
  universe.  Transitivity, pairing, and power-set closure follow from
  Mathlib's `ZFSet.vonNeumann` lemmas; indexed-union closure over an
  internal function graph `g : I → V_ κ.ord` with `I ∈ V_ κ.ord` uses
  strong limitness (`card_lt_of_mem_vonNeumann`: `I.card < κ` via
  `preBeth_lt_of_lt_ord`) and regularity (`κ.ord.cof = κ`) to bound
  `⨆ i ∈ I, (F i).rank + 1 < κ.ord`.

* `setTheoryOfChain κ hmono hinacc : ConLeche.SetTheory ZFSet.{u}` — the
  explicit instance: ZFC⁻ fields from Mathlib (`ZFSet.ext`, `{a, b}`,
  `⋃₀`, `powerset`, `mem_wf`, first-order replacement over `Formula` via
  `image` under `Classical.allZFSetDefinable`, Jech-form `choice` via
  Kuratowski pairs `zfKPair` and `Classical.choose`), `univChain n := V_ (κ n).ord`.

* `carneiro_implies_conleche : OmegaInaccessibles.{u} → Nonempty (Σ V : Type (u + 1), ConLeche.SetTheory V)`.

* Axiom pin (`#guard_msgs in #print axioms`): `propext`,
  `Classical.choice`, `Quot.sound` — nothing else.

Nothing beyond Carneiro's hypothesis was needed: `ℵ₀ < κ` is used only
to make `κ.ord` a limit ordinal (for `powerset y ∈ V_ κ`), regularity
and strong limitness exactly as described above.

### `Nat` denotes the standard naturals

`SetTheory` is first-order, so if it has a model it has one whose `ω` is
not standard (by compactness; not mechanized).  The set theory built
above is not one of them, and in it Lean's `Nat` denotes exactly the
standard naturals.  Three modules, each importing the one before:

`ConLecheBridge/IsModelNat.lean` — about every `SetTheory V` (no
Mathlib), for a stream that declares the prelude's `Nat` and `Eq`
(`DeclaresNat`, `DeclaresEq`):

* `nat_eq_omega` — in every model, what `Nat` denotes is a copy of `V`'s
  own `ω`: the numerals `natOfOmega model i` at `i ∈ ω` (`⟦Nat.succ⟧`
  iterated on `⟦Nat.zero⟧` by `V`'s recursion on `ω`) are exactly its
  members, each once.  Surjectivity is `Nat.rec`'s typing clause at a
  motive into `Prop` (`nat_ind`); injectivity is `Nat.rec`'s two rule
  equations (`natRec_rules`, giving `natSucc_ne_zero` and `natSucc_inj`).
* `nat_standard` — if `ω` is standard (`OmegaStandard`: every member is
  a meta-level `vnat k`), the literals' values `natLitVal model : Nat → V`
  are exactly the members of what `Nat` denotes, each once.
  `omegaStandard_of_nat` is the converse.

`ConLecheBridge/StandardNat.lean`:

* `omegaStandard_chain` — the `ω` of `setTheoryOfChain κ` is standard:
  `ZFSet.sep` separates by an arbitrary Lean predicate, and `ω` is the
  least inductive set.  This is the one second-order step.
* `carneiro_nat_standard` — under `OmegaInaccessibles`, in every model in
  `setTheoryOfCarneiro` of a stream declaring `Nat` and `Eq`,
  `natLitVal model : ℕ → ZFSet` is injective and its values are exactly
  the members of `model natName []`.  It takes `0` to `⟦Nat.zero⟧` and
  `k + 1` to `⟦Nat.succ⟧` at `k`'s value by definition, so it is an
  isomorphism of Lean's `ℕ` with what `Nat` denotes.

`ConLecheBridge/Accepted.lean`:

* `checkDecls_declaresNat` — an accepted stream that stores `Nat`
  declares the prelude's `Nat` (the pin comparison, as
  `Cached.checkDecls_declaresEq` for `Eq`).
* `carneiro_accepted_nat_standard` — under `OmegaInaccessibles`, every
  stream `checkDecls` accepts that stores `Nat` and `Eq` has a model in
  `setTheoryOfCarneiro` in which `Nat` is the standard naturals.

`carneiro_nat_standard`, `nat_eq_omega` and
`carneiro_accepted_nat_standard` carry axiom pins: `propext`,
`Classical.choice`, `Quot.sound`.

"Standard" compares with the `ℕ` of the Lean the theorems are stated in;
there is no other way to say it.

## The converse

With the first-order `SetTheory` the converse is not available:
`ModelExists` is much weaker than `OmegaInaccessibles`.  By the
completeness theorem a model exists as soon as the theory is consistent
(the `ModelExists` docstring in `ConLeche/SetTheory/Core.lean`), and such
a model need not be well-founded or have a standard `ω`, so its
universes are not inaccessible cardinals of the Lean it lives in.

What holds is the statement inside the theory.  In ZFC, a universe in
the four-clause form of `IsGrothendieck` is `∅`, `V_ω`, or `V_κ` with
`κ` strongly inaccessible: the classical characterization of
Grothendieck universes.  (The indexed-union clause is what excludes a
singular strong limit: for `κ = ℶ_ω`, the family `n ↦ V_{ω+n}` is
indexed by `ω ∈ H(κ)` with values in `H(κ)`, and its union `V_{ω+ω}`
has `ℶ_ω = κ` members, so it is not in `H(κ)`.)  Applied to ConLeche's
chain, the theory proves that `univChain (n + 2)` is `V_{κ_n}` for a
strictly increasing sequence of inaccessibles (the bottom two may be
`∅` and `V_ω`), hence "there are `n` inaccessible cardinals" for every
`n`; and each finite part of the theory holds in ZFC with enough
inaccessibles.  So the theory is equiconsistent with ZFC plus `n`
inaccessible cardinals for every `n`, the strength Carneiro's thesis
assigns to Lean.  None of this is mechanized here.

## CI

Not part of the default gates.  `.github/workflows/bridge.yml` builds
it on demand (`workflow_dispatch`) and on pushes touching `bridge/**` or
`ConLeche/SetTheory/Core.lean`.
