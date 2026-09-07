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
pinned to the matching tag (`v4.33.0`).  `ConLeche.SetTheory.Core` is built
from `../..` by the path `require`.  Everything lands in this
directory's `.lake` (gitignored).

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
  ¬ ∃ e, env.HasType U [] e VExpr.false` (sorried there, pending his
  model construction).

* `isTGUniverse_vonNeumann : κ.IsInaccessible → ConLeche.IsTGUniverse (· ∈ ·) (V_ κ.ord)`
  — Mathlib's von Neumann stage at an inaccessible is a Grothendieck
  universe in Tarski's form.  Transitivity, subset- and power-set
  closure are Mathlib's `ZFSet.vonNeumann` lemmas; Tarski's cardinality
  clause is the work: a subset `y ⊆ V_ κ` has rank `≤ κ`; if `< κ` it
  is a member (`mem_vonNeumann`); otherwise `|y| ≥ κ` by **regularity**
  (`rank_lt_ord_of_card_lt`: fewer than `κ` ordinals below `κ` are
  bounded), and `|V_ κ| = ℶ_κ = κ` by **strong limitness**
  (`card_vonNeumann_ord`), so `|y| = |V_ κ|` and a bijection exists.

* `setTheoryOfChain κ hmono hinacc : ConLeche.SetTheory ZFSet.{u}` — the
  explicit instance: ZF⁻ fields from Mathlib (`ZFSet.ext`, `{a, b}`,
  `⋃₀`, `powerset`, `mem_wf`, `image` under
  `Classical.allZFSetDefinable`), `univChain n := V_ (κ n).ord`.

* `carneiro_implies_con-leche : OmegaInaccessibles.{u} → Nonempty (Σ V : Type (u + 1), ConLeche.SetTheory V)`.

* Axiom pin (`#guard_msgs in #print axioms`): `propext`,
  `Classical.choice`, `Quot.sound` — nothing else.

Nothing beyond Carneiro's hypothesis was needed: `ℵ₀ < κ` is used only
to make `κ.ord` a limit ordinal (for `powerset y ∈ V_ κ`), regularity
and strong limitness exactly as described above.

## The converse

The briefing for this task expected the converse to fail, with `H(κ)`
for a *singular* strong-limit `κ` (hereditarily `< κ`-sized sets) as a
Tarski-form universe that is not a `V_λ` for `λ` inaccessible.  **That
countermodel is wrong.**  Take `κ = ℶ_ω` and `y = {V_{ω+n} | n < ω}`:
every member is in `H(κ)` (`|TC(V_{ω+n})| = ℶ_n < κ`), so `y ⊆ H(κ)`;
but `|TC(y)| = ℶ_ω = κ`, so `y ∉ H(κ)`; and `|y| = ℵ₀ ≠ κ = |H(κ)|`, so
`y` is not equinumerous with `H(κ)`.  Tarski's clause fails.

In fact, over any model with the ambient cardinal arithmetic, a
transitive Tarski-form universe `U` is `∅`, `V_ω`, or `V_κ` with `κ`
strongly inaccessible.  Sketch, with `κ := |U|`: `U` is closed under
power sets of members, so every member has size `< κ` and `κ` is a
strong limit; the ordinals in `U` are exactly those `< κ`; and `κ` is
regular because `U` contains **every** subset of itself of size `< κ`
(Tarski's clause), of which there are `κ^{<κ}` many, while
`κ^{<κ} ≥ κ^{cof κ} > κ` for singular `κ` (König).  Hence
`U = V_κ`.  Applied to ConLeche's chain, `univChain (n + 2)` is `V_{κ_n}` for
a strictly increasing sequence of inaccessibles (the bottom two may be
`∅` and `V_ω`), so the two hypotheses are **equivalent up to that
shift**.  The converse is not mechanized here (the counting argument
needs a lower bound on the number of small subsets that Mathlib does
not provide off the shelf); it is recorded in `DESIGN.md` as a
follow-up.

## CI

Not part of the default gates.  `.github/workflows/bridge.yml` builds
it on demand (`workflow_dispatch`) and on pushes touching `bridge/**` or
`ConLeche/SetTheory/Core.lean`.
