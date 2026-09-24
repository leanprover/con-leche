module

public import ConLeche.Kernel.Inductives.BlockParts

@[expose] public section

/-!
# The recursor stage's shared pieces (the uniform route)

The uniform route CHECKS the stream's recursors instead of generating
them (charter item 5); the check itself is `targetRecCheck`
(`ConLeche/Kernel/Inductives/RecCheck.lean`, classification-free
primitive recursion).  What lives here is what that check and the
conformance check share:

* the ELIMINATION guard, official's `elim_only_at_universe_zero` said
  declaratively (`blockLargeElimAllowed`): unless the block's sort is
  never `0`, a large eliminator needs the generated large SHAPE (a
  fresh elimination level parameter, `BlockShape.large`), ONE member,
  no container occurrence and at most one constructor — and when it is
  not allowed, the recursor's CONCLUSION must be a proposition;
* the frames' variable numbering (below);
* `nameIdxOf?`, the callee lookup the check's call recogniser uses.
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

/-! ## The frames

A rule of `rec_m` binds `rP` prefix variables and then the
constructor's `nF` fields, so under `d` further binders inside its
body

* `x_l` (`l < rP`) is `bvar (d + nF + rP - 1 - l)`,
* `f_i` is `bvar (d + nF - 1 - i)`.

A field's own data (its telescope and its index expressions) is
spelled at the CONSTRUCTOR's frame — the `nP` parameters, then the `i`
earlier fields — so moving it to a rule's frame lifts the earlier
fields to all `nF` of them and the parameters past the `rP - nP`
binders that stand between them and the fields: that is
`structIdxAt nF (rP - nP) i l m` and `structTeleAt nF (rP - nP) i l`
(`ConLeche/Kernel/Inductives/FieldTele.lean`). -/

/-! ## The elimination restriction, declaratively -/

/-- **When a large eliminator is allowed**, official's
`elim_only_at_universe_zero` said declaratively: always when the
block's sort is never `0`; otherwise only for ONE member with no
container occurrence and at most one constructor — and at one
constructor the per-field subsingleton criterion, which the
CONSTRUCTORS' stage has already applied (`checkStructFieldSortsI`'s
`large` arm).  When this is `false` the recursor's conclusion must be
a proposition.

**Why `p.large` is a CONJUNCT of the second disjunct** (lane SEC1, the
falsifier's witness of 2026-09-22).  The route CHECKS the recursor
instead of generating it, so the two halves of official's criterion
are split: this one is keyed on the block's counts, while the per-field
subsingleton half runs in the constructors' stage under `p.isProp &&
p.large` — and `BlockShape.large` is a LEVEL-PARAMETER SHAPE ("a fresh
elimination level parameter in front"), not a property of the
elimination.  A MONOMORPHIC large motive (`{motive : ∀ n, T n → Type}`,
which needs no level parameter) therefore has `large = false`, so the
per-field half did not run at all, and this guard — had it kept letting
a one-member, one-constructor `Prop` block through unconditionally —
would not have asked for a propositional conclusion either.  Neither
half fired, and `Hidden : Nat → Prop | mk (n m : Nat) : Hidden (n+1)`
eliminated into `Type`: proof irrelevance collapses `mk 0 0` and
`mk 0 1` while the eliminator tells them apart, which is a proof of
`0 = 1` (fixture `corner_rec_mono_large_bad`).

With `p.large` required, a recursor that does NOT declare the generated
large shape must conclude in `Sort 0` — checked, not assumed, by the
`isDefEq` beside the call — so the one flag now implies the other:
`large = false` ⇒ the elimination level is provably `0`.  That is the
invariant the model's per-field clause (`CtorDataI.srcProp`, keyed on
the same `large`) needs to be about the blocks it is used at, and it is
what the fixpoint route gets for free by GENERATING the recursor
(`structElimLevel`, which is `Level.zero` at `large = false`).  Nothing
official emits is lost: official's own recursor for a large-eliminating
block always carries the fresh parameter. -/
def blockLargeElimAllowed (p : BlockShape) (nested : Bool) : Bool :=
  p.resSort.isNeverZero ||
    (p.large && p.k == 1 && !nested && (p.numCtors == 0 || p.numCtors == 1))

/-! ## Lookup -/

/-- The position of a name in a list (`none` when absent). -/
def nameIdxOf? (names : List Name) (n : Name) : Option Nat :=
  (List.range names.length).find? fun i => names.getD i default == n

end ConLeche
