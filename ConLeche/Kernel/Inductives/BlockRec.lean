module

public import ConLeche.Kernel.Inductives.BlockParts

@[expose] public section

/-!
# The recursor stage's shared pieces (the uniform route)

The uniform route GENERATES the recursors (charter item 5, as amended
by GENREC); the stage itself is `genRecCheck`
(`ConLeche/Kernel/Inductives/GenRec.lean`).  What lives here is what
that stage shares with the rest of the install:

* the ELIMINATION guard, official's `elim_only_at_universe_zero` said
  declaratively (`blockLargeElimAllowed`, the recursor stage's one
  guard): unless the block's sort is never `0`, a large eliminator needs
  the large SHAPE (a fresh elimination level parameter,
  `BlockShape.large`), ONE member, no container occurrence and at most
  one constructor;
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

**Why `p.large` is a CONJUNCT of the second disjunct.**  The two
halves of official's criterion are split: this one is keyed on the
block's counts, and it is the recursor stage's ONE elimination guard
(`genRecCheck`: `p.large && !blockLargeElimAllowed …`, the container bit
or'ed with every outside class); the per-field subsingleton half runs in
the constructors' stage under `p.isProp && p.large`
(`checkStructFieldSortsI`).  `BlockShape.large` is read off the stream's
recursor records (a fresh elimination level parameter in front), and the
generated family eliminates at that parameter when `large`, at `Sort 0`
otherwise (`structElimLevel`); the stream's recursor TYPE must be
definitionally the generated one, so a MONOMORPHIC large motive
(`{motive : ∀ n, T n → Type}`, no level parameter, `large = false`) is
rejected by that comparison — it would otherwise let
`Hidden : Nat → Prop | mk (n m : Nat) : Hidden (n+1)` eliminate into
`Type`, where proof irrelevance collapses `mk 0 0` and `mk 0 1` while
the eliminator tells them apart (fixture `corner_rec_mono_large_bad`).
With `p.large` required here, the one flag decides both halves, and the
model's per-field clause (`CtorDataI.srcProp`, keyed on the same
`large`) is about exactly the blocks this guard lets through: its
uniqueness premise (`huniq`) at a possibly-`Prop` block is this
function's second disjunct plus the per-field criterion.  Nothing
official emits is lost: official's own recursor for a large-eliminating
block always carries the fresh parameter. -/
def blockLargeElimAllowed (p : BlockShape) (nested : Bool) : Bool :=
  p.resSort.isNeverZero ||
    (p.large && p.k == 1 && !nested && (p.numCtors == 0 || p.numCtors == 1))

end ConLeche
