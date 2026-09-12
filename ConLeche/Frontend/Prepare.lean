module

public import ConLeche.Frontend.NatOpGround

@[expose] public section

/-!
# `preparePrelude` — what happens between the file and the fold (task #293)

**The ruling** (maintainer, 2026-09-12): *"Why does the parser deal with
basis things?  That's clearly a layering violation; it's the fold that
may or may not want to treat them specially. … We can also move this
functionality into a new function, `preparePrelude` or so, to keep
concerns separate.  (Ideally that's `List Declaration` to
`List Declaration`?)"* — and, on the shape: *"If that `preparePrelude`
reorders anyways, then it can just as well reorder any existing prelude
declaration, and only synthesize any that are missing.  This way, we get
a simple spec: it is a permutation of the input plus additional
declarations, but nothing missing."*

So the decoder (`ConLeche/Frontend/ExportC.lean`) emits the file's
records and nothing else, this module PREPARES the list the fold runs
over, and every verdict is the fold's.  `preparePrelude` is total and
pure — it has no error channel, nothing it does can fail, and **no
record of the stream is dropped, rewritten or retagged**:

1. **the prelude's declarations first.**  The pin-certified `Nat`
   operations need `Eq`, `Nat`, `Bool` and the other prelude blocks
   installed before them, and `lean4export` walks a hash map: the
   report task #191 answered was a stream that emits `Nat.shiftLeft`
   before the `Bool` block its certificate statements are spelled over.
   So the stream's OWN copy of each prelude declaration is moved to the
   front, in the prelude's (dependency-correct) order, and only the
   prelude records the stream does NOT declare are synthesised there
   from `ConLeche/Frontend/Prelude.lean`'s committed
   `pins/<toolchain>.prelude.ndjson`.  A stream that declares the
   toolchain's `Bool` is therefore CHECKED on its own `Bool` record,
   not on a copy of ours;
2. **the ground hoist** (`ConLeche/Frontend/NatOpGround.lean`): a
   pinned `Nat` operation's stream-certified structural ground
   (`Nat.ble`, `Nat.sub`, `Nat.mul`) is moved ahead of it when the
   stream declares it later.  A dependency-closed set moved earlier is
   still a valid stream.

Both steps only REORDER, and the second one is the reason the first can
be one too.  The spec is therefore as simple as the maintainer asked
for, and it is what `ConLeche/Verify/Frontend/Prepare.lean` proves:

    ∃ extra, (∀ d ∈ extra, d ∈ prelude) ∧ (preparePrelude ds).Perm (ds ++ extra)

with the pass-through corollary `pd ∈ ds → pd ∈ preparePrelude ds`.

**What is NOT here.**  Recognising a block as one of the five pinned
basis blocks, and a quotient record as the pinned package's, is the
FOLD's (`checkDecl`, `ConLeche/Kernel/Checker.lean`): it compares the
record with the pin up to `ConstantInfo.canon` and installs the pinned
block, rejects a differing block through the reserved-name check and
declines a differing quotient record.  Nothing in this file looks at a
record's contents; it reads names, and only to find the stream's copy
of a prelude declaration.
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## The prelude -/

/-- The built-in prelude: its records, in the order the committed file
declares them (`ConLeche/Frontend/Prelude.lean`).  Dependency-correct
by construction — it is an export of the toolchain's own environment —
which is what makes it usable as the front of every prepared stream. -/
structure PreludeIx where
  decls : Array Declaration := #[]

/-- The name a prelude record is looked up by: the block's type former,
the quotient constant, the axiom.  (`Declaration.names` lists every
name a record declares; the first is the record's own handle.) -/
def preludeKey (d : Declaration) : Name := (d.names.head?).getD .anonymous

/-! ## Pulling the stream's own copy out

A prelude declaration the stream declares itself is MOVED, not
duplicated: the stream's record is what the fold checks, and it must
appear exactly once.  `pick` is the removal, as a specification (a
plain list recursion) and as the implementation (the same fold with an
array accumulator — a stream is millions of records long, and a list
recursion that is not tail-recursive is a stack frame per record).
-/

/-- The first record declaring `n`, and the list without it. -/
def pickSpec (n : Name) : List Declaration → Option Declaration × List Declaration
  | [] => (none, [])
  | d :: ds =>
    if d.names.contains n then (some d, ds)
    else
      let (m, ds') := pickSpec n ds
      (m, d :: ds')

/-- `pickSpec`, tail-recursively. -/
def pickGo (n : Name) (acc : Array Declaration) :
    List Declaration → Option Declaration × List Declaration
  | [] => (none, acc.toList)
  | d :: ds =>
    if d.names.contains n then (some d, acc.toList ++ ds)
    else pickGo n (acc.push d) ds

/-- The front of the prepared list — the prelude's declarations, each
one the stream's own copy where the stream has one — and the rest of
the stream, in the stream's order. -/
def frontOf : List Declaration → List Declaration → List Declaration × List Declaration
  | [], ds => ([], ds)
  | p :: ps, ds =>
    let (m, ds') := pickGo (preludeKey p) #[] ds
    let (f, rest) := frontOf ps ds'
    ((m.getD p) :: f, rest)

/-- `frontOf` over `pickSpec`: the specification the lemmas are stated
over. -/
def frontSpec : List Declaration → List Declaration → List Declaration × List Declaration
  | [], ds => ([], ds)
  | p :: ps, ds =>
    let (m, ds') := pickSpec (preludeKey p) ds
    let (f, rest) := frontSpec ps ds'
    ((m.getD p) :: f, rest)

/-! ## The prepared list -/

/-- The prepared list and the driver's receipts. -/
structure Prepared where
  /-- the prelude's declarations, then the rest of the stream -/
  decls : Array Declaration
  /-- how many prelude records the stream did not declare and this step
  synthesised -/
  synthesised : Nat := 0
  /-- the records moved ahead of a pinned `Nat` operation they ground
  (names, for the driver's receipt) -/
  hoisted : Array Name := #[]

/-- **`preparePrelude`, with its receipts.** -/
def prepareD (pre : PreludeIx) (ds : List Declaration) : Prepared :=
  let (front, rest) := frontOf pre.decls.toList ds
  let (decls, hoisted) := hoistNatOpGround (front ++ rest).toArray
  ⟨decls, decls.size - ds.length, hoisted⟩

/-- **`preparePrelude`**: the parsed stream, prepared for the fold —
the prelude's declarations first (the stream's own copies where it has
them), the rest of the stream after them, every pinned `Nat`
operation's stream-certified ground ahead of it.  Total, pure, and the
fold's input. -/
def preparePrelude (pre : PreludeIx) (ds : List Declaration) : List Declaration :=
  (prepareD pre ds).decls.toList

end ConLeche.Frontend
