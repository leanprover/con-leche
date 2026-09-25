module

public import ConLeche.Frontend.InModel.Nested
public import ConLeche.Kernel.Inductives.BlockParts

@[expose] public section

/-!
# The in-process modeller (task #200)

Entry point of the in-process construction of `_model` families for the
inductive blocks the uniform route does not install and the modeled
install expects a model for: **nested** blocks (every other block is
the uniform route's, `blockParts?`).  The
frontend calls `generate` at the block's record, before the block is
pushed, when the stream carries no model for it; the records it returns
are pushed ahead of the block and checked by the fold like any stream
declaration (the "certification tax"), and the block itself installs
through the modeled route.

Since task #207 this is the **only** model source: there is no
external preprocessor and no dependency, and every input is a raw
`lean4export` stream.  Soundness needs nothing from this module: a
wrong record is rejected or declined by the fold, never accepted.  Its
correctness decides only *coverage* — which blocks accept — and every
decline names its class, so the residual is exact and positive.

The one rung is `genNested` (`ConLeche/Frontend/InModel/Nested.lean`).
-/

namespace ConLeche.Frontend.InModel

open ConLeche

/-- Is the block one this modeller is for: a NESTED block
(`numNested > 0`) the uniform route does NOT install (`uniformRoute`,
the install dispatch's own test, lane FLIPPREP).  Since the flip that
is a nested block the recogniser does not read, which the fold declines
(`checkShapeless`) whatever records are generated ahead of it; the
modeller goes with NESTPLAN L10.  The nested conjunct stays: without it
the modeller runs at every block the recogniser does not read, the
pinned basis blocks included, and declines the built-in prelude's `Eq`
at parse time, before `preparePrelude` retags it to its pin. -/
def wants (b : BlockRec) (nPd : Nat) (block : List ConstantInfo) : Bool :=
  b.types.any (·.numNested > 0) && !uniformRoute nPd block

/-- Generate the model records of a block, in stream order, or the
reason the block is declined. -/
def generate (ctx : Ctx) (b : BlockRec) : Except String (List Declaration) :=
  genNested ctx b

end ConLeche.Frontend.InModel
