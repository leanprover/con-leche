module

public import ConLeche.Frontend.InModel.Nested

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

/-- Is the block one this modeller is for: nested (`numNested > 0`)? -/
def wants (b : BlockRec) : Bool :=
  b.types.any (·.numNested > 0)

/-- Generate the model records of a block, in stream order, or the
reason the block is declined. -/
def generate (ctx : Ctx) (b : BlockRec) : Except String (List Declaration) :=
  genNested ctx b

end ConLeche.Frontend.InModel
