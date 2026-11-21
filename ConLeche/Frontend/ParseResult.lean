module

public import ConLeche.Kernel.Env

@[expose] public section

/-!
# What the JSON parse reads and returns

The two data the statements about a lean4export file mention beside the parse itself
(`parseChunks`, `ConLeche/Frontend/ExportC.lean`): the bytes a list of chunks adds up to
(`concatBytes`) and the parse's result (`ParseResultD`).
-/

namespace ConLeche.Frontend

open ConLeche

/-- The bytes of a list of chunks, in order: what the chunks a handle
hands out add up to (task #290). -/
def concatBytes : List ByteArray → ByteArray
  | [] => .empty
  | c :: cs => c ++ concatBytes cs

/-- The direct parse result: the declarations over `Expr`.  No arena. -/
structure ParseResultD where
  /-- the FILE's declaration records, in the file's order (the prelude, the dedupe and the
  ground hoist are `preparePrelude`'s) -/
  decls : Array Declaration

end ConLeche.Frontend
