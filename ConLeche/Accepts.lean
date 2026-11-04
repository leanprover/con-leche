module

public import ConLeche.Frontend.ExportC

@[expose] public section

/-!
# One JSON file that declares a theorem of type `False`

The main theorem (`ConLeche/Challenge.lean`) is about `checkDecls`, the
fold over the PARSED stream; the main corollary is about the CHUNKS the
binary reads, and this module names the one thing it needs beyond the
three functions of the binary's accept path (`builtinPreludeE`,
`parseChunks`, `checkDecls` over `preparePrelude`):

* `jsonWithTheoremFalse chunks` — the file, read as bytes, is ONE
  particular JSON file declaring a theorem of type `False`: a whole-file
  template in the exporter's own line shapes, with a name entry for
  `False`, an expression entry for the constant `False`, a name entry
  for the theorem's own name, and the theorem record whose `type` is
  that expression, in that order.  The parts before, between and after
  the four lines are arbitrary strings, and so are the indices `i`, `j`,
  `k`, `v` and the theorem's name.

The name says what the predicate is and what it is not: it describes ONE
way of putting a theorem of type `False` into a JSON file, not every
proof of `False` a file might hold.  The main corollary
`no_False_declaration` (`ConLeche/Challenge.lean`) takes it as its
hypothesis: hand the binary such a file, however cut into chunks, and
the chain of its three pure steps — the built-in prelude parses, the
chunks parse, the verified fold accepts the prepared records — returns
an error.
-/

namespace ConLeche


/-- **One JSON file that declares a theorem of type `False`.**  The
whole file, as one template: four lines of the lean4export format, in
this order, each on a line of its own, with anything at all before,
between and after them:

* `{"in":i,"str":{"pre":0,"str":"False"}}` — name entry `i` is `False`;
* `{"ie":j,"const":{"name":i,"us":[]}}` — expression entry `j` is the
  constant `False`;
* `{"in":k,"str":{"pre":0,"str":"<name>"}}` — name entry `k` is the
  theorem's own name, any name;
* `{"thm":{"all":[k],"levelParams":[],"name":k,"type":j,"value":v}}` —
  a theorem named `k` whose type is `j` and whose proof is expression
  entry `v`, whatever that is.

This is ONE shape of such a file, not every proof of `False`: a file
that declares the same theorem with its lines in another order, or
proves a contradiction some other way, is outside the predicate — what
the corollary says of the files inside it is that the checker rejects
them.  The five parts are unconstrained otherwise: a part may hold any
number of further lines, including malformed ones — then the file does
not parse and is rejected for that reason.  They are `String`s, so the
file is the UTF-8 of one interpolated Lean string; a file whose parts
carry bytes that are no UTF-8 at all is outside the predicate too,
which costs nothing for an export, the exporter writing UTF-8. -/
def jsonWithTheoremFalse (chunks : List ByteArray) : Prop :=
  ∃ (before between₁ between₂ between₃ after name : String) (i j k v : Nat),
    Frontend.concatBytes chunks = (s!"{before}
\{\"in\":{i},\"str\":\{\"pre\":0,\"str\":\"False\"}}
{between₁}
\{\"ie\":{j},\"const\":\{\"name\":{i},\"us\":[]}}
{between₂}
\{\"in\":{k},\"str\":\{\"pre\":0,\"str\":\"{name}\"}}
{between₃}
\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}
{after}").toUTF8

end ConLeche
