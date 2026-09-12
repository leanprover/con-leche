module

public import ConLeche.Frontend.ExportC

@[expose] public section

/-!
# What a file that proves `False` looks like

The main theorem (`ConLeche/Challenge.lean`) is about `checkDecls`, the
fold over the PARSED stream; the main corollary is about the CHUNKS the
binary reads, and this module names the one thing it needs beyond the
three functions of the binary's accept path (`builtinPreludeE`,
`parseChunks`, `checkDecls` over `preparePrelude`):

* `hasProofOfFalse chunks` — the file, read as bytes, declares a
  theorem of type `False`, said as a template in the exporter's own
  line shapes: a name entry for `False`, an expression entry for the
  constant `False`, a name entry for the theorem's own name, and the
  theorem record whose `type` is that expression.  The parts before,
  between and after the four lines are arbitrary byte strings —
  anything at all, well-formed or not — and the indices `i`, `j`, `k`,
  `v` and the theorem's name are arbitrary too.

The main corollary `no_False_declaration` (`ConLeche/Challenge.lean`)
then reads: for chunks that match the template, the chain of the three
functions — one `Except` `do` block, the three steps failing in one
error type — is an error.
-/

namespace ConLeche


/-- **The file declares a theorem of type `False`.**  Four lines of the
lean4export format, in this order, each on a line of its own, with
anything at all before, between and after them:

* `{"in":i,"str":{"pre":0,"str":"False"}}` — name entry `i` is `False`;
* `{"ie":j,"const":{"name":i,"us":[]}}` — expression entry `j` is the
  constant `False`;
* `{"in":k,"str":{"pre":0,"str":"<name>"}}` — name entry `k` is the
  theorem's own name, any name;
* `{"thm":{"all":[k],"levelParams":[],"name":k,"type":j,"value":v}}` —
  a theorem named `k` whose type is `j` and whose proof is expression
  entry `v`, whatever that is.

The file is the concatenation of the chunks the binary read, as bytes;
the four lines are the UTF-8 of their templates.  The five byte-string
parts are unconstrained: a part may hold any number of further lines,
including malformed ones or bytes that are no UTF-8 at all — then the
file does not parse and is not accepted for that reason.  The only
thing the template fixes is that the four lines appear, whole, in this
order. -/
def hasProofOfFalse (chunks : List ByteArray) : Prop :=
  ∃ (before between₁ between₂ between₃ after : ByteArray) (i j k v : Nat) (name : String),
    Frontend.concatBytes chunks =
      before ++ "\n".toUTF8 ++
      (s!"\{\"in\":{i},\"str\":\{\"pre\":0,\"str\":\"False\"}}").toUTF8 ++ "\n".toUTF8 ++
      between₁ ++ "\n".toUTF8 ++
      (s!"\{\"ie\":{j},\"const\":\{\"name\":{i},\"us\":[]}}").toUTF8 ++ "\n".toUTF8 ++
      between₂ ++ "\n".toUTF8 ++
      (s!"\{\"in\":{k},\"str\":\{\"pre\":0,\"str\":\"{name}\"}}").toUTF8 ++ "\n".toUTF8 ++
      between₃ ++ "\n".toUTF8 ++
      (s!"\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}").toUTF8 ++ "\n".toUTF8 ++
      after

end ConLeche
