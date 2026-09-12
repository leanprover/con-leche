module

public import ConLeche.Accepts
public import ConLeche.Frontend.Prelude
public import ConLeche.Cached.Installed
/- The `#guard`s below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Accepts
meta import ConLeche.Frontend.Prelude
meta import ConLeche.Cached.Installed
/- `import all`: the template interpolates `Nat`s with `toString`, which
is `Nat.repr`, and `Init/Data/Repr.lean` is a module that does not
expose it — so the kernel could not decide the string equation below
without the private view.  The same import, for the same reason, is in
`ConLeche/Verify/Frontend/Digits.lean`, where the decimal rendering is
characterised once. -/
import all Init.Data.Repr

public section

/-!
# The file-level statement: the template is real

`ConLeche/Accepts.lean` states `hasProofOfFalse` as a byte template
over the exporter's line shapes.  Two things a theorem about it cannot
show are pinned here: that an actual export matches it — the four
lines below are `tests/e2e/zero_ctor_false_proof.ndjson`'s, the
fixture the binary rejects for proving `False` with `Prop` — and that
the parser reads such chunks, however cut, into a `thmDecl` of type
`False`, so the template describes what the frontend does and not only
what a reader imagines it does.
-/

namespace ConLecheTests

open ConLeche ConLeche.Cached ConLeche.Frontend

/-- The lines of `zero_ctor_false_proof.ndjson` that make it a proof of
`False` (`bogus : False := Prop`), with a header, an unrelated entry and
a second name entry in between. -/
@[expose] def falseFile : String :=
  "{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}\n" ++
  "{\"in\":75,\"str\":{\"pre\":0,\"str\":\"False\"}}\n" ++
  "{\"ie\":159,\"sort\":0}\n" ++
  "{\"ie\":223,\"const\":{\"name\":75,\"us\":[]}}\n" ++
  "{\"in\":85,\"str\":{\"pre\":0,\"str\":\"unused\"}}\n" ++
  "{\"in\":84,\"str\":{\"pre\":0,\"str\":\"bogus\"}}\n" ++
  "{\"ie\":224,\"sort\":0}\n" ++
  "{\"thm\":{\"all\":[84],\"levelParams\":[],\"name\":84,\"type\":223,\"value\":159}}\n"

-- the template matches it, with the witnesses spelled out; the byte
-- equation is decided by the kernel
set_option maxRecDepth 100000 in
example : hasProofOfFalse [falseFile.toUTF8] :=
  ⟨"{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}".toUTF8,
   "{\"ie\":159,\"sort\":0}".toUTF8,
   "{\"in\":85,\"str\":{\"pre\":0,\"str\":\"unused\"}}".toUTF8,
   "{\"ie\":224,\"sort\":0}".toUTF8,
   "".toUTF8,
   75, 223, 84, 159, "bogus", by
    -- the bytes are the UTF-8 of one string, and that string equation
    -- is decided
    simp only [Frontend.concatBytes, ByteArray.append_empty, String.toUTF8_eq_toByteArray,
      ← String.toByteArray_append]
    exact congrArg String.toByteArray (by decide)⟩

/-- The parsed prelude (empty only if it did not parse, which
`PreludeTests` rules out). -/
private def preludeIx : PreludeIx :=
  match builtinPreludeE with
  | .ok p => p
  | .error _ => {}

/-- The record the parse should produce. -/
private def bogusFalse (r : ParseResultD) : Bool :=
  r.decls.any fun
    | .thmDecl cv _ => cv.name == .str .anonymous "bogus" && cv.type == .const falseName []
    | _ => false

-- the parser reads the chunks into a theorem record of type `False` …
#guard
  match parseChunks [falseFile.toUTF8] with
  | .ok r => bogusFalse r
  | .error _ => false

-- … however the file is cut, empty chunks included (the pure fold
-- runs over the whole list; only the read loop takes an empty READ
-- for the end of the file) …
#guard
  let b := falseFile.toUTF8
  match parseChunks [b.extract 0 70, ByteArray.empty, b.extract 70 71, b.extract 71 b.size,
      ByteArray.empty] with
  | .ok r => bogusFalse r && r.decls.size == 1
  | .error _ => false

-- … which the fold then rejects (`Prop` is not a proof of `False`)
#guard
  match parseChunks [falseFile.toUTF8] with
  | .ok r => match checkDecls .verified (preparePrelude preludeIx r.decls.toList) with
    | .ok _ => false
    | .error _ => true
  | .error _ => false

-- a rebound index is a parse error (the property the file theorem
-- reads off the tables: an entry bound once is the entry every later
-- line reads)
#guard
  match parseChunks [("{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}\n" ++
      "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"b\"}}\n").toUTF8] with
  | .ok _ => false
  | .error (.parseError 2 _) => true
  | .error _ => false

end ConLecheTests
