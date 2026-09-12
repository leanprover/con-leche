module

public import ConLeche.Accepts
/- The `#guard`s below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Accepts
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

`ConLeche/Accepts.lean` states `hasProofOfFalse` as a string template
over the exporter's line shapes.  Two things a theorem about it cannot
show are pinned here: that an actual export matches it — the four
lines below are `tests/e2e/zero_ctor_false_proof.ndjson`'s, the
fixture the binary rejects for proving `False` with `Prop` — and that
the parser reads such a file into a `thmDecl` of type `False`, so the
template describes what the frontend does and not only what a reader
imagines it does.
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

-- the template matches it, with the witnesses spelled out; the string
-- equation is decided by the kernel
set_option maxRecDepth 100000 in
example : hasProofOfFalse falseFile :=
  ⟨"{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}",
   "{\"ie\":159,\"sort\":0}",
   "{\"in\":85,\"str\":{\"pre\":0,\"str\":\"unused\"}}",
   "{\"ie\":224,\"sort\":0}",
   "",
   75, 223, 84, 159, "bogus", by decide⟩

/-- The parsed prelude (empty only if it did not parse, which
`PreludeTests` rules out). -/
private def preludeIx : PreludeIx :=
  match builtinPreludeE with
  | .ok p => p
  | .error _ => {}

-- the parser reads the file into a theorem record of type `False` …
#guard
  match parseExportD falseFile preludeIx with
  | .ok r => r.decls.any fun
    | .thmDecl cv _ => cv.name == .str .anonymous "bogus" && cv.type == .const falseName []
    | _ => false
  | .error _ => false

-- … which the fold then rejects (`Prop` is not a proof of `False`)
#guard
  match parseExportD falseFile preludeIx with
  | .ok r => match checkDecls .verified r.decls.toList with
    | .ok _ => false
    | .error _ => true
  | .error _ => false

end ConLecheTests
