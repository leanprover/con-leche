import Setlec

/-!
Test suite.  Tests are `#guard`s and `example`s, so `lake test` (which
builds this library) fails if any of them break.
-/

namespace SetlecTests

open Setlec

def dummyAxiom : Declaration :=
  .axiomDecl { name := .str .anonymous "foo", levelParams := [], type := .sort .zero }

-- The trivial checker rejects any declaration.
#guard (checkDecl Env.empty dummyAxiom).toBool == false

-- The trivial checker still accepts the empty list of declarations.
#guard (checkDecls []).toBool == true

-- ... and rejects any non-empty list.
#guard (checkDecls [dummyAxiom]).toBool == false

end SetlecTests
