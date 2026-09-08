module

public import ConLeche.Frontend.Prelude
public import ConLeche.Cached.ParsedC
/- The `#guard`s below are EVALUATED, so the constants they name have to be
reachable from meta code too; a plain import is not (`IO of declaration …
not available`).  A module needed at both levels is imported twice. -/
meta import ConLeche.Frontend.Prelude
meta import ConLeche.Cached.ParsedC

@[expose] public section

/-!
# The built-in prelude (task #191): what it holds, and that the fold
accepts it

`ConLeche/Frontend/Prelude.lean` embeds `pins/<toolchain>.prelude.ndjson`
and parses it at process initialisation; every stream is checked as
`prelude ++ stream'`.  These guards pin the prelude's content — the six
pinned basis blocks and the `Bool` block, seven fold records — and run
the verified fold over the prelude alone at both modes: the prelude is
itself an accepted stream, so prepending it can never be what fails a
run.  (The dedupe against a later stream copy is exercised end to end
by the `prelude_*` e2e fixtures, `tests/e2e-expected.txt`.)
-/

namespace ConLecheTests

open ConLeche ConLeche.Cached ConLeche.Frontend

/-- The parsed prelude (empty only if it did not parse, which the first
guard below rules out). -/
def preludeIx : PreludeIx :=
  match builtinPreludeE with
  | .ok p => p
  | .error _ => {}

-- the prelude parses
#guard builtinPreludeE.toOption.isSome

-- seven records: the six basis blocks (the four `quot` records and
-- `Quot.sound` fold into one) and the `Bool` inductive block
#guard preludeIx.decls.size == 7
#guard preludeIx.basis.length == 6
#guard [BasisKind.eqK, .natK, .punitK, .emptyK, .falseK, .quotK].all
  (preludeIx.basis.contains ·)
#guard preludeIx.byName.contains (Name.str .anonymous "Bool")
#guard preludeIx.byName.contains ((Name.str .anonymous "Bool").str "rec")
#guard preludeIx.byName.contains ((Name.str .anonymous "Bool").str "true")
#guard preludeIx.byName.contains ((Name.str .anonymous "Bool").str "false")
#guard preludeIx.byName.size == 4
-- no basis name is in the by-name index: a stream's mismatching basis
-- redefinition keeps REJECTING through the reserved-name check
#guard !(preludeIx.byName.contains natName)
#guard !(preludeIx.byName.contains eqName)

/-- The fold accepts the prelude alone, at both modes, from the empty
environment: 23 constants (19 basis + `Bool`, `Bool.false`,
`Bool.true`, `Bool.rec`). -/
def preludeEnvSize (mode : CheckMode) : Option Nat :=
  match checkDecls mode preludeIx.decls.toList with
  | .ok env => some env.consts.length
  | .error _ => none

#guard preludeEnvSize .verified == some 23
#guard preludeEnvSize .trusted == some 23

-- the dedupe: the prelude's own text, parsed AGAINST the prelude,
-- drops every record (all identical) — the result is the prelude and
-- nothing more
#guard match parseExportD builtinPreludeText preludeIx with
  | .ok r => r.decls.size == 7 && r.preludeCount == 7 && r.preludeDropped == 7
  | .error _ => false

end ConLecheTests
