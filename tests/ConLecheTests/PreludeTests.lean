module

public import ConLeche.Frontend.Prelude
public import ConLeche.Cached.Installed
/- The `#guard`s below are EVALUATED, so the constants they name have to be
reachable from meta code too; a plain import is not (`IO of declaration …
not available`).  A module needed at both levels is imported twice. -/
meta import ConLeche.Frontend.Prelude
meta import ConLeche.Cached.Installed

public section

/-!
# The built-in prelude (task #191) and `preparePrelude` (task #293):
what the prelude holds, that the fold accepts it, and what preparing a
stream does to it

`ConLeche/Frontend/Prelude.lean` embeds `pins/<toolchain>.prelude.ndjson`
and parses it at process initialisation; `preparePrelude`
(`ConLeche/Frontend/Prepare.lean`) puts those declarations at the front
of every stream it prepares — **the stream's own record where the
stream has one**, one of these where it has none.  These guards pin the
prelude's content — the five pinned inductive basis blocks, the four
quotient records with the soundness axiom, `And` and `Bool`: twelve
records — and run the verified fold over the prelude alone at both
modes: the prelude is itself an accepted stream, so prepending it can
never be what fails a run.  (The pinned-block RECOGNITION is the fold's
since task #293, and the `prelude_*` e2e fixtures exercise it end to
end, `tests/e2e-expected.txt`.)
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

-- twelve records, in the committed file's order: the five pinned
-- inductive basis blocks, the four `#QUOT` records, the `Quot.sound`
-- axiom record, and the `And` and `Bool` blocks (`And` is pinned by
-- design: the one propositional structure the stuck-major rescue
-- serves, `ConLeche/PinGen/Prelude.lean`'s `pinnedPreludeMembers`)
#guard preludeIx.decls.size == 12
#guard preludeIx.decls.toList.map (fun d => (d.names.head?).getD .anonymous) ==
  [eqName, natName, punitName, emptyName, falseName,
   quotName, quotMkName, quotLiftName, quotIndName, quotSoundName,
   andName, boolName]
-- and the kinds: five inductive blocks, four quotient records, one
-- axiom record, two more inductive blocks — no `basisDecl`, which no
-- frontend function produces since task #293
#guard preludeIx.decls.toList.map (fun d => match d with
  | .indDecl .. => 0 | .quotDecl .. => 1 | .axiomDecl _ => 2 | _ => 3) ==
  [0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 0, 0]

/-- The fold accepts the prelude alone, at both modes, from the empty
environment: 27 constants (19 basis + `And`, `And.intro`, `And.rec` and
`And`'s projection table + `Bool`, `Bool.false`, `Bool.true`,
`Bool.rec`).  The five pinned blocks and the quotient package install
as the PINS — `checkDecl` recognises them (`basisPinHit`,
`quotPinHit`), which is the whole of task #293's move. -/
def preludeEnvSize (mode : CheckMode) : Option Nat :=
  match checkDecls mode preludeIx.decls.toList with
  | .ok env => some env.consts.length
  | .error _ => none

#guard preludeEnvSize .verified == some 27
#guard preludeEnvSize .trusted == some 27

-- `preparePrelude` on a stream that declares NOTHING synthesises the
-- whole prelude, in the prelude's order, and nothing else
#guard preparePrelude preludeIx [] == preludeIx.decls.toList

-- …and on the prelude's own records it synthesises nothing: every
-- declaration is found in the stream and MOVED, so the result is the
-- input (already in prelude order)
#guard preparePrelude preludeIx preludeIx.decls.toList == preludeIx.decls.toList

-- a stream record that is not the prelude's passes through, after the
-- prelude's declarations
def probeRec : Declaration :=
  .axiomDecl ⟨.str .anonymous "ConLecheTests.probe", [], .sort .zero⟩

#guard (preparePrelude preludeIx [probeRec]).length == 13
#guard (preparePrelude preludeIx [probeRec]).getLast? == some probeRec

end ConLecheTests
