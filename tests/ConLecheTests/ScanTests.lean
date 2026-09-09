module

public import ConLeche.Frontend.Prelude
/- The `#guard`s below are EVALUATED, so the constants they name have to be
reachable from meta code too; a plain import is not.  A module needed at
both levels is imported twice. -/
meta import ConLeche.Frontend.Prelude

public section

/-!
# The lean4export recogniser (task #256)

`ConLeche/Frontend/Scan/Fast.lean` reads the stream's bytes directly.
These guards pin the properties the recogniser's shape is chosen for,
which no end-to-end fixture would isolate:

* **key order does not matter.**  The raw stream sorts its keys and so
  writes the payload before the index (`{"app":…,"ie":8}`); the
  hand-written fixtures put the tag first.  Both, and every
  permutation, decode to the same record.
* **JSON whitespace is whitespace**, inside the record as well as
  around it.
* **a key outside the dialect, a repeated key, a missing key and bytes
  after the record are errors**, not silently tolerated.
* **the chunk boundary is invisible**: feeding the same bytes in
  three-byte pieces through `feedChunk`, carrying the incomplete tail
  exactly as the streaming driver does, yields the parse the
  whole-buffer reader yields.
-/

namespace ConLecheTests

open ConLeche ConLeche.Cached ConLeche.Frontend

/-! ## One line, many spellings -/

/-- The scanned record of a whole line. -/
def scan1 (s : String) : Option LineRec :=
  let b := s.toUTF8
  match scanLineFwd b 0 with
  | .ok r _ => some r
  | .err _ => none

/-- The tag a line fails with, for the negative guards. -/
def scanErr (s : String) : Option ErrTag :=
  let b := s.toUTF8
  match scanLineFwd b 0 with
  | .ok _ _ => none
  | .err e => some e.what

def isApp (f a i : Nat) : LineRec → Bool
  | .expr j (.app f' a') => j == i && f' == f && a' == a
  | _ => false

-- the emitter's sorted layout and the tag-first layout are one record
#guard (scan1 "{\"app\":{\"arg\":1,\"fn\":7},\"ie\":8}").any (isApp 7 1 8)
#guard (scan1 "{\"ie\":8,\"app\":{\"fn\":7,\"arg\":1}}").any (isApp 7 1 8)
#guard (scan1 "{\"ie\": 8 , \"app\" : { \"fn\" : 7 , \"arg\" : 1 } }").any (isApp 7 1 8)

-- a name entry, both ways round
#guard (scan1 "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"Nat\"}}").any fun
  | .name 3 (.str 0 s) => s == "Nat"
  | _ => false
#guard (scan1 "{\"str\":{\"str\":\"Nat\",\"pre\":0},\"in\":3}").any fun
  | .name 3 (.str 0 s) => s == "Nat"
  | _ => false

-- the level entries
#guard (scan1 "{\"il\":1,\"succ\":0}").any fun | .level 1 (.succ 0) => true | _ => false
#guard (scan1 "{\"il\":2,\"max\":[1,0]}").any fun | .level 2 (.max 1 0) => true | _ => false
#guard (scan1 "{\"imax\":[1,0],\"il\":2}").any fun | .level 2 (.imax 1 0) => true | _ => false

-- the literals: a `natVal` is a quoted decimal, a `strVal` a JSON string
#guard (scan1 "{\"ie\":9,\"natVal\":\"40000\"}").any fun
  | .expr 9 (.natVal n) => n == 40000
  | _ => false
#guard (scan1 "{\"ie\":9,\"strVal\":\"a\\\"b\\\\c\"}").any fun
  | .expr 9 (.strVal s) => s == "a\"b\\c"
  | _ => false

-- a binder: `binderInfo` and `name` are validated and dropped, `pw` is
-- the checker's own annotation and defaults to `never`
#guard (scan1 "{\"ie\":5,\"lam\":{\"binderInfo\":\"instImplicit\",\"body\":4,\"name\":1,\"type\":0}}").any fun
  | .expr 5 (.lam 0 4 .never) => true
  | _ => false
#guard (scan1 "{\"ie\":5,\"lam\":{\"binderInfo\":\"default\",\"body\":4,\"name\":1,\"type\":0,\"pw\":[2]}}").any fun
  | .expr 5 (.lam 0 4 (.ifAllZero [2])) => true
  | _ => false

-- the header record is validated loosely and skipped; a blank line is blank
#guard (scan1 "{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}").any fun
  | .header => true | _ => false
#guard (scan1 "   ").any fun | .blank => true | _ => false

/-! ## What the recogniser refuses -/

#guard scanErr "{\"ie\":8,\"app\":{\"arg\":1,\"fn\":7},\"nope\":1}" == some .unknownKey
#guard scanErr "{\"ie\":8,\"ie\":9,\"bvar\":0}" == some .duplicateKey
#guard scanErr "{\"ie\":8,\"app\":{\"arg\":1}}" == some .missingKey
#guard scanErr "{\"ie\":8,\"bvar\":0} x" == some .trailing
#guard scanErr "{\"ie\":8,\"str\":{\"pre\":0,\"str\":\"a\"}}" == some .mixedKeys
#guard scanErr "{\"ie\":8,\"bvar\":x}" == some .expectedNat
#guard scanErr "{\"ie\":8,\"lam\":{\"binderInfo\":\"nope\",\"body\":4,\"name\":1,\"type\":0}}"
    == some .badBinderInfo
#guard scanErr "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"a}}" == some .expectedString
#guard scanErr "{\"ie\":8,\"const\":{\"name\":1,\"us\":[1,]}}" == some .expectedList
#guard scanErr "not an object" == some .expectedObject

/-! ## The chunk boundary is invisible

`chunked` is the streaming driver's carry logic, purely: the bytes
arrive in `sz`-byte pieces, `feedChunk` consumes the complete lines and
reports where the incomplete tail begins, and the tail is prepended to
the next piece.  At `sz = 3` every line of the fixture is cut several
times. -/

private partial def chunked (st : StateD) (b : ByteArray) (sz pos : Nat)
    (carry : ByteArray) (lineNo : Nat) : Except FrontendError StateD :=
  if b.size ≤ pos then
    if carry.isEmpty then .ok st else applyFinalLine st carry 0 (lineNo + 1)
  else
    let buf := carry ++ b.extract pos (min b.size (pos + sz))
    match feedChunk st buf 0 lineNo with
    | .error e => .error e
    | .ok (st, lineNo, tail) =>
      chunked st b sz (pos + sz) (buf.extract tail.toNat buf.size) lineNo

def chunkFixture : String :=
  include_str "../e2e/delta_chain.ndjson"

-- the whole-buffer parse and the three-byte-piece parse agree record
-- for record (up to the canonical form the prelude dedupe compares at)
#guard
  match parseExportD chunkFixture, chunked (.init {} true) chunkFixture.toUTF8 3 0 .empty 0 with
  | .ok r, .ok st =>
    let s := ParseResultD.ofState st
    r.decls.size == s.decls.size && r.decls.size > 0 &&
      (r.decls.zip s.decls).all (fun p => p.1.sameCanon p.2)
  | _, _ => false

end ConLecheTests
