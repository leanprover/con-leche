module

public import ConLeche.Frontend.Prelude
public import ConLeche.Frontend.Scan.Naive
public import ConLeche.Frontend.Scan.Equiv
/- The `#guard`s below are EVALUATED, so the constants they name have to be
reachable from meta code too; a plain import is not.  A module needed at
both levels is imported twice. -/
meta import ConLeche.Frontend.Prelude
meta import ConLeche.Frontend.Scan.Naive

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
* **the naive reference agrees** (task #261): on every line above and a
  line of each declaration kind, the naive recogniser
  (`ConLeche/Frontend/Scan/Naive.lean`) EVALUATES to the fast one's
  result — the same record, or the same tag at the same byte.  The
  theorem `scanLineSpec_eq_scanLineFwd` says so for every input; these
  guards are what catches a slip in the spec's fidelity to the format
  that the theorem, being about two Lean functions, cannot.
-/

namespace ConLecheTests

open ConLeche ConLeche.Frontend

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

/-! ## The naive reference agrees, by evaluation

`specLine` spells the lift of `naiveLine` out rather than calling
`scanLineSpec`: the compiler replaces `scanLineSpec` by `scanLineFwd` on
the strength of the very equality under test (`@[csimp]`), so a `#guard`
on `scanLineSpec` would compare the fast recogniser with itself.
`naiveLine` is a different constant and is compiled as written. -/

deriving instance DecidableEq for NameRec, LevelRec, PwRec, ExprRec, CVRec, HintsRec, RuleRec,
  IndTypeRec, IndCtorRec, IndRecRec, DeclRec, LineRec, ScanErr, ScanRes

/-- The naive recogniser's reading of a whole line, as a `ScanRes`: a
rest becomes a position by how much the input is short. -/
def specLine (s : String) : ScanRes LineRec :=
  let l := s.toUTF8.data.toList
  match naiveLine l with
  | .ok (r, some _) rest => .ok r (l.length - rest.length).toUSize
  | .ok (r, none) _ => .ok r 0
  | .err t rest => .err ⟨l.length - rest.length, t⟩

def fastLine (s : String) : ScanRes LineRec := scanLineFwd s.toUTF8 0

/-- Every line the guards above read, a line of each declaration kind
from the fixtures, the escapes, and the corners the spec exposed
(a leading-zero list member, a hints object without its colon). -/
def probes : List String :=
  ["{\"app\":{\"arg\":1,\"fn\":7},\"ie\":8}",
   "{\"ie\":8,\"app\":{\"fn\":7,\"arg\":1}}",
   "{\"ie\": 8 , \"app\" : { \"fn\" : 7 , \"arg\" : 1 } }",
   "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"Nat\"}}",
   "{\"str\":{\"str\":\"Nat\",\"pre\":0},\"in\":3}",
   "{\"in\":4,\"num\":{\"i\":2,\"pre\":3}}",
   "{\"il\":1,\"succ\":0}",
   "{\"il\":2,\"max\":[1,0]}",
   "{\"imax\":[1,0],\"il\":2}",
   "{\"il\":3,\"param\":5}",
   "{\"ie\":9,\"natVal\":\"40000\"}",
   "{\"ie\":9,\"natVal\":\"123456789012345678901234567890\"}",
   "{\"ie\":9,\"strVal\":\"a\\\"b\\\\c\"}",
   "{\"ie\":9,\"strVal\":\"caf\\u00e9 \\ud83d\\ude00 \\n\"}",
   "{\"ie\":9,\"strVal\":\"\\ud800\"}",
   "{\"ie\":9,\"strVal\":\"\\x\"}",
   "{\"ie\":40,\"strVal\":\"a\"}",
   "{\"ie\":5,\"lam\":{\"binderInfo\":\"instImplicit\",\"body\":4,\"name\":1,\"type\":0}}",
   "{\"ie\":5,\"lam\":{\"binderInfo\":\"default\",\"body\":4,\"name\":1,\"type\":0,\"pw\":[2]}}",
   "{\"ie\":5,\"forallE\":{\"binderInfo\":\"implicit\",\"body\":4,\"name\":1,\"type\":0,\"pw\":\"never\"}}",
   "{\"ie\":1855,\"letE\":{\"body\":1854,\"name\":430,\"nondep\":false,\"type\":1809,\"value\":1845}}",
   "{\"ie\":112,\"proj\":{\"idx\":1,\"struct\":5,\"typeName\":23}}",
   "{\"ie\":7,\"const\":{\"name\":1,\"us\":[1, 2 ,3]}}",
   "{\"ie\":0,\"bvar\":0}",
   "{\"ie\":1,\"sort\":2}",
   "{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"}}}",
   "   ",
   "",
   "{\"ie\":8,\"bvar\":0}\n{\"ie\":9,\"bvar\":1}",
   "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":2}}",
   "{\"def\":{\"all\":[28],\"hints\":\"abbrev\",\"levelParams\":[11],\"name\":28,\"safety\":\"safe\",\"type\":96,\"value\":99}}",
   "{\"def\":{\"all\":[46],\"hints\":{\"regular\":1},\"levelParams\":[],\"name\":46,\"safety\":\"safe\",\"type\":155,\"value\":160}}",
   "{\"def\":{\"all\":[46],\"hints\":{ \"regular\" : 1 },\"levelParams\":[],\"name\":46,\"safety\":\"safe\",\"type\":155,\"value\":160}}",
   "{\"thm\":{\"all\":[43],\"levelParams\":[],\"name\":43,\"type\":161,\"value\":166}}",
   "{\"quot\": {\"name\": 5, \"levelParams\": [], \"type\": 132, \"kind\": \"type\"}}",
   "{\"opaque\":{\"all\":[31],\"isUnsafe\":false,\"levelParams\":[],\"name\":31,\"type\":43,\"value\":108}}",
   "{\"inductive\":{\"ctors\":[{\"cidx\":0,\"induct\":1,\"isUnsafe\":false,\"levelParams\":[2],\"name\":9,\"numFields\":0,\"numParams\":2,\"type\":12}],\"recs\":[{\"all\":[1],\"isUnsafe\":false,\"k\":true,\"levelParams\":[11,2],\"name\":10,\"numIndices\":1,\"numMinors\":1,\"numMotives\":1,\"numParams\":2,\"rules\":[{\"ctor\":9,\"nfields\":0,\"rhs\":41}],\"type\":37}],\"types\":[{\"all\":[1],\"ctors\":[9],\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,\"levelParams\":[2],\"name\":1,\"numIndices\":1,\"numNested\":0,\"numParams\":2,\"type\":6}]}}",
   "{\"inductive\":{\"ctors\":[],\"recs\":[],\"types\":[]}}",
   -- the refusals
   "{\"ie\":8,\"app\":{\"arg\":1,\"fn\":7},\"nope\":1}",
   "{\"ie\":8,\"ie\":9,\"bvar\":0}",
   "{\"ie\":8,\"app\":{\"arg\":1}}",
   "{\"ie\":8,\"bvar\":0} x",
   "{\"ie\":8,\"str\":{\"pre\":0,\"str\":\"a\"}}",
   "{\"ie\":8,\"bvar\":x}",
   "{\"ie\":8,\"lam\":{\"binderInfo\":\"nope\",\"body\":4,\"name\":1,\"type\":0}}",
   "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"a}}",
   "{\"ie\":8,\"const\":{\"name\":1,\"us\":[1,]}}",
   "not an object",
   "{\"ie\":8,\"const\":{\"name\":1,\"us\":[01]}}",
   "{\"ie\":08,\"bvar\":0}",
   "{\"def\":{\"hints\":{\"regular\" 1},\"levelParams\":[],\"name\":46,\"type\":155,\"value\":160}}",
   "{\"def\":{\"hints\":{\"regulax\":1},\"levelParams\":[],\"name\":46,\"type\":155,\"value\":160}}",
   "{\"ie\":8,\"bvar\":0,}",
   "{,\"ie\":8}",
   "{\"ie\":8 \"bvar\":0}",
   "{\"ie\"8}",
   "{\"ie\":8,\"app\":{\"arg\":1,\"fn\":7}",
   "{\"ie\":8,\"lam\":{\"binderInfo\":\"default\",\"body\":4,\"name\":1,\"type\":0,\"pw\":[2,]}}",
   "{\"ie\":8,\"lam\":{\"binderInfo\":\"default\",\"body\":4,\"name\":1,\"type\":0,\"pw\":\"nope\"}}",
   "{\"meta\":{\"unbalanced\":[}}",
   "{\"meta\":[1,2]}",
   "{\"il\":2,\"max\":[1,0,3]}"]

#guard probes.all fun s => specLine s == fastLine s

-- The equality's footprint: the standard three, nothing else (the
-- companion of the pin in `Axioms.lean`, for the frontend's theorem).
/--
info: 'ConLeche.Frontend.scanLineSpec_eq_scanLineFwd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms scanLineSpec_eq_scanLineFwd

end ConLecheTests
