module

public import Std.Data.HashMap.Basic
/- The laws of `IdTable` below are proved here, beside the structure (the
Std.HashMap pattern: the representation carries its own verification). -/
import Std.Data.HashMap.Lemmas

@[expose] public section

/-!
# The lean4export dialect: its syntax records and its key alphabet (task #256)

The stream the checker reads is NDJSON in one fixed dialect —
lean4export 3.x, plus the `pw` field the checker's own annotated
output writes (`ConLeche/Frontend/ExportWrite.lean`).  This module is
the dialect's *syntax*: one record per line shape, in **stream
indices**, with nothing resolved and no representation in sight.  The
byte recogniser (`ConLeche/Frontend/Scan/Fast.lean`) produces these;
the semantic layer (`applyLine` in `ConLeche/Frontend/ExportC.lean`)
consumes them and does what it always did — resolve the indices,
build the `ExprC`/`Name`/`Level` nodes through the smart
constructors, run the taint policy, the prelude dedupe, the
projection rewrite and the in-process modeller.

Three things live here besides the records:

* `Key`, the dialect's whole key alphabet as a no-argument
  enumeration (Lean compiles such a type to a scalar, so classifying a
  key allocates nothing) — the recogniser is order-insensitive, so
  every object is read by a slot loop that classifies a key, fills its
  slot and marks a seen-bit;
* `ScanErr` and `ScanRes`: a failure is a position and a static tag,
  so the recogniser never formats a message, and a success is ONE
  object carrying the value and the position after it;
* `IdTable`, the stream-index-keyed table the parse state uses for
  names, levels and expressions.  lean4export emits ids densely and in
  order, and a dense `Array` serves them without hashing; the sparse
  overflow map keeps the hand-written arena fixtures with gaps and
  out-of-order ids working (`_tmp/arena-tests/good/sparse-name-index`,
  `level-index-out-of-order`).
-/

namespace ConLeche.Frontend

/-! ## Errors -/

/-- What went wrong, as a static tag: the recogniser reports a
position and one of these, and the driver renders the sentence.  No
`s!"…"` runs while a stream is being read. -/
inductive ErrTag where
  /-- a line that is not `{`…`}` -/
  | expectedObject
  /-- a key was expected (an opening quote) -/
  | expectedKey
  /-- `:` was expected after a key -/
  | expectedColon
  /-- `,` or `}` was expected after a member -/
  | expectedComma
  /-- `[` or `]` was expected, or a list member -/
  | expectedList
  /-- a key that is not in the dialect -/
  | unknownKey
  /-- the same key twice in one object -/
  | duplicateKey
  /-- an object that lacks a key its kind requires -/
  | missingKey
  /-- an object that mixes two kinds' keys (e.g. `in` with `app`) -/
  | mixedKeys
  /-- a decimal number was expected -/
  | expectedNat
  /-- a JSON string was expected, or one that does not end -/
  | expectedString
  /-- `true` or `false` was expected -/
  | expectedBool
  /-- a string escape the dialect does not have -/
  | badEscape
  /-- a string whose bytes are not UTF-8 -/
  | badUtf8
  /-- a `binderInfo` spelling that is not one of the four -/
  | badBinderInfo
  /-- a `hints` field that is neither a spelling nor `{"regular":n}` -/
  | badHints
  /-- a `pw` field that is neither `"never"` nor a list -/
  | badPw
  /-- a `natVal` literal that is not a quoted decimal -/
  | badNatVal
  /-- bytes after the line's closing brace -/
  | trailing
  /-- a scanner that did not advance (unreachable: every scanner
  consumes at least the byte it dispatched on; the check is what makes
  the loops' termination measure the remaining bytes) -/
  | noProgress
  deriving DecidableEq

/-- Where the recogniser stopped, and why. -/
structure ScanErr where
  /-- byte offset from the start of the line -/
  offset : Nat
  what : ErrTag

/-- The sentence the driver prints for a syntactic failure. -/
def ErrTag.describe : ErrTag → String
  | .expectedObject => "expected a JSON object"
  | .expectedKey => "expected a key"
  | .expectedColon => "expected ':' after a key"
  | .expectedComma => "expected ',' or '}'"
  | .expectedList => "expected a JSON list"
  | .unknownKey => "unknown key"
  | .duplicateKey => "duplicate key"
  | .missingKey => "missing key"
  | .mixedKeys => "keys of two different record kinds in one line"
  | .expectedNat => "expected a decimal number"
  | .expectedString => "expected a JSON string"
  | .expectedBool => "expected true or false"
  | .badEscape => "unknown string escape"
  | .badUtf8 => "string is not valid UTF-8"
  | .badBinderInfo => "unknown binderInfo"
  | .badHints => "malformed hints field"
  | .badPw => "malformed pw field"
  | .badNatVal => "malformed natVal literal"
  | .trailing => "trailing bytes after the record"
  | .noProgress => "a scanner made no progress"

/-- A scanner's result: the value and the position after it, or a
failure.  ONE constructor, with the position in the constructor's
scalar area: an `Except ScanErr (α × USize)` would be three heap
objects per scan — the `ok`, the pair, and a box for the machine word
— and the recogniser makes tens of millions of them. -/
inductive ScanRes (α : Type) where
  | ok (val : α) (pos : USize)
  | err (e : ScanErr)

/-- The parse-error message, at the byte offset in the line. -/
def ScanErr.render (e : ScanErr) : String :=
  s!"{e.what.describe} (byte {e.offset})"

/-! ## The syntax records -/

/-- A name-table entry: `{"in":i,"str":{"pre":p,"str":s}}` or
`{"in":i,"num":{"i":n,"pre":p}}`. -/
inductive NameRec where
  | str (pre : Nat) (s : String)
  | num (pre : Nat) (n : Nat)

/-- A level-table entry. -/
inductive LevelRec where
  | succ (u : Nat)
  | max (u v : Nat)
  | imax (u v : Nat)
  | param (n : Nat)

/-- The `pw` datum a binder may carry (the checker's own annotated
output; absent in a raw export, which is `never`).  Name indices. -/
inductive PwRec where
  | never
  | ifAllZero (names : List Nat)

/-- An expression-table entry.  The binder `name` index is required to
be present and well-formed and is then DROPPED (task #203: parsed
binders are anonymous), as is `binderInfo` (task #142) and `letE`'s
`nondep`. -/
inductive ExprRec where
  | bvar (k : Nat)
  | sort (u : Nat)
  | const (name : Nat) (us : List Nat)
  | app (fn arg : Nat)
  | lam (type body : Nat) (pw : PwRec)
  | forallE (type body : Nat) (pw : PwRec)
  | letE (type value body : Nat)
  | proj (typeName idx struct : Nat)
  | natVal (n : Nat)
  | strVal (s : String)

/-- A declaration's common data, in stream indices. -/
structure CVRec where
  name : Nat
  levelParams : List Nat
  type : Nat

/-- A definition's reducibility hint. -/
inductive HintsRec where
  | «abbrev»
  | «opaque»
  | regular (n : Nat)

/-- One recursor rule. -/
structure RuleRec where
  ctor : Nat
  nfields : Nat
  rhs : Nat

/-- One member of an inductive block's `types`. -/
structure IndTypeRec where
  cv : CVRec
  ctors : List Nat
  isRec : Bool
  isReflexive : Bool
  isUnsafe : Bool
  numIndices : Nat
  numNested : Nat
  numParams : Nat

/-- One member of an inductive block's `ctors`.  `cidx` and `induct`
are the format's REDUNDANT fields (task #271, issues #5 and #7): the
block's own records determine both, and the parse validates what the
stream claims against them.  They are optional in the dialect — a
record that omits one carries `none` and is not contradicted. -/
structure IndCtorRec where
  cv : CVRec
  isUnsafe : Bool
  numFields : Nat
  numParams : Nat
  /-- the claimed position of this constructor in its type's `ctors` -/
  cidx : Option Nat := none
  /-- the claimed owning inductive type, as a name index -/
  induct : Option Nat := none

/-- One member of an inductive block's `recs`. -/
structure IndRecRec where
  cv : CVRec
  isUnsafe : Bool
  k : Bool
  numIndices : Nat
  numMinors : Nat
  numMotives : Nat
  numParams : Nat
  rules : List RuleRec

/-- A declaration record.  `safety` and `kind` keep their spelling:
both are reported back to the user verbatim (an unsupported safety is
a DECLINE naming it). -/
inductive DeclRec where
  | ax (cv : CVRec) (isUnsafe : Bool)
  | defn (cv : CVRec) (value : Nat) (hints : HintsRec) (safety : String)
  | thm (cv : CVRec) (value : Nat)
  | opaq (cv : CVRec) (value : Nat) (isUnsafe : Bool)
  | quot (cv : CVRec) (kind : String)
  | ind (types : List IndTypeRec) (ctors : List IndCtorRec)
        (recs : List IndRecRec)

/-- One line of the stream. -/
inductive LineRec where
  | name (i : Nat) (r : NameRec)
  | level (i : Nat) (r : LevelRec)
  | expr (i : Nat) (r : ExprRec)
  | decl (d : DeclRec)
  /-- the header record, validated loosely and skipped -/
  | header
  /-- whitespace only -/
  | blank

/-! ## The key alphabet -/

/-- Every key of the dialect, as a no-argument enumeration: Lean
compiles such a type to a scalar, so classifying a key allocates
nothing.  A key outside this alphabet is an error — the recogniser
knows the whole format, and a key it does not know is a stream it does
not know. -/
inductive Key where
  /-- not a key of the dialect -/
  | kUnknown
  | kAll
  | kApp
  | kArg
  | kAxiom
  | kBinderInfo
  | kBody
  | kBvar
  | kCidx
  | kConst
  | kCtor
  | kCtors
  | kDef
  | kFn
  | kForallE
  | kHints
  | kI
  | kIdx
  | kIe
  | kIl
  | kImax
  | kIn
  | kInduct
  | kInductive
  | kIsRec
  | kIsReflexive
  | kIsUnsafe
  | kK
  | kKind
  | kLam
  | kLetE
  | kLevelParams
  | kMax
  | kMeta
  | kName
  | kNatVal
  | kNfields
  | kNondep
  | kNum
  | kNumFields
  | kNumIndices
  | kNumMinors
  | kNumMotives
  | kNumNested
  | kNumParams
  | kOpaque
  | kParam
  | kPre
  | kProj
  | kPw
  | kQuot
  | kRecs
  | kRegular
  | kRhs
  | kRules
  | kSafety
  | kSort
  | kStr
  | kStrVal
  | kStruct
  | kSucc
  | kThm
  | kType
  | kTypeName
  | kTypes
  | kUs
  | kValue
  deriving DecidableEq

/-! ## The stream-index tables

`IdTable` is the partial map from stream indices the parse state keeps
for names, levels and expressions.  lean4export emits ids densely and
in increasing order, so the common insert is a push onto the dense
array — O(1), no hashing, and in place while the table is unshared
(which the state discipline of `ExportC.lean` keeps it).  A gap or an
out-of-order id goes to the sparse overflow map, which is what keeps
the hand-written arena fixtures working; the map is otherwise never
touched. -/

/-- A stream-index-keyed partial map: dense prefix, sparse overflow. -/
structure IdTable (α : Type) where
  dense : Array α := #[]
  sparse : Std.HashMap Nat α := {}

/-- The value at a stream index, dense array first. -/
def IdTable.get? (t : @& IdTable α) (i : Nat) : Option α :=
  if h : i < t.dense.size then some t.dense[i] else t.sparse[i]?

/-- Bind a stream index.  The dense case is a push; a rebinding below
the frontier overwrites; anything beyond the frontier goes sparse.
`t` is mentioned once per expression so the array stays unshared and
the push is in place. -/
def IdTable.insert (t : IdTable α) (i : Nat) (x : α) : IdTable α :=
  if i == t.dense.size then { t with dense := t.dense.push x }
  else if h : i < t.dense.size then { t with dense := t.dense.set i x h }
  else { t with sparse := t.sparse.insert i x }

/-- A table with index 0 bound (the implicit `Name.anonymous` /
`Level.zero` of the format). -/
def IdTable.singleton (x : α) : IdTable α := { dense := #[x] }

/-- Is the index bound?  The parse asks before every insert (task #290:
lean4export writes every index once, and a stream that rebinds one is
malformed — a bound entry never changes, which is what lets a theorem
about the file read an entry off the line that bound it).  The common
case — the index is the dense frontier and nothing is sparse — costs
the two comparisons and no hashing. -/
def IdTable.bound (t : @& IdTable α) (i : Nat) : Bool :=
  if i < t.dense.size then true
  else if t.sparse.isEmpty then false
  else t.sparse.contains i

/-! ### The table is its naive map

`get?` is the abstraction of the dense-plus-sparse table to the partial
map it represents, and these three laws say the operations are the
naive map's — a function from stream indices, rebound one index at a
time.  Nothing about the dense frontier or the overflow map is visible
through `get?`, and these are the only facts the semantic layer uses
about the table (task #261). -/

theorem IdTable.get?_empty (i : Nat) : ({} : IdTable α).get? i = none := by
  simp [IdTable.get?]

theorem IdTable.get?_singleton (x : α) (i : Nat) :
    (IdTable.singleton x).get? i = if i = 0 then some x else none := by
  simp [IdTable.get?, IdTable.singleton]

theorem IdTable.get?_insert (t : IdTable α) (i : Nat) (x : α) (j : Nat) :
    (t.insert i x).get? j = if j = i then some x else t.get? j := by
  unfold IdTable.insert
  by_cases hi : i = t.dense.size
  · subst hi
    simp only [BEq.rfl, ↓reduceIte, IdTable.get?, Array.size_push]
    by_cases hj : j < t.dense.size + 1
    · rw [dif_pos hj, Array.getElem_push]
      by_cases hj' : j < t.dense.size
      · simp [hj', Nat.ne_of_lt hj']
      · have : j = t.dense.size := by omega
        simp [this]
    · have h1 : j ≠ t.dense.size := by omega
      have h2 : ¬ j < t.dense.size := by omega
      simp [hj, h1, h2]
  · have hne : (i == t.dense.size) = false := by simp [hi]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    by_cases hlt : i < t.dense.size
    · simp only [hlt, ↓reduceDIte, IdTable.get?, Array.size_set]
      by_cases hj : j < t.dense.size
      · simp only [hj, ↓reduceDIte, Array.getElem_set]
        by_cases hji : j = i
        · subst hji; simp
        · simp [hji, Ne.symm hji]
      · have : j ≠ i := by omega
        simp [hj, this]
    · simp only [hlt, ↓reduceDIte, IdTable.get?]
      by_cases hj : j < t.dense.size
      · have : j ≠ i := by omega
        simp [hj, this]
      · rw [dif_neg hj, dif_neg hj, Std.HashMap.getElem?_insert]
        by_cases hji : j = i
        · subst hji; simp
        · simp [hji, Ne.symm hji]

/-- `bound` is `get?` answering: the sparse map's emptiness test is
only a shortcut. -/
theorem IdTable.bound_eq (t : IdTable α) (i : Nat) : t.bound i = (t.get? i).isSome := by
  unfold IdTable.bound IdTable.get?
  by_cases hi : i < t.dense.size
  · simp [hi]
  · simp only [hi, ↓reduceIte, ↓reduceDIte]
    by_cases he : t.sparse.isEmpty
    · simp only [he, ↓reduceIte]
      simp [Std.HashMap.getElem?_of_isEmpty he]
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      exact Std.HashMap.contains_eq_isSome_getElem?

end ConLeche.Frontend
