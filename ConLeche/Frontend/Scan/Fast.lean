module

public import ConLeche.Frontend.Scan.Types

@[expose] public section

/-!
# The byte recogniser for the lean4export dialect (task #256)
-/

namespace ConLeche.Frontend

/-! ## The bounds kit -/

/-- A `USize` position inside the array indexes it (`probe/Bound.lean`
of task #255's design). -/
theorem usizeInBounds (b : ByteArray) (i : USize) (h : i < b.usize) :
    i.toNat < b.size := by
  have h' := USize.lt_iff_toNat_lt.mp h
  simp only [ByteArray.usize, Nat.toUSize] at h'
  exact Nat.lt_of_lt_of_le h' (Nat.mod_le _ _)

/-- Stepping a position inside the array cannot wrap. -/
theorem usizeStep (b : ByteArray) (i : USize) (h : i < b.usize) :
    (i + 1).toNat = i.toNat + 1 := by
  have h' := USize.lt_iff_toNat_lt.mp h
  have hb : b.usize.toNat < USize.size := b.usize.toFin.isLt
  have : i.toNat + 1 < USize.size := by omega
  simp [USize.toNat_add, Nat.mod_eq_of_lt this]

/-- The byte at `i`, or `0` past the end.  A NUL byte never occurs in
the dialect, so `0` is a safe "nothing here" and lookahead needs no
bounds proof at the call site. -/
@[inline] def byteAt (b : @& ByteArray) (i : USize) : UInt8 :=
  if h : i < b.usize then b.uget i (usizeInBounds b i h) else 0

/-- JSON whitespace inside a line (a newline ends the line, so it is
not one here). -/
@[inline] def isWs (c : UInt8) : Bool := c == 32 || c == 9 || c == 13

@[inline] def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

/-- The first non-whitespace position at or after `i`. -/
def skipWs (b : @& ByteArray) (i : USize) : USize :=
  if h : i < b.usize then
    if isWs (b.uget i (usizeInBounds b i h)) then skipWs b (i + 1) else i
  else i
termination_by b.size - i.toNat
decreasing_by
  have := usizeInBounds b i h; have := usizeStep b i h; omega

/-- The position after the decimal digit run at `i`; `i` itself when
there is no digit there. -/
def skipDigits (b : @& ByteArray) (i : USize) : USize :=
  if h : i < b.usize then
    if isDigit (b.uget i (usizeInBounds b i h)) then skipDigits b (i + 1) else i
  else i
termination_by b.size - i.toNat
decreasing_by
  have := usizeInBounds b i h; have := usizeStep b i h; omega

/-- The value of the decimal digit run at `i`.  `Nat` accumulation, so
a literal too large for a machine word overflows into GMP by itself. -/
def readNat (b : @& ByteArray) (i : USize) (acc : Nat) : Nat :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isDigit c then readNat b (i + 1) (acc * 10 + (c.toNat - 48)) else acc
  else acc
termination_by b.size - i.toNat
decreasing_by
  have := usizeInBounds b i h; have := usizeStep b i h; omega

/-! ## Keys

A key is classified by its first byte and then by one literal
compare, the closing quote included — so `"i"` is never mistaken for
`"ie"`.  `keyLen` (`ConLeche/Frontend/Scan/Types.lean`) gives the
position after the key without a second scan. -/

/-- The bytes of `lit` from `k` on match `b` from `i` on. -/
def matchLit (b : @& ByteArray) (i : USize) (lit : @& ByteArray) (k : USize) : Bool :=
  if hk : k < lit.usize then
    if h : i < b.usize then
      b.uget i (usizeInBounds b i h) == lit.uget k (usizeInBounds lit k hk) &&
        matchLit b (i + 1) lit (k + 1)
    else false
  else true
termination_by lit.size - k.toNat
decreasing_by
  have := usizeInBounds lit k hk; have := usizeStep lit k hk; omega

/-- The position of the closing quote of the key whose *contents*
start at `j`; `0` when there is none within the line (a key never
carries an escape or a control byte).  The length it yields is what
narrows the classification below to at most a handful of candidates. -/
def keyEnd (b : @& ByteArray) (j : USize) : USize :=
  if h : j < b.usize then
    let c := b.uget j (usizeInBounds b j h)
    if c == 34 then j
    else if c < 32 || c == 92 then 0
    else keyEnd b (j + 1)
  else 0
termination_by b.size - j.toNat
decreasing_by
  have := usizeInBounds b j h; have := usizeStep b j h; omega

/-- Classify the key whose opening quote is at `i` and whose length
is `kl` bytes: a switch on the first byte, then on the length — which
leaves at most four candidates — and one literal compare of the rest.
A key outside the dialect is `kUnknown`, which every slot loop
rejects. -/
def keyAt (b : @& ByteArray) (i : USize) (kl : USize) : Key :=
  match byteAt b (i + 1) with
  | 97 =>   -- 'a'
    if kl == 3 then
      if matchLit b (i + 1 + 1) "pp".toUTF8 0 then .kApp
      else if matchLit b (i + 1 + 1) "rg".toUTF8 0 then .kArg
      else if matchLit b (i + 1 + 1) "ll".toUTF8 0 then .kAll
      else .kUnknown
    else if kl == 5 then
      if matchLit b (i + 1 + 1) "xiom".toUTF8 0 then .kAxiom
      else .kUnknown
    else .kUnknown
  | 98 =>   -- 'b'
    if kl == 4 then
      if matchLit b (i + 1 + 1) "ody".toUTF8 0 then .kBody
      else if matchLit b (i + 1 + 1) "var".toUTF8 0 then .kBvar
      else .kUnknown
    else if kl == 10 then
      if matchLit b (i + 1 + 1) "inderInfo".toUTF8 0 then .kBinderInfo
      else .kUnknown
    else .kUnknown
  | 99 =>   -- 'c'
    if kl == 5 then
      if matchLit b (i + 1 + 1) "onst".toUTF8 0 then .kConst
      else if matchLit b (i + 1 + 1) "tors".toUTF8 0 then .kCtors
      else .kUnknown
    else if kl == 4 then
      if matchLit b (i + 1 + 1) "tor".toUTF8 0 then .kCtor
      else if matchLit b (i + 1 + 1) "idx".toUTF8 0 then .kCidx
      else .kUnknown
    else .kUnknown
  | 100 =>   -- 'd'
    if kl == 3 then
      if matchLit b (i + 1 + 1) "ef".toUTF8 0 then .kDef
      else .kUnknown
    else .kUnknown
  | 102 =>   -- 'f'
    if kl == 2 then
      if matchLit b (i + 1 + 1) "n".toUTF8 0 then .kFn
      else .kUnknown
    else if kl == 7 then
      if matchLit b (i + 1 + 1) "orallE".toUTF8 0 then .kForallE
      else .kUnknown
    else .kUnknown
  | 104 =>   -- 'h'
    if kl == 5 then
      if matchLit b (i + 1 + 1) "ints".toUTF8 0 then .kHints
      else .kUnknown
    else .kUnknown
  | 105 =>   -- 'i'
    if kl == 2 then
      if matchLit b (i + 1 + 1) "e".toUTF8 0 then .kIe
      else if matchLit b (i + 1 + 1) "n".toUTF8 0 then .kIn
      else if matchLit b (i + 1 + 1) "l".toUTF8 0 then .kIl
      else .kUnknown
    else if kl == 1 then
      .kI
    else if kl == 3 then
      if matchLit b (i + 1 + 1) "dx".toUTF8 0 then .kIdx
      else .kUnknown
    else if kl == 4 then
      if matchLit b (i + 1 + 1) "max".toUTF8 0 then .kImax
      else .kUnknown
    else if kl == 9 then
      if matchLit b (i + 1 + 1) "nductive".toUTF8 0 then .kInductive
      else .kUnknown
    else if kl == 5 then
      if matchLit b (i + 1 + 1) "sRec".toUTF8 0 then .kIsRec
      else .kUnknown
    else if kl == 11 then
      if matchLit b (i + 1 + 1) "sReflexive".toUTF8 0 then .kIsReflexive
      else .kUnknown
    else if kl == 8 then
      if matchLit b (i + 1 + 1) "sUnsafe".toUTF8 0 then .kIsUnsafe
      else .kUnknown
    else if kl == 6 then
      if matchLit b (i + 1 + 1) "nduct".toUTF8 0 then .kInduct
      else .kUnknown
    else .kUnknown
  | 107 =>   -- 'k'
    if kl == 4 then
      if matchLit b (i + 1 + 1) "ind".toUTF8 0 then .kKind
      else .kUnknown
    else if kl == 1 then
      .kK
    else .kUnknown
  | 108 =>   -- 'l'
    if kl == 3 then
      if matchLit b (i + 1 + 1) "am".toUTF8 0 then .kLam
      else .kUnknown
    else if kl == 4 then
      if matchLit b (i + 1 + 1) "etE".toUTF8 0 then .kLetE
      else .kUnknown
    else if kl == 11 then
      if matchLit b (i + 1 + 1) "evelParams".toUTF8 0 then .kLevelParams
      else .kUnknown
    else .kUnknown
  | 109 =>   -- 'm'
    if kl == 3 then
      if matchLit b (i + 1 + 1) "ax".toUTF8 0 then .kMax
      else .kUnknown
    else if kl == 4 then
      if matchLit b (i + 1 + 1) "eta".toUTF8 0 then .kMeta
      else .kUnknown
    else .kUnknown
  | 110 =>   -- 'n'
    if kl == 4 then
      if matchLit b (i + 1 + 1) "ame".toUTF8 0 then .kName
      else .kUnknown
    else if kl == 3 then
      if matchLit b (i + 1 + 1) "um".toUTF8 0 then .kNum
      else .kUnknown
    else if kl == 6 then
      if matchLit b (i + 1 + 1) "atVal".toUTF8 0 then .kNatVal
      else if matchLit b (i + 1 + 1) "ondep".toUTF8 0 then .kNondep
      else .kUnknown
    else if kl == 7 then
      if matchLit b (i + 1 + 1) "fields".toUTF8 0 then .kNfields
      else .kUnknown
    else if kl == 9 then
      if matchLit b (i + 1 + 1) "umParams".toUTF8 0 then .kNumParams
      else if matchLit b (i + 1 + 1) "umFields".toUTF8 0 then .kNumFields
      else if matchLit b (i + 1 + 1) "umMinors".toUTF8 0 then .kNumMinors
      else if matchLit b (i + 1 + 1) "umNested".toUTF8 0 then .kNumNested
      else .kUnknown
    else if kl == 10 then
      if matchLit b (i + 1 + 1) "umIndices".toUTF8 0 then .kNumIndices
      else if matchLit b (i + 1 + 1) "umMotives".toUTF8 0 then .kNumMotives
      else .kUnknown
    else .kUnknown
  | 111 =>   -- 'o'
    if kl == 6 then
      if matchLit b (i + 1 + 1) "paque".toUTF8 0 then .kOpaque
      else .kUnknown
    else .kUnknown
  | 112 =>   -- 'p'
    if kl == 3 then
      if matchLit b (i + 1 + 1) "re".toUTF8 0 then .kPre
      else .kUnknown
    else if kl == 5 then
      if matchLit b (i + 1 + 1) "aram".toUTF8 0 then .kParam
      else .kUnknown
    else if kl == 4 then
      if matchLit b (i + 1 + 1) "roj".toUTF8 0 then .kProj
      else .kUnknown
    else if kl == 2 then
      if matchLit b (i + 1 + 1) "w".toUTF8 0 then .kPw
      else .kUnknown
    else .kUnknown
  | 113 =>   -- 'q'
    if kl == 4 then
      if matchLit b (i + 1 + 1) "uot".toUTF8 0 then .kQuot
      else .kUnknown
    else .kUnknown
  | 114 =>   -- 'r'
    if kl == 4 then
      if matchLit b (i + 1 + 1) "ecs".toUTF8 0 then .kRecs
      else .kUnknown
    else if kl == 5 then
      if matchLit b (i + 1 + 1) "ules".toUTF8 0 then .kRules
      else .kUnknown
    else if kl == 3 then
      if matchLit b (i + 1 + 1) "hs".toUTF8 0 then .kRhs
      else .kUnknown
    else if kl == 7 then
      if matchLit b (i + 1 + 1) "egular".toUTF8 0 then .kRegular
      else .kUnknown
    else .kUnknown
  | 115 =>   -- 's'
    if kl == 3 then
      if matchLit b (i + 1 + 1) "tr".toUTF8 0 then .kStr
      else .kUnknown
    else if kl == 4 then
      if matchLit b (i + 1 + 1) "ort".toUTF8 0 then .kSort
      else if matchLit b (i + 1 + 1) "ucc".toUTF8 0 then .kSucc
      else .kUnknown
    else if kl == 6 then
      if matchLit b (i + 1 + 1) "truct".toUTF8 0 then .kStruct
      else if matchLit b (i + 1 + 1) "trVal".toUTF8 0 then .kStrVal
      else if matchLit b (i + 1 + 1) "afety".toUTF8 0 then .kSafety
      else .kUnknown
    else .kUnknown
  | 116 =>   -- 't'
    if kl == 4 then
      if matchLit b (i + 1 + 1) "ype".toUTF8 0 then .kType
      else .kUnknown
    else if kl == 8 then
      if matchLit b (i + 1 + 1) "ypeName".toUTF8 0 then .kTypeName
      else .kUnknown
    else if kl == 3 then
      if matchLit b (i + 1 + 1) "hm".toUTF8 0 then .kThm
      else .kUnknown
    else if kl == 5 then
      if matchLit b (i + 1 + 1) "ypes".toUTF8 0 then .kTypes
      else .kUnknown
    else .kUnknown
  | 117 =>   -- 'u'
    if kl == 2 then
      if matchLit b (i + 1 + 1) "s".toUTF8 0 then .kUs
      else .kUnknown
    else .kUnknown
  | 118 =>   -- 'v'
    if kl == 5 then
      if matchLit b (i + 1 + 1) "alue".toUTF8 0 then .kValue
      else .kUnknown
    else .kUnknown
  | _ => .kUnknown

/-- The position of a key's value, given the key's closing quote at
`ke`: past the colon, whitespace skipped on both sides.  `i` when the
colon is missing, which every caller rejects. -/
def valueAt (b : @& ByteArray) (i ke : USize) : USize :=
  let p := skipWs b (ke + 1)
  if byteAt b p == 58 then skipWs b (p + 1) else i

/-! ## Scalars

Every scanner below takes the position of its value and returns the
value with the position after it.  The primitive digit scanners
(`skipDigits`, `readNat`) return positions and values separately, so
reading a `Nat` — the overwhelmingly common value — allocates
nothing at all. -/

/-- `true` or `false`. -/
def scanBool (b : @& ByteArray) (i : USize) : ScanRes Bool :=
  if matchLit b i "true".toUTF8 0 then .ok true (i + 4)
  else if matchLit b i "false".toUTF8 0 then .ok false (i + 5)
  else .err ⟨i.toNat, .expectedBool⟩

/-- The value of the decimal digit run `[i, e)` in a machine word.
The caller checks the run is at most 18 digits, which cannot
overflow — every stream index and every `numParams` is far below
that, and the rare long `natVal` literal takes `readNat`. -/
def readNat64 (b : @& ByteArray) (i e : USize) (acc : UInt64) : UInt64 :=
  if h : i < b.usize then
    if i < e then
      readNat64 b (i + 1) e (acc * 10 + (b.uget i (usizeInBounds b i h) - 48).toUInt64)
    else acc
  else acc
termination_by b.size - i.toNat
decreasing_by
  have := usizeInBounds b i h; have := usizeStep b i h; omega

/-- The value of the decimal digit run `[i, e)`: a machine word while
the run is short enough for one, `Nat` accumulation (which overflows
into GMP by itself) for a long literal. -/
def readNatAt (b : @& ByteArray) (i e : USize) : Nat :=
  if e - i ≤ 18 then (readNat64 b i e 0).toNat else readNat b i 0

/-- The position of the closing quote of the string whose *contents*
start at `j`; `0` when it is unterminated or holds a raw control byte
(`0` is not a possible answer — a closing quote is at least one byte
past the opening one). -/
def strClose (b : @& ByteArray) (j : USize) : USize :=
  if h : j < b.usize then
    let c := b.uget j (usizeInBounds b j h)
    if c == 34 then j
    else if c == 92 then
      if h2 : j + 1 < b.usize then strClose b (j + 1 + 1) else 0
    else if c < 32 then 0
    else strClose b (j + 1)
  else 0
termination_by b.size - j.toNat
decreasing_by
  · have := usizeInBounds b j h; have := usizeStep b j h
    have := usizeStep b (j + 1) h2; omega
  · have := usizeInBounds b j h; have := usizeStep b j h; omega

/-- Does the string body `[j, e)` contain a backslash? -/
def hasEscape (b : @& ByteArray) (j e : USize) : Bool :=
  if h : j < b.usize then
    if j < e then
      if b.uget j (usizeInBounds b j h) == 92 then true else hasEscape b (j + 1) e
    else false
  else false
termination_by b.size - j.toNat
decreasing_by
  have := usizeInBounds b j h; have := usizeStep b j h; omega

/-- The value of a hexadecimal digit. -/
def hexVal (c : UInt8) : Option UInt32 :=
  if 48 ≤ c && c ≤ 57 then some (c.toUInt32 - 48)
  else if 97 ≤ c && c ≤ 102 then some (c.toUInt32 - 87)
  else if 65 ≤ c && c ≤ 70 then some (c.toUInt32 - 55)
  else none

/-- The value of the four hexadecimal digits at `j`. -/
def hex4 (b : @& ByteArray) (j : USize) : Option UInt32 := do
  let a ← hexVal (byteAt b j)
  let c ← hexVal (byteAt b (j + 1))
  let d ← hexVal (byteAt b (j + 1 + 1))
  let e ← hexVal (byteAt b (j + 1 + 1 + 1))
  some ((a <<< 12) ||| (c <<< 8) ||| (d <<< 4) ||| e)

/-- The value of the three hexadecimal digits at `j` (a surrogate
continuation `\uDxxx`, whose leading `d` the caller has matched). -/
def hex3 (b : @& ByteArray) (j : USize) : Option UInt32 := do
  let a ← hexVal (byteAt b j)
  let c ← hexVal (byteAt b (j + 1))
  let d ← hexVal (byteAt b (j + 1 + 1))
  some ((a <<< 8) ||| (c <<< 4) ||| d)

/-- The UTF-8 bytes of a code point. -/
def utf8Of (v : UInt32) : ByteArray := (String.singleton (Char.ofNat v.toNat)).toUTF8

/-- The Unicode replacement character, which is what a lone surrogate
decodes to (the toolchain's own `Lean.Json` reader does the same). -/
def replacementChar : UInt32 := 0xFFFD

/-- Decode the string body `[j, e)`, resolving escapes into `acc`.
The no-escape case never comes here (`scanString` slices instead), so
this is the rare path: 38 lines of `init-full` reach it. -/
def unescape (b : @& ByteArray) (j e : USize) (acc : ByteArray) : Option String :=
  if h : j < b.usize then
    if j < e then
      let c := b.uget j (usizeInBounds b j h)
      if c != 92 then
        (if _hj : j < j + 1 then unescape b (j + 1) e (acc.push c) else none)
      else
        let d := byteAt b (j + 1)
        let simple : Option UInt32 :=
          if d == 34 then some 34
          else if d == 92 then some 92
          else if d == 47 then some 47
          else if d == 98 then some 8
          else if d == 102 then some 12
          else if d == 110 then some 10
          else if d == 114 then some 13
          else if d == 116 then some 9
          else none
        match simple with
        | some v =>
          let j' := j + 1 + 1
          if _hj : j < j' then unescape b j' e (acc ++ utf8Of v) else none
        | none =>
          if d != 117 then none
          else
            match hex4 b (j + 1 + 1) with
            | none => none
            | some v =>
              let j6 := j + 1 + 1 + 1 + 1 + 1 + 1
              if v < 0xD800 || 0xE000 ≤ v then
                (if _hj : j < j6 then unescape b j6 e (acc ++ utf8Of v) else none)
              else if 0xDC00 ≤ v then
                (if _hj : j < j6 then
                    unescape b j6 e (acc ++ utf8Of replacementChar) else none)
              else
                -- a high surrogate: the toolchain's reader looks for a
                -- `\uDxxx` continuation and falls back to U+FFFD
                let cont :=
                  byteAt b j6 == 92 && byteAt b (j6 + 1) == 117 &&
                    (byteAt b (j6 + 1 + 1) == 100 || byteAt b (j6 + 1 + 1) == 68)
                match (if cont then hex3 b (j6 + 1 + 1 + 1) else none) with
                | some v2 =>
                  if v2 < 0xC00 then
                    (if _hj : j < j6 then
                        unescape b j6 e (acc ++ utf8Of replacementChar) else none)
                  else
                    let j12 := j6 + 1 + 1 + 1 + 1 + 1 + 1
                    let cv := (((v &&& 0x3FF) <<< 10) ||| (v2 &&& 0x3FF)) + 0x10000
                    if _hj : j < j12 then unescape b j12 e (acc ++ utf8Of cv) else none
                | none =>
                  if _hj : j < j6 then
                    unescape b j6 e (acc ++ utf8Of replacementChar) else none
    else String.fromUTF8? acc
  else String.fromUTF8? acc
termination_by b.size - j.toNat
decreasing_by
  all_goals exact Nat.sub_lt_sub_left (usizeInBounds b j h) (USize.lt_iff_toNat_lt.mp _hj)

/-- A JSON string at `i`: the no-escape body is sliced out of the
chunk and validated by `String.fromUTF8?`; a backslash diverts to
`unescape`. -/
def scanString (b : @& ByteArray) (i : USize) : ScanRes String :=
  if byteAt b i != 34 then .err ⟨i.toNat, .expectedString⟩
  else
    let e := strClose b (i + 1)
    if e == 0 then .err ⟨i.toNat, .expectedString⟩
    else if hasEscape b (i + 1) e then
      match unescape b (i + 1) e ByteArray.empty with
      | some s => .ok s (e + 1)
      | none => .err ⟨i.toNat, .badEscape⟩
    else
      match String.fromUTF8? (b.extract (i + 1).toNat e.toNat) with
      | some s => .ok s (e + 1)
      | none => .err ⟨i.toNat, .badUtf8⟩

/-- A quoted decimal (`"natVal":"12"`). -/
def scanQuotedNat (b : @& ByteArray) (i : USize) : ScanRes Nat :=
  if byteAt b i != 34 then .err ⟨i.toNat, .badNatVal⟩
  else
    let e := skipDigits b (i + 1)
    if e == i + 1 || byteAt b e != 34 then .err ⟨i.toNat, .badNatVal⟩
    else .ok (readNatAt b (i + 1) e) (e + 1)

/-- The four `binderInfo` spellings, validated and dropped (task
#142): kernel typing erases binder annotations, and an unknown
spelling is a malformed record rather than a silently ignored one. -/
def scanBinderInfo (b : @& ByteArray) (i : USize) : USize :=
  if byteAt b i != 34 then 0
  else if matchLit b (i + 1) "default\"".toUTF8 0 then i + 9
  else if matchLit b (i + 1) "implicit\"".toUTF8 0 then i + 10
  else if matchLit b (i + 1) "strictImplicit\"".toUTF8 0 then i + 16
  else if matchLit b (i + 1) "instImplicit\"".toUTF8 0 then i + 14
  else 0

/-! ## Lists -/

/-- `[n, …]`, the shape every index list of the format has.
`wantItem` is JSON's own alternation: no empty member, no trailing
comma. -/
def scanNatListLoop (b : @& ByteArray) (i : USize) (acc : List Nat)
    (wantItem : Bool) : ScanRes (List Nat) :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanNatListLoop b (i + 1) acc wantItem
    else if c == 93 then
      if wantItem && !acc.isEmpty then .err ⟨i.toNat, .expectedList⟩
      else .ok acc.reverse (i + 1)
    else if c == 44 then
      if wantItem then .err ⟨i.toNat, .expectedList⟩
      else scanNatListLoop b (i + 1) acc true
    else if isDigit c then
      if !wantItem then .err ⟨i.toNat, .expectedList⟩
      else
        let e := skipDigits b i
        if _hj : i < e then scanNatListLoop b e (readNatAt b i e :: acc) false
        else .err ⟨i.toNat, .noProgress⟩
    else .err ⟨i.toNat, .expectedList⟩
  else .err ⟨i.toNat, .expectedList⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

def scanNatList (b : @& ByteArray) (i : USize) : ScanRes (List Nat) :=
  if byteAt b i == 91 then scanNatListLoop b (i + 1) [] true
  else .err ⟨i.toNat, .expectedList⟩

/-! ## The two variant-valued fields -/

/-- The `pw` datum: `"never"` or a list of name indices. -/
def scanPw (b : @& ByteArray) (i : USize) : ScanRes PwRec :=
  if byteAt b i == 91 then
    match scanNatListLoop b (i + 1) [] true with
    | .err e => .err e
    | .ok ns j => .ok (.ifAllZero ns) j
  else if byteAt b i == 34 then
    if matchLit b (i + 1) "never\"".toUTF8 0 then .ok .never (i + 7)
    else .err ⟨i.toNat, .badPw⟩
  else .err ⟨i.toNat, .badPw⟩

/-- A definition's `hints`: `"abbrev"`, `"opaque"` or `{"regular":n}`. -/
def scanHints (b : @& ByteArray) (i : USize) : ScanRes HintsRec :=
  if byteAt b i == 34 then
    if matchLit b (i + 1) "abbrev\"".toUTF8 0 then .ok .«abbrev» (i + 8)
    else if matchLit b (i + 1) "opaque\"".toUTF8 0 then .ok .«opaque» (i + 8)
    else .err ⟨i.toNat, .badHints⟩
  else if byteAt b i == 123 then
    let p := skipWs b (i + 1)
    if byteAt b p != 34 then .err ⟨i.toNat, .badHints⟩
    else
      match keyAt b p (keyEnd b (p + 1) - (p + 1)) with
      | .kRegular =>
        let v := valueAt b p (p + 8)
        let e := skipDigits b v
        if e == v then .err ⟨v.toNat, .expectedNat⟩
        else
          let q := skipWs b e
          if byteAt b q == 125 then .ok (.regular (readNatAt b v e)) (q + 1)
          else .err ⟨q.toNat, .expectedComma⟩
      | _ => .err ⟨p.toNat, .badHints⟩
  else .err ⟨i.toNat, .badHints⟩

/-! ## The `meta` header

Decision of task #256: the header is validated *loosely* — its value
must be a bracket- and string-balanced JSON value — and skipped.  It
carries the exporter's name and version and nothing the checker
reads. -/

/-- Skip a `{`/`[`-opened value whose opening bracket is at `i - 1`,
counting brackets and stepping over strings; `0` when it does not
close. -/
def skipBraced (b : @& ByteArray) (i : USize) (depth : Nat) : USize :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if c == 34 then
      let e := strClose b (i + 1)
      if e == 0 then 0
      else if _hj : i < e + 1 then skipBraced b (e + 1) depth else 0
    else if c == 123 || c == 91 then skipBraced b (i + 1) (depth + 1)
    else if c == 125 || c == 93 then
      match depth with
      | 0 => i + 1
      | d + 1 => skipBraced b (i + 1) d
    else skipBraced b (i + 1) depth
  else 0
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)


/-! ## The objects

Every object of the dialect is read by the same **slot loop**: a
key is classified, its value is scanned into a slot, and a bit is set
in `seen`.  Key order is therefore irrelevant (the raw stream sorts
its keys; hand-written fixtures do not, and JSON's contract is that
neither matters), a duplicate key is an error, a key outside the
dialect is an error, and the closing brace checks that every key the
record kind requires has been seen.  `wantMember` is JSON's own
alternation: no empty member, no trailing comma.

Slots the checker does not read (`all`, `cidx`, `induct`, `k`,
`nondep`, a binder's `name` and `binderInfo`) are still parsed and
validated — the format has them, so a record missing one is a record
this recogniser does not know.
-/

def scanStrNameLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (pre : Nat)
    (s : String) : ScanRes NameRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanStrNameLoop b (i + 1) wantMember seen pre s
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 3) != 3 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.str pre s) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanStrNameLoop b (i + 1) true seen pre s
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kPre =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanStrNameLoop b e false (seen ||| 1) (readNatAt b v e) s
            else .err ⟨i.toNat, .noProgress⟩
        | .kStr =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanString b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanStrNameLoop b e false (seen ||| 2) pre x
              else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- `{"pre":p,"str":s}` — a name-table entry's string payload. -/
def scanStrName (b : @& ByteArray) (i : USize) : ScanRes NameRec :=
  if byteAt b i == 123 then
    scanStrNameLoop b (i + 1) true 0 0 ""
  else .err ⟨i.toNat, .expectedObject⟩

def scanNumNameLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (n : Nat)
    (pre : Nat) : ScanRes NameRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanNumNameLoop b (i + 1) wantMember seen n pre
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 3) != 3 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.num pre n) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanNumNameLoop b (i + 1) true seen n pre
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kI =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanNumNameLoop b e false (seen ||| 1) (readNatAt b v e) pre
            else .err ⟨i.toNat, .noProgress⟩
        | .kPre =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanNumNameLoop b e false (seen ||| 2) n (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- `{"i":n,"pre":p}` — a name-table entry's numeric payload. -/
def scanNumName (b : @& ByteArray) (i : USize) : ScanRes NameRec :=
  if byteAt b i == 123 then
    scanNumNameLoop b (i + 1) true 0 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanAppExprLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (arg : Nat)
    (fn : Nat) : ScanRes ExprRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanAppExprLoop b (i + 1) wantMember seen arg fn
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 3) != 3 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.app fn arg) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanAppExprLoop b (i + 1) true seen arg fn
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kArg =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanAppExprLoop b e false (seen ||| 1) (readNatAt b v e) fn
            else .err ⟨i.toNat, .noProgress⟩
        | .kFn =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanAppExprLoop b e false (seen ||| 2) arg (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- `{"arg":A,"fn":F}` — 80 % of every stream's lines. -/
def scanAppExpr (b : @& ByteArray) (i : USize) : ScanRes ExprRec :=
  if byteAt b i == 123 then
    scanAppExprLoop b (i + 1) true 0 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanLamExprLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (bd : Nat)
    (ty : Nat)
    (pw : PwRec) : ScanRes ExprRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanLamExprLoop b (i + 1) wantMember seen bd ty pw
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 15) != 15 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.lam ty bd pw) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanLamExprLoop b (i + 1) true seen bd ty pw
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kBinderInfo =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := scanBinderInfo b v
            if e == 0 then .err ⟨v.toNat, .badBinderInfo⟩
            else if _hj : i < e then
              scanLamExprLoop b e false (seen ||| 1) bd ty pw
            else .err ⟨i.toNat, .noProgress⟩
        | .kBody =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanLamExprLoop b e false (seen ||| 2) (readNatAt b v e) ty pw
            else .err ⟨i.toNat, .noProgress⟩
        | .kName =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanLamExprLoop b e false (seen ||| 4) bd ty pw
            else .err ⟨i.toNat, .noProgress⟩
        | .kType =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanLamExprLoop b e false (seen ||| 8) bd (readNatAt b v e) pw
            else .err ⟨i.toNat, .noProgress⟩
        | .kPw =>
          if (seen &&& 16) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanPw b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanLamExprLoop b e false (seen ||| 16) bd ty x
              else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- A `lam` binder.  `binderInfo` and `name` are validated and dropped
(tasks #142, #203); `pw` is the checker's own annotation and is absent from a
raw export. -/
def scanLamExpr (b : @& ByteArray) (i : USize) : ScanRes ExprRec :=
  if byteAt b i == 123 then
    scanLamExprLoop b (i + 1) true 0 0 0 .never
  else .err ⟨i.toNat, .expectedObject⟩

def scanForallExprLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (bd : Nat)
    (ty : Nat)
    (pw : PwRec) : ScanRes ExprRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanForallExprLoop b (i + 1) wantMember seen bd ty pw
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 15) != 15 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.forallE ty bd pw) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanForallExprLoop b (i + 1) true seen bd ty pw
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kBinderInfo =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := scanBinderInfo b v
            if e == 0 then .err ⟨v.toNat, .badBinderInfo⟩
            else if _hj : i < e then
              scanForallExprLoop b e false (seen ||| 1) bd ty pw
            else .err ⟨i.toNat, .noProgress⟩
        | .kBody =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanForallExprLoop b e false (seen ||| 2) (readNatAt b v e) ty pw
            else .err ⟨i.toNat, .noProgress⟩
        | .kName =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanForallExprLoop b e false (seen ||| 4) bd ty pw
            else .err ⟨i.toNat, .noProgress⟩
        | .kType =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanForallExprLoop b e false (seen ||| 8) bd (readNatAt b v e) pw
            else .err ⟨i.toNat, .noProgress⟩
        | .kPw =>
          if (seen &&& 16) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanPw b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanForallExprLoop b e false (seen ||| 16) bd ty x
              else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- A `forallE` binder; as `lam`. -/
def scanForallExpr (b : @& ByteArray) (i : USize) : ScanRes ExprRec :=
  if byteAt b i == 123 then
    scanForallExprLoop b (i + 1) true 0 0 0 .never
  else .err ⟨i.toNat, .expectedObject⟩

def scanLetExprLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (bd : Nat)
    (ty : Nat)
    (vl : Nat) : ScanRes ExprRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanLetExprLoop b (i + 1) wantMember seen bd ty vl
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 27) != 27 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.letE ty vl bd) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanLetExprLoop b (i + 1) true seen bd ty vl
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kBody =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanLetExprLoop b e false (seen ||| 1) (readNatAt b v e) ty vl
            else .err ⟨i.toNat, .noProgress⟩
        | .kName =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanLetExprLoop b e false (seen ||| 2) bd ty vl
            else .err ⟨i.toNat, .noProgress⟩
        | .kNondep =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanBool b v with
            | .err err => .err err
            | .ok _x e =>
              if _hj : i < e then
                scanLetExprLoop b e false (seen ||| 4) bd ty vl
              else .err ⟨i.toNat, .noProgress⟩
        | .kType =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanLetExprLoop b e false (seen ||| 8) bd (readNatAt b v e) vl
            else .err ⟨i.toNat, .noProgress⟩
        | .kValue =>
          if (seen &&& 16) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanLetExprLoop b e false (seen ||| 16) bd ty (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- A `letE` binder.  `nondep` is the format's field and is not read. -/
def scanLetExpr (b : @& ByteArray) (i : USize) : ScanRes ExprRec :=
  if byteAt b i == 123 then
    scanLetExprLoop b (i + 1) true 0 0 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanConstExprLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (nm : Nat)
    (us : List Nat) : ScanRes ExprRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanConstExprLoop b (i + 1) wantMember seen nm us
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 3) != 3 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.const nm us) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanConstExprLoop b (i + 1) true seen nm us
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kName =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanConstExprLoop b e false (seen ||| 1) (readNatAt b v e) us
            else .err ⟨i.toNat, .noProgress⟩
        | .kUs =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanConstExprLoop b e false (seen ||| 2) nm x
              else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- `{"name":N,"us":[…]}`. -/
def scanConstExpr (b : @& ByteArray) (i : USize) : ScanRes ExprRec :=
  if byteAt b i == 123 then
    scanConstExprLoop b (i + 1) true 0 0 []
  else .err ⟨i.toNat, .expectedObject⟩

def scanProjExprLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (ix : Nat)
    (st : Nat)
    (tn : Nat) : ScanRes ExprRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanProjExprLoop b (i + 1) wantMember seen ix st tn
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 7) != 7 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.proj tn ix st) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanProjExprLoop b (i + 1) true seen ix st tn
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kIdx =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanProjExprLoop b e false (seen ||| 1) (readNatAt b v e) st tn
            else .err ⟨i.toNat, .noProgress⟩
        | .kStruct =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanProjExprLoop b e false (seen ||| 2) ix (readNatAt b v e) tn
            else .err ⟨i.toNat, .noProgress⟩
        | .kTypeName =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanProjExprLoop b e false (seen ||| 4) ix st (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- `{"idx":i,"struct":S,"typeName":T}`. -/
def scanProjExpr (b : @& ByteArray) (i : USize) : ScanRes ExprRec :=
  if byteAt b i == 123 then
    scanProjExprLoop b (i + 1) true 0 0 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanRuleLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (ct : Nat)
    (nf : Nat)
    (rhs : Nat) : ScanRes RuleRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanRuleLoop b (i + 1) wantMember seen ct nf rhs
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 7) != 7 then .err ⟨i.toNat, .missingKey⟩
      else .ok (⟨ct, nf, rhs⟩) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanRuleLoop b (i + 1) true seen ct nf rhs
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kCtor =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanRuleLoop b e false (seen ||| 1) (readNatAt b v e) nf rhs
            else .err ⟨i.toNat, .noProgress⟩
        | .kNfields =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanRuleLoop b e false (seen ||| 2) ct (readNatAt b v e) rhs
            else .err ⟨i.toNat, .noProgress⟩
        | .kRhs =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanRuleLoop b e false (seen ||| 4) ct nf (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- One recursor rule of an inductive record. -/
def scanRule (b : @& ByteArray) (i : USize) : ScanRes RuleRec :=
  if byteAt b i == 123 then
    scanRuleLoop b (i + 1) true 0 0 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanRuleListLoop (b : @& ByteArray) (i : USize) (acc : List RuleRec)
    (wantItem : Bool) : ScanRes (List RuleRec) :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanRuleListLoop b (i + 1) acc wantItem
    else if c == 93 then
      if wantItem && !acc.isEmpty then .err ⟨i.toNat, .expectedList⟩
      else .ok acc.reverse (i + 1)
    else if c == 44 then
      if wantItem then .err ⟨i.toNat, .expectedList⟩
      else scanRuleListLoop b (i + 1) acc true
    else if c == 123 then
      if !wantItem then .err ⟨i.toNat, .expectedList⟩
      else
        match scanRule b i with
        | .err err => .err err
        | .ok x e =>
          if _hj : i < e then scanRuleListLoop b e (x :: acc) false
          else .err ⟨i.toNat, .noProgress⟩
    else .err ⟨i.toNat, .expectedList⟩
  else .err ⟨i.toNat, .expectedList⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- The `[…]` of Rule records. -/
def scanRules (b : @& ByteArray) (i : USize) :
    ScanRes (List RuleRec) :=
  if byteAt b i == 91 then scanRuleListLoop b (i + 1) [] true
  else .err ⟨i.toNat, .expectedList⟩

def scanIndRecLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (isUns : Bool)
    (kf : Bool)
    (lps : List Nat)
    (nm : Nat)
    (nIdx : Nat)
    (nMin : Nat)
    (nMot : Nat)
    (nP : Nat)
    (rules : List RuleRec)
    (ty : Nat) : ScanRes IndRecRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanIndRecLoop b (i + 1) wantMember seen isUns kf lps nm nIdx nMin nMot nP rules ty
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 2046) != 2046 then .err ⟨i.toNat, .missingKey⟩
      else .ok (⟨⟨nm, lps, ty⟩, isUns, kf, nIdx, nMin, nMot, nP, rules⟩) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanIndRecLoop b (i + 1) true seen isUns kf lps nm nIdx nMin nMot nP rules ty
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kAll =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok _x e =>
              if _hj : i < e then
                scanIndRecLoop b e false (seen ||| 1) isUns kf lps nm nIdx nMin nMot nP rules ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kIsUnsafe =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanBool b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndRecLoop b e false (seen ||| 2) x kf lps nm nIdx nMin nMot nP rules ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kK =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanBool b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndRecLoop b e false (seen ||| 4) isUns x lps nm nIdx nMin nMot nP rules ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kLevelParams =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndRecLoop b e false (seen ||| 8) isUns kf x nm nIdx nMin nMot nP rules ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kName =>
          if (seen &&& 16) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndRecLoop b e false (seen ||| 16) isUns kf lps (readNatAt b v e) nIdx nMin nMot nP rules ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kNumIndices =>
          if (seen &&& 32) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndRecLoop b e false (seen ||| 32) isUns kf lps nm (readNatAt b v e) nMin nMot nP rules ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kNumMinors =>
          if (seen &&& 64) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndRecLoop b e false (seen ||| 64) isUns kf lps nm nIdx (readNatAt b v e) nMot nP rules ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kNumMotives =>
          if (seen &&& 128) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndRecLoop b e false (seen ||| 128) isUns kf lps nm nIdx nMin (readNatAt b v e) nP rules ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kNumParams =>
          if (seen &&& 256) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndRecLoop b e false (seen ||| 256) isUns kf lps nm nIdx nMin nMot (readNatAt b v e) rules ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kRules =>
          if (seen &&& 512) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanRules b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndRecLoop b e false (seen ||| 512) isUns kf lps nm nIdx nMin nMot nP x ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kType =>
          if (seen &&& 1024) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndRecLoop b e false (seen ||| 1024) isUns kf lps nm nIdx nMin nMot nP rules (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- One member of an inductive record's `recs`. -/
def scanIndRec (b : @& ByteArray) (i : USize) : ScanRes IndRecRec :=
  if byteAt b i == 123 then
    scanIndRecLoop b (i + 1) true 0 false false [] 0 0 0 0 0 [] 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanIndRecListLoop (b : @& ByteArray) (i : USize) (acc : List IndRecRec)
    (wantItem : Bool) : ScanRes (List IndRecRec) :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanIndRecListLoop b (i + 1) acc wantItem
    else if c == 93 then
      if wantItem && !acc.isEmpty then .err ⟨i.toNat, .expectedList⟩
      else .ok acc.reverse (i + 1)
    else if c == 44 then
      if wantItem then .err ⟨i.toNat, .expectedList⟩
      else scanIndRecListLoop b (i + 1) acc true
    else if c == 123 then
      if !wantItem then .err ⟨i.toNat, .expectedList⟩
      else
        match scanIndRec b i with
        | .err err => .err err
        | .ok x e =>
          if _hj : i < e then scanIndRecListLoop b e (x :: acc) false
          else .err ⟨i.toNat, .noProgress⟩
    else .err ⟨i.toNat, .expectedList⟩
  else .err ⟨i.toNat, .expectedList⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- The `[…]` of IndRec records. -/
def scanIndRecs (b : @& ByteArray) (i : USize) :
    ScanRes (List IndRecRec) :=
  if byteAt b i == 91 then scanIndRecListLoop b (i + 1) [] true
  else .err ⟨i.toNat, .expectedList⟩

def scanIndTypeLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (ctors : List Nat)
    (isRec : Bool)
    (isRefl : Bool)
    (isUns : Bool)
    (lps : List Nat)
    (nm : Nat)
    (nIdx : Nat)
    (nNest : Nat)
    (nP : Nat)
    (ty : Nat) : ScanRes IndTypeRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanIndTypeLoop b (i + 1) wantMember seen ctors isRec isRefl isUns lps nm nIdx nNest nP ty
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 2046) != 2046 then .err ⟨i.toNat, .missingKey⟩
      else .ok (⟨⟨nm, lps, ty⟩, ctors, isRec, isRefl, isUns, nIdx, nNest, nP⟩) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanIndTypeLoop b (i + 1) true seen ctors isRec isRefl isUns lps nm nIdx nNest nP ty
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kAll =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok _x e =>
              if _hj : i < e then
                scanIndTypeLoop b e false (seen ||| 1) ctors isRec isRefl isUns lps nm nIdx nNest nP ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kCtors =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndTypeLoop b e false (seen ||| 2) x isRec isRefl isUns lps nm nIdx nNest nP ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kIsRec =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanBool b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndTypeLoop b e false (seen ||| 4) ctors x isRefl isUns lps nm nIdx nNest nP ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kIsReflexive =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanBool b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndTypeLoop b e false (seen ||| 8) ctors isRec x isUns lps nm nIdx nNest nP ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kIsUnsafe =>
          if (seen &&& 16) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanBool b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndTypeLoop b e false (seen ||| 16) ctors isRec isRefl x lps nm nIdx nNest nP ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kLevelParams =>
          if (seen &&& 32) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndTypeLoop b e false (seen ||| 32) ctors isRec isRefl isUns x nm nIdx nNest nP ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kName =>
          if (seen &&& 64) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndTypeLoop b e false (seen ||| 64) ctors isRec isRefl isUns lps (readNatAt b v e) nIdx nNest nP ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kNumIndices =>
          if (seen &&& 128) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndTypeLoop b e false (seen ||| 128) ctors isRec isRefl isUns lps nm (readNatAt b v e) nNest nP ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kNumNested =>
          if (seen &&& 256) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndTypeLoop b e false (seen ||| 256) ctors isRec isRefl isUns lps nm nIdx (readNatAt b v e) nP ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kNumParams =>
          if (seen &&& 512) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndTypeLoop b e false (seen ||| 512) ctors isRec isRefl isUns lps nm nIdx nNest (readNatAt b v e) ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kType =>
          if (seen &&& 1024) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndTypeLoop b e false (seen ||| 1024) ctors isRec isRefl isUns lps nm nIdx nNest nP (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- One member of an inductive record's `types`. -/
def scanIndType (b : @& ByteArray) (i : USize) : ScanRes IndTypeRec :=
  if byteAt b i == 123 then
    scanIndTypeLoop b (i + 1) true 0 [] false false false [] 0 0 0 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanIndTypeListLoop (b : @& ByteArray) (i : USize) (acc : List IndTypeRec)
    (wantItem : Bool) : ScanRes (List IndTypeRec) :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanIndTypeListLoop b (i + 1) acc wantItem
    else if c == 93 then
      if wantItem && !acc.isEmpty then .err ⟨i.toNat, .expectedList⟩
      else .ok acc.reverse (i + 1)
    else if c == 44 then
      if wantItem then .err ⟨i.toNat, .expectedList⟩
      else scanIndTypeListLoop b (i + 1) acc true
    else if c == 123 then
      if !wantItem then .err ⟨i.toNat, .expectedList⟩
      else
        match scanIndType b i with
        | .err err => .err err
        | .ok x e =>
          if _hj : i < e then scanIndTypeListLoop b e (x :: acc) false
          else .err ⟨i.toNat, .noProgress⟩
    else .err ⟨i.toNat, .expectedList⟩
  else .err ⟨i.toNat, .expectedList⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- The `[…]` of IndType records. -/
def scanIndTypes (b : @& ByteArray) (i : USize) :
    ScanRes (List IndTypeRec) :=
  if byteAt b i == 91 then scanIndTypeListLoop b (i + 1) [] true
  else .err ⟨i.toNat, .expectedList⟩

def scanIndCtorLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (isUns : Bool)
    (lps : List Nat)
    (nm : Nat)
    (nF : Nat)
    (nP : Nat)
    (ty : Nat) : ScanRes IndCtorRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanIndCtorLoop b (i + 1) wantMember seen isUns lps nm nF nP ty
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 252) != 252 then .err ⟨i.toNat, .missingKey⟩
      else .ok (⟨⟨nm, lps, ty⟩, isUns, nF, nP⟩) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanIndCtorLoop b (i + 1) true seen isUns lps nm nF nP ty
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kCidx =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndCtorLoop b e false (seen ||| 1) isUns lps nm nF nP ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kInduct =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndCtorLoop b e false (seen ||| 2) isUns lps nm nF nP ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kIsUnsafe =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanBool b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndCtorLoop b e false (seen ||| 4) x lps nm nF nP ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kLevelParams =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndCtorLoop b e false (seen ||| 8) isUns x nm nF nP ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kName =>
          if (seen &&& 16) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndCtorLoop b e false (seen ||| 16) isUns lps (readNatAt b v e) nF nP ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kNumFields =>
          if (seen &&& 32) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndCtorLoop b e false (seen ||| 32) isUns lps nm (readNatAt b v e) nP ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kNumParams =>
          if (seen &&& 64) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndCtorLoop b e false (seen ||| 64) isUns lps nm nF (readNatAt b v e) ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kType =>
          if (seen &&& 128) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanIndCtorLoop b e false (seen ||| 128) isUns lps nm nF nP (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- One member of an inductive record's `ctors`.  `cidx` and `induct`
are the format's fields and are not read. -/
def scanIndCtor (b : @& ByteArray) (i : USize) : ScanRes IndCtorRec :=
  if byteAt b i == 123 then
    scanIndCtorLoop b (i + 1) true 0 false [] 0 0 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanIndCtorListLoop (b : @& ByteArray) (i : USize) (acc : List IndCtorRec)
    (wantItem : Bool) : ScanRes (List IndCtorRec) :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanIndCtorListLoop b (i + 1) acc wantItem
    else if c == 93 then
      if wantItem && !acc.isEmpty then .err ⟨i.toNat, .expectedList⟩
      else .ok acc.reverse (i + 1)
    else if c == 44 then
      if wantItem then .err ⟨i.toNat, .expectedList⟩
      else scanIndCtorListLoop b (i + 1) acc true
    else if c == 123 then
      if !wantItem then .err ⟨i.toNat, .expectedList⟩
      else
        match scanIndCtor b i with
        | .err err => .err err
        | .ok x e =>
          if _hj : i < e then scanIndCtorListLoop b e (x :: acc) false
          else .err ⟨i.toNat, .noProgress⟩
    else .err ⟨i.toNat, .expectedList⟩
  else .err ⟨i.toNat, .expectedList⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- The `[…]` of IndCtor records. -/
def scanIndCtors (b : @& ByteArray) (i : USize) :
    ScanRes (List IndCtorRec) :=
  if byteAt b i == 91 then scanIndCtorListLoop b (i + 1) [] true
  else .err ⟨i.toNat, .expectedList⟩

def scanAxiomDeclLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (isUns : Bool)
    (lps : List Nat)
    (nm : Nat)
    (ty : Nat) : ScanRes DeclRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanAxiomDeclLoop b (i + 1) wantMember seen isUns lps nm ty
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 15) != 15 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.ax ⟨nm, lps, ty⟩ isUns) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanAxiomDeclLoop b (i + 1) true seen isUns lps nm ty
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kIsUnsafe =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanBool b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanAxiomDeclLoop b e false (seen ||| 1) x lps nm ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kLevelParams =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanAxiomDeclLoop b e false (seen ||| 2) isUns x nm ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kName =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanAxiomDeclLoop b e false (seen ||| 4) isUns lps (readNatAt b v e) ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kType =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanAxiomDeclLoop b e false (seen ||| 8) isUns lps nm (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- An `axiom` record. -/
def scanAxiomDecl (b : @& ByteArray) (i : USize) : ScanRes DeclRec :=
  if byteAt b i == 123 then
    scanAxiomDeclLoop b (i + 1) true 0 false [] 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanDefDeclLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (hints : HintsRec)
    (lps : List Nat)
    (nm : Nat)
    (safety : String)
    (ty : Nat)
    (vl : Nat) : ScanRes DeclRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanDefDeclLoop b (i + 1) wantMember seen hints lps nm safety ty vl
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 124) != 124 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.defn ⟨nm, lps, ty⟩ vl hints safety) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanDefDeclLoop b (i + 1) true seen hints lps nm safety ty vl
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kAll =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok _x e =>
              if _hj : i < e then
                scanDefDeclLoop b e false (seen ||| 1) hints lps nm safety ty vl
              else .err ⟨i.toNat, .noProgress⟩
        | .kHints =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanHints b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanDefDeclLoop b e false (seen ||| 2) x lps nm safety ty vl
              else .err ⟨i.toNat, .noProgress⟩
        | .kLevelParams =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanDefDeclLoop b e false (seen ||| 4) hints x nm safety ty vl
              else .err ⟨i.toNat, .noProgress⟩
        | .kName =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanDefDeclLoop b e false (seen ||| 8) hints lps (readNatAt b v e) safety ty vl
            else .err ⟨i.toNat, .noProgress⟩
        | .kSafety =>
          if (seen &&& 16) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanString b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanDefDeclLoop b e false (seen ||| 16) hints lps nm x ty vl
              else .err ⟨i.toNat, .noProgress⟩
        | .kType =>
          if (seen &&& 32) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanDefDeclLoop b e false (seen ||| 32) hints lps nm safety (readNatAt b v e) vl
            else .err ⟨i.toNat, .noProgress⟩
        | .kValue =>
          if (seen &&& 64) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanDefDeclLoop b e false (seen ||| 64) hints lps nm safety ty (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- A `def` record.  A missing `hints` field is `regular 0` — hints
steer only the unfolding order of lazy delta, so any default is behaviourally
safe. -/
def scanDefDecl (b : @& ByteArray) (i : USize) : ScanRes DeclRec :=
  if byteAt b i == 123 then
    scanDefDeclLoop b (i + 1) true 0 (.regular 0) [] 0 "" 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanThmDeclLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (lps : List Nat)
    (nm : Nat)
    (ty : Nat)
    (vl : Nat) : ScanRes DeclRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanThmDeclLoop b (i + 1) wantMember seen lps nm ty vl
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 30) != 30 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.thm ⟨nm, lps, ty⟩ vl) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanThmDeclLoop b (i + 1) true seen lps nm ty vl
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kAll =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok _x e =>
              if _hj : i < e then
                scanThmDeclLoop b e false (seen ||| 1) lps nm ty vl
              else .err ⟨i.toNat, .noProgress⟩
        | .kLevelParams =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanThmDeclLoop b e false (seen ||| 2) x nm ty vl
              else .err ⟨i.toNat, .noProgress⟩
        | .kName =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanThmDeclLoop b e false (seen ||| 4) lps (readNatAt b v e) ty vl
            else .err ⟨i.toNat, .noProgress⟩
        | .kType =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanThmDeclLoop b e false (seen ||| 8) lps nm (readNatAt b v e) vl
            else .err ⟨i.toNat, .noProgress⟩
        | .kValue =>
          if (seen &&& 16) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanThmDeclLoop b e false (seen ||| 16) lps nm ty (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- A `thm` record. -/
def scanThmDecl (b : @& ByteArray) (i : USize) : ScanRes DeclRec :=
  if byteAt b i == 123 then
    scanThmDeclLoop b (i + 1) true 0 [] 0 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanOpaqueDeclLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (isUns : Bool)
    (lps : List Nat)
    (nm : Nat)
    (ty : Nat)
    (vl : Nat) : ScanRes DeclRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanOpaqueDeclLoop b (i + 1) wantMember seen isUns lps nm ty vl
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 62) != 62 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.opaq ⟨nm, lps, ty⟩ vl isUns) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanOpaqueDeclLoop b (i + 1) true seen isUns lps nm ty vl
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kAll =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok _x e =>
              if _hj : i < e then
                scanOpaqueDeclLoop b e false (seen ||| 1) isUns lps nm ty vl
              else .err ⟨i.toNat, .noProgress⟩
        | .kIsUnsafe =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanBool b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanOpaqueDeclLoop b e false (seen ||| 2) x lps nm ty vl
              else .err ⟨i.toNat, .noProgress⟩
        | .kLevelParams =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanOpaqueDeclLoop b e false (seen ||| 4) isUns x nm ty vl
              else .err ⟨i.toNat, .noProgress⟩
        | .kName =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanOpaqueDeclLoop b e false (seen ||| 8) isUns lps (readNatAt b v e) ty vl
            else .err ⟨i.toNat, .noProgress⟩
        | .kType =>
          if (seen &&& 16) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanOpaqueDeclLoop b e false (seen ||| 16) isUns lps nm (readNatAt b v e) vl
            else .err ⟨i.toNat, .noProgress⟩
        | .kValue =>
          if (seen &&& 32) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanOpaqueDeclLoop b e false (seen ||| 32) isUns lps nm ty (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- An `opaque` record. -/
def scanOpaqueDecl (b : @& ByteArray) (i : USize) : ScanRes DeclRec :=
  if byteAt b i == 123 then
    scanOpaqueDeclLoop b (i + 1) true 0 false [] 0 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanQuotDeclLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (kind : String)
    (lps : List Nat)
    (nm : Nat)
    (ty : Nat) : ScanRes DeclRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanQuotDeclLoop b (i + 1) wantMember seen kind lps nm ty
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 15) != 15 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.quot ⟨nm, lps, ty⟩ kind) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanQuotDeclLoop b (i + 1) true seen kind lps nm ty
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kKind =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanString b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanQuotDeclLoop b e false (seen ||| 1) x lps nm ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kLevelParams =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanQuotDeclLoop b e false (seen ||| 2) kind x nm ty
              else .err ⟨i.toNat, .noProgress⟩
        | .kName =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanQuotDeclLoop b e false (seen ||| 4) kind lps (readNatAt b v e) ty
            else .err ⟨i.toNat, .noProgress⟩
        | .kType =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := skipDigits b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              scanQuotDeclLoop b e false (seen ||| 8) kind lps nm (readNatAt b v e)
            else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- A `quot` record. -/
def scanQuotDecl (b : @& ByteArray) (i : USize) : ScanRes DeclRec :=
  if byteAt b i == 123 then
    scanQuotDeclLoop b (i + 1) true 0 "" [] 0 0
  else .err ⟨i.toNat, .expectedObject⟩

def scanIndDeclLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (seen : UInt32)
    (ctors : List IndCtorRec)
    (recs : List IndRecRec)
    (types : List IndTypeRec) : ScanRes DeclRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanIndDeclLoop b (i + 1) wantMember seen ctors recs types
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& 26) != 26 then .err ⟨i.toNat, .missingKey⟩
      else .ok (.ind types ctors recs) (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanIndDeclLoop b (i + 1) true seen ctors recs types
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match keyAt b i (ke - (i + 1)) with
        | .kAll =>
          if (seen &&& 1) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanNatList b v with
            | .err err => .err err
            | .ok _x e =>
              if _hj : i < e then
                scanIndDeclLoop b e false (seen ||| 1) ctors recs types
              else .err ⟨i.toNat, .noProgress⟩
        | .kCtors =>
          if (seen &&& 2) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanIndCtors b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndDeclLoop b e false (seen ||| 2) x recs types
              else .err ⟨i.toNat, .noProgress⟩
        | .kIsUnsafe =>
          if (seen &&& 4) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanBool b v with
            | .err err => .err err
            | .ok _x e =>
              if _hj : i < e then
                scanIndDeclLoop b e false (seen ||| 4) ctors recs types
              else .err ⟨i.toNat, .noProgress⟩
        | .kRecs =>
          if (seen &&& 8) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanIndRecs b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndDeclLoop b e false (seen ||| 8) ctors x types
              else .err ⟨i.toNat, .noProgress⟩
        | .kTypes =>
          if (seen &&& 16) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            match scanIndTypes b v with
            | .err err => .err err
            | .ok x e =>
              if _hj : i < e then
                scanIndDeclLoop b e false (seen ||| 16) ctors recs x
              else .err ⟨i.toNat, .noProgress⟩
        | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- An `inductive` record: three arrays of member records. -/
def scanIndDecl (b : @& ByteArray) (i : USize) : ScanRes DeclRec :=
  if byteAt b i == 123 then
    scanIndDeclLoop b (i + 1) true 0 [] [] []
  else .err ⟨i.toNat, .expectedObject⟩


/-! ## The line

A line carries at most one index key (`in`/`il`/`ie`) and exactly one
payload key.  The payload keys of the three table kinds are disjoint,
so the payload is read before it is known which table it belongs to
and the two are matched at the closing brace — which is what makes
the recogniser indifferent to key order even though the raw stream
sorts its keys and writes the payload first
(`{"app":{"arg":1,"fn":7},"ie":8}`). -/

/-- A line's payload, before it is matched with its index key. -/
inductive LinePayload where
  | absent
  | name (r : NameRec)
  | level (r : LevelRec)
  | expr (r : ExprRec)
  | decl (d : DeclRec)
  | header

def LinePayload.isAbsent : LinePayload → Bool
  | .absent => true
  | _ => false

/-- The members of one line.  `idxKind` is `0` for none, `1` for
`in`, `2` for `il`, `3` for `ie`. -/
def scanLineLoop (b : @& ByteArray) (i : USize) (wantMember : Bool)
    (idxKind : UInt8) (idx : Nat) (pl : LinePayload) : ScanRes LineRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then scanLineLoop b (i + 1) wantMember idxKind idx pl
    else if c == 125 then
      if wantMember && (idxKind != 0 || !pl.isAbsent) then
        .err ⟨i.toNat, .expectedKey⟩
      else
        match pl, idxKind with
        | .name r, 1 => .ok (.name idx r) (i + 1)
        | .level r, 2 => .ok (.level idx r) (i + 1)
        | .expr r, 3 => .ok (.expr idx r) (i + 1)
        | .decl d, 0 => .ok (.decl d) (i + 1)
        | .header, 0 => .ok .header (i + 1)
        | .absent, _ => .err ⟨i.toNat, .missingKey⟩
        | _, _ => .err ⟨i.toNat, .mixedKeys⟩
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else scanLineLoop b (i + 1) true idxKind idx pl
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
          let k := keyAt b i (ke - (i + 1))
          match k with
          | .kIn | .kIl | .kIe =>
            if idxKind != 0 then .err ⟨i.toNat, .duplicateKey⟩
            else
              let e := skipDigits b v
              if e == v then .err ⟨v.toNat, .expectedNat⟩
              else if _hj : i < e then
                scanLineLoop b e false
                  (match k with | .kIn => 1 | .kIl => 2 | _ => 3)
                  (readNatAt b v e) pl
              else .err ⟨i.toNat, .noProgress⟩
          | .kBvar | .kSort | .kSucc | .kParam =>
            if !pl.isAbsent then .err ⟨i.toNat, .duplicateKey⟩
            else
              let e := skipDigits b v
              if e == v then .err ⟨v.toNat, .expectedNat⟩
              else if _hj : i < e then
                let n := readNatAt b v e
                scanLineLoop b e false idxKind idx
                  (match k with
                   | .kBvar => .expr (.bvar n)
                   | .kSort => .expr (.sort n)
                   | .kSucc => .level (.succ n)
                   | _ => .level (.param n))
              else .err ⟨i.toNat, .noProgress⟩
          | .kMax | .kImax =>
            if !pl.isAbsent then .err ⟨i.toNat, .duplicateKey⟩
            else
              match scanNatList b v with
              | .err err => .err err
              | .ok us e =>
                match us with
                | [a, d] =>
                  if _hj : i < e then
                    scanLineLoop b e false idxKind idx
                      (match k with
                       | .kMax => .level (.max a d)
                       | _ => .level (.imax a d))
                  else .err ⟨i.toNat, .noProgress⟩
                | _ => .err ⟨v.toNat, .expectedList⟩
          | .kStr | .kNum =>
            if !pl.isAbsent then .err ⟨i.toNat, .duplicateKey⟩
            else
              match (match k with
                     | .kStr => scanStrName b v
                     | _ => scanNumName b v) with
              | .err err => .err err
              | .ok r e =>
                if _hj : i < e then
                  scanLineLoop b e false idxKind idx (.name r)
                else .err ⟨i.toNat, .noProgress⟩
          | .kApp | .kLam | .kForallE | .kLetE | .kConst | .kProj =>
            if !pl.isAbsent then .err ⟨i.toNat, .duplicateKey⟩
            else
              match (match k with
                     | .kApp => scanAppExpr b v
                     | .kLam => scanLamExpr b v
                     | .kForallE => scanForallExpr b v
                     | .kLetE => scanLetExpr b v
                     | .kConst => scanConstExpr b v
                     | _ => scanProjExpr b v) with
              | .err err => .err err
              | .ok r e =>
                if _hj : i < e then
                  scanLineLoop b e false idxKind idx (.expr r)
                else .err ⟨i.toNat, .noProgress⟩
          | .kNatVal =>
            if !pl.isAbsent then .err ⟨i.toNat, .duplicateKey⟩
            else
              match scanQuotedNat b v with
              | .err err => .err err
              | .ok n e =>
                if _hj : i < e then
                  scanLineLoop b e false idxKind idx (.expr (.natVal n))
                else .err ⟨i.toNat, .noProgress⟩
          | .kStrVal =>
            if !pl.isAbsent then .err ⟨i.toNat, .duplicateKey⟩
            else
              match scanString b v with
              | .err err => .err err
              | .ok str e =>
                if _hj : i < e then
                  scanLineLoop b e false idxKind idx (.expr (.strVal str))
                else .err ⟨i.toNat, .noProgress⟩
          | .kAxiom | .kDef | .kThm | .kOpaque | .kQuot | .kInductive =>
            if !pl.isAbsent then .err ⟨i.toNat, .duplicateKey⟩
            else
              match (match k with
                     | .kAxiom => scanAxiomDecl b v
                     | .kDef => scanDefDecl b v
                     | .kThm => scanThmDecl b v
                     | .kOpaque => scanOpaqueDecl b v
                     | .kQuot => scanQuotDecl b v
                     | _ => scanIndDecl b v) with
              | .err err => .err err
              | .ok d e =>
                if _hj : i < e then
                  scanLineLoop b e false idxKind idx (.decl d)
                else .err ⟨i.toNat, .noProgress⟩
          | .kMeta =>
            if !pl.isAbsent then .err ⟨i.toNat, .duplicateKey⟩
            else if byteAt b v != 123 then .err ⟨v.toNat, .expectedObject⟩
            else
              let e := skipBraced b (v + 1) 0
              if e == 0 then .err ⟨v.toNat, .expectedObject⟩
              else if _hj : i < e then
                scanLineLoop b e false idxKind idx .header
              else .err ⟨i.toNat, .noProgress⟩
          | _ => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- One line of the stream from `i`: the record, and **the position
after its newline** — or `0` when the buffer ran out before a newline
did, which tells the driver that these bytes are an incomplete tail to
carry into the next chunk rather than a line (a continue position is
never `0`: it is at least one past the newline).  A line of
whitespace is `blank`; anything between the record's closing brace and
the newline is an error.

Reading the line and finding its end are therefore ONE pass: the
record scanner stops at the closing brace and only the handful of
bytes after it are looked at again. -/
def scanLineFwd (b : @& ByteArray) (i : USize) : ScanRes LineRec :=
  let s := skipWs b i
  if byteAt b s == 10 then .ok .blank (s + 1)
  else if b.usize ≤ s then .ok .blank 0
  else if byteAt b s != 123 then .err ⟨s.toNat, .expectedObject⟩
  else
    match scanLineLoop b (s + 1) true 0 0 .absent with
    | .err e => .err e
    | .ok r j =>
      let p := skipWs b j
      if byteAt b p == 10 then .ok r (p + 1)
      else if b.usize ≤ p then .ok r 0
      else .err ⟨p.toNat, .trailing⟩

/-- Is there a newline at or after `i`?  Asked only when a line failed
to scan, to tell a malformed record from one a chunk boundary cut in
half. -/
def newlineFrom (b : @& ByteArray) (i : USize) : Bool :=
  if h : i < b.usize then
    b.uget i (usizeInBounds b i h) == 10 || newlineFrom b (i + 1)
  else false
termination_by b.size - i.toNat
decreasing_by
  have := usizeInBounds b i h; have := usizeStep b i h; omega

end ConLeche.Frontend
