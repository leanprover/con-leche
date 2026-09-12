module

public import ConLeche.Frontend.Scan.Fast

/- Exposed, like the checker code it specifies: the twin lemmas of
`ConLeche/Frontend/Scan/Equiv/*` unfold every definition here. -/
@[expose] public section

/-!
# The naive reference recogniser (task #261)

The lean4export dialect, written the way one would write it on a
whiteboard: over `List UInt8`, one function per grammatical shape, no
positions, no `ByteArray`, no machine words, hopelessly slow.  This is
the SPECIFICATION of `ConLeche/Frontend/Scan/Fast.lean`: the theorem
`scanLineSpec_eq_scanLineFwd` (`ConLeche/Frontend/Scan/Equiv.lean`)
says the fast recogniser accepts exactly this language, with the same
record on every line and the same tag at the same byte on every
malformed one, and it is what the compiler substitutes for the spec
(`@[csimp]`).  Nothing here is ever executed on a stream.

**What a naive scanner returns.**  `NRes α` is the value and the
UNREAD REST of the input, or the tag and the suffix at which the
scanner stopped.  A byte offset is a derived quantity — how much of
the input the rest is short by — and the lift to the fast recogniser's
`ScanRes` (`liftRes`, in `Equiv.lean`) computes it; the naive scanner
itself never counts.

**What is shared, not specified here.**  The character classes `isWs`
and `isDigit`; the escape decoder `unescape`, which both sides run on
the same bytes (an escape is the rare path, and its reads never leave
the string body); `String.fromUTF8?`, the runtime's validator; and the
payload type `LinePayload`.

**The objects.**  Every JSON object of the dialect is read by ONE
generic slot loop, `naiveObjLoop`: a table gives each key of the object
its seen-bit and how its value is read into the object's state, and
the loop is JSON's member grammar — whitespace, a key, a colon, a
value, a comma or the closing brace — with a key outside the table an
error, a key twice an error, and a required key missing at the brace
an error.  The record kinds differ only in their tables, which is the
whole of what a reader has to check against the format.

**One deliberate mirror.**  A loop that continues after a sub-scanner
guards its recursion with `if h : rest.length < l.length` and fails
with `noProgress` otherwise — the fast side's `if _hj : i < e` — so
that termination is the input's length and needs no lemma about the
sub-scanners.  The guard is never false: every scanner that returns
`.ok` consumed at least the byte it dispatched on.
-/

namespace ConLeche.Frontend

/-! ## Results -/

/-- A naive scanner's result: the value and the unread rest, or the tag
and the suffix where the scanner stopped. -/
inductive NRes (α : Type) where
  | ok (val : α) (rest : List UInt8)
  | err (tag : ErrTag) (rest : List UInt8)

/-- The unread rest, on either outcome. -/
def NRes.rest : NRes α → List UInt8
  | .ok _ r => r
  | .err _ r => r

def NRes.map (f : α → β) : NRes α → NRes β
  | .ok v r => .ok (f v) r
  | .err t r => .err t r

/-- The bytes of a string literal, as the list the naive scanner
compares against. -/
def lit (s : String) : List UInt8 := s.toUTF8.data.toList

/-! ## Scalars -/

/-- The value of a decimal digit run. -/
def digitsVal (ds : List UInt8) : Nat :=
  ds.foldl (fun acc d => acc * 10 + (d.toNat - 48)) 0

/-- A JSON number: a digit run, where `0` stands alone and no other
number starts with one.  `none` when there is no number here. -/
def naiveNum (l : List UInt8) : Option (Nat × List UInt8) :=
  let ds := l.takeWhile isDigit
  if ds.isEmpty || (ds.head? == some 48 && ds.length != 1) then none
  else some (digitsVal ds, l.dropWhile isDigit)

/-- A JSON number as a scanner: `expectedNat` at the value when there
is none. -/
def naiveNat (l : List UInt8) : NRes Nat :=
  match naiveNum l with
  | none => .err .expectedNat l
  | some (n, r) => .ok n r

/-- The rest after a literal, when the input starts with it. -/
def naiveLit (s : String) (l : List UInt8) : Option (List UInt8) :=
  if (lit s).isPrefixOf l then some (l.drop (lit s).length) else none

/-- `true` or `false`. -/
def naiveBool (l : List UInt8) : NRes Bool :=
  match naiveLit "true" l with
  | some r => .ok true r
  | none =>
    match naiveLit "false" l with
    | some r => .ok false r
    | none => .err .expectedBool l

/-- The body of a string whose opening quote has been read — up to the
closing quote, stepping over every `\x` pair — and the rest after the
quote; `none` when the string does not close or holds a raw control
byte, before or after a backslash.  (A control byte after a backslash
is no escape the format has, so the escape decoder would refuse it
anyway; refusing it here is what keeps a line inside its line: no
scanner of the dialect steps over a newline, task #290.) -/
def naiveStrBody : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | c :: l =>
    if c == 34 then some ([], l)
    else if c == 92 then
      match l with
      | [] => none
      | d :: l' =>
        if d < 32 then none
        else (naiveStrBody l').map fun (body, r) => (c :: d :: body, r)
    else if c < 32 then none
    else (naiveStrBody l).map fun (body, r) => (c :: body, r)

/-- A JSON string.  A body without a backslash is the UTF-8 of the
value; one with a backslash goes through the shared escape decoder on
the same bytes — from the opening quote, so that its lookahead reads
what the fast side's read. -/
def naiveStr (l : List UInt8) : NRes String :=
  match l with
  | 34 :: l' =>
    match naiveStrBody l' with
    | none => .err .expectedString l
    | some (body, rest) =>
      if body.contains 92 then
        match unescape ⟨⟨l⟩⟩ 1 (1 + body.length).toUSize .empty with
        | some s => .ok s rest
        | none => .err .badEscape l
      else
        match String.fromUTF8? ⟨⟨body⟩⟩ with
        | some s => .ok s rest
        | none => .err .badUtf8 l
  | _ => .err .expectedString l

/-- A quoted decimal, `"natVal":"12"`. -/
def naiveQuotedNat (l : List UInt8) : NRes Nat :=
  match l with
  | 34 :: l' =>
    match l'.takeWhile isDigit, l'.dropWhile isDigit with
    | [], _ => .err .badNatVal l
    | ds, 34 :: rest => .ok (digitsVal ds) rest
    | _, _ => .err .badNatVal l
  | _ => .err .badNatVal l

/-- The four `binderInfo` spellings, validated and dropped. -/
def naiveBinderInfo (l : List UInt8) : NRes Unit :=
  match l with
  | 34 :: l' =>
    match naiveLit "default\"" l' with
    | some r => .ok () r
    | none =>
      match naiveLit "implicit\"" l' with
      | some r => .ok () r
      | none =>
        match naiveLit "strictImplicit\"" l' with
        | some r => .ok () r
        | none =>
          match naiveLit "instImplicit\"" l' with
          | some r => .ok () r
          | none => .err .badBinderInfo l
  | _ => .err .badBinderInfo l

/-! ## Keys -/

/-- The contents of a key whose opening quote has been read, and the
rest after its closing quote; `none` when a control byte or a
backslash comes first (a key carries neither) or the key does not
close. -/
def naiveKeyBody : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | c :: l =>
    if c == 34 then some ([], l)
    else if c < 32 || c == 92 then none
    else (naiveKeyBody l).map fun (k, r) => (c :: k, r)

/-- The dialect's keys, by spelling. -/
def keyTable : List (String × Key) :=
  [("all", .kAll), ("app", .kApp), ("arg", .kArg), ("axiom", .kAxiom),
   ("binderInfo", .kBinderInfo), ("body", .kBody), ("bvar", .kBvar),
   ("cidx", .kCidx), ("const", .kConst), ("ctor", .kCtor), ("ctors", .kCtors),
   ("def", .kDef), ("fn", .kFn), ("forallE", .kForallE), ("hints", .kHints),
   ("i", .kI), ("idx", .kIdx), ("ie", .kIe), ("il", .kIl), ("imax", .kImax),
   ("in", .kIn), ("induct", .kInduct), ("inductive", .kInductive),
   ("isRec", .kIsRec), ("isReflexive", .kIsReflexive), ("isUnsafe", .kIsUnsafe),
   ("k", .kK), ("kind", .kKind), ("lam", .kLam), ("letE", .kLetE),
   ("levelParams", .kLevelParams), ("max", .kMax), ("meta", .kMeta),
   ("name", .kName), ("natVal", .kNatVal), ("nfields", .kNfields),
   ("nondep", .kNondep), ("num", .kNum), ("numFields", .kNumFields),
   ("numIndices", .kNumIndices), ("numMinors", .kNumMinors),
   ("numMotives", .kNumMotives), ("numNested", .kNumNested),
   ("numParams", .kNumParams), ("opaque", .kOpaque), ("param", .kParam),
   ("pre", .kPre), ("proj", .kProj), ("pw", .kPw), ("quot", .kQuot),
   ("recs", .kRecs), ("regular", .kRegular), ("rhs", .kRhs), ("rules", .kRules),
   ("safety", .kSafety), ("sort", .kSort), ("str", .kStr), ("strVal", .kStrVal),
   ("struct", .kStruct), ("succ", .kSucc), ("thm", .kThm), ("type", .kType),
   ("typeName", .kTypeName), ("types", .kTypes), ("us", .kUs), ("value", .kValue)]

/-- The key with these contents; `kUnknown` outside the dialect. -/
def keyOf (k : List UInt8) : Key :=
  match keyTable.find? fun (s, _) => lit s == k with
  | some (_, key) => key
  | none => .kUnknown

/-- The value after a key: whitespace, a colon, whitespace; `none`
when the colon is missing. -/
def naiveValue (l : List UInt8) : Option (List UInt8) :=
  match l.dropWhile isWs with
  | 58 :: r => some (r.dropWhile isWs)
  | _ => none

/-! ## Lists -/

/-- `[x, …]` after its opening bracket: `start` says which byte
begins a member, `item` reads one; JSON's alternation, so no empty
member and no trailing comma. -/
def naiveListLoop (start : UInt8 → Bool) (item : List UInt8 → NRes α) :
    List UInt8 → List α → Bool → NRes (List α)
  | [], _, _ => .err .expectedList []
  | l@(c :: l'), acc, wantItem =>
    if isWs c then naiveListLoop start item l' acc wantItem
    else if c == 93 then
      if wantItem && !acc.isEmpty then .err .expectedList l
      else .ok acc.reverse l'
    else if c == 44 then
      if wantItem then .err .expectedList l
      else naiveListLoop start item l' acc true
    else if start c then
      if !wantItem then .err .expectedList l
      else
        match item l with
        | .err t r => .err t r
        | .ok x rest =>
          if _h : rest.length < l.length then naiveListLoop start item rest (x :: acc) false
          else .err .noProgress l
    else .err .expectedList l
termination_by l => l.length

/-- `[x, …]`. -/
def naiveList (start : UInt8 → Bool) (item : List UInt8 → NRes α) (l : List UInt8) :
    NRes (List α) :=
  match l with
  | 91 :: l' => naiveListLoop start item l' [] true
  | _ => .err .expectedList l

/-- `[n, …]`, the shape of every index list of the format. -/
def naiveNatList : List UInt8 → NRes (List Nat) := naiveList isDigit naiveNat

/-! ## The two variant-valued fields -/

/-- The `pw` datum: `"never"` or a list of name indices. -/
def naivePw (l : List UInt8) : NRes PwRec :=
  match l with
  | 91 :: l' => (naiveListLoop isDigit naiveNat l' [] true).map .ifAllZero
  | 34 :: l' =>
    match naiveLit "never\"" l' with
    | some r => .ok .never r
    | none => .err .badPw l
  | _ => .err .badPw l

/-- A definition's `hints`: `"abbrev"`, `"opaque"` or `{"regular":n}`. -/
def naiveHints (l : List UInt8) : NRes HintsRec :=
  match l with
  | 34 :: l' =>
    match naiveLit "abbrev\"" l' with
    | some r => .ok .«abbrev» r
    | none =>
      match naiveLit "opaque\"" l' with
      | some r => .ok .«opaque» r
      | none => .err .badHints l
  | 123 :: l' =>
    match l'.dropWhile isWs with
    | p@(34 :: p') =>
      match naiveKeyBody p' with
      | none => .err .badHints p
      | some (key, r1) =>
        match keyOf key with
        | .kRegular =>
          match naiveValue r1 with
          | none => .err .expectedColon p
          | some lv =>
            match naiveNum lv with
            | none => .err .expectedNat lv
            | some (n, r2) =>
              match r2.dropWhile isWs with
              | 125 :: rest => .ok (.regular n) rest
              | q => .err .expectedComma q
        | _ => .err .badHints p
    | _ => .err .badHints l
  | _ => .err .badHints l

/-! ## The `meta` header

Validated loosely — a bracket- and string-balanced value — and
skipped. -/

/-- The rest after a `{`/`[`-opened value whose opening bracket has
been read; `none` when it does not close, or when a newline comes
first — the header is one line like every other record (task #290: no
scanner of the dialect steps over a newline, so a line ends at the
first one whatever it holds). -/
def naiveSkipBraced : List UInt8 → Nat → Option (List UInt8)
  | [], _ => none
  | l@(c :: l'), depth =>
    if c == 34 then
      match naiveStrBody l' with
      | none => none
      | some (_, r) =>
        if _h : r.length < l.length then naiveSkipBraced r depth else none
    else if c == 10 then none
    else if c == 123 || c == 91 then naiveSkipBraced l' (depth + 1)
    else if c == 125 || c == 93 then
      match depth with
      | 0 => some l'
      | d + 1 => naiveSkipBraced l' d
    else naiveSkipBraced l' depth
termination_by l => l.length

/-! ## Objects -/

/-- A slot of an object: the bit that records its key was seen, and
how its value is read into the object's state. -/
structure Slot (σ : Type) where
  mask : UInt32
  read : List UInt8 → σ → NRes σ

/-- The slot that reads a value with `scan` and stores it with `set`. -/
def Slot.of (mask : UInt32) (scan : List UInt8 → NRes α) (set : α → σ → σ) : Slot σ :=
  ⟨mask, fun l st =>
    match scan l with
    | .err t r => .err t r
    | .ok x r => .ok (set x st) r⟩

/-- A slot the format has and the checker does not read: validated,
then dropped. -/
def Slot.drop (mask : UInt32) (scan : List UInt8 → NRes α) : Slot σ :=
  .of mask scan fun _ st => st

/-- The members of an object after its opening brace: `fields` is the
object's slot table and `required` the seen-bits its kind demands at
the closing brace.  `wantMember` is JSON's alternation — a member is
due after `{` or `,`, a comma or the brace after a member. -/
def naiveObjLoop (fields : Key → Option (Slot σ)) (required : UInt32) :
    List UInt8 → Bool → UInt32 → σ → NRes σ
  | [], _, _, _ => .err .expectedComma []
  | l@(c :: l'), wantMember, seen, st =>
    if isWs c then naiveObjLoop fields required l' wantMember seen st
    else if c == 125 then
      if wantMember && seen != 0 then .err .expectedKey l
      else if (seen &&& required) != required then .err .missingKey l
      else .ok st l'
    else if c == 44 then
      if wantMember then .err .expectedKey l
      else naiveObjLoop fields required l' true seen st
    else if c == 34 then
      if !wantMember then .err .expectedComma l
      else
        match naiveKeyBody l' with
        | none => .err .expectedKey l
        | some (key, r1) =>
          match naiveValue r1 with
          | none => .err .expectedColon l
          | some lv =>
            match fields (keyOf key) with
            | none => .err .unknownKey l
            | some slot =>
              if (seen &&& slot.mask) != 0 then .err .duplicateKey l
              else
                match slot.read lv st with
                | .err t r => .err t r
                | .ok st' rest =>
                  if _h : rest.length < l.length then
                    naiveObjLoop fields required rest false (seen ||| slot.mask) st'
                  else .err .noProgress l
    else .err .expectedComma l
termination_by l => l.length

/-- An object of one kind: its slot table, required bits, initial
state and the record built from the final state. -/
def naiveObject (fields : Key → Option (Slot σ)) (required : UInt32) (init : σ)
    (finish : σ → α) (l : List UInt8) : NRes α :=
  match l with
  | 123 :: l' => (naiveObjLoop fields required l' true 0 init).map finish
  | _ => .err .expectedObject l

/-! ### The name-table payloads -/

/-- `{"pre":p,"str":s}` — state `(pre, s)`. -/
def strNameFields : Key → Option (Slot (Nat × String))
  | .kPre => some (.of 1 naiveNat fun p (_, s) => (p, s))
  | .kStr => some (.of 2 naiveStr fun s (p, _) => (p, s))
  | _ => none

def naiveStrName : List UInt8 → NRes NameRec :=
  naiveObject strNameFields 3 (0, "") fun (p, s) => .str p s

/-- `{"i":n,"pre":p}` — state `(n, pre)`. -/
def numNameFields : Key → Option (Slot (Nat × Nat))
  | .kI => some (.of 1 naiveNat fun n (_, p) => (n, p))
  | .kPre => some (.of 2 naiveNat fun p (n, _) => (n, p))
  | _ => none

def naiveNumName : List UInt8 → NRes NameRec :=
  naiveObject numNameFields 3 (0, 0) fun (n, p) => .num p n

/-! ### The expression payloads -/

/-- `{"arg":A,"fn":F}` — state `(arg, fn)`. -/
def appFields : Key → Option (Slot (Nat × Nat))
  | .kArg => some (.of 1 naiveNat fun a (_, f) => (a, f))
  | .kFn => some (.of 2 naiveNat fun f (a, _) => (a, f))
  | _ => none

def naiveAppExpr : List UInt8 → NRes ExprRec :=
  naiveObject appFields 3 (0, 0) fun (a, f) => .app f a

/-- A binder, `lam` or `forallE`: `binderInfo` and `name` validated and
dropped, `pw` optional — state `(body, type, pw)`. -/
def binderFields : Key → Option (Slot (Nat × Nat × PwRec))
  | .kBinderInfo => some (.drop 1 naiveBinderInfo)
  | .kBody => some (.of 2 naiveNat fun b (_, t, p) => (b, t, p))
  | .kName => some (.drop 4 naiveNat)
  | .kType => some (.of 8 naiveNat fun t (b, _, p) => (b, t, p))
  | .kPw => some (.of 16 naivePw fun p (b, t, _) => (b, t, p))
  | _ => none

def naiveLamExpr : List UInt8 → NRes ExprRec :=
  naiveObject binderFields 15 (0, 0, .never) fun (b, t, p) => .lam t b p

def naiveForallExpr : List UInt8 → NRes ExprRec :=
  naiveObject binderFields 15 (0, 0, .never) fun (b, t, p) => .forallE t b p

/-- `letE`: `name` and `nondep` validated and dropped — state
`(body, type, value)`. -/
def letFields : Key → Option (Slot (Nat × Nat × Nat))
  | .kBody => some (.of 1 naiveNat fun b (_, t, v) => (b, t, v))
  | .kName => some (.drop 2 naiveNat)
  | .kNondep => some (.drop 4 naiveBool)
  | .kType => some (.of 8 naiveNat fun t (b, _, v) => (b, t, v))
  | .kValue => some (.of 16 naiveNat fun v (b, t, _) => (b, t, v))
  | _ => none

def naiveLetExpr : List UInt8 → NRes ExprRec :=
  naiveObject letFields 27 (0, 0, 0) fun (b, t, v) => .letE t v b

/-- `{"name":N,"us":[…]}` — state `(name, us)`. -/
def constFields : Key → Option (Slot (Nat × List Nat))
  | .kName => some (.of 1 naiveNat fun n (_, us) => (n, us))
  | .kUs => some (.of 2 naiveNatList fun us (n, _) => (n, us))
  | _ => none

def naiveConstExpr : List UInt8 → NRes ExprRec :=
  naiveObject constFields 3 (0, []) fun (n, us) => .const n us

/-- `{"idx":i,"struct":S,"typeName":T}` — state `(idx, struct, typeName)`. -/
def projFields : Key → Option (Slot (Nat × Nat × Nat))
  | .kIdx => some (.of 1 naiveNat fun i (_, s, t) => (i, s, t))
  | .kStruct => some (.of 2 naiveNat fun s (i, _, t) => (i, s, t))
  | .kTypeName => some (.of 4 naiveNat fun t (i, s, _) => (i, s, t))
  | _ => none

def naiveProjExpr : List UInt8 → NRes ExprRec :=
  naiveObject projFields 7 (0, 0, 0) fun (i, s, t) => .proj t i s

/-! ### The inductive block's members -/

def ruleFields : Key → Option (Slot RuleRec)
  | .kCtor => some (.of 1 naiveNat fun c r => { r with ctor := c })
  | .kNfields => some (.of 2 naiveNat fun n r => { r with nfields := n })
  | .kRhs => some (.of 4 naiveNat fun e r => { r with rhs := e })
  | _ => none

def naiveRule : List UInt8 → NRes RuleRec :=
  naiveObject ruleFields 7 ⟨0, 0, 0⟩ id

def naiveRules : List UInt8 → NRes (List RuleRec) := naiveList (· == 123) naiveRule

/-- A recursor: `all` validated and dropped. -/
def indRecFields : Key → Option (Slot IndRecRec)
  | .kAll => some (.drop 1 naiveNatList)
  | .kIsUnsafe => some (.of 2 naiveBool fun u r => { r with isUnsafe := u })
  | .kK => some (.of 4 naiveBool fun k r => { r with k := k })
  | .kLevelParams => some (.of 8 naiveNatList fun ls r => { r with cv.levelParams := ls })
  | .kName => some (.of 16 naiveNat fun n r => { r with cv.name := n })
  | .kNumIndices => some (.of 32 naiveNat fun n r => { r with numIndices := n })
  | .kNumMinors => some (.of 64 naiveNat fun n r => { r with numMinors := n })
  | .kNumMotives => some (.of 128 naiveNat fun n r => { r with numMotives := n })
  | .kNumParams => some (.of 256 naiveNat fun n r => { r with numParams := n })
  | .kRules => some (.of 512 naiveRules fun rs r => { r with rules := rs })
  | .kType => some (.of 1024 naiveNat fun t r => { r with cv.type := t })
  | _ => none

def naiveIndRec : List UInt8 → NRes IndRecRec :=
  naiveObject indRecFields 2046 ⟨⟨0, [], 0⟩, false, false, 0, 0, 0, 0, []⟩ id

def naiveIndRecs : List UInt8 → NRes (List IndRecRec) := naiveList (· == 123) naiveIndRec

/-- An inductive type: `all` validated and dropped. -/
def indTypeFields : Key → Option (Slot IndTypeRec)
  | .kAll => some (.drop 1 naiveNatList)
  | .kCtors => some (.of 2 naiveNatList fun cs r => { r with ctors := cs })
  | .kIsRec => some (.of 4 naiveBool fun b r => { r with isRec := b })
  | .kIsReflexive => some (.of 8 naiveBool fun b r => { r with isReflexive := b })
  | .kIsUnsafe => some (.of 16 naiveBool fun b r => { r with isUnsafe := b })
  | .kLevelParams => some (.of 32 naiveNatList fun ls r => { r with cv.levelParams := ls })
  | .kName => some (.of 64 naiveNat fun n r => { r with cv.name := n })
  | .kNumIndices => some (.of 128 naiveNat fun n r => { r with numIndices := n })
  | .kNumNested => some (.of 256 naiveNat fun n r => { r with numNested := n })
  | .kNumParams => some (.of 512 naiveNat fun n r => { r with numParams := n })
  | .kType => some (.of 1024 naiveNat fun t r => { r with cv.type := t })
  | _ => none

def naiveIndType : List UInt8 → NRes IndTypeRec :=
  naiveObject indTypeFields 2046 ⟨⟨0, [], 0⟩, [], false, false, false, 0, 0, 0⟩ id

def naiveIndTypes : List UInt8 → NRes (List IndTypeRec) := naiveList (· == 123) naiveIndType

/-- A constructor.  `cidx` and `induct` are the format's redundant
fields (task #271): read here, validated against the block's own
records at `ConLeche/Frontend/ExportC.lean`. -/
def indCtorFields : Key → Option (Slot IndCtorRec)
  | .kCidx => some (.of 1 naiveNat fun n r => { r with cidx := some n })
  | .kInduct => some (.of 2 naiveNat fun n r => { r with induct := some n })
  | .kIsUnsafe => some (.of 4 naiveBool fun b r => { r with isUnsafe := b })
  | .kLevelParams => some (.of 8 naiveNatList fun ls r => { r with cv.levelParams := ls })
  | .kName => some (.of 16 naiveNat fun n r => { r with cv.name := n })
  | .kNumFields => some (.of 32 naiveNat fun n r => { r with numFields := n })
  | .kNumParams => some (.of 64 naiveNat fun n r => { r with numParams := n })
  | .kType => some (.of 128 naiveNat fun t r => { r with cv.type := t })
  | _ => none

def naiveIndCtor : List UInt8 → NRes IndCtorRec :=
  naiveObject indCtorFields 252 ⟨⟨0, [], 0⟩, false, 0, 0, none, none⟩ id

def naiveIndCtors : List UInt8 → NRes (List IndCtorRec) := naiveList (· == 123) naiveIndCtor

/-! ### The declarations -/

/-- The state of every simple declaration object: the common data and
whichever of the kind-specific fields it has. -/
structure DeclFields where
  cv : CVRec := ⟨0, [], 0⟩
  isUnsafe : Bool := false
  value : Nat := 0
  hints : HintsRec := .regular 0
  safety : String := ""
  kind : String := ""

/-- The `all` list of a declaration is validated and dropped. -/
def cvSlots (maskAll maskLps maskName maskType : UInt32) : Key → Option (Slot DeclFields)
  | .kAll => some (.drop maskAll naiveNatList)
  | .kLevelParams => some (.of maskLps naiveNatList fun ls d => { d with cv.levelParams := ls })
  | .kName => some (.of maskName naiveNat fun n d => { d with cv.name := n })
  | .kType => some (.of maskType naiveNat fun t d => { d with cv.type := t })
  | _ => none

/-- `axiom`: `isUnsafe`, `levelParams`, `name`, `type`. -/
def axiomFields : Key → Option (Slot DeclFields)
  | .kIsUnsafe => some (.of 1 naiveBool fun b d => { d with isUnsafe := b })
  | .kLevelParams => some (.of 2 naiveNatList fun ls d => { d with cv.levelParams := ls })
  | .kName => some (.of 4 naiveNat fun n d => { d with cv.name := n })
  | .kType => some (.of 8 naiveNat fun t d => { d with cv.type := t })
  | _ => none

def naiveAxiomDecl : List UInt8 → NRes DeclRec :=
  naiveObject axiomFields 15 {} fun d => .ax d.cv d.isUnsafe

/-- `def`: `all`, `hints`, `levelParams`, `name`, `safety`, `type`,
`value`; a missing `hints` is `regular 0`. -/
def defFields : Key → Option (Slot DeclFields)
  | .kHints => some (.of 2 naiveHints fun h d => { d with hints := h })
  | .kSafety => some (.of 16 naiveStr fun s d => { d with safety := s })
  | .kValue => some (.of 64 naiveNat fun v d => { d with value := v })
  | k => cvSlots 1 4 8 32 k

def naiveDefDecl : List UInt8 → NRes DeclRec :=
  naiveObject defFields 124 {} fun d => .defn d.cv d.value d.hints d.safety

/-- `thm`: `all`, `levelParams`, `name`, `type`, `value`. -/
def thmFields : Key → Option (Slot DeclFields)
  | .kValue => some (.of 16 naiveNat fun v d => { d with value := v })
  | k => cvSlots 1 2 4 8 k

def naiveThmDecl : List UInt8 → NRes DeclRec :=
  naiveObject thmFields 30 {} fun d => .thm d.cv d.value

/-- `opaque`: `all`, `isUnsafe`, `levelParams`, `name`, `type`, `value`. -/
def opaqueFields : Key → Option (Slot DeclFields)
  | .kIsUnsafe => some (.of 2 naiveBool fun b d => { d with isUnsafe := b })
  | .kValue => some (.of 32 naiveNat fun v d => { d with value := v })
  | k => cvSlots 1 4 8 16 k

def naiveOpaqueDecl : List UInt8 → NRes DeclRec :=
  naiveObject opaqueFields 62 {} fun d => .opaq d.cv d.value d.isUnsafe

/-- `quot`: `kind`, `levelParams`, `name`, `type`. -/
def quotFields : Key → Option (Slot DeclFields)
  | .kKind => some (.of 1 naiveStr fun s d => { d with kind := s })
  | .kLevelParams => some (.of 2 naiveNatList fun ls d => { d with cv.levelParams := ls })
  | .kName => some (.of 4 naiveNat fun n d => { d with cv.name := n })
  | .kType => some (.of 8 naiveNat fun t d => { d with cv.type := t })
  | _ => none

def naiveQuotDecl : List UInt8 → NRes DeclRec :=
  naiveObject quotFields 15 {} fun d => .quot d.cv d.kind

/-- `inductive`: `all` and `isUnsafe` validated and dropped — state
`(ctors, recs, types)`. -/
def indFields : Key → Option (Slot (List IndCtorRec × List IndRecRec × List IndTypeRec))
  | .kAll => some (.drop 1 naiveNatList)
  | .kCtors => some (.of 2 naiveIndCtors fun cs (_, rs, ts) => (cs, rs, ts))
  | .kIsUnsafe => some (.drop 4 naiveBool)
  | .kRecs => some (.of 8 naiveIndRecs fun rs (cs, _, ts) => (cs, rs, ts))
  | .kTypes => some (.of 16 naiveIndTypes fun ts (cs, rs, _) => (cs, rs, ts))
  | _ => none

def naiveIndDecl : List UInt8 → NRes DeclRec :=
  naiveObject indFields 26 ([], [], []) fun (cs, rs, ts) => .ind ts cs rs

/-! ## The line

A line carries at most one index key (`in`/`il`/`ie`) and exactly one
payload key, in either order; the two are matched at the closing
brace. -/

/-- The index key a line may carry. -/
inductive IdxKey where
  | «in»
  | il
  | ie

/-- The members of a line after its opening brace: `idx` is the index
key and value seen so far, `pl` the payload. -/
def naiveLineLoop : List UInt8 → Bool → Option (IdxKey × Nat) → LinePayload → NRes LineRec
  | [], _, _, _ => .err .expectedComma []
  | l@(c :: l'), wantMember, idx, pl =>
    if isWs c then naiveLineLoop l' wantMember idx pl
    else if c == 125 then
      if wantMember && (idx.isSome || !pl.isAbsent) then .err .expectedKey l
      else
        match pl, idx with
        | .name r, some (.«in», i) => .ok (.name i r) l'
        | .level r, some (.il, i) => .ok (.level i r) l'
        | .expr r, some (.ie, i) => .ok (.expr i r) l'
        | .decl d, none => .ok (.decl d) l'
        | .header, none => .ok .header l'
        | .absent, _ => .err .missingKey l
        | _, _ => .err .mixedKeys l
    else if c == 44 then
      if wantMember then .err .expectedKey l
      else naiveLineLoop l' true idx pl
    else if c == 34 then
      if !wantMember then .err .expectedComma l
      else
        match naiveKeyBody l' with
        | none => .err .expectedKey l
        | some (key, r1) =>
          match naiveValue r1 with
          | none => .err .expectedColon l
          | some lv =>
            let k := keyOf key
            match k with
            | .kIn | .kIl | .kIe =>
              if idx.isSome then .err .duplicateKey l
              else
                match naiveNum lv with
                | none => .err .expectedNat lv
                | some (n, rest) =>
                  if _h : rest.length < l.length then
                    naiveLineLoop rest false
                      (some ((match k with | .kIn => .«in» | .kIl => .il | _ => .ie), n)) pl
                  else .err .noProgress l
            | .kBvar | .kSort | .kSucc | .kParam =>
              if !pl.isAbsent then .err .duplicateKey l
              else
                match naiveNum lv with
                | none => .err .expectedNat lv
                | some (n, rest) =>
                  if _h : rest.length < l.length then
                    naiveLineLoop rest false idx
                      (match k with
                       | .kBvar => .expr (.bvar n)
                       | .kSort => .expr (.sort n)
                       | .kSucc => .level (.succ n)
                       | _ => .level (.param n))
                  else .err .noProgress l
            | .kMax | .kImax =>
              if !pl.isAbsent then .err .duplicateKey l
              else
                match naiveNatList lv with
                | .err t r => .err t r
                | .ok us rest =>
                  match us with
                  | [a, d] =>
                    if _h : rest.length < l.length then
                      naiveLineLoop rest false idx
                        (match k with
                         | .kMax => .level (.max a d)
                         | _ => .level (.imax a d))
                    else .err .noProgress l
                  | _ => .err .expectedList lv
            | .kStr | .kNum =>
              if !pl.isAbsent then .err .duplicateKey l
              else
                match (match k with
                       | .kStr => naiveStrName lv
                       | _ => naiveNumName lv) with
                | .err t r => .err t r
                | .ok r rest =>
                  if _h : rest.length < l.length then naiveLineLoop rest false idx (.name r)
                  else .err .noProgress l
            | .kApp | .kLam | .kForallE | .kLetE | .kConst | .kProj =>
              if !pl.isAbsent then .err .duplicateKey l
              else
                match (match k with
                       | .kApp => naiveAppExpr lv
                       | .kLam => naiveLamExpr lv
                       | .kForallE => naiveForallExpr lv
                       | .kLetE => naiveLetExpr lv
                       | .kConst => naiveConstExpr lv
                       | _ => naiveProjExpr lv) with
                | .err t r => .err t r
                | .ok r rest =>
                  if _h : rest.length < l.length then naiveLineLoop rest false idx (.expr r)
                  else .err .noProgress l
            | .kNatVal =>
              if !pl.isAbsent then .err .duplicateKey l
              else
                match naiveQuotedNat lv with
                | .err t r => .err t r
                | .ok n rest =>
                  if _h : rest.length < l.length then
                    naiveLineLoop rest false idx (.expr (.natVal n))
                  else .err .noProgress l
            | .kStrVal =>
              if !pl.isAbsent then .err .duplicateKey l
              else
                match naiveStr lv with
                | .err t r => .err t r
                | .ok s rest =>
                  if _h : rest.length < l.length then
                    naiveLineLoop rest false idx (.expr (.strVal s))
                  else .err .noProgress l
            | .kAxiom | .kDef | .kThm | .kOpaque | .kQuot | .kInductive =>
              if !pl.isAbsent then .err .duplicateKey l
              else
                match (match k with
                       | .kAxiom => naiveAxiomDecl lv
                       | .kDef => naiveDefDecl lv
                       | .kThm => naiveThmDecl lv
                       | .kOpaque => naiveOpaqueDecl lv
                       | .kQuot => naiveQuotDecl lv
                       | _ => naiveIndDecl lv) with
                | .err t r => .err t r
                | .ok d rest =>
                  if _h : rest.length < l.length then naiveLineLoop rest false idx (.decl d)
                  else .err .noProgress l
            | .kMeta =>
              if !pl.isAbsent then .err .duplicateKey l
              else
                match lv with
                | 123 :: lv' =>
                  match naiveSkipBraced lv' 0 with
                  | none => .err .expectedObject lv
                  | some rest =>
                    if _h : rest.length < l.length then naiveLineLoop rest false idx .header
                    else .err .noProgress l
                | _ => .err .expectedObject lv
            | _ => .err .unknownKey l
    else .err .expectedComma l
termination_by l => l.length

/-- One line: the record and the rest after its newline, or the record
and `none` when the input ended before a newline did (an incomplete
tail, for the chunked reader to carry).  A line of whitespace is
`blank`; bytes between the closing brace and the newline are an
error. -/
def naiveLine (l : List UInt8) : NRes (LineRec × Option (List UInt8)) :=
  match l.dropWhile isWs with
  | 10 :: rest => .ok (.blank, some rest) rest
  | [] => .ok (.blank, none) []
  | 123 :: l' =>
    match naiveLineLoop l' true none .absent with
    | .err t r => .err t r
    | .ok r l2 =>
      match l2.dropWhile isWs with
      | 10 :: rest => .ok (r, some rest) rest
      | [] => .ok (r, none) []
      | l3 => .err .trailing l3
  | l1 => .err .expectedObject l1

end ConLeche.Frontend
