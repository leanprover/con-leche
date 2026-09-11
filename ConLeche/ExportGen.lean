module
/-!
# Decision-byte generator for the Lean 4 export format (version 3.1.0)

Turns an arbitrary byte string into an `.ndjson` export. Every choice is driven
by the next input byte, so a coverage-guided fuzzer that mutates the bytes
explores the space of exports, and a byte flip changes one local decision
instead of invalidating the whole file. Once the input is exhausted every
choice returns `0`, which is always a terminal alternative, so generation
terminates and its size is bounded by the input length.

The only invariant maintained is that every back reference (name, level,
expression index) points at an already emitted entry. Index `0` is the implicit
anonymous name and the implicit `Level.zero`. Nothing else is checked: terms are
not well scoped, universe arguments are arbitrary, declarations may reuse
names, recursor data is random.
-/

public section

namespace ExportGen

structure GenState where
  input : ByteArray
  pos : Nat := 0
  out : Array String := #[]
  /-- Emitted entry counts; names and levels start at 1 for the implicit entry. -/
  numNames : Nat := 1
  numLevels : Nat := 1
  numExprs : Nat := 0

abbrev GenM := StateM GenState

/-! ## Decision primitives -/

/-- Next input byte, `0` once the input is exhausted. -/
def byte : GenM UInt8 := do
  let s ← get
  if h : s.pos < s.input.size then
    set { s with pos := s.pos + 1 }
    return s.input[s.pos]
  else
    return 0

def exhausted : GenM Bool := do
  let s ← get
  return s.pos ≥ s.input.size

def choose (n : Nat) : GenM Nat := do
  if n ≤ 1 then return 0
  return (← byte).toNat % n

def flag : GenM Bool := do
  return (← byte) &&& 1 == 1

def smallNat : GenM Nat := do
  return (← byte).toNat % 8

def bigNat : GenM Nat := do
  match ← choose 4 with
  | 0 => return (← byte).toNat
  | 1 => return (← byte).toNat * 256 + (← byte).toNat
  | 2 => return 2 ^ (← byte).toNat
  | _ => return 2 ^ (← byte).toNat - 1

/-! ## Valid back references -/

def anyName : GenM Nat := do choose (← get).numNames
def anyLevel : GenM Nat := do choose (← get).numLevels

/-- Some already emitted expression; forces one into existence if there is none yet. -/
def anyExpr : GenM Nat := do
  let n := (← get).numExprs
  if n == 0 then
    modify fun s => { s with numExprs := 1, out := s.out.push "{\"sort\":0,\"ie\":0}" }
    return 0
  choose n

def list (gen : GenM Nat) : GenM (Array Nat) := do
  let n ← choose 4
  let mut r := #[]
  for _ in [0:n] do r := r.push (← gen)
  return r

/-! ## JSON emission -/

def emit (line : String) : GenM Unit :=
  modify fun s => { s with out := s.out.push line }

def hex4 (n : Nat) : String :=
  let h := Nat.toDigits 16 n
  String.ofList (List.replicate (4 - h.length) '0' ++ h)

def jsonStr (s : String) : String := Id.run do
  let mut r := "\""
  for c in s.toList do
    r := r ++ match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | c => if c.toNat < 0x20 then "\\u" ++ hex4 c.toNat else c.toString
  return r ++ "\""

def obj (fields : List (String × String)) : String :=
  "{" ++ ",".intercalate (fields.map fun (k, v) => jsonStr k ++ ":" ++ v) ++ "}"

def arr (xs : Array Nat) : String :=
  "[" ++ ",".intercalate (xs.toList.map toString) ++ "]"

def arrS (xs : Array String) : String :=
  "[" ++ ",".intercalate xs.toList ++ "]"

def jbool (b : Bool) : String := if b then "true" else "false"

def n (x : Nat) : String := toString x

/-! ## Primitives -/

def strings : Array String :=
  #["a", "b", "f", "x", "T", "u", "v", "Nat", "Eq", "Quot", "rec", "mk", "_", "", "\"", "\\", "\n", "🦀", "a.b"]

def genString : GenM String := do
  match ← choose 4 with
  | 0 | 1 | 2 => return strings[← choose strings.size]!
  | _ => return s!"n{← byte}"

def genName : GenM Unit := do
  let body ← match ← choose 2 with
    | 0 => do pure ("str", obj [("pre", n (← anyName)), ("str", jsonStr (← genString))])
    | _ => do pure ("num", obj [("pre", n (← anyName)), ("i", n (← smallNat))])
  let i := (← get).numNames
  modify fun s => { s with numNames := i + 1 }
  emit <| obj [body, ("in", n i)]

def genLevel : GenM Unit := do
  let body ← match ← choose 4 with
    | 0 => do pure ("succ", n (← anyLevel))
    | 1 => do pure ("max", arr #[← anyLevel, ← anyLevel])
    | 2 => do pure ("imax", arr #[← anyLevel, ← anyLevel])
    | _ => do pure ("param", n (← anyName))
  let i := (← get).numLevels
  modify fun s => { s with numLevels := i + 1 }
  emit <| obj [body, ("il", n i)]

def binderInfos : Array String := #["\"default\"", "\"implicit\"", "\"strictImplicit\"", "\"instImplicit\""]

def genBinderInfo : GenM String := do
  return binderInfos[← choose 4]!

def genExpr : GenM Unit := do
  let body ← match ← choose 11 with
    | 0 => do pure ("bvar", n (← smallNat))
    | 1 => do pure ("sort", n (← anyLevel))
    | 2 => do pure ("const", obj [("name", n (← anyName)), ("us", arr (← list anyLevel))])
    | 3 => do pure ("app", obj [("fn", n (← anyExpr)), ("arg", n (← anyExpr))])
    | 4 => do pure ("lam", obj [("name", n (← anyName)), ("type", n (← anyExpr)), ("body", n (← anyExpr)),
                                ("binderInfo", ← genBinderInfo)])
    | 5 => do pure ("forallE", obj [("name", n (← anyName)), ("type", n (← anyExpr)), ("body", n (← anyExpr)),
                                    ("binderInfo", ← genBinderInfo)])
    | 6 => do pure ("letE", obj [("name", n (← anyName)), ("type", n (← anyExpr)), ("value", n (← anyExpr)),
                                 ("body", n (← anyExpr)), ("nondep", jbool (← flag))])
    | 7 => do pure ("proj", obj [("typeName", n (← anyName)), ("idx", n (← smallNat)), ("struct", n (← anyExpr))])
    | 8 => do pure ("natVal", jsonStr (toString (← bigNat)))
    | 9 => do pure ("strVal", jsonStr (← genString))
    | _ => do pure ("mdata", obj [("expr", n (← anyExpr)), ("data", "{}")])
  let i := (← get).numExprs
  modify fun s => { s with numExprs := i + 1 }
  emit <| obj [body, ("ie", n i)]

/-! ## Declarations -/

def genAxiom : GenM Unit := do
  emit <| obj [("axiom", obj [("name", n (← anyName)), ("levelParams", arr (← list anyName)),
    ("type", n (← anyExpr)), ("isUnsafe", jbool (← flag))])]

def genDef : GenM Unit := do
  let hints ← match ← choose 3 with
    | 0 => do pure (obj [("regular", n (← smallNat))])
    | 1 => pure "\"abbrev\""
    | _ => pure "\"opaque\""
  let safety ← match ← choose 3 with
    | 0 => pure "\"safe\""
    | 1 => pure "\"unsafe\""
    | _ => pure "\"partial\""
  emit <| obj [("def", obj [("name", n (← anyName)), ("levelParams", arr (← list anyName)),
    ("type", n (← anyExpr)), ("value", n (← anyExpr)), ("hints", hints), ("safety", safety),
    ("all", arr (← list anyName))])]

def genOpaque : GenM Unit := do
  emit <| obj [("opaque", obj [("name", n (← anyName)), ("levelParams", arr (← list anyName)),
    ("type", n (← anyExpr)), ("value", n (← anyExpr)), ("isUnsafe", jbool (← flag)),
    ("all", arr (← list anyName))])]

def genTheorem : GenM Unit := do
  emit <| obj [("thm", obj [("name", n (← anyName)), ("levelParams", arr (← list anyName)),
    ("type", n (← anyExpr)), ("value", n (← anyExpr)), ("all", arr (← list anyName))])]

def quotKinds : Array String := #["\"type\"", "\"ctor\"", "\"lift\"", "\"ind\""]

def genQuot : GenM Unit := do
  emit <| obj [("quot", obj [("name", n (← anyName)), ("levelParams", arr (← list anyName)),
    ("type", n (← anyExpr)), ("kind", quotKinds[← choose 4]!)])]

def genInductiveVal : GenM String := do
  return obj [("name", n (← anyName)), ("levelParams", arr (← list anyName)), ("type", n (← anyExpr)),
    ("numParams", n (← smallNat)), ("numIndices", n (← smallNat)), ("all", arr (← list anyName)),
    ("ctors", arr (← list anyName)), ("numNested", n (← smallNat)), ("isRec", jbool (← flag)),
    ("isUnsafe", jbool (← flag)), ("isReflexive", jbool (← flag))]

def genCtorVal : GenM String := do
  return obj [("name", n (← anyName)), ("levelParams", arr (← list anyName)), ("type", n (← anyExpr)),
    ("induct", n (← anyName)), ("cidx", n (← smallNat)), ("numParams", n (← smallNat)),
    ("numFields", n (← smallNat)), ("isUnsafe", jbool (← flag))]

def genRule : GenM String := do
  return obj [("ctor", n (← anyName)), ("nfields", n (← smallNat)), ("rhs", n (← anyExpr))]

def genRecVal : GenM String := do
  let numRules ← choose 4
  let mut rules := #[]
  for _ in [0:numRules] do rules := rules.push (← genRule)
  return obj [("name", n (← anyName)), ("levelParams", arr (← list anyName)), ("type", n (← anyExpr)),
    ("all", arr (← list anyName)), ("numParams", n (← smallNat)), ("numIndices", n (← smallNat)),
    ("numMotives", n (← smallNat)), ("numMinors", n (← smallNat)), ("rules", arrS rules),
    ("k", jbool (← flag)), ("isUnsafe", jbool (← flag))]

def genInductive : GenM Unit := do
  let mut types := #[]
  for _ in [0:(← choose 3)] do types := types.push (← genInductiveVal)
  let mut ctors := #[]
  for _ in [0:(← choose 4)] do ctors := ctors.push (← genCtorVal)
  let mut recs := #[]
  for _ in [0:(← choose 3)] do recs := recs.push (← genRecVal)
  emit <| obj [("inductive", obj [("types", arrS types), ("ctors", arrS ctors), ("recs", arrS recs)])]

/-! ## Driver -/

def genLine : GenM Unit := do
  match ← choose 16 with
  | 0 | 1 | 2 | 3 => genName
  | 4 | 5 => genLevel
  | 6 | 7 | 8 | 9 | 10 => genExpr
  | 11 => genAxiom
  | 12 => genDef
  | 13 => genTheorem
  | 14 => genOpaque
  | _ => if (← flag) then genInductive else genQuot

def metaLine : String :=
  obj [("meta", obj [
    ("exporter", obj [("name", jsonStr "export-fuzz"), ("version", jsonStr "0.1.0")]),
    ("lean", obj [("githash", jsonStr "0000000000000000000000000000000000000000"), ("version", jsonStr "4.0.0")]),
    ("format", obj [("version", jsonStr "3.1.0")])])]

def generate (input : ByteArray) (maxLines : Nat := 4096) : Array String :=
  let gen : GenM Unit := do
    emit metaLine
    for _ in [0:maxLines] do
      if ← exhausted then break
      genLine
  (Id.run (gen.run { input })).2.out

@[export export_fuzz_generate]
def generateString (input : ByteArray) : String :=
  "\n".intercalate (generate input).toList ++ "\n"

end ExportGen
