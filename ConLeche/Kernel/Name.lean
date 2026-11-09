module

public import Std.Data.HashMap
/- `withPtrEq` is `public` but not `@[expose]`, and its whole point here
is that it is *definitionally* `k ()` — which is what
`Name.beqPtr_eq` proves.  `import all` makes that body visible **in
this module only**; that theorem is the public relay, so no importer
needs it, and the executed `Name.beq` stays the plain
`decide (· = ·)` that the kernel can still reduce. -/
import all Init.Util

/-!
# Hierarchical names

`ConLeche.Name`, the checker's own mirror of `Lean.Name` (cached hash in
a `@[computed_field]`, pointer-and-hash-guarded equality substituted by
`@[csimp]`).  Split out of `ConLeche/Kernel/Expr.lean` on 2026-09-06 so
that `ConLeche/Kernel/PropWhen.lean` — which needs names and nothing
else — can sit *below* the expression and level types.
-/

@[expose] public section

namespace ConLeche

/-- Hierarchical names, same shape as `Lean.Name` — including the
cached hash, which lives in a `@[computed_field]` exactly as
`Lean.Name`'s does (`@[computed_field, inline] hash : Name → UInt64`,
`Init/Prelude.lean`; the C runtime stores it in the object header and
reads it with `lean_name_hash_ptr`).  Logically the field is a
*function of the value*, so it is invisible to every statement:
`DecidableEq` is still the derived structural equality, and the field
only spares the `Hashable` instance a walk (task #176 P3). -/
inductive Name where
  | anonymous
  | str (pre : Name) (s : String)
  | num (pre : Name) (n : Nat)
with
  /-- The cached hash of a name (official: the `uint64` in the `Name`
  object's header). -/
  @[computed_field] hashData : Name → UInt64
    | .anonymous => 1723
    | .str p s => mixHash (mixHash 1 p.hashData) (hash s)
    | .num p n => mixHash (mixHash 2 p.hashData) (hash n)
deriving DecidableEq, Repr, Inhabited

/-- Hashing a name is an `O(1)` field read, not a structural walk with
a byte-wise `String` hash per limb. -/
instance : Hashable Name := ⟨Name.hashData⟩

/-- Name equality in the official kernel's shape (task #176 P1):
**pointer** (`lean_name_eq`'s `if (n1 == n2) return true`), then the
**cached hash** (`lean_name_hash_ptr`), then the structural walk —
`_tmp/lean4-master-kernel/lean4_object.cpp:2762`.  This is the
*implementation* of `Name.beq`; `Name.beqPtr_eq` proves the two guards
redundant. -/
@[inline] def Name.beqPtr (a b : Name) : Bool :=
  withPtrEq a b (fun _ => a.hashData == b.hashData && decide (a = b))
    (fun h => by subst h; simp)

/-- Both guards are redundant: `withPtrEq a b k h` is *defined* as
`k ()`, and `hashData` is a function of the value, so a hash mismatch
**is** an inequality. -/
theorem Name.beqPtr_eq (a b : Name) : Name.beqPtr a b = decide (a = b) := by
  show (a.hashData == b.hashData && decide (a = b)) = decide (a = b)
  by_cases h : a = b
  · subst h; simp
  · simp [h]

/-- The executed name equality.  Definitionally `decide (a = b)` — so
the kernel, `by decide` and `#guard` still see plain structural
equality — with `beqPtr` substituted by the compiler on the strength
of the `@[csimp]` equation below. -/
def Name.beq (a b : Name) : Bool := decide (a = b)

/-- **The compiler substitution, on a kernel-checked equality.**
`@[csimp]` (not `@[implemented_by]`) is what replaces `Name.beq` by
`Name.beqPtr` in compiled code — *"do not use `implemented_by`.  If
you can prove them equal, use `csimp`"* (user ruling, 2026-09-05).
Nothing here is taken on faith: `withPtrEq a b k h` is *defined* as
`k ()` and its obligation is discharged at `beqPtr`, and `hashData` is
a function of the value, so the hash guard cannot reject an equal
pair.  `Expr.beq` is substituted the same way (`Expr.beq_eq_beqMemo`),
so no equality in the tree is an escape. -/
@[csimp] theorem Name.beq_eq_beqPtr : @Name.beq = @Name.beqPtr := by
  funext a b; exact (Name.beqPtr_eq a b).symm

instance : BEq Name := ⟨Name.beq⟩

/-- `Name.beq` is lawful — it *is* `decide (· = ·)`. -/
instance : LawfulBEq Name where
  eq_of_beq h := of_decide_eq_true h
  rfl := by simp [BEq.beq, Name.beq]

/-! ## Display rendering

Everything the checker prints that comes from the input — names,
strings — goes through `Display.Acc`, so no input reaches the
terminal (or a CI log, where a line starting with `::` is a workflow
command) as a control sequence, an invisible character or a spoofed
separator.  Inside the delimiters of a quoted component or string, `\`
is written `\\` and every *unsafe* character (`Display.unsafeChar`),
and the closing delimiter, as `\u{XXXX}` (upper-case hex, at least
four digits).  A rendering is capped at `Display.maxLen` characters;
what does not fit is replaced by `…[N more characters]`. -/

/-- The characters a display never prints raw: Unicode's control (Cc)
and format (Cf, Unicode 15.1) characters, the line and paragraph
separators (Zl, Zp) and every space separator (Zs) other than the
ASCII space — the C0/C1 controls and DEL, the bidi embeddings,
overrides, isolates and marks, the zero-width characters, the BOM, the
tag characters, and the spaces that look like U+0020 but are not. -/
def Display.unsafeChar (c : Char) : Bool :=
  let v := c.val
  v < 0x20 || (0x7F ≤ v && v ≤ 0xA0) || v == 0xAD ||
  (0x600 ≤ v && v ≤ 0x605) || v == 0x61C || v == 0x6DD || v == 0x70F ||
  (0x890 ≤ v && v ≤ 0x891) || v == 0x8E2 || v == 0x1680 || v == 0x180E ||
  (0x2000 ≤ v && v ≤ 0x200F) || (0x2028 ≤ v && v ≤ 0x202F) ||
  (0x205F ≤ v && v ≤ 0x2064) || (0x2066 ≤ v && v ≤ 0x206F) || v == 0x3000 ||
  v == 0xFEFF || (0xFFF9 ≤ v && v ≤ 0xFFFB) ||
  v == 0x110BD || v == 0x110CD || (0x13430 ≤ v && v ≤ 0x1343F) ||
  (0x1BCA0 ≤ v && v ≤ 0x1BCA3) || (0x1D173 ≤ v && v ≤ 0x1D17A) ||
  v == 0xE0001 || (0xE0020 ≤ v && v ≤ 0xE007F)

/-- The cap on one rendering, in characters (before the marker). -/
def Display.maxLen : Nat := 512

/-- `\u{XXXX}`: the code point in upper-case hex, at least four digits. -/
def Display.codeEscape (c : Char) : String :=
  let ds := (Nat.toDigits 16 c.val.toNat).map Char.toUpper
  "\\u{" ++ String.ofList (List.replicate (4 - ds.length) '0' ++ ds) ++ "}"

/-- A capped rendering under construction: the output, its length, the
input characters dropped since the cap was reached, and whether it was. -/
structure Display.Acc where
  out : String
  len : Nat
  dropped : Nat
  full : Bool

/-- Appends `p`, which stands for `raw` characters of the input,
unless the cap is reached; past the cap only the count grows. -/
def Display.Acc.piece (a : Display.Acc) (p : String) (raw : Nat) : Display.Acc :=
  if a.full || a.len + p.length > Display.maxLen then
    { a with full := true, dropped := a.dropped + raw }
  else { a with out := a.out ++ p, len := a.len + p.length }

/-- Appends characters that need no escaping (an identifier, a numeral). -/
def Display.Acc.chars (a : Display.Acc) (s : String) : Display.Acc :=
  s.foldl (fun a c => a.piece c.toString 1) a

/-- Appends the inside of a quoted component or string closed by
`close`: `\` doubled, `close` and the unsafe characters as `\u{XXXX}`. -/
def Display.Acc.escaped (a : Display.Acc) (close : Char) (s : String) : Display.Acc :=
  s.foldl (init := a) fun a c =>
    if c = '\\' then a.piece "\\\\" 1
    else if c = close || Display.unsafeChar c then a.piece (Display.codeEscape c) 1
    else a.piece c.toString 1

/-- The rendering, with the elision marker when the cap was reached. -/
def Display.Acc.finish (a : Display.Acc) : String :=
  if a.full then a.out ++ s!"…[{a.dropped} more characters]" else a.out

/-- Whether a string component prints bare: Lean's own rule
(`Lean.Name.escapePart`, `Init/Data/ToString/Name.lean`) — a nonempty
identifier, `isIdFirst` then `isIdRest`.  No such component contains a
`.`, a control, format or separator character, a `«`, a `»` or a `\`. -/
def Display.idShaped (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => Lean.isIdFirst c && cs.all Lean.isIdRest

/-- Pushes one component.  An identifier-shaped one bare; any other
(including the empty one, a numeral-looking one and one with a `.`)
between `«`…`»`, with `»` escaped like an unsafe character. -/
def Display.Acc.component (a : Display.Acc) (s : String) : Display.Acc :=
  if Display.idShaped s then a.chars s
  else ((a.piece "«" 0).escaped '»' s).piece "»" 0

/-- **The display rendering of a raw string from the input** (a
`safety` field, a quotient kind): between `"`…`"`, escaped and capped
like a quoted name component. -/
def Display.str (s : String) : String :=
  (((Display.Acc.mk "" 0 0 false).piece "\"" 0 |>.escaped '"' s).piece "\"" 0).finish

namespace Name

/-- Conversion from `Lean.Name` (dropping macro scopes is the caller's duty). -/
def ofLeanName : Lean.Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (ofLeanName p) s
  | .num p n => .num (ofLeanName p) n

/-- The name's components, root first (a tail-recursive walk, so a deep
name renders in constant stack). -/
def componentList : Name → List (String ⊕ Nat) → List (String ⊕ Nat)
  | .anonymous, acc => acc
  | .str p s, acc => componentList p (.inl s :: acc)
  | .num p n, acc => componentList p (.inr n :: acc)

/-- **The one display rendering of a name** (`ToString Name`): the
components joined by `.`, each bare when identifier-shaped and
otherwise `«…»` with its unsafe characters escaped (`Display.Acc`),
numeric components as decimals, the anonymous name `[anonymous]`, the
whole capped at `Display.maxLen` characters.  Display only: nothing
compares, hashes or parses the result. -/
def render (n : Name) : String :=
  match n with
  | .anonymous => "[anonymous]"
  | _ =>
    let (a, _) := (componentList n []).foldl (init := ((Display.Acc.mk "" 0 0 false), true))
      fun (a, first) c =>
        let a := if first then a else a.piece "." 1
        match c with
        | .inl s => (a.component s, false)
        | .inr k => (a.chars (toString k), false)
    a.finish

instance : ToString Name := ⟨Name.render⟩

end Name

end ConLeche
