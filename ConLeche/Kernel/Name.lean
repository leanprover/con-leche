module

public import Std.Data.HashMap
/-!
# Hierarchical names

`ConLeche.Name`, the checker's own mirror of `Lean.Name` (cached hash in
a `@[computed_field]`, pointer-and-hash-guarded equality substituted by
`@[csimp]` for the structural decision).  Split out of `ConLeche/Kernel/Expr.lean` on 2026-09-06 so
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
*function of the value*, so it is invisible to every statement: the
`DecidableEq` below is structural equality, and the field only spares
the `Hashable` instance a walk (task #176 P3) and the executed equality
a descent. -/
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
deriving Repr, Inhabited

/-- Hashing a name is an `O(1)` field read, not a structural walk with
a byte-wise `String` hash per limb. -/
instance : Hashable Name := ⟨Name.hashData⟩

/-- The specification of name equality: the structural decision, the
one the kernel, `by decide` and `#guard` reduce. -/
def Name.decEq : (a b : Name) → Decidable (a = b)
  | .anonymous, .anonymous => isTrue rfl
  | .str p s, .str q t =>
    match Name.decEq p q with
    | isTrue hp => if hs : s = t then isTrue (by rw [hp, hs])
                   else isFalse (fun e => hs (Name.str.inj e).2)
    | isFalse hp => isFalse (fun e => hp (Name.str.inj e).1)
  | .num p n, .num q m =>
    match Name.decEq p q with
    | isTrue hp => if hn : n = m then isTrue (by rw [hp, hn])
                   else isFalse (fun e => hn (Name.num.inj e).2)
    | isFalse hp => isFalse (fun e => hp (Name.num.inj e).1)
  | .anonymous, .str .. | .anonymous, .num .. | .str .., .anonymous
  | .str .., .num .. | .num .., .anonymous | .num .., .str .. =>
    isFalse (fun e => Name.noConfusion e)

/-- Name equality in the official kernel's shape (task #176 P1, at
every level since task #551): **pointer** (`lean_name_eq`'s
`if (n1 == n2) return true`), then the **cached hash**
(`lean_name_hash_ptr`), then the components and the prefix, which
starts over with the pointer —
`_tmp/lean4-master-kernel/lean4_object.cpp:2762`.  A prefix shared by
reference is decided by one pointer test, and two different names
almost always by their hashes.  The component comparison is
pointer-first too (`lean_string_eq` tests `s1 == s2`; the `Nat`
component goes through `withPtrEqDecEq`). -/
def Name.decEqPtr (a b : Name) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ =>
    if hh : a.hashData = b.hashData then
      match a, b with
      | .anonymous, .anonymous => isTrue rfl
      | .str p s, .str q t =>
        if hs : s = t then
          match Name.decEqPtr p q with
          | isTrue hp => isTrue (by rw [hp, hs])
          | isFalse hp => isFalse (fun e => hp (Name.str.inj e).1)
        else isFalse (fun e => hs (Name.str.inj e).2)
      | .num p n, .num q m =>
        match withPtrEqDecEq n m (fun _ => Nat.decEq n m) with
        | isTrue hn =>
          match Name.decEqPtr p q with
          | isTrue hp => isTrue (by rw [hp, hn])
          | isFalse hp => isFalse (fun e => hp (Name.num.inj e).1)
        | isFalse hn => isFalse (fun e => hn (Name.num.inj e).2)
      | .anonymous, .str .. | .anonymous, .num .. | .str .., .anonymous
      | .str .., .num .. | .num .., .anonymous | .num .., .str .. =>
        isFalse (fun e => Name.noConfusion e)
    else isFalse (fun e => hh (by rw [e]))

/-- **The compiler substitution, on a kernel-checked equality.**
`@[csimp]` (not `@[implemented_by]`) is what replaces `Name.decEq` by
`Name.decEqPtr` in compiled code — *"do not use `implemented_by`.  If
you can prove them equal, use `csimp`"* (user ruling, 2026-09-05).
The equation is `Decidable`'s subsingleton property: both sides decide
the same proposition, so they are the same decision, whatever
`withPtrEqDecEq` does at runtime (its pure definition is `k ()`, its
runtime pointer test answers `isTrue` only on one object).  `Level`,
`Literal` and `Expr` are substituted the same way
(`Level.decEq_eq_decEqPtr`, `Literal.decEq_eq_decEqPtr`,
`Expr.beq_eq_beqMemo`), so no equality in the tree is an escape. -/
@[csimp] theorem Name.decEq_eq_decEqPtr : @Name.decEq = @Name.decEqPtr := by
  funext a b; exact Subsingleton.elim _ _

/-- Every name equality — `=` in an `if`, `==`, a hash-map probe —
runs `Name.decEqPtr`. -/
instance : DecidableEq Name := Name.decEq

/-- The executed name equality: definitionally `decide (a = b)`. -/
def Name.beq (a b : Name) : Bool := decide (a = b)

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
