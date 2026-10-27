module

public import ConLeche.Frontend.ExportC

@[expose] public section

/-!
# Reading `.olean` files: the byte region (task #369)

An `.olean` file is a *compacted region*: the Lean runtime's object
graph of the module's `ModuleData`, written by `CompactedRegion.save`
(`src/runtime/compact.cpp`, `src/library/module.cpp` of the toolchain)
with every pointer an absolute address in the address range the file
was laid out at.  A module of the module system has three such files —
`X.olean` (the exported level), `X.olean.server` and `X.olean.private`
— written by ONE compactor in sequence, so they form one address space:
each file starts at its header's `base_addr`, the later files at higher
addresses, and an object of a later file may point into an earlier one.

**Nothing in the files is trusted.**  The files are read into memory
(`IO.FS.readBinFile`; no mapping, no unsafe cast), and every object the
decoder (`ConLeche/Frontend/Olean/Decode.lean`) visits is located, bounds-checked and
read field by field from the bytes; a cached field the runtime keeps
beside the data (`Name`'s hash, `Level`'s and `Expr`'s data words) is
never read.  What comes out is the checker's own `Declaration` records,
which the fold checks like any other — the main theorem
`ConLeche.model_exists` is stated for every record array, so it holds
whatever the files contain.

The layout this file reads (v4.35.0, `olean_header` in
`src/library/module.cpp`):

* bytes `0..5` the marker `olean`, byte `5` the format version (`2`),
  byte `6` the flags (bit 0: bignums in GMP layout), bytes `7..40` the
  Lean version string, `40..80` the build githash, `80..88` the
  base address — all little-endian;
* bytes `88..96` the root pointer (`object_compactor::operator()`
  reserves the root slot first), then the objects;
* an object is the 8-byte header `lean_object` (`m_rc : int32`,
  `m_cs_sz : uint16`, `m_other : uint8`, `m_tag : uint8`) followed by
  its payload.

**The compactor writes children before parents** (`insert_constructor`
computes its fields' offsets before copying the object itself, and a
max-sharing hit reuses an earlier copy), so every pointer of a well-formed
region points strictly *below* the object holding it.  The reader
insists on it (`Obj.field`): it is what makes every walk over the graph
terminate and lets the decoder build bottom-up.
-/

namespace ConLeche.Frontend.Olean

/-! ## Little-endian reads

Total: past the end they read `0`.  Every caller checks the extent of
what it reads first (`Region.obj`, `Obj.field`, `Obj.u8`), so the
default is never observed; it keeps the reads free of a panic path
(`LEAN_ABORT_ON_PANIC` is set in every run). -/

@[inline] def rdU8 (b : @& ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b[i] else 0

@[inline] def rdU32 (b : @& ByteArray) (i : Nat) : UInt32 :=
  (rdU8 b i).toUInt32 ||| ((rdU8 b (i + 1)).toUInt32 <<< 8) |||
  ((rdU8 b (i + 2)).toUInt32 <<< 16) ||| ((rdU8 b (i + 3)).toUInt32 <<< 24)

/-- One bounds check for the eight bytes. -/
@[inline] def rdU64 (b : @& ByteArray) (i : Nat) : UInt64 :=
  if h : i + 8 ≤ b.size then
    (b[i]'(by omega)).toUInt64 ||| ((b[i + 1]'(by omega)).toUInt64 <<< 8) |||
    ((b[i + 2]'(by omega)).toUInt64 <<< 16) ||| ((b[i + 3]'(by omega)).toUInt64 <<< 24) |||
    ((b[i + 4]'(by omega)).toUInt64 <<< 32) ||| ((b[i + 5]'(by omega)).toUInt64 <<< 40) |||
    ((b[i + 6]'(by omega)).toUInt64 <<< 48) ||| ((b[i + 7]'(by omega)).toUInt64 <<< 56)
  else 0

/-! ## The files of one module -/

/-- One file of a module: its bytes and the address its byte `0` stands
for (the header's `base_addr`). -/
structure Part where
  base : UInt64
  bytes : ByteArray

/-- The toolchain the reader understands: `.olean` files written by the
checker's own toolchain, and nothing else (maintainer ruling,
2026-10-27).  The object layouts below are that toolchain's. -/
def toolchainVersion : String := "4.35.0"
def toolchainGithash : String := "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"

/-- The byte offset of the first object: the 88-byte header, then the
root slot. -/
def headerSize : Nat := 88
def dataStart : Nat := 96

/-- A NUL-padded fixed-width string field of the header. -/
def padded (b : ByteArray) (lo hi : Nat) : String :=
  let bs := (b.extract lo hi).toList.takeWhile (· != 0)
  String.fromUTF8? ⟨bs.toArray⟩ |>.getD "?"

/-- **The header, validated.**  A wrong marker or a truncated file is
malformed input (`.internal`, exit 3); a well-formed header of another
format version, bignum encoding or toolchain is a positive decline
(`.notImplemented`): the file is an `.olean`, of a kind this reader
does not read. -/
def Part.ofBytes (path : String) (b : ByteArray) : Except CheckError Part := do
  unless b.size ≥ dataStart && b.extract 0 5 == "olean".toUTF8 do
    throw (.internal s!"{path}: not an .olean file")
  let ver := rdU8 b 5
  unless ver == 2 do
    throw (.notImplemented s!"{path}: .olean format version {ver} (this reader reads version 2)")
  unless rdU8 b 6 &&& 1 == 1 do
    throw (.notImplemented s!"{path}: .olean with non-GMP bignums")
  let v := padded b 7 40
  let g := padded b 40 80
  unless v == toolchainVersion && g == toolchainGithash do
    throw (.notImplemented s!"{path}: .olean written by Lean {Display.str v} \
      ({Display.str g}); this checker reads the oleans of Lean {toolchainVersion} \
      ({toolchainGithash}) only")
  let base := rdU64 b 80
  unless base % 8 == 0 && base.toNat + b.size < 2 ^ 64 do
    throw (.internal s!"{path}: bad base address")
  pure ⟨base, b⟩

/-- The root pointer of a file (the root slot after the header). -/
def Part.root (p : @& Part) : UInt64 := rdU64 p.bytes headerSize

/-- The address space of one module: its files, in the order they were
written (increasing base addresses, checked by `Region.ofParts`). -/
structure Region where
  parts : Array Part
  /-- each part's first memo slot (`Region.slot`) -/
  starts : Array Nat
  /-- the number of memo slots -/
  words : Nat

/-- The region of one file. -/
def Region.single (p : Part) : Region := ⟨#[p], #[0], p.bytes.size / 8 + 1⟩

/-- The parts must not overlap and must come in increasing address
order, as one compactor writes them. -/
def Region.ofParts (ps : Array Part) : Except CheckError Region := do
  for i in [1:ps.size] do
    if h : i < ps.size then
      let p := ps[i - 1]
      unless p.base.toNat + p.bytes.size ≤ ps[i].base.toNat do
        throw (.internal "the .olean files of a module overlap")
  let (starts, words) := ps.foldl (fun (st, n) p => (st.push n, n + p.bytes.size / 8 + 1)) (#[], 0)
  pure ⟨ps, starts, words⟩

/-- **The scalar test**: a Lean value that is not a pointer (a small
`Nat`, a nullary constructor) is stored as `(n <<< 1) ||| 1`. -/
@[inline] def isScalar (v : UInt64) : Bool := v &&& 1 == 1

/-- The value of a boxed scalar. -/
@[inline] def unbox (v : UInt64) : Nat := (v >>> 1).toNat

/-- **The part holding an address**: its index, or the number of parts
when no part holds it.  A plain number, so that locating allocates
nothing.  The search starts at the LAST part, the private one, where
most objects of a module-system module are. -/
def Region.partOf (r : @& Region) (a : UInt64) : Nat :=
  go r.parts.size
where
  go : Nat → Nat
    | 0 => r.parts.size
    | i + 1 =>
      if h : i < r.parts.size then
        let p := r.parts[i]
        if p.base ≤ a && (a - p.base).toNat < p.bytes.size then i else go i
      else r.parts.size

/-- **The memo slot of an address**: its word index in the module's files
laid end to end (each file taking its size in words plus one), or
`r.words` — no slot — outside them.  The decoder memoizes by slot in
dense arrays (`DS`). -/
@[inline] def Region.slot (r : @& Region) (a : UInt64) : Nat :=
  let i := r.partOf a
  if h : i < r.parts.size then
    (r.starts[i]?.getD r.words) + (a - r.parts[i].base).toNat / 8
  else r.words

/-- A located and VALIDATED object: its file's bytes, its offset in
them, its address, its memo slot and its header's tag and `m_other`
byte (a constructor's pointer-field count). -/
structure Obj where
  bytes : ByteArray
  off : Nat
  addr : UInt64
  slot : Nat
  tag : UInt8
  other : UInt8

/-- Every pointer field of a constructor object is a scalar or points
strictly below the object. -/
def fieldsBelow (b : @& ByteArray) (off : Nat) (a : UInt64) (n : Nat) : Bool :=
  go 0
where
  go (i : Nat) : Bool :=
    if i < n then
      let v := rdU64 b (off + 8 + 8 * i)
      (v &&& 1 == 1 || v < a) && go (i + 1)
    else true
  termination_by n - i

/-- **Locate and validate an object**: the address must fall in one of
the module's files, past its header, 8-aligned, with room for the
object header; a constructor object (tag at most 243) must have room
for its pointer fields, and every one of them must be a scalar or point
strictly below the object.  After this, `Obj.f` reads a field without
a check. -/
def Region.obj (r : @& Region) (a : UInt64) : Except String Obj :=
  let i := r.partOf a
  if h : i < r.parts.size then
    let p := r.parts[i]
    let b := p.bytes
    let o := (a - p.base).toNat
    if o % 8 != 0 || o < dataStart || o + 8 > b.size then
      throw s!"pointer {a} is not an object start"
    else
      let tag := rdU8 b (o + 7)
      let other := rdU8 b (o + 6)
      if tag ≤ 243 && (o + 8 + 8 * other.toNat > b.size || !fieldsBelow b o a other.toNat) then
        throw s!"object {a}: a field outside the file or not below its object"
      else
        pure ⟨b, o, a, (r.starts[i]?.getD r.words) + o / 8, tag, other⟩
  else throw s!"pointer {a} outside the module's files"

/-- **A constructor's pointer field** `i` of a validated object (scalar
`0` past the field count). -/
@[inline] def Obj.f (x : @& Obj) (i : Nat) : UInt64 :=
  if i < x.other.toNat then rdU64 x.bytes (x.off + 8 + 8 * i) else 1

/-- The field, in the error monad (for the decoders written in it). -/
@[inline] def Obj.field (x : @& Obj) (i : Nat) : Except String UInt64 :=
  if i < x.other.toNat then pure (x.f i)
  else throw s!"object {x.addr}: no field {i}"

/-- A one-byte scalar field of a constructor: byte `k` of the scalar
area after the pointer fields (word-size scalars first, then the
narrower ones in declaration order — the compiler's layout). -/
def Obj.u8 (x : @& Obj) (k : Nat) : Except String UInt8 :=
  let i := x.off + 8 + 8 * x.other.toNat + k
  if i < x.bytes.size then pure (rdU8 x.bytes i)
  else throw s!"object {x.addr}: no scalar byte {k}"

/-- A four-byte scalar field at byte `k` of the scalar area. -/
def Obj.u32 (x : @& Obj) (k : Nat) : Except String UInt32 :=
  let i := x.off + 8 + 8 * x.other.toNat + k
  if i + 4 ≤ x.bytes.size then pure (rdU32 x.bytes i)
  else throw s!"object {x.addr}: no scalar word at {k}"

/-- The constructor shape a decoder expects: tag and field count. -/
def Obj.expect (x : @& Obj) (tag nobjs : Nat) (what : String) : Except String Unit :=
  if x.tag.toNat == tag && x.other.toNat == nobjs then pure ()
  else throw s!"object {x.addr}: expected {what} (tag {tag}, {nobjs} fields), \
    found tag {x.tag} with {x.other} fields"

/-! ## The runtime's own object kinds -/

def tagArray : UInt8 := 246
def tagString : UInt8 := 249
def tagMPZ : UInt8 := 250

/-- **A `Nat`**: a boxed scalar, or a GMP bignum object (`mpz_object`:
the header, `int _mp_alloc`, `int _mp_size`, the limb pointer — which
the compactor points at the limbs right after the object — then the
64-bit limbs, least significant first). -/
def Region.nat (r : @& Region) (v : UInt64) : Except String Nat := do
  if isScalar v then return unbox v
  let x ← r.obj v
  unless x.tag == tagMPZ do throw s!"object {v}: expected a Nat"
  let size := rdU32 x.bytes (x.off + 12)
  if size ≥ 2 ^ 31 then throw s!"object {v}: negative Nat"
  let n := size.toNat
  unless rdU64 x.bytes (x.off + 16) == v + 24 && x.off + 24 + 8 * n ≤ x.bytes.size do
    throw s!"object {v}: malformed bignum"
  let rec limbs (i : Nat) (acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | i + 1 => limbs i (acc * 2 ^ 64 + (rdU64 x.bytes (x.off + 24 + 8 * i)).toNat)
  pure (limbs n 0)

/-- **A `String`** (`lean_string_object`: the header, `m_size` — the
byte length with the terminating NUL — `m_capacity`, `m_length`, the
bytes), which must be valid UTF-8. -/
def Region.str (r : @& Region) (v : UInt64) : Except String String := do
  let x ← r.obj v
  unless x.tag == tagString do throw s!"object {v}: expected a string"
  let sz := (rdU64 x.bytes (x.off + 8)).toNat
  unless sz ≥ 1 && x.off + 32 + sz ≤ x.bytes.size && rdU8 x.bytes (x.off + 32 + sz - 1) == 0 do
    throw s!"object {v}: malformed string"
  match String.fromUTF8? (x.bytes.extract (x.off + 32) (x.off + 32 + sz - 1)) with
  | some s => pure s
  | none => throw s!"object {v}: string is not valid UTF-8"

/-- **An `Array`'s elements** (`lean_array_object`: the header,
`m_size`, `m_capacity`, the element pointers), each below the array. -/
def Region.array (r : @& Region) (v : UInt64) : Except String (Array UInt64) := do
  let x ← r.obj v
  unless x.tag == tagArray do throw s!"object {v}: expected an array"
  let n := (rdU64 x.bytes (x.off + 8)).toNat
  unless x.off + 24 + 8 * n ≤ x.bytes.size do throw s!"object {v}: malformed array"
  let rec go (i : Nat) (acc : Array UInt64) : Except String (Array UInt64) :=
    if i < n then
      let e := rdU64 x.bytes (x.off + 24 + 8 * i)
      if isScalar e || e < v then go (i + 1) (acc.push e)
      else throw s!"object {v}: element {i} does not point below the array"
    else pure acc
  termination_by n - i
  go 0 (Array.mkEmpty n)

/-- **A `List`'s elements**: `[]` is the scalar `0`, `a :: as` the
constructor `1` with two fields.  Each cell's tail points below it, so
the walk terminates; the fuel is the region's size in words. -/
def Region.list (r : @& Region) (v : UInt64) : Except String (Array UInt64) :=
  go v r.words #[]
where
  go (v : UInt64) (fuel : Nat) (acc : Array UInt64) : Except String (Array UInt64) :=
    match fuel with
    | 0 => throw "list longer than its region"
    | fuel + 1 =>
      if v == 1 then pure acc
      else do
        let x ← r.obj v
        x.expect 1 2 "a list cell"
        go (← x.field 1) fuel (acc.push (← x.field 0))

end ConLeche.Frontend.Olean
