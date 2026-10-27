module

public import ConLeche.Kernel.Core

@[expose] public section

/-!
# Reading `.olean` files: the byte region (tasks #369, #371)

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
(`IO.FS.readBinFile`; no mapping, no unsafe cast) and laid end to end
in one byte array, the module's *region*; an address stands for a
*location* in it (`Region.loc`), and every object the reader visits is
located, bounds-checked and read field by field from the bytes; a
cached field the runtime keeps beside the data (`Name`'s hash, `Level`'s
and `Expr`'s data words) is never read.  What comes out is the checker's
own values, then its own `Declaration` records, which the fold checks
like any other — the main theorem `ConLeche.model_exists` is stated for
every record array, so it holds whatever the files contain.

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
  its payload; a constructor object (tag at most 243) has `m_other`
  pointer fields, then its scalar area.

**The compactor writes children before parents** (`insert_constructor`
computes its fields' offsets before copying the object itself, and a
max-sharing hit reuses an earlier copy), so every pointer of a
well-formed region points to an object at an *earlier location*.  The
reader insists on it for every pointer it follows (`Region.down`): it is
what makes the reading a well-founded recursion
(`ConLeche/Frontend/Olean/Spec.lean`) and lets the fast decoder build
bottom-up (`ConLeche/Frontend/Olean/Fast.lean`).

Everything here is shared by the specification and the fast decoder:
both read objects through these functions.
-/

namespace ConLeche.Frontend.Olean

/-! ## Little-endian reads

Total: past the end they read `0`.  Every caller checks the extent of
what it reads first, so the default is never observed; it keeps the
reads free of a panic path (`LEAN_ABORT_ON_PANIC` is set in every run). -/

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

/-- **The header, validated.**  A wrong marker, a truncated file or a
size that is not a whole number of words is malformed input
(`.internal`, exit 3); a well-formed header of another format version,
bignum encoding or toolchain is a positive decline (`.notImplemented`):
the file is an `.olean`, of a kind this reader does not read. -/
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
  unless b.size % 8 == 0 do
    throw (.internal s!"{path}: not a whole number of words")
  let base := rdU64 b 80
  unless base % 8 == 0 && base.toNat + b.size < 2 ^ 64 do
    throw (.internal s!"{path}: bad base address")
  pure ⟨base, b⟩

/-- The root pointer of a file (the root slot after the header). -/
def Part.root (p : @& Part) : UInt64 := rdU64 p.bytes headerSize

/-! ## The region -/

/-- One file inside the region: the address its byte `0` stands for,
the location of its byte `0` in the region, its size. -/
structure Seg where
  base : UInt64
  off : Nat
  size : Nat

/-- **The address space of one module**: its files laid end to end in
`bytes`, in the order they were written, and where each one is. -/
structure Region where
  bytes : ByteArray
  segs : Array Seg

/-- The region of one file. -/
def Region.single (p : Part) : Region := ⟨p.bytes, #[⟨p.base, 0, p.bytes.size⟩]⟩

/-- The region of a module's files.  The files must not overlap and
must come in increasing address order, as one compactor writes them. -/
def Region.ofParts (ps : Array Part) : Except CheckError Region := do
  for i in [1:ps.size] do
    if h : i < ps.size then
      let p := ps[i - 1]
      unless p.base.toNat + p.bytes.size ≤ ps[i].base.toNat do
        throw (.internal "the .olean files of a module overlap")
  if h : ps.size = 1 then return Region.single ps[0]
  let total := ps.foldl (fun n p => n + p.bytes.size) 0
  let (bytes, segs) := ps.foldl (fun (b, ss) p =>
    (b ++ p.bytes, ss.push ⟨p.base, b.size, p.bytes.size⟩))
    (ByteArray.emptyWithCapacity total, #[])
  pure ⟨bytes, segs⟩

/-- **The scalar test**: a Lean value that is not a pointer (a small
`Nat`, a nullary constructor) is stored as `(n <<< 1) ||| 1`. -/
@[inline] def isScalar (v : UInt64) : Bool := v &&& 1 == 1

/-- The value of a boxed scalar. -/
@[inline] def unbox (v : UInt64) : Nat := (v >>> 1).toNat

/-- `Region.loc`'s search, from the last file (most objects of a
module-system module are in its private part, the last one); `0` when
no file holds an object at the address. -/
def Region.locGo (r : @& Region) (a : UInt64) : Nat → Nat
  | 0 => 0
  | i + 1 =>
    if h : i < r.segs.size then
      let s := r.segs[i]
      if s.base ≤ a && (a - s.base).toNat < s.size then
        let o := (a - s.base).toNat
        if a % 8 == 0 && (s.off + o) % 8 == 0 && dataStart ≤ o && o + 8 ≤ s.size &&
            s.off + s.size ≤ r.bytes.size then s.off + o
        else 0
      else r.locGo a i
    else 0

/-- **The location of the object at an address**: the address must fall
in one of the module's files, past its header, 8-aligned, with room for
the object header.  Locations are multiples of 8 and never `0` (the
header comes first). -/
@[inline] def Region.loc (r : @& Region) (a : UInt64) : Option Nat :=
  let g := r.locGo a r.segs.size
  if g == 0 then none else some g

/-- `Region.fileEnd`'s search. -/
def Region.endGo (r : @& Region) (g : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 =>
    if h : i < r.segs.size then
      let s := r.segs[i]
      if s.off ≤ g && g < s.off + s.size then s.off + s.size else r.endGo g i
    else 0

/-- **The end of the file a location is in**: an object's bytes must lie
inside its file. -/
@[inline] def Region.fileEnd (r : @& Region) (g : Nat) : Nat := r.endGo g r.segs.size

/-- **A pointer the object at `g` holds**, followed: the location of the
object it points to, which must lie below `g`. -/
@[inline] def Region.down (r : @& Region) (g : Nat) (v : UInt64) : Option Nat :=
  match r.loc v with
  | some c => if c < g then some c else none
  | none => none

theorem Region.down_lt {r : Region} {g c : Nat} {v : UInt64} (h : r.down g v = some c) :
    c < g := by
  unfold Region.down at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-- A pointer field the reader does not follow yet: a scalar, or a
pointer to an object below `g`. -/
@[inline] def Region.okPtr (r : @& Region) (g : Nat) (v : UInt64) : Bool :=
  isScalar v || (r.down g v).isSome

/-! ## Objects -/

/-- The header's tag byte. -/
@[inline] def Region.tag (r : @& Region) (g : Nat) : Nat := (rdU8 r.bytes (g + 7)).toNat

/-- The header's `m_other` byte: a constructor object's pointer-field count. -/
@[inline] def Region.nobjs (r : @& Region) (g : Nat) : Nat := (rdU8 r.bytes (g + 6)).toNat

/-- A constructor object's pointer fields lie inside its file. -/
@[inline] def Region.fits (r : @& Region) (g : Nat) : Bool :=
  g + 8 + 8 * r.nobjs g ≤ r.fileEnd g

/-- **A constructor's pointer field** `i`. -/
@[inline] def Region.fld (r : @& Region) (g i : Nat) : UInt64 := rdU64 r.bytes (g + 8 + 8 * i)

/-- A pointer field, checked (`okPtr`) and returned as it is. -/
@[inline] def Region.ptrFld (r : @& Region) (g i : Nat) : Option UInt64 :=
  let v := r.fld g i
  if r.okPtr g v then some v else none

/-- A one-byte scalar field of a constructor: byte `k` of the scalar
area after the pointer fields (word-size scalars first, then the
narrower ones in declaration order — the compiler's layout). -/
@[inline] def Region.u8 (r : @& Region) (g k : Nat) : Option UInt8 :=
  let i := g + 8 + 8 * r.nobjs g + k
  if i < r.fileEnd g then some (rdU8 r.bytes i) else none

/-- A four-byte scalar field at byte `k` of the scalar area. -/
@[inline] def Region.u32 (r : @& Region) (g k : Nat) : Option UInt32 :=
  let i := g + 8 + 8 * r.nobjs g + k
  if i + 4 ≤ r.fileEnd g then some (rdU32 r.bytes i) else none

/-- A one-byte `Bool` scalar. -/
@[inline] def Region.bool (r : @& Region) (g k : Nat) : Option Bool :=
  match r.u8 g k with
  | some 0 => some false
  | some 1 => some true
  | _ => none

/-- A constructor of tag `t` with `n` pointer fields, inside its file. -/
@[inline] def Region.isCtor (r : @& Region) (g t n : Nat) : Bool :=
  r.tag g == t && r.nobjs g == n && r.fits g

/-! ## The runtime's own object kinds -/

def tagArray : Nat := 246
def tagString : Nat := 249
def tagMPZ : Nat := 250

/-- The limbs of a bignum, most significant first into the accumulator. -/
def limbs (b : @& ByteArray) (lo : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc => limbs b lo i (acc * 2 ^ 64 + (rdU64 b (lo + 8 * i)).toNat)

/-- **A bignum object** at location `c`, the address `v` pointing at it
(`mpz_object`: the header, `int _mp_alloc`, `int _mp_size`, the limb
pointer — which the compactor points at the limbs right after the
object — then the 64-bit limbs, least significant first). -/
def Region.mpzAt (r : @& Region) (c : Nat) (v : UInt64) : Option Nat :=
  if r.tag c == tagMPZ then
    let size := rdU32 r.bytes (c + 12)
    let n := size.toNat
    if size < 2 ^ 31 && rdU64 r.bytes (c + 16) == v + 24 && c + 24 + 8 * n ≤ r.fileEnd c then
      some (limbs r.bytes (c + 24) n 0)
    else none
  else none

/-- **A `Nat` the object at `g` holds**: a boxed scalar, or a bignum
object below `g`. -/
@[inline] def Region.natP (r : @& Region) (g : Nat) (v : UInt64) : Option Nat :=
  if isScalar v then some (unbox v)
  else match r.down g v with
    | some c => r.mpzAt c v
    | none => none

/-- **A string object** at location `c` (`lean_string_object`: the
header, `m_size` — the byte length with the terminating NUL —
`m_capacity`, `m_length`, the bytes), which must be valid UTF-8. -/
def Region.strAt (r : @& Region) (c : Nat) : Option String :=
  if r.tag c == tagString then
    let sz := (rdU64 r.bytes (c + 8)).toNat
    if 1 ≤ sz && c + 32 + sz ≤ r.fileEnd c && rdU8 r.bytes (c + 32 + sz - 1) == 0 then
      String.fromUTF8? (r.bytes.extract (c + 32) (c + 32 + sz - 1))
    else none
  else none

/-- **A `String` the object at `g` holds.** -/
@[inline] def Region.strP (r : @& Region) (g : Nat) (v : UInt64) : Option String :=
  match r.down g v with
  | some c => r.strAt c
  | none => none

/-- `Region.objArray`'s loop over the elements. -/
def Region.objArrayGo (r : @& Region) (c lo n : Nat) (i : Nat) (acc : Array Nat) :
    Option (Array Nat) :=
  if i < n then
    match r.down c (rdU64 r.bytes (lo + 8 * i)) with
    | some e => r.objArrayGo c lo n (i + 1) (acc.push e)
    | none => none
  else some acc
termination_by n - i

/-- **An `Array` of objects the object at `g` holds**
(`lean_array_object`: the header, `m_size`, `m_capacity`, the element
pointers): the elements' locations, each below the array. -/
def Region.objArray (r : @& Region) (g : Nat) (v : UInt64) : Option (Array Nat) :=
  match r.down g v with
  | some c =>
    if r.tag c == tagArray then
      let n := (rdU64 r.bytes (c + 8)).toNat
      if c + 24 + 8 * n ≤ r.fileEnd c then r.objArrayGo c (c + 24) n 0 (Array.mkEmpty n)
      else none
    else none
  | none => none

/-- `Region.list`'s walk over the cells: `[]` is the scalar `0`,
`a :: as` the constructor `1` with two fields. -/
def Region.listGo (r : @& Region) (c : Nat) (acc : Array UInt64) : Option (Array UInt64) :=
  if r.isCtor c 1 2 then
    match r.ptrFld c 0 with
    | some hd =>
      let tl := r.fld c 1
      if tl == 1 then some (acc.push hd)
      else match _h : r.down c tl with
        | some c' => r.listGo c' (acc.push hd)
        | none => none
    | none => none
  else none
termination_by c
decreasing_by exact Region.down_lt _h

/-- **A `List` the object at `g` holds**: its elements, each a scalar
or a pointer below its cell (`okPtr`). -/
def Region.list (r : @& Region) (g : Nat) (v : UInt64) : Option (Array UInt64) :=
  if v == 1 then some #[]
  else match r.down g v with
    | some c => r.listGo c #[]
    | none => none

end ConLeche.Frontend.Olean
