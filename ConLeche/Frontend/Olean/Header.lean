module

public import ConLeche.Frontend.Olean.Spec

@[expose] public section

/-!
# Reading `.olean` files: a module's imports from the start of its file

The root `ModuleData` is the last object of an `.olean` (the compactor
writes children before parents), but its imports are its first field,
and the compactor copies a constructor's fields depth first in field
order (`insert_constructor`, `src/runtime/compact.cpp`): the imports'
names, the `Import` objects and the imports array are the file's first
objects, from `dataStart` on, the array the first array object.  So the
imports can be read off a prefix of the file: walk the objects from
`dataStart` (`hdrWalk`; a constructor's size is its header's `m_cs_sz`,
a string's its `m_size` past its 32-byte header, each rounded up to a
word, as `object_compactor::alloc` lays them out) to the first array,
and decode it in the region of the bytes up to its end (`importsPre`).
The result is a function of that prefix alone (`importsPre_extract`,
`ConLeche/Verify/Frontend/Olean/Reads.lean`).  A file's full read checks
that the root's imports are these (`parseExported`), so that a file whose
root points elsewhere is malformed for every reader.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- The outcome of the walk to the imports array: its location and the
end of its element pointers; the walk ran off the bytes given; or an
object the import section does not hold. -/
inductive HdrWalk where
  | found (c e : Nat)
  | short
  | bad
  deriving Inhabited, BEq

/-- An object size rounded up to a word. -/
def wordUp (n : Nat) : Nat := (n + 7) / 8 * 8

/-- The bytes an object of the import section takes at location `g`: a
string its `m_size` past its 32-byte header, a constructor or a bignum
its header's `m_cs_sz`, rounded up to a word. -/
def hdrAdv (b : ByteArray) (g : Nat) : Nat :=
  wordUp (if (rdU8 b (g + 7)).toNat == tagString then 32 + (rdU64 b (g + 8)).toNat
    else (rdU8 b (g + 4)).toNat + 256 * (rdU8 b (g + 5)).toNat)

/-- **The walk to the imports array** from location `g`: every object
up to the first array is a constructor (a name, an `Import`), a string
or a bignum, laid end to end; each read is inside the bytes. -/
def hdrWalk (b : ByteArray) (g : Nat) : HdrWalk :=
  if _h : g + 16 ≤ b.size then
    if (rdU8 b (g + 7)).toNat = tagArray then
      if g + 24 + 8 * (rdU64 b (g + 8)).toNat ≤ b.size then
        .found g (g + 24 + 8 * (rdU64 b (g + 8)).toNat)
      else .short
    else if (rdU8 b (g + 7)).toNat ≤ 243 ∨ (rdU8 b (g + 7)).toNat = tagString ∨
        (rdU8 b (g + 7)).toNat = tagMPZ then
      if _hs : 8 ≤ hdrAdv b g then hdrWalk b (g + hdrAdv b g) else .bad
    else .bad
  else .short
termination_by b.size - g
decreasing_by omega

/-- The imports array at location `c` of a region, decoded. -/
def importsIn (r : Region) (c : Nat) : Option (Array ImportRec) := do
  unless r.tag c == tagArray do none
  let n := (rdU64 r.bytes (c + 8)).toNat
  unless c + 24 + 8 * n ≤ r.fileEnd c do none
  let imps ← r.objArrayGo c (c + 24) n 0 (Array.mkEmpty n)
  imps.mapM fun i => importSkel r i >>= ImportF.mapM (nameP r)

/-- **A module's imports from the start of its exported file**: the walk
to the imports array, and the array decoded in the region of the bytes
up to its end (the base address from the header). -/
def importsPre (b : ByteArray) : Option (Array ImportRec) :=
  match hdrWalk b dataStart with
  | .found c e =>
    let pre := b.extract 0 e
    importsIn (Region.single ⟨rdU64 pre 80, pre⟩) c
  | _ => none

end ConLeche.Frontend.Olean
