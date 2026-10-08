module

public import ConLeche.Frontend.Scan.Types

@[expose] public section

/-!
# Scanned lines as flat bytes (task #329)

The pipelined parse (`ConLeche/Frontend/Pipeline.lean`) scans a chunk
on a worker task and applies the scan on the parse's own thread.  What
crosses between the two must be FLAT: a task's value is walked and
marked multi-threaded by the runtime when the task finishes, under the
task manager's one global lock, and every object of it then pays
atomic reference counts on the applying thread.  A boxed `LineRec` per
line (and its nested records) is about `10^8` such objects on Mathlib.

So the worker writes each scanned record into ONE `ByteArray`, and the
applying thread reads the record's fields back out of it as it applies
them.  This module is the byte format:

* `enc*` — a value's bytes, as a `List UInt8` (the specification);
* `w*` — the writer, which appends exactly those bytes to a buffer
  (`w*_spec`);
* `r*` — the reader, which from a position returns the value and the
  position after it; `RD r x bs` says that `r` reads `x` back from any
  buffer whose bytes at the position begin with `bs`, and `rd*` proves
  it for `bs = enc* x`.

A natural number is four little-endian bytes when it is below
`2^32 - 1`, and otherwise the marker `0xFFFFFFFF` followed by its
base-128 digits (`natVal` literals are unbounded); a string is its
byte length and its UTF-8 bytes; a list its length and its members; a
record a tag byte and its fields in declaration order.  Nothing here
is trusted: the round trip (`rdLine`) is a theorem, and the parse's
statements are carried through it (`Pipeline.lean`).
-/

namespace ConLeche.Frontend.Flat

open ConLeche.Frontend

/-! ## The reading judgement -/

/-- **`r` reads `x` from bytes beginning with `bs`**: from any position
of any buffer whose bytes from there on are `bs` and then anything,
`r` returns `x` and the position after `bs`. -/
def RD {α : Type} (r : ByteArray → Nat → α × Nat) (x : α) (bs : List UInt8) : Prop :=
  ∀ (d : ByteArray) (p : Nat) (rest : List UInt8),
    d.data.toList.drop p = bs ++ rest → r d p = (x, p + bs.length)

/-- What follows a prefix that was read. -/
theorem drop_after {d : ByteArray} {p : Nat} {bs rest : List UInt8}
    (h : d.data.toList.drop p = bs ++ rest) : d.data.toList.drop (p + bs.length) = rest := by
  rw [← List.drop_drop, h, List.drop_left]

/-- A reader's step: its value, and the bytes after it. -/
theorem RD.run {α : Type} {r : ByteArray → Nat → α × Nat} {x : α} {bs : List UInt8}
    (hr : RD r x bs) {d : ByteArray} {p : Nat} {rest : List UInt8}
    (h : d.data.toList.drop p = bs ++ rest) :
    r d p = (x, p + bs.length) ∧ d.data.toList.drop (p + bs.length) = rest :=
  ⟨hr d p rest h, drop_after h⟩

/-- A byte at a position, and the bytes after it. -/
theorem drop_cons {d : ByteArray} {p : Nat} {b : UInt8} {rest : List UInt8}
    (h : d.data.toList.drop p = b :: rest) : d.data.toList.drop (p + 1) = rest :=
  drop_after (bs := [b]) h

/-- The byte at a position whose bytes begin with it. -/
theorem get!_of_drop {d : ByteArray} {p : Nat} {b : UInt8} {rest : List UInt8}
    (h : d.data.toList.drop p = b :: rest) : d.get! p = b := by
  have hp : p < d.data.toList.length := by
    rcases Nat.lt_or_ge p d.data.toList.length with hp | hp
    · exact hp
    · rw [List.drop_eq_nil_of_le hp] at h; cases h
  have h0 : (d.data.toList.drop p)[0]'(by rw [h]; simp) = b := by simp only [h]; rfl
  rw [List.getElem_drop] at h0
  simp only [ByteArray.get!, Nat.add_zero] at h0 ⊢
  cases d with
  | mk a =>
    simp only [Array.length_toList] at hp
    simp only [getElem!_pos a p hp, ← h0, Array.getElem_toList]

theorem lt_size_of_drop {d : ByteArray} {p : Nat} {b : UInt8} {rest : List UInt8}
    (h : d.data.toList.drop p = b :: rest) : p < d.size := by
  rcases Nat.lt_or_ge p d.size with hp | hp
  · exact hp
  · rw [List.drop_eq_nil_of_le (by simpa using hp)] at h; cases h

theorem get!_eq_getElem (d : ByteArray) (p : Nat) (h : p < d.size) : d.get! p = d[p] := by
  cases d with
  | mk a => simp only [ByteArray.get!]; exact getElem!_pos a p h

/-! ## Bytes -/

/-- One byte. -/
@[inline] def rByte (d : @& ByteArray) (p : Nat) : UInt8 × Nat := (d.get! p, p + 1)

theorem rdByte (b : UInt8) : RD rByte b [b] := by
  intro d p rest h
  simp only [rByte, get!_of_drop h, List.length_singleton]

/-! ## Natural numbers -/

/-- Four little-endian bytes.  (Shifts, not multiplications by
literals: the kernel unfolds `Nat.mul` along a literal second
argument, and a reader's matcher makes it reduce these terms.) -/
def le4 (x : UInt32) : List UInt8 :=
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8]

/-- Four little-endian bytes, appended. -/
@[inline] def w4 (d : ByteArray) (x : UInt32) : ByteArray :=
  (((d.push x.toUInt8).push (x >>> 8).toUInt8).push (x >>> 16).toUInt8).push (x >>> 24).toUInt8

/-- Four little-endian bytes, read. -/
@[inline] def r4 (d : @& ByteArray) (p : Nat) : UInt32 :=
  if h : p + 3 < d.size then
    d[p].toUInt32 + (d[p + 1].toUInt32 <<< 8) + (d[p + 2].toUInt32 <<< 16) +
      (d[p + 3].toUInt32 <<< 24)
  else 0

theorem le4_inv (x : UInt32) :
    x.toUInt8.toUInt32 + ((x >>> 8).toUInt8.toUInt32 <<< 8) +
      ((x >>> 16).toUInt8.toUInt32 <<< 16) + ((x >>> 24).toUInt8.toUInt32 <<< 24) = x := by
  apply UInt32.toNat_inj.mp
  have hx := x.toNat_lt
  simp only [UInt32.toNat_add, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt32.toNat_toUInt8,
    UInt32.toNat_shiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, UInt32.reduceToNat,
    Nat.reduceMod, Nat.reducePow]
  omega

theorem r4_of_drop {d : ByteArray} {p : Nat} {x : UInt32} {rest : List UInt8}
    (h : d.data.toList.drop p = le4 x ++ rest) : r4 d p = x := by
  simp only [le4, List.cons_append, List.nil_append] at h
  have h1 := drop_after (bs := [x.toUInt8]) h
  have h2 := drop_after (bs := [(x >>> 8).toUInt8]) h1
  have h3 := drop_after (bs := [(x >>> 16).toUInt8]) h2
  simp only [List.length_singleton, Nat.add_assoc] at h1 h2 h3
  have hs : p + 3 < d.size := lt_size_of_drop h3
  simp only [r4, hs, ↓reduceDIte, ← get!_eq_getElem, get!_of_drop h, get!_of_drop h1,
    get!_of_drop h2, get!_of_drop h3]
  exact le4_inv x

theorem w4_spec (d : ByteArray) (x : UInt32) :
    (w4 d x).data.toList = d.data.toList ++ le4 x := by
  simp [w4, le4, ByteArray.push]

/-- Base-128 digits, least significant first, the high bit marking
"more follow". -/
def leb (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: leb (n / 128)
termination_by n
decreasing_by omega

def wLeb (d : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then d.push n.toUInt8 else wLeb (d.push (n % 128 + 128).toUInt8) (n / 128)
termination_by n
decreasing_by omega

def rLeb (d : @& ByteArray) (p : Nat) : Nat × Nat :=
  if p < d.size then
    let b := d.get! p
    if b < 128 then (b.toNat, p + 1)
    else
      let (r, q) := rLeb d (p + 1)
      (b.toNat - 128 + 128 * r, q)
  else (0, p)
termination_by d.size - p

theorem wLeb_spec (d : ByteArray) (n : Nat) :
    (wLeb d n).data.toList = d.data.toList ++ leb n := by
  induction n using Nat.strongRecOn generalizing d with
  | _ n ih =>
    rw [wLeb, leb]
    split
    · simp [ByteArray.push]
    · rw [ih _ (by omega)]
      simp [ByteArray.push]

theorem rdLeb (n : Nat) : RD rLeb n (leb n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro d p rest h
    rw [leb] at h ⊢
    split at h
    · rename_i hn
      rw [List.cons_append] at h
      simp only [hn, ↓reduceIte]
      rw [rLeb]; simp only [lt_size_of_drop h, ↓reduceIte, get!_of_drop h]
      have : n.toUInt8 < 128 := by
        rw [UInt8.lt_iff_toNat_lt]; simp only [Nat.toUInt8, UInt8.toNat_ofNat']; simp; omega
      simp only [this, ↓reduceIte, List.length_singleton]
      simp only [Nat.toUInt8, UInt8.toNat_ofNat']; congr; omega
    · rename_i hn
      rw [List.cons_append] at h
      simp only [hn, ↓reduceIte]
      have h1 := drop_after (bs := [(n % 128 + 128).toUInt8]) (by simpa using h)
      simp only [List.length_singleton] at h1
      rw [rLeb]; simp only [lt_size_of_drop h, ↓reduceIte, get!_of_drop h]
      have hb : ¬ (n % 128 + 128).toUInt8 < 128 := by
        rw [UInt8.lt_iff_toNat_lt]; simp only [Nat.toUInt8, UInt8.toNat_ofNat']; simp; omega
      simp only [hb, ↓reduceIte, ih (n / 128) (by omega) d (p + 1) rest h1, List.length_cons]
      simp only [Nat.toUInt8, UInt8.toNat_ofNat', Prod.mk.injEq]
      constructor
      · omega
      · omega

/-- The escape marker: a number at or above it is written after it in
base 128. -/
def natEsc : Nat := 0xFFFFFFFF

/-- A natural number's bytes. -/
def encNat (n : Nat) : List UInt8 :=
  if n < natEsc then le4 n.toUInt32 else le4 0xFFFFFFFF ++ leb n

/-- A natural number, appended. -/
@[inline] def wNat (d : ByteArray) (n : Nat) : ByteArray :=
  if n < natEsc then w4 d n.toUInt32 else wLeb (w4 d 0xFFFFFFFF) n

@[noinline] def rNatBig (d : @& ByteArray) (p : Nat) : Nat × Nat := rLeb d (p + 4)

/-- A natural number, read. -/
@[inline] def rNat (d : @& ByteArray) (p : Nat) : Nat × Nat :=
  let v := r4 d p
  if v == 0xFFFFFFFF then rNatBig d p else (v.toNat, p + 4)

theorem wNat_spec (d : ByteArray) (n : Nat) :
    (wNat d n).data.toList = d.data.toList ++ encNat n := by
  unfold wNat encNat
  split
  · exact w4_spec d _
  · rw [wLeb_spec, w4_spec, List.append_assoc]

theorem rdNat (n : Nat) : RD rNat n (encNat n) := by
  intro d p rest h
  unfold encNat at h ⊢
  split at h
  · rename_i hn
    simp only [hn, ↓reduceIte]
    have hv := r4_of_drop h
    have : n.toUInt32.toNat = n := by
      simp only [Nat.toUInt32, UInt32.toNat_ofNat']; unfold natEsc at hn; omega
    have hne : (n.toUInt32 == 0xFFFFFFFF) = false := by
      apply beq_false_of_ne; intro he; rw [he] at this; unfold natEsc at hn; simp at this; omega
    simp only [rNat, hv, hne, Bool.false_eq_true, ↓reduceIte, this]
    simp [le4]
  · rename_i hn
    simp only [hn, ↓reduceIte]
    rw [List.append_assoc] at h
    have hv := r4_of_drop h
    have h1 := drop_after h
    simp only [rNat, hv, BEq.rfl, ↓reduceIte, rNatBig]
    simp only [le4, List.length_cons, List.length_nil] at h1
    rw [rdLeb n d (p + 4) rest h1]
    simp [le4]; omega

/-! ## Strings, booleans, optional numbers -/

/-- The bytes at `[q, q + l.length)` of a buffer whose bytes from `q` on
begin with `l`. -/
theorem extract_of_drop {d : ByteArray} {q : Nat} {l rest : List UInt8}
    (h : d.data.toList.drop q = l ++ rest) : (d.extract q (q + l.length)).data.toList = l := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop, h,
    Nat.add_sub_cancel_left, List.take_left' rfl]

/-- A string's bytes: its byte length, then its UTF-8 bytes. -/
def encStr (s : String) : List UInt8 := encNat s.utf8ByteSize ++ s.toByteArray.data.toList

@[inline] def wStr (d : ByteArray) (s : String) : ByteArray := wNat d s.utf8ByteSize ++ s.toByteArray

/-- Bytes as a string (malformed bytes read as the empty string: the
writer never makes them). -/
def strOf (b : ByteArray) : String := (String.fromUTF8? b).getD ""

/-- A string, read. -/
def rStr (d : @& ByteArray) (p : Nat) : String × Nat :=
  let (n, q) := rNat d p
  (strOf (d.extract q (q + n)), q + n)

theorem wStr_spec (d : ByteArray) (s : String) :
    (wStr d s).data.toList = d.data.toList ++ encStr s := by
  simp [wStr, encStr, wNat_spec]

theorem strOf_toByteArray (s : String) : strOf s.toByteArray = s := by
  simp only [strOf, String.fromUTF8?, s.isValidUTF8, ↓reduceDIte, Option.getD_some]; rfl

theorem rdStr (s : String) : RD rStr s (encStr s) := by
  intro d p rest h
  simp only [encStr, List.append_assoc] at h
  obtain ⟨e1, h⟩ := (rdNat _).run h
  have hsz : s.toByteArray.data.toList.length = s.utf8ByteSize := by simp
  have hx : d.extract (p + (encNat s.utf8ByteSize).length)
      (p + ((encNat s.utf8ByteSize).length + s.utf8ByteSize)) = s.toByteArray := by
    apply ByteArray.ext; apply Array.toList_inj.mp; rw [← Nat.add_assoc, ← hsz]
    exact extract_of_drop h
  simp only [rStr, e1, hx, strOf_toByteArray, encStr, List.length_append, hsz, Nat.add_assoc]

/-- A boolean: one byte. -/
def encBool (b : Bool) : List UInt8 := [if b then 1 else 0]

@[inline] def wBool (d : ByteArray) (b : Bool) : ByteArray := d.push (if b then 1 else 0)

@[inline] def rBool (d : @& ByteArray) (p : Nat) : Bool × Nat := (d.get! p != 0, p + 1)

theorem wBool_spec (d : ByteArray) (b : Bool) :
    (wBool d b).data.toList = d.data.toList ++ encBool b := by
  simp [wBool, encBool, ByteArray.push]

theorem rdBool (b : Bool) : RD rBool b (encBool b) := by
  intro d p rest h
  simp only [encBool, List.cons_append, List.nil_append] at h
  cases b <;> simp [rBool, get!_of_drop h, encBool]

/-- An optional number: a byte, then the number if present. -/
def encOpt : Option Nat → List UInt8
  | none => [0]
  | some n => 1 :: encNat n

def wOpt (d : ByteArray) : Option Nat → ByteArray
  | none => d.push 0
  | some n => wNat (d.push 1) n

def rOpt (d : @& ByteArray) (p : Nat) : Option Nat × Nat :=
  if d.get! p == 0 then (none, p + 1)
  else
    let (n, q) := rNat d (p + 1)
    (some n, q)

theorem wOpt_spec (d : ByteArray) (o : Option Nat) :
    (wOpt d o).data.toList = d.data.toList ++ encOpt o := by
  cases o <;> simp [wOpt, encOpt, ByteArray.push, wNat_spec]

/-! ## Lists -/

/-- The members' bytes, one after the other. -/
def encElems {α : Type} (e : α → List UInt8) : List α → List UInt8
  | [] => []
  | x :: xs => e x ++ encElems e xs

/-- A list's bytes: its length, then its members. -/
def encList {α : Type} (e : α → List UInt8) (xs : List α) : List UInt8 :=
  encNat xs.length ++ encElems e xs

def wElems {α : Type} (w : ByteArray → α → ByteArray) : ByteArray → List α → ByteArray
  | d, [] => d
  | d, x :: xs => wElems w (w d x) xs

@[inline] def wList {α : Type} (w : ByteArray → α → ByteArray) (d : ByteArray) (xs : List α) :
    ByteArray :=
  wElems w (wNat d xs.length) xs

@[specialize] def rElems {α : Type} (r : ByteArray → Nat → α × Nat) (d : @& ByteArray) :
    Nat → Nat → List α × Nat
  | 0, p => ([], p)
  | k + 1, p =>
    let (x, p) := r d p
    let (xs, p) := rElems r d k p
    (x :: xs, p)

@[inline] def rList {α : Type} (r : ByteArray → Nat → α × Nat) (d : @& ByteArray) (p : Nat) :
    List α × Nat :=
  let (k, p) := rNat d p
  rElems r d k p

theorem wElems_spec {α : Type} {w : ByteArray → α → ByteArray} {e : α → List UInt8}
    (hw : ∀ d x, (w d x).data.toList = d.data.toList ++ e x) (d : ByteArray) (xs : List α) :
    (wElems w d xs).data.toList = d.data.toList ++ encElems e xs := by
  induction xs generalizing d with
  | nil => simp [wElems, encElems]
  | cons x xs ih => simp [wElems, encElems, ih, hw]

theorem wList_spec {α : Type} {w : ByteArray → α → ByteArray} {e : α → List UInt8}
    (hw : ∀ d x, (w d x).data.toList = d.data.toList ++ e x) (d : ByteArray) (xs : List α) :
    (wList w d xs).data.toList = d.data.toList ++ encList e xs := by
  simp [wList, encList, wElems_spec hw, wNat_spec]

theorem rdElems {α : Type} {r : ByteArray → Nat → α × Nat} {e : α → List UInt8}
    (xs : List α) (hr : ∀ x ∈ xs, RD r x (e x)) :
    RD (fun d p => rElems r d xs.length p) xs (encElems e xs) := by
  induction xs with
  | nil => intro d p rest h; simp [rElems, encElems]
  | cons x xs ih =>
    intro d p rest h
    simp only [encElems, List.append_assoc] at h
    obtain ⟨e1, h⟩ := (hr x (by simp)).run h
    have e2 := ih (fun y hy => hr y (by simp [hy])) d _ rest h
    simp only [List.length_cons, rElems, e1, e2, encElems, List.length_append, Nat.add_assoc]

theorem rdList {α : Type} {r : ByteArray → Nat → α × Nat} {e : α → List UInt8}
    (xs : List α) (hr : ∀ x ∈ xs, RD r x (e x)) : RD (rList r) xs (encList e xs) := by
  intro d p rest h
  simp only [encList, List.append_assoc] at h
  obtain ⟨e1, h⟩ := (rdNat _).run h
  have e2 := rdElems xs hr d _ rest h
  simp only [rList, e1, e2, encList, List.length_append, Nat.add_assoc]

theorem rdOpt (o : Option Nat) : RD rOpt o (encOpt o) := by
  intro d p rest h
  cases o with
  | none =>
    simp only [encOpt, List.cons_append, List.nil_append] at h
    simp [rOpt, get!_of_drop h, encOpt]
  | some n =>
    simp only [encOpt, List.cons_append] at h
    have h1 := drop_cons h
    simp only [rOpt, get!_of_drop h, (rdNat n) d (p + 1) rest h1]
    simp [encOpt]; omega

/-! ## The reading tactic

A record's reader is a chain of `let (x, p) := r d p` steps; its proof
reads the fields in order, each by its `RD` lemma, against the bytes
hypothesis `h`, which each step advances. -/

set_option hygiene false in
/-- Read one field with the given `RD` lemma: rewrite the reader call
and advance `h`. -/
macro "rd_field " t:term : tactic =>
  `(tactic| (obtain ⟨e, h⟩ := ($t).run h; simp only [e]))

set_option hygiene false in
/-- Read the tag byte. -/
macro "rd_tag" : tactic =>
  `(tactic| (simp only [List.cons_append] at h;
             have ht := get!_of_drop h;
             have h := drop_after (bs := [_]) (by rw [List.singleton_append]; exact h);
             simp only [List.length_singleton] at h))

/-! ## Declaration records -/

def encCV (cv : CVRec) : List UInt8 :=
  encNat cv.name ++ (encList encNat cv.levelParams ++ encNat cv.type)

def wCV (d : ByteArray) (cv : CVRec) : ByteArray :=
  wNat (wList wNat (wNat d cv.name) cv.levelParams) cv.type

def rCV (d : @& ByteArray) (p : Nat) : CVRec × Nat :=
  let (name, p) := rNat d p
  let (lps, p) := rList rNat d p
  let (ty, p) := rNat d p
  (⟨name, lps, ty⟩, p)

theorem wCV_spec (d : ByteArray) (cv : CVRec) :
    (wCV d cv).data.toList = d.data.toList ++ encCV cv := by
  simp [wCV, encCV, wNat_spec, wList_spec wNat_spec]

theorem rdCV (cv : CVRec) : RD rCV cv (encCV cv) := by
  intro d p rest h
  simp only [encCV, List.append_assoc] at h
  unfold rCV
  rd_field rdNat _
  rd_field rdList _ (fun x _ => rdNat x)
  rd_field rdNat _
  simp [encCV, Nat.add_assoc]

def encHints : HintsRec → List UInt8
  | .abbrev => [0]
  | .opaque => [1]
  | .regular n => 2 :: encNat n

def wHints (d : ByteArray) : HintsRec → ByteArray
  | .abbrev => d.push 0
  | .opaque => d.push 1
  | .regular n => wNat (d.push 2) n

def rHints (d : @& ByteArray) (p : Nat) : HintsRec × Nat :=
  let t := d.get! p
  if t == 0 then (.abbrev, p + 1)
  else if t == 1 then (.opaque, p + 1)
  else
    let (n, p) := rNat d (p + 1)
    (.regular n, p)

theorem wHints_spec (d : ByteArray) (x : HintsRec) :
    (wHints d x).data.toList = d.data.toList ++ encHints x := by
  cases x <;> simp [wHints, encHints, ByteArray.push, wNat_spec]

theorem rdHints (x : HintsRec) : RD rHints x (encHints x) := by
  intro d p rest h
  cases x with
  | «abbrev» => simp only [encHints, List.cons_append, List.nil_append] at h; simp [rHints, get!_of_drop h, encHints]
  | «opaque» => simp only [encHints, List.cons_append, List.nil_append] at h; simp [rHints, get!_of_drop h, encHints]
  | regular n =>
    simp only [encHints, List.cons_append] at h
    have ht := get!_of_drop h
    have h := drop_cons h
    unfold rHints
    simp only [ht]
    rd_field rdNat _
    simp [encHints]; omega

def encRule (x : RuleRec) : List UInt8 := encNat x.ctor ++ (encNat x.nfields ++ encNat x.rhs)

def wRule (d : ByteArray) (x : RuleRec) : ByteArray := wNat (wNat (wNat d x.ctor) x.nfields) x.rhs

def rRule (d : @& ByteArray) (p : Nat) : RuleRec × Nat :=
  let (c, p) := rNat d p
  let (n, p) := rNat d p
  let (r, p) := rNat d p
  (⟨c, n, r⟩, p)

theorem wRule_spec (d : ByteArray) (x : RuleRec) :
    (wRule d x).data.toList = d.data.toList ++ encRule x := by
  simp [wRule, encRule, wNat_spec]

theorem rdRule (x : RuleRec) : RD rRule x (encRule x) := by
  intro d p rest h
  simp only [encRule, List.append_assoc] at h
  unfold rRule
  rd_field rdNat _
  rd_field rdNat _
  rd_field rdNat _
  simp [encRule, Nat.add_assoc]

def encIndType (x : IndTypeRec) : List UInt8 :=
  encCV x.cv ++ (encList encNat x.ctors ++ (encBool x.isRec ++ (encBool x.isReflexive ++
    (encBool x.isUnsafe ++ (encNat x.numIndices ++ (encNat x.numNested ++ encNat x.numParams))))))

def wIndType (d : ByteArray) (x : IndTypeRec) : ByteArray :=
  let d := wCV d x.cv
  let d := wList wNat d x.ctors
  let d := wBool d x.isRec
  let d := wBool d x.isReflexive
  let d := wBool d x.isUnsafe
  let d := wNat d x.numIndices
  let d := wNat d x.numNested
  wNat d x.numParams

def rIndType (d : @& ByteArray) (p : Nat) : IndTypeRec × Nat :=
  let (cv, p) := rCV d p
  let (ctors, p) := rList rNat d p
  let (isRec, p) := rBool d p
  let (isReflexive, p) := rBool d p
  let (isUnsafe, p) := rBool d p
  let (numIndices, p) := rNat d p
  let (numNested, p) := rNat d p
  let (numParams, p) := rNat d p
  (⟨cv, ctors, isRec, isReflexive, isUnsafe, numIndices, numNested, numParams⟩, p)

theorem wIndType_spec (d : ByteArray) (x : IndTypeRec) :
    (wIndType d x).data.toList = d.data.toList ++ encIndType x := by
  simp [wIndType, encIndType, wNat_spec, wCV_spec, wBool_spec, wList_spec wNat_spec]

theorem rdIndType (x : IndTypeRec) : RD rIndType x (encIndType x) := by
  intro d p rest h
  simp only [encIndType, List.append_assoc] at h
  unfold rIndType
  rd_field rdCV _
  rd_field rdList _ (fun x _ => rdNat x)
  rd_field rdBool _
  rd_field rdBool _
  rd_field rdBool _
  rd_field rdNat _
  rd_field rdNat _
  rd_field rdNat _
  simp [encIndType, Nat.add_assoc]

def encIndCtor (x : IndCtorRec) : List UInt8 :=
  encCV x.cv ++ (encBool x.isUnsafe ++ (encNat x.numFields ++ (encNat x.numParams ++
    (encOpt x.cidx ++ encOpt x.induct))))

def wIndCtor (d : ByteArray) (x : IndCtorRec) : ByteArray :=
  let d := wCV d x.cv
  let d := wBool d x.isUnsafe
  let d := wNat d x.numFields
  let d := wNat d x.numParams
  let d := wOpt d x.cidx
  wOpt d x.induct

def rIndCtor (d : @& ByteArray) (p : Nat) : IndCtorRec × Nat :=
  let (cv, p) := rCV d p
  let (isUnsafe, p) := rBool d p
  let (numFields, p) := rNat d p
  let (numParams, p) := rNat d p
  let (cidx, p) := rOpt d p
  let (induct, p) := rOpt d p
  (⟨cv, isUnsafe, numFields, numParams, cidx, induct⟩, p)

theorem wIndCtor_spec (d : ByteArray) (x : IndCtorRec) :
    (wIndCtor d x).data.toList = d.data.toList ++ encIndCtor x := by
  simp [wIndCtor, encIndCtor, wNat_spec, wCV_spec, wBool_spec, wOpt_spec]

theorem rdIndCtor (x : IndCtorRec) : RD rIndCtor x (encIndCtor x) := by
  intro d p rest h
  simp only [encIndCtor, List.append_assoc] at h
  unfold rIndCtor
  rd_field rdCV _
  rd_field rdBool _
  rd_field rdNat _
  rd_field rdNat _
  rd_field rdOpt _
  rd_field rdOpt _
  simp [encIndCtor, Nat.add_assoc]

def encIndRec (x : IndRecRec) : List UInt8 :=
  encCV x.cv ++ (encBool x.isUnsafe ++ (encBool x.k ++ (encNat x.numIndices ++
    (encNat x.numMinors ++ (encNat x.numMotives ++ (encNat x.numParams ++
      encList encRule x.rules))))))

def wIndRec (d : ByteArray) (x : IndRecRec) : ByteArray :=
  let d := wCV d x.cv
  let d := wBool d x.isUnsafe
  let d := wBool d x.k
  let d := wNat d x.numIndices
  let d := wNat d x.numMinors
  let d := wNat d x.numMotives
  let d := wNat d x.numParams
  wList wRule d x.rules

def rIndRec (d : @& ByteArray) (p : Nat) : IndRecRec × Nat :=
  let (cv, p) := rCV d p
  let (isUnsafe, p) := rBool d p
  let (k, p) := rBool d p
  let (numIndices, p) := rNat d p
  let (numMinors, p) := rNat d p
  let (numMotives, p) := rNat d p
  let (numParams, p) := rNat d p
  let (rules, p) := rList rRule d p
  (⟨cv, isUnsafe, k, numIndices, numMinors, numMotives, numParams, rules⟩, p)

theorem wIndRec_spec (d : ByteArray) (x : IndRecRec) :
    (wIndRec d x).data.toList = d.data.toList ++ encIndRec x := by
  simp [wIndRec, encIndRec, wNat_spec, wCV_spec, wBool_spec, wList_spec wRule_spec]

theorem rdIndRec (x : IndRecRec) : RD rIndRec x (encIndRec x) := by
  intro d p rest h
  simp only [encIndRec, List.append_assoc] at h
  unfold rIndRec
  rd_field rdCV _
  rd_field rdBool _
  rd_field rdBool _
  rd_field rdNat _
  rd_field rdNat _
  rd_field rdNat _
  rd_field rdNat _
  rd_field rdList _ (fun x _ => rdRule x)
  simp [encIndRec, Nat.add_assoc]

def encDecl : DeclRec → List UInt8
  | .ax cv u => 0 :: (encCV cv ++ encBool u)
  | .defn cv v hs sf => 1 :: (encCV cv ++ (encNat v ++ (encHints hs ++ encStr sf)))
  | .thm cv v => 2 :: (encCV cv ++ encNat v)
  | .opaq cv v u => 3 :: (encCV cv ++ (encNat v ++ encBool u))
  | .quot cv k => 4 :: (encCV cv ++ encStr k)
  | .ind tys cts rcs =>
    5 :: (encList encIndType tys ++ (encList encIndCtor cts ++ encList encIndRec rcs))

def wDecl (d : ByteArray) : DeclRec → ByteArray
  | .ax cv u => wBool (wCV (d.push 0) cv) u
  | .defn cv v hs sf => wStr (wHints (wNat (wCV (d.push 1) cv) v) hs) sf
  | .thm cv v => wNat (wCV (d.push 2) cv) v
  | .opaq cv v u => wBool (wNat (wCV (d.push 3) cv) v) u
  | .quot cv k => wStr (wCV (d.push 4) cv) k
  | .ind tys cts rcs =>
    wList wIndRec (wList wIndCtor (wList wIndType (d.push 5) tys) cts) rcs

def rDecl (d : @& ByteArray) (p : Nat) : DeclRec × Nat :=
  let t := d.get! p
  if t == 0 then
    let (cv, q) := rCV d (p + 1)
    let (u, q) := rBool d q
    (.ax cv u, q)
  else if t == 1 then
    let (cv, q) := rCV d (p + 1)
    let (v, q) := rNat d q
    let (hs, q) := rHints d q
    let (sf, q) := rStr d q
    (.defn cv v hs sf, q)
  else if t == 2 then
    let (cv, q) := rCV d (p + 1)
    let (v, q) := rNat d q
    (.thm cv v, q)
  else if t == 3 then
    let (cv, q) := rCV d (p + 1)
    let (v, q) := rNat d q
    let (u, q) := rBool d q
    (.opaq cv v u, q)
  else if t == 4 then
    let (cv, q) := rCV d (p + 1)
    let (k, q) := rStr d q
    (.quot cv k, q)
  else
    let (tys, q) := rList rIndType d (p + 1)
    let (cts, q) := rList rIndCtor d q
    let (rcs, q) := rList rIndRec d q
    (.ind tys cts rcs, q)

theorem wDecl_spec (d : ByteArray) (x : DeclRec) :
    (wDecl d x).data.toList = d.data.toList ++ encDecl x := by
  cases x <;> simp [wDecl, encDecl, ByteArray.push, wNat_spec, wCV_spec, wBool_spec, wHints_spec,
    wStr_spec, wList_spec wIndType_spec, wList_spec wIndCtor_spec, wList_spec wIndRec_spec]

theorem rdDecl (x : DeclRec) : RD rDecl x (encDecl x) := by
  intro d p rest h
  cases x with
  | ax cv u =>
    simp only [encDecl, List.cons_append, List.append_assoc] at h
    have ht := get!_of_drop h; have h := drop_cons h
    unfold rDecl; simp only [ht]
    rd_field rdCV _
    rd_field rdBool _
    simp [encDecl]; omega
  | defn cv v hs sf =>
    simp only [encDecl, List.cons_append, List.append_assoc] at h
    have ht := get!_of_drop h; have h := drop_cons h
    unfold rDecl; simp only [ht]
    rd_field rdCV _
    rd_field rdNat _
    rd_field rdHints _
    rd_field rdStr _
    simp [encDecl]; omega
  | thm cv v =>
    simp only [encDecl, List.cons_append, List.append_assoc] at h
    have ht := get!_of_drop h; have h := drop_cons h
    unfold rDecl; simp only [ht]
    rd_field rdCV _
    rd_field rdNat _
    simp [encDecl]; omega
  | opaq cv v u =>
    simp only [encDecl, List.cons_append, List.append_assoc] at h
    have ht := get!_of_drop h; have h := drop_cons h
    unfold rDecl; simp only [ht]
    rd_field rdCV _
    rd_field rdNat _
    rd_field rdBool _
    simp [encDecl]; omega
  | quot cv k =>
    simp only [encDecl, List.cons_append, List.append_assoc] at h
    have ht := get!_of_drop h; have h := drop_cons h
    unfold rDecl; simp only [ht]
    rd_field rdCV _
    rd_field rdStr _
    simp [encDecl]; omega
  | ind tys cts rcs =>
    simp only [encDecl, List.cons_append, List.append_assoc] at h
    have ht := get!_of_drop h; have h := drop_cons h
    unfold rDecl; simp only [ht]
    rd_field rdList _ (fun x _ => rdIndType x)
    rd_field rdList _ (fun x _ => rdIndCtor x)
    rd_field rdList _ (fun x _ => rdIndRec x)
    simp [encDecl]; omega

/-! ## Lines -/

def encPw : PwRec → List UInt8
  | .never => [0]
  | .ifAllZero ns => 1 :: encList encNat ns

def wPw (d : ByteArray) : PwRec → ByteArray
  | .never => d.push 0
  | .ifAllZero ns => wList wNat (d.push 1) ns

@[inline] def rPw (d : @& ByteArray) (p : Nat) : PwRec × Nat :=
  if d.get! p == 0 then (.never, p + 1)
  else
    let (ns, q) := rList rNat d (p + 1)
    (.ifAllZero ns, q)

theorem wPw_spec (d : ByteArray) (x : PwRec) :
    (wPw d x).data.toList = d.data.toList ++ encPw x := by
  cases x <;> simp [wPw, encPw, ByteArray.push, wList_spec wNat_spec]

theorem rdPw (x : PwRec) : RD rPw x (encPw x) := by
  intro d p rest h
  cases x with
  | never => simp only [encPw, List.cons_append, List.nil_append] at h; simp [rPw, get!_of_drop h, encPw]
  | ifAllZero ns =>
    simp only [encPw, List.cons_append] at h
    have ht := get!_of_drop h; have h := drop_cons h
    unfold rPw; simp only [ht]
    rd_field rdList _ (fun x _ => rdNat x)
    simp [encPw]; omega

/-- A line's bytes: a tag byte, the table index if any, the fields.
The tags are ordered by how often the line kind occurs in Mathlib
(`app` is four lines in five), which is the order the reader tests
them in. -/
def encLine : LineRec → List UInt8
  | .expr i (.app f a) => 0 :: (encNat i ++ (encNat f ++ encNat a))
  | .expr i (.lam ty bd pw) => 1 :: (encNat i ++ (encNat ty ++ (encNat bd ++ encPw pw)))
  | .expr i (.forallE ty bd pw) => 2 :: (encNat i ++ (encNat ty ++ (encNat bd ++ encPw pw)))
  | .name i (.str pre s) => 3 :: (encNat i ++ (encNat pre ++ encStr s))
  | .name i (.num pre n) => 4 :: (encNat i ++ (encNat pre ++ encNat n))
  | .expr i (.const n us) => 5 :: (encNat i ++ (encNat n ++ encList encNat us))
  | .expr i (.letE ty v bd) => 6 :: (encNat i ++ (encNat ty ++ (encNat v ++ encNat bd)))
  | .expr i (.bvar k) => 7 :: (encNat i ++ encNat k)
  | .expr i (.sort u) => 8 :: (encNat i ++ encNat u)
  | .expr i (.proj tn ix st) => 9 :: (encNat i ++ (encNat tn ++ (encNat ix ++ encNat st)))
  | .expr i (.natVal n) => 10 :: (encNat i ++ encNat n)
  | .expr i (.strVal s) => 11 :: (encNat i ++ encStr s)
  | .level i (.succ u) => 12 :: (encNat i ++ encNat u)
  | .level i (.max u v) => 13 :: (encNat i ++ (encNat u ++ encNat v))
  | .level i (.imax u v) => 14 :: (encNat i ++ (encNat u ++ encNat v))
  | .level i (.param n) => 15 :: (encNat i ++ encNat n)
  | .decl dr => 16 :: encDecl dr
  | .header => [17]
  | .blank => [18]

/-- A line, appended. -/
def wLine (d : ByteArray) : LineRec → ByteArray
  | .expr i (.app f a) => wNat (wNat (wNat (d.push 0) i) f) a
  | .expr i (.lam ty bd pw) => wPw (wNat (wNat (wNat (d.push 1) i) ty) bd) pw
  | .expr i (.forallE ty bd pw) => wPw (wNat (wNat (wNat (d.push 2) i) ty) bd) pw
  | .name i (.str pre s) => wStr (wNat (wNat (d.push 3) i) pre) s
  | .name i (.num pre n) => wNat (wNat (wNat (d.push 4) i) pre) n
  | .expr i (.const n us) => wList wNat (wNat (wNat (d.push 5) i) n) us
  | .expr i (.letE ty v bd) => wNat (wNat (wNat (wNat (d.push 6) i) ty) v) bd
  | .expr i (.bvar k) => wNat (wNat (d.push 7) i) k
  | .expr i (.sort u) => wNat (wNat (d.push 8) i) u
  | .expr i (.proj tn ix st) => wNat (wNat (wNat (wNat (d.push 9) i) tn) ix) st
  | .expr i (.natVal n) => wNat (wNat (d.push 10) i) n
  | .expr i (.strVal s) => wStr (wNat (d.push 11) i) s
  | .level i (.succ u) => wNat (wNat (d.push 12) i) u
  | .level i (.max u v) => wNat (wNat (wNat (d.push 13) i) u) v
  | .level i (.imax u v) => wNat (wNat (wNat (d.push 14) i) u) v
  | .level i (.param n) => wNat (wNat (d.push 15) i) n
  | .decl dr => wDecl (d.push 16) dr
  | .header => d.push 17
  | .blank => d.push 18

theorem wLine_spec (d : ByteArray) (r : LineRec) :
    (wLine d r).data.toList = d.data.toList ++ encLine r := by
  rcases r with ⟨i, r⟩ | ⟨i, r⟩ | ⟨i, r⟩ | dr | _ | _
  · cases r <;> simp [wLine, encLine, ByteArray.push, wNat_spec, wStr_spec]
  · cases r <;> simp [wLine, encLine, ByteArray.push, wNat_spec]
  · cases r <;> simp [wLine, encLine, ByteArray.push, wNat_spec, wStr_spec, wPw_spec,
      wList_spec wNat_spec]
  · simp [wLine, encLine, ByteArray.push, wDecl_spec]
  · simp [wLine, encLine, ByteArray.push]
  · simp [wLine, encLine, ByteArray.push]

/-- **A line, read, and handed to `k`** with the position after it.
The reader is written in this continuation form so that the applying
loop can consume a line's fields where they are read: with `k`
inlined, the record `k` matches on is a known constructor and is
never built. -/
@[inline] def withLine {β : Type} (d : @& ByteArray) (p : Nat) (k : LineRec → Nat → β) : β :=
  if d.get! p == 0 then
    let (i, p) := rNat d (p + 1)
    let (f, p) := rNat d p
    let (a, p) := rNat d p
    k (.expr i (.app f a)) p
  else if d.get! p == 1 then
    let (i, p) := rNat d (p + 1)
    let (ty, p) := rNat d p
    let (bd, p) := rNat d p
    let (pw, p) := rPw d p
    k (.expr i (.lam ty bd pw)) p
  else if d.get! p == 2 then
    let (i, p) := rNat d (p + 1)
    let (ty, p) := rNat d p
    let (bd, p) := rNat d p
    let (pw, p) := rPw d p
    k (.expr i (.forallE ty bd pw)) p
  else if d.get! p == 3 then
    let (i, p) := rNat d (p + 1)
    let (pre, p) := rNat d p
    let (s, p) := rStr d p
    k (.name i (.str pre s)) p
  else if d.get! p == 4 then
    let (i, p) := rNat d (p + 1)
    let (pre, p) := rNat d p
    let (n, p) := rNat d p
    k (.name i (.num pre n)) p
  else if d.get! p == 5 then
    let (i, p) := rNat d (p + 1)
    let (n, p) := rNat d p
    let (us, p) := rList rNat d p
    k (.expr i (.const n us)) p
  else if d.get! p == 6 then
    let (i, p) := rNat d (p + 1)
    let (ty, p) := rNat d p
    let (v, p) := rNat d p
    let (bd, p) := rNat d p
    k (.expr i (.letE ty v bd)) p
  else if d.get! p == 7 then
    let (i, p) := rNat d (p + 1)
    let (n, p) := rNat d p
    k (.expr i (.bvar n)) p
  else if d.get! p == 8 then
    let (i, p) := rNat d (p + 1)
    let (u, p) := rNat d p
    k (.expr i (.sort u)) p
  else if d.get! p == 9 then
    let (i, p) := rNat d (p + 1)
    let (tn, p) := rNat d p
    let (ix, p) := rNat d p
    let (st, p) := rNat d p
    k (.expr i (.proj tn ix st)) p
  else if d.get! p == 10 then
    let (i, p) := rNat d (p + 1)
    let (n, p) := rNat d p
    k (.expr i (.natVal n)) p
  else if d.get! p == 11 then
    let (i, p) := rNat d (p + 1)
    let (s, p) := rStr d p
    k (.expr i (.strVal s)) p
  else if d.get! p == 12 then
    let (i, p) := rNat d (p + 1)
    let (u, p) := rNat d p
    k (.level i (.succ u)) p
  else if d.get! p == 13 then
    let (i, p) := rNat d (p + 1)
    let (u, p) := rNat d p
    let (v, p) := rNat d p
    k (.level i (.max u v)) p
  else if d.get! p == 14 then
    let (i, p) := rNat d (p + 1)
    let (u, p) := rNat d p
    let (v, p) := rNat d p
    k (.level i (.imax u v)) p
  else if d.get! p == 15 then
    let (i, p) := rNat d (p + 1)
    let (n, p) := rNat d p
    k (.level i (.param n)) p
  else if d.get! p == 16 then
    let (dr, p) := rDecl d (p + 1)
    k (.decl dr) p
  else if d.get! p == 17 then k .header (p + 1)
  else k .blank (p + 1)

/-- A line, read. -/
def rLine (d : @& ByteArray) (p : Nat) : LineRec × Nat := withLine d p Prod.mk

/-- The continuation form is the reader followed by the continuation. -/
theorem withLine_eq {β : Type} (d : ByteArray) (p : Nat) (k : LineRec → Nat → β) :
    withLine d p k = k (rLine d p).1 (rLine d p).2 := by
  unfold rLine withLine
  by_cases h0 : (d.get! p == 0) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), ite_eq_left_of_eq_true _ _ (eq_true h0)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h0), ite_eq_right_of_eq_false _ _ (eq_false h0)]
  by_cases h1 : (d.get! p == 1) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h1)]
  by_cases h2 : (d.get! p == 2) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2)]
  by_cases h3 : (d.get! p == 3) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h3), ite_eq_left_of_eq_true _ _ (eq_true h3)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h3), ite_eq_right_of_eq_false _ _ (eq_false h3)]
  by_cases h4 : (d.get! p == 4) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h4), ite_eq_left_of_eq_true _ _ (eq_true h4)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h4), ite_eq_right_of_eq_false _ _ (eq_false h4)]
  by_cases h5 : (d.get! p == 5) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h5), ite_eq_left_of_eq_true _ _ (eq_true h5)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h5), ite_eq_right_of_eq_false _ _ (eq_false h5)]
  by_cases h6 : (d.get! p == 6) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h6), ite_eq_left_of_eq_true _ _ (eq_true h6)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h6), ite_eq_right_of_eq_false _ _ (eq_false h6)]
  by_cases h7 : (d.get! p == 7) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h7), ite_eq_left_of_eq_true _ _ (eq_true h7)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h7), ite_eq_right_of_eq_false _ _ (eq_false h7)]
  by_cases h8 : (d.get! p == 8) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h8), ite_eq_left_of_eq_true _ _ (eq_true h8)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h8), ite_eq_right_of_eq_false _ _ (eq_false h8)]
  by_cases h9 : (d.get! p == 9) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h9), ite_eq_left_of_eq_true _ _ (eq_true h9)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h9), ite_eq_right_of_eq_false _ _ (eq_false h9)]
  by_cases h10 : (d.get! p == 10) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h10), ite_eq_left_of_eq_true _ _ (eq_true h10)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h10), ite_eq_right_of_eq_false _ _ (eq_false h10)]
  by_cases h11 : (d.get! p == 11) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h11), ite_eq_left_of_eq_true _ _ (eq_true h11)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h11), ite_eq_right_of_eq_false _ _ (eq_false h11)]
  by_cases h12 : (d.get! p == 12) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h12), ite_eq_left_of_eq_true _ _ (eq_true h12)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h12), ite_eq_right_of_eq_false _ _ (eq_false h12)]
  by_cases h13 : (d.get! p == 13) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h13), ite_eq_left_of_eq_true _ _ (eq_true h13)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h13), ite_eq_right_of_eq_false _ _ (eq_false h13)]
  by_cases h14 : (d.get! p == 14) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h14), ite_eq_left_of_eq_true _ _ (eq_true h14)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h14), ite_eq_right_of_eq_false _ _ (eq_false h14)]
  by_cases h15 : (d.get! p == 15) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h15), ite_eq_left_of_eq_true _ _ (eq_true h15)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h15), ite_eq_right_of_eq_false _ _ (eq_false h15)]
  by_cases h16 : (d.get! p == 16) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h16), ite_eq_left_of_eq_true _ _ (eq_true h16)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h16), ite_eq_right_of_eq_false _ _ (eq_false h16)]
  by_cases h17 : (d.get! p == 17) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h17), ite_eq_left_of_eq_true _ _ (eq_true h17)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h17), ite_eq_right_of_eq_false _ _ (eq_false h17)]

theorem rdLine (r : LineRec) : RD rLine r (encLine r) := by
  intro d p rest h
  unfold rLine withLine
  rcases r with ⟨i, r⟩ | ⟨i, r⟩ | ⟨i, r⟩ | dr | _ | _
  all_goals first | cases r | skip
  all_goals
    simp only [encLine, List.cons_append, List.append_assoc] at h
    have ht := get!_of_drop h; have h := drop_cons h
    simp (config := { decide := true }) only [ht, ↓reduceIte]
    repeat (first
      | rd_field rdNat _
      | rd_field rdStr _
      | rd_field rdPw _
      | rd_field rdList _ (fun x _ => rdNat x)
      | rd_field rdDecl _)
    simp only [encLine, List.length_cons, List.length_append, List.length_nil, Prod.mk.injEq,
      true_and]
    try omega

/-! ## A run of lines -/

/-- `k` lines read from position `p`, one after the other. -/
def decodeN (d : ByteArray) : Nat → Nat → List LineRec
  | _, 0 => []
  | p, k + 1 => (rLine d p).1 :: decodeN d (rLine d p).2 k

/-- **The round trip**: lines written one after the other read back as
themselves. -/
theorem decodeN_encElems (rs : List LineRec) :
    ∀ (d : ByteArray) (p : Nat) (rest : List UInt8),
    d.data.toList.drop p = encElems encLine rs ++ rest → decodeN d p rs.length = rs := by
  induction rs with
  | nil => intro d p rest _; rfl
  | cons r rs ih =>
    intro d p rest h
    simp only [encElems, List.append_assoc] at h
    obtain ⟨e, h⟩ := (rdLine r).run h
    simp only [List.length_cons, decodeN, e]
    rw [ih d _ rest h]

end ConLeche.Frontend.Flat
