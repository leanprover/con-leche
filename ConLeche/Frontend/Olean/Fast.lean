module

public import ConLeche.Frontend.Olean.Spec

@[expose] public section

/-!
# Reading `.olean` files: the fast decoder (task #371)

The specification (`ConLeche/Frontend/Olean/Spec.lean`) reads every
value by recursion on its object, so a node shared by many parents is
read once per path to it.  This file reads each object once, in two
passes over the module's region, using the specification's own node
functions for the reading itself:

1. **Mark, downwards.**  The objects the module's constants need are
   *marked* with the kind they are read as (a name, a level, a list of
   levels, an expression), the roots first: the names and expressions
   of the constants' skeletons (`constSkel`).  Then the region is
   swept from its last word to its first; a marked object's shape is
   checked and the objects its fields point to are marked in turn
   (`markName` … `markExpr`).  They lie below it, so the sweep reaches
   them later.
2. **Build, upwards.**  The region is swept from its first word to its
   last, and every marked object is read by its node function
   (`nameNode` … `exprNode`) with the values of the objects it points
   to taken from the memo: they lie below it, so they are built
   already.  The value goes into the memo at the object's slot.

The result shares every node exactly as the file shares it (the
compactor max-shares a module's objects).  There is no recursion, so
nothing depends on how deep the values nest, and no worklist.  Across
modules nothing is shared: each module's values are its own (a
run-wide hash-consing of names and levels was dropped with this
decoder; DESIGN.md, task #371).

`decodeModuleFast` is the fast twin of `decodeModuleSpec`; the theorem
`decodeModuleSpec_eq_fast` (`ConLeche/Verify/Frontend/Olean/Equiv.lean`)
says they are equal, and is the `@[csimp]` lemma that makes the
compiler run this one where the driver calls the specification.

**The memo** is dense, by slot (a location divided by 8), and ends at
the highest root: one mark byte per slot (a bit per kind), and the
values (`DS`), one array per kind.  The downward sweep threads the mark
bytes alone, the upward sweep reads them and threads the values.  Each
update of the values takes the array it changes OUT of the record first
(the destructuring `let`), so that the array is changed at reference
count 1 (the linearity rules of the `lean-rc-linearity` skill).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## The memo -/

/-- `n` zero bytes, by doubling. -/
def zeros (n : Nat) : ByteArray :=
  if n = 0 then .empty
  else
    let h := zeros (n / 2)
    let b := h ++ h
    if n % 2 = 1 then b.push 0 else b
termination_by n
decreasing_by omega

/-- The kinds an object is read as, as mark bits. -/
def kName : UInt8 := 1
def kLevel : UInt8 := 2
def kExpr : UInt8 := 4
def kLevels : UInt8 := 8

/-! The marks: per slot `s`, bit `k` of byte `s` says the object at
location `8 s` is read as kind `k`.  The marking pass threads the mark
bytes alone; the building pass reads them and threads the values. -/

/-- The mark byte of slot `s`.  Not inlined: a read of the marks that
the compiler sank past the next update would hold the array at
reference count 2 and make that update copy it. -/
@[noinline] def marksAt (m : @& ByteArray) (s : Nat) : UInt8 := rdU8 m s

/-- Is the object at slot `s` read as kind `k`? -/
@[inline] def marked (m : @& ByteArray) (k : UInt8) (s : Nat) : Bool := marksAt m s &&& k != 0

/-- Mark the object at slot `s` as kind `k`. -/
@[inline] def mark (m : ByteArray) (k : UInt8) (s : Nat) : ByteArray :=
  let x := marksAt m s
  m.set! s (x ||| k)

/-- The decoder's values, per slot, one array per kind. -/
structure DS where
  names : Array Name
  levels : Array Level
  exprs : Array Expr
  lists : Array (List Level)

/-- Fresh values for `n` slots.  The expressions' filler is `.bvar n`,
built here: a closed term would be a shared constant of the runtime,
marked multi-threaded, and freeing the array would pay an atomic
decrement per slot. -/
def DS.fresh (n : Nat) : DS :=
  ⟨Array.replicate n .anonymous, Array.replicate n .zero, Array.replicate n (.bvar n),
   Array.replicate n []⟩

@[inline] def DS.setName (st : DS) (s : Nat) (v : Name) : DS :=
  let { names, levels, exprs, lists } := st
  { names := names.set! s v, levels, exprs, lists }

@[inline] def DS.setLevel (st : DS) (s : Nat) (v : Level) : DS :=
  let { names, levels, exprs, lists } := st
  { names, levels := levels.set! s v, exprs, lists }

@[inline] def DS.setExpr (st : DS) (s : Nat) (v : Expr) : DS :=
  let { names, levels, exprs, lists } := st
  { names, levels, exprs := exprs.set! s v, lists }

@[inline] def DS.setLevels (st : DS) (s : Nat) (v : List Level) : DS :=
  let { names, levels, exprs, lists } := st
  { names, levels, exprs, lists := lists.set! s v }

/-- The memoized values of the object at location `c`. -/
@[inline] def DS.nameV (st : @& DS) (c : Nat) : Name := st.names.getD (c / 8) .anonymous
@[inline] def DS.levelV (st : @& DS) (c : Nat) : Level := st.levels.getD (c / 8) .zero
@[inline] def DS.exprV (st : @& DS) (c : Nat) : Expr := st.exprs.getD (c / 8) (.bvar 0)
@[inline] def DS.levelsV (st : @& DS) (c : Nat) : List Level := st.lists.getD (c / 8) []

/-! ## Pass 1: marking

The marking fails where the specification fails to read.  The failure
is recorded in the marks themselves, bit 7 of slot 0's byte (no object
starts at location 0, `Region.loc`), so that no step of the pass
returns an `Option`: an `Option` per step is an allocation per pointer. -/

/-- Record a failure. -/
@[inline] def failM (m : ByteArray) : ByteArray := m.set! 0 0x80

/-- Has the marking failed? -/
@[inline] def failedM (m : @& ByteArray) : Bool := marksAt m 0 &&& 0x80 != 0

/-- Mark the object a pointer field of the object at `g` leads to, as
kind `k`; `nil` says the kind's nullary constructor is the scalar `0`
(`Name.anonymous`, `Level.zero`, `[]`). -/
@[inline] def markPtr (r : @& Region) (m : ByteArray) (g : Nat) (k : UInt8) (nil : Bool)
    (v : UInt64) : ByteArray :=
  if nil && v == 1 then m
  else match r.down g v with
    | some c => mark m k (c / 8)
    | none => failM m

/-- The fields of a `Name` object (`nameNode`). -/
@[inline] def markName (r : @& Region) (g : Nat) (m : ByteArray) : ByteArray :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 1, 2 => markPtr r m g kName true (r.fld g 0)
    | 2, 2 => markPtr r m g kName true (r.fld g 0)
    | _, _ => failM m
  else failM m

/-- The fields of a `Level` object (`levelNode`). -/
@[inline] def markLevel (r : @& Region) (g : Nat) (m : ByteArray) : ByteArray :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 0, 0 => m
    | 1, 1 => markPtr r m g kLevel true (r.fld g 0)
    | 2, 2 => markPtr r (markPtr r m g kLevel true (r.fld g 0)) g kLevel true (r.fld g 1)
    | 3, 2 => markPtr r (markPtr r m g kLevel true (r.fld g 0)) g kLevel true (r.fld g 1)
    | 4, 1 => markPtr r m g kName true (r.fld g 0)
    | _, _ => failM m
  else failM m

/-- The fields of a `List Level` cell (`levelsNode`). -/
@[inline] def markLevels (r : @& Region) (g : Nat) (m : ByteArray) : ByteArray :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 1, 2 => markPtr r (markPtr r m g kLevel true (r.fld g 0)) g kLevels true (r.fld g 1)
    | _, _ => failM m
  else failM m

/-- The fields of an `Expr` object (`exprNode`); the fields holding a
`Nat` or a `Literal` are read by the build alone. -/
@[inline] def markExpr (r : @& Region) (g : Nat) (m : ByteArray) : ByteArray :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 0, 1 => m
    | 3, 1 => markPtr r m g kLevel true (r.fld g 0)
    | 4, 2 => markPtr r (markPtr r m g kName true (r.fld g 0)) g kLevels true (r.fld g 1)
    | 5, 2 => markPtr r (markPtr r m g kExpr false (r.fld g 0)) g kExpr false (r.fld g 1)
    | 6, 3 => markPtr r (markPtr r m g kExpr false (r.fld g 1)) g kExpr false (r.fld g 2)
    | 7, 3 => markPtr r (markPtr r m g kExpr false (r.fld g 1)) g kExpr false (r.fld g 2)
    | 8, 4 => markPtr r (markPtr r (markPtr r m g kExpr false (r.fld g 1)) g kExpr false
        (r.fld g 2)) g kExpr false (r.fld g 3)
    | 9, 1 => m
    | 10, 2 => markPtr r m g kExpr false (r.fld g 1)
    | 11, 3 => markPtr r (markPtr r m g kName true (r.fld g 0)) g kExpr false (r.fld g 2)
    | _, _ => failM m
  else failM m

/-- Slot `p`'s fields, if it is marked as kind `k`. -/
@[inline] def markKind (r : @& Region) (k : UInt8)
    (markK : Region → Nat → ByteArray → ByteArray) (p : Nat) (m : ByteArray) : ByteArray :=
  if marked m k p then markK r (8 * p) m else m

/-- One slot of the downward sweep: its marked kinds' fields. -/
@[inline] def markSlot (r : @& Region) (p : Nat) (m : ByteArray) : ByteArray :=
  markKind r kExpr markExpr p (markKind r kLevels markLevels p
    (markKind r kLevel markLevel p (markKind r kName markName p m)))

/-- **The downward sweep** over the slots below `p`; it stops at the
first failure. -/
def markPass (r : @& Region) (m : ByteArray) : Nat → ByteArray
  | 0 => m
  | p + 1 =>
    if marksAt m p != 0 then
      let m := markSlot r p m
      if failedM m then m else markPass r m p
    else markPass r m p

/-! ## Pass 2: building -/

@[inline] def buildName (r : @& Region) (g : Nat) (st : @& DS) : Option Name :=
  nameNode r g fun c _ => some (st.nameV c)

@[inline] def buildLevel (r : @& Region) (g : Nat) (st : @& DS) : Option Level :=
  levelNode r g (fun c _ => some (st.levelV c)) (fun c _ => some (st.nameV c))

@[inline] def buildLevels (r : @& Region) (g : Nat) (st : @& DS) : Option (List Level) :=
  levelsNode r g (fun c _ => some (st.levelsV c)) (fun c _ => some (st.levelV c))

@[inline] def buildExpr (r : @& Region) (g : Nat) (st : @& DS) : Option Expr :=
  exprNode r g (fun c _ => some (st.exprV c)) (fun c _ => some (st.nameV c))
    (fun c _ => some (st.levelV c)) (fun c _ => some (st.levelsV c))

/-- Slot `p`'s value as kind `k`, if it is marked so, and whether it
read. -/
@[inline] def buildKind {α : Type} (r : @& Region) (m : @& ByteArray) (k : UInt8)
    (build : Region → Nat → DS → Option α) (set : DS → Nat → α → DS) (p : Nat) (st : DS) :
    DS × Bool :=
  if marked m k p then
    match build r (8 * p) st with
    | some v => (set st p v, true)
    | none => (st, false)
  else (st, true)

/-- **The upward sweep** over the slots from `p` to `n`: each slot's
marked kinds' values. -/
def buildPass (r : @& Region) (m : @& ByteArray) (n : Nat) (st : DS) (p : Nat) : Option DS :=
  if p < n then
    if marksAt m p != 0 then
      let (st, ok1) := buildKind r m kName buildName DS.setName p st
      let (st, ok2) := buildKind r m kLevel buildLevel DS.setLevel p st
      let (st, ok3) := buildKind r m kLevels buildLevels DS.setLevels p st
      let (st, ok4) := buildKind r m kExpr buildExpr DS.setExpr p st
      if ok1 && ok2 && ok3 && ok4 then buildPass r m n st (p + 1) else none
    else buildPass r m n st (p + 1)
  else some st
termination_by n - p

/-! ## The roots -/

/-- Mark a root: a name (`nil`) or an expression the skeletons hold. -/
@[inline] def markRoot (r : @& Region) (k : UInt8) (nil : Bool) (m : ByteArray) (v : UInt64) :
    Option ByteArray :=
  if nil && v == 1 then some m
  else match r.loc v with
    | some c => some (mark m k (c / 8))
    | none => none

/-- The highest location of a root. -/
@[inline] def maxLoc (r : @& Region) (vs : List UInt64) (m : Nat) : Nat :=
  vs.foldl (fun m v => max m (r.locGo v r.segs.size)) m

/-- **Both passes** from the given name and expression roots.  Every
object they reach lies at or below the highest root, so the memo ends
there. -/
def runPasses (r : @& Region) (names exprs : List UInt64) : Option DS := do
  let n := maxLoc r exprs (maxLoc r names 0) / 8 + 1
  let m ← names.foldlM (markRoot r kName true) (zeros n)
  let m ← exprs.foldlM (markRoot r kExpr false) m
  let m := markPass r m n
  if failedM m then none else buildPass r m n (DS.fresh n) 0

/-- A root's value, from the memo. -/
@[inline] def DS.nameOf (r : @& Region) (st : @& DS) (v : UInt64) : Option Name :=
  if v == 1 then some .anonymous
  else match r.loc v with
    | some c => some (st.nameV c)
    | none => none

@[inline] def DS.exprOf (r : @& Region) (st : @& DS) (v : UInt64) : Option Expr :=
  match r.loc v with
  | some c => some (st.exprV c)
  | none => none

/-- The names a constant's skeleton holds. -/
def CEntryF.names {N E : Type} (c : CEntryF N E) : List N :=
  c.name :: c.levelParams ++
  match c.kind with
  | .thm _ all => all
  | .induct _ _ all cs .. => all ++ cs
  | .ctor ind .. => [ind]
  | .recur all _ _ _ _ rules .. => all ++ rules.map (·.1)
  | _ => []

/-- The expressions a constant's skeleton holds. -/
def CEntryF.exprs {N E : Type} (c : CEntryF N E) : List E :=
  c.type ::
  match c.kind with
  | .defn v .. | .thm v _ | .opaq v _ => [v]
  | .recur _ _ _ _ _ rules .. => rules.map (·.2.2)
  | _ => []

/-- **THE FAST DECODER**: `decodeModuleSpec`, reading each object once. -/
def decodeModuleFast (r : Region) (root : UInt64) (consts : Bool) : Option ModDecoded := do
  let sk ← moduleSkel r root
  let skels ← if consts then sk.consts.mapM (constSkel r) else pure []
  let st ← runPasses r (sk.imports ++ skels.flatMap CEntryF.names) (skels.flatMap CEntryF.exprs)
  let imports ← sk.imports.mapM (st.nameOf r)
  let constants ← skels.mapM (CEntryF.mapM (st.nameOf r) (st.exprOf r))
  pure ⟨sk.isModule, imports.toArray, constants.toArray⟩

end ConLeche.Frontend.Olean
