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

**The memo** (`DS`) is dense, by slot (a location divided by 8): one
array per kind, as long as the region in words, and four mark bytes per
slot.  Each update takes the array it changes OUT of the record first
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

/-- The decoder's memo: per slot `s`, bit `k` of mark byte `s` says the
object at location `8 s` is read as kind `k`; the arrays hold the
values. -/
structure DS where
  marks : ByteArray
  names : Array Name
  levels : Array Level
  exprs : Array Expr
  lists : Array (List Level)

/-- A fresh memo for `n` slots.  The expressions' filler is `.bvar n`,
built here: a closed term would be a shared constant of the runtime,
marked multi-threaded, and freeing the array would pay an atomic
decrement per slot. -/
def DS.fresh (n : Nat) : DS :=
  ⟨zeros n, Array.replicate n .anonymous, Array.replicate n .zero,
   Array.replicate n (.bvar n), Array.replicate n []⟩

/-- The mark byte of slot `s`.  Not inlined: a read of `marks` that the
compiler sank past the next update would hold the array at reference
count 2 and make that update copy it. -/
@[noinline] def DS.marksAt (st : @& DS) (s : Nat) : UInt8 := rdU8 st.marks s

/-- Is the object at slot `s` read as kind `k`? -/
@[inline] def DS.marked (st : @& DS) (k : UInt8) (s : Nat) : Bool := st.marksAt s &&& k != 0

@[inline] def DS.mark (st : DS) (k : UInt8) (s : Nat) : DS :=
  let m := st.marksAt s
  let { marks, names, levels, exprs, lists } := st
  { marks := marks.set! s (m ||| k), names, levels, exprs, lists }

@[inline] def DS.setName (st : DS) (s : Nat) (v : Name) : DS :=
  let { marks, names, levels, exprs, lists } := st
  { marks, names := names.set! s v, levels, exprs, lists }

@[inline] def DS.setLevel (st : DS) (s : Nat) (v : Level) : DS :=
  let { marks, names, levels, exprs, lists } := st
  { marks, names, levels := levels.set! s v, exprs, lists }

@[inline] def DS.setExpr (st : DS) (s : Nat) (v : Expr) : DS :=
  let { marks, names, levels, exprs, lists } := st
  { marks, names, levels, exprs := exprs.set! s v, lists }

@[inline] def DS.setLevels (st : DS) (s : Nat) (v : List Level) : DS :=
  let { marks, names, levels, exprs, lists } := st
  { marks, names, levels, exprs, lists := lists.set! s v }

/-- The memoized values of the object at location `c`. -/
@[inline] def DS.nameV (st : @& DS) (c : Nat) : Name := st.names.getD (c / 8) .anonymous
@[inline] def DS.levelV (st : @& DS) (c : Nat) : Level := st.levels.getD (c / 8) .zero
@[inline] def DS.exprV (st : @& DS) (c : Nat) : Expr := st.exprs.getD (c / 8) (.bvar 0)
@[inline] def DS.levelsV (st : @& DS) (c : Nat) : List Level := st.lists.getD (c / 8) []

/-! ## Pass 1: marking -/

/-- Mark the object a pointer field of the object at `g` leads to, as
kind `k`; `nil` says the kind's nullary constructor is the scalar `0`
(`Name.anonymous`, `Level.zero`, `[]`). -/
@[inline] def DS.markPtr (r : @& Region) (g : Nat) (k : UInt8) (nil : Bool) (v : UInt64)
    (st : DS) : Option DS :=
  if nil && v == 1 then some st
  else match r.down g v with
    | some c => some (st.mark k (c / 8))
    | none => none

/-- The fields of a `Name` object (`nameNode`). -/
@[inline] def markName (r : @& Region) (g : Nat) (st : DS) : Option DS :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 1, 2 => st.markPtr r g kName true (r.fld g 0)
    | 2, 2 => st.markPtr r g kName true (r.fld g 0)
    | _, _ => none
  else none

/-- The fields of a `Level` object (`levelNode`). -/
@[inline] def markLevel (r : @& Region) (g : Nat) (st : DS) : Option DS :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 0, 0 => some st
    | 1, 1 => st.markPtr r g kLevel true (r.fld g 0)
    | 2, 2 => (st.markPtr r g kLevel true (r.fld g 0)).bind (·.markPtr r g kLevel true (r.fld g 1))
    | 3, 2 => (st.markPtr r g kLevel true (r.fld g 0)).bind (·.markPtr r g kLevel true (r.fld g 1))
    | 4, 1 => st.markPtr r g kName true (r.fld g 0)
    | _, _ => none
  else none

/-- The fields of a `List Level` cell (`levelsNode`). -/
@[inline] def markLevels (r : @& Region) (g : Nat) (st : DS) : Option DS :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 1, 2 => (st.markPtr r g kLevel true (r.fld g 0)).bind (·.markPtr r g kLevels true (r.fld g 1))
    | _, _ => none
  else none

/-- The fields of an `Expr` object (`exprNode`); the fields holding a
`Nat` or a `Literal` are read by the build alone. -/
@[inline] def markExpr (r : @& Region) (g : Nat) (st : DS) : Option DS :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 0, 1 => some st
    | 3, 1 => st.markPtr r g kLevel true (r.fld g 0)
    | 4, 2 => (st.markPtr r g kName true (r.fld g 0)).bind (·.markPtr r g kLevels true (r.fld g 1))
    | 5, 2 => (st.markPtr r g kExpr false (r.fld g 0)).bind (·.markPtr r g kExpr false (r.fld g 1))
    | 6, 3 => (st.markPtr r g kExpr false (r.fld g 1)).bind (·.markPtr r g kExpr false (r.fld g 2))
    | 7, 3 => (st.markPtr r g kExpr false (r.fld g 1)).bind (·.markPtr r g kExpr false (r.fld g 2))
    | 8, 4 => ((st.markPtr r g kExpr false (r.fld g 1)).bind
        (·.markPtr r g kExpr false (r.fld g 2))).bind (·.markPtr r g kExpr false (r.fld g 3))
    | 9, 1 => some st
    | 10, 2 => st.markPtr r g kExpr false (r.fld g 1)
    | 11, 3 => (st.markPtr r g kName true (r.fld g 0)).bind (·.markPtr r g kExpr false (r.fld g 2))
    | _, _ => none
  else none

/-- One slot of the downward sweep: its marked kinds' fields. -/
@[inline] def markSlot (r : @& Region) (p : Nat) (st : DS) : Option DS := do
  let g := 8 * p
  let st ← if st.marked kName p then markName r g st else some st
  let st ← if st.marked kLevel p then markLevel r g st else some st
  let st ← if st.marked kLevels p then markLevels r g st else some st
  if st.marked kExpr p then markExpr r g st else some st

/-- **The downward sweep** over the slots below `p`. -/
def markPass (r : @& Region) (st : DS) : Nat → Option DS
  | 0 => some st
  | p + 1 =>
    if st.marksAt p != 0 then
      match markSlot r p st with
      | some st => markPass r st p
      | none => none
    else markPass r st p

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

/-- One slot of the upward sweep: its marked kinds' values. -/
@[inline] def buildSlot (r : @& Region) (p : Nat) (st : DS) : Option DS := do
  let g := 8 * p
  let st ← if st.marked kName p then
      match buildName r g st with
      | some v => some (st.setName p v)
      | none => none
    else some st
  let st ← if st.marked kLevel p then
      match buildLevel r g st with
      | some v => some (st.setLevel p v)
      | none => none
    else some st
  let st ← if st.marked kLevels p then
      match buildLevels r g st with
      | some v => some (st.setLevels p v)
      | none => none
    else some st
  if st.marked kExpr p then
    match buildExpr r g st with
    | some v => some (st.setExpr p v)
    | none => none
  else some st

/-- **The upward sweep** over the slots from `p` to `n`. -/
def buildPass (r : @& Region) (n : Nat) (st : DS) (p : Nat) : Option DS :=
  if p < n then
    if st.marksAt p != 0 then
      match buildSlot r p st with
      | some st => buildPass r n st (p + 1)
      | none => none
    else buildPass r n st (p + 1)
  else some st
termination_by n - p

/-! ## The roots -/

/-- Mark a root: a name (`nil`) or an expression the skeletons hold. -/
@[inline] def DS.markRoot (r : @& Region) (k : UInt8) (nil : Bool) (st : DS) (v : UInt64) :
    Option DS :=
  if nil && v == 1 then some st
  else match r.loc v with
    | some c => some (st.mark k (c / 8))
    | none => none

/-- The highest location of a root. -/
@[inline] def maxLoc (r : @& Region) (vs : List UInt64) (m : Nat) : Nat :=
  vs.foldl (fun m v => max m (r.locGo v r.segs.size)) m

/-- **Both passes** from the given name and expression roots.  Every
object they reach lies at or below the highest root, so the memo ends
there. -/
def runPasses (r : @& Region) (names exprs : List UInt64) : Option DS := do
  let n := maxLoc r exprs (maxLoc r names 0) / 8 + 1
  let st ← names.foldlM (DS.markRoot r kName true) (DS.fresh n)
  let st ← exprs.foldlM (DS.markRoot r kExpr false) st
  let st ← markPass r st n
  buildPass r n st 0

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
