module

public import ConLeche.Frontend.Olean.View
public import Std.Data.HashSet.Basic

@[expose] public section

/-!
# Reading `.olean` files: a module's load, its theorems' values left in the file

Most of what a module stores is the values of its theorems (on Mathlib's
closure, 93 of 138 million expression objects are reached from nothing else), and
a theorem's value is read by one thing only: the check of that theorem.  The
merge compares statements, the emission needs to know which constants the value
mentions, and the install stores a theorem by its statement.  So the load
(`loadAt`) reads everything of a module except those values, and each value stays
in the file until its check reads it (task #481):

* **a theorem's value is a reference** (`valueRef`) to where it is stored, in the
  records and in the install's record of the check; the rest of the pipeline never
  looks at it;
* **what a constant mentions is read off the file** (`usesOf`), without building
  anything: that is all the emission's order needs of a value;
* **the frontier** (`frontierOf`) is what the load keeps of its memo: the objects it
  read that a value reaches directly.  A later read of a value takes those from it
  (`frontierExpr`, `ConLeche/Frontend/Olean/Sparse.lean`), so the value shares them
  with the environment, and everything below them too, without keeping the
  memo: on Mathlib's closure 6 million entries, of 48 million objects read.

The walks are `partial`: nothing is proved about them, and nothing needs to be.
What a constant mentions decides the records' order, which the checker then checks;
what the frontier holds is a matter of speed, because `frontierOf` takes only values
the passes read (`ConLeche/Verify/Frontend/Olean/Lazy.lean`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## The constants a constant mentions -/

/-- A name from its components. -/
def mkN (cs : List String) : Name := cs.foldl .str .anonymous

/-- A numeral's mark in `usesGo`'s output (no name field is `0`: `0` is no
pointer, and the scalar `Name.anonymous` is `1`). -/
def usesNat : UInt64 := 0
/-- A string's mark in `usesGo`'s output. -/
def usesStr : UInt64 := 2

/-- The kids of an expression object, last first, onto the walk's stack. -/
@[inline] def pushKid (r : @& Region) (g : Nat) (i : Nat) (stack : Option (Array Nat)) :
    Option (Array Nat) :=
  match stack with
  | none => none
  | some st =>
    match r.down g (r.fld g i) with
    | some c => some (st.push c)
    | none => none

/-- **The DAG walk of what an expression mentions**: each object once in a walk (`stamps`,
by slot, holds the walk that saw it last), left to right, every constant's name field
into `out`, as it stands in the file, and `usesNat`/`usesStr` at a literal.
`none` at an object no expression is stored as. -/
partial def usesGo (r : @& Region) (stamps : Array Nat) (stamp : Nat) (stack : Array Nat)
    (out : Array UInt64) : Option (Array Nat × Array UInt64) :=
  if stack.isEmpty then some (stamps, out) else
  let g := stack.back!
  let stack := stack.pop
  let s := g / 8
  if stamps[s]! == stamp then usesGo r stamps stamp stack out else
  let stamps := stamps.set! s stamp
  if !r.fits g then none else
  match r.tag g, r.nobjs g with
  | 0, 1 | 3, 1 => usesGo r stamps stamp stack out
  | 4, 2 => usesGo r stamps stamp stack (out.push (r.fld g 0))
  | 5, 2 =>
    match pushKid r g 0 (pushKid r g 1 (some stack)) with
    | some st => usesGo r stamps stamp st out
    | none => none
  | 6, 3 | 7, 3 =>
    match pushKid r g 1 (pushKid r g 2 (some stack)) with
    | some st => usesGo r stamps stamp st out
    | none => none
  | 8, 4 =>
    match pushKid r g 1 (pushKid r g 2 (pushKid r g 3 (some stack))) with
    | some st => usesGo r stamps stamp st out
    | none => none
  | 9, 1 =>
    match r.down g (r.fld g 0) with
    | some c =>
      if r.isCtor c 0 1 then usesGo r stamps stamp stack (out.push usesNat)
      else if r.isCtor c 1 1 then usesGo r stamps stamp stack (out.push usesStr)
      else none
    | none => none
  | 10, 2 =>
    match pushKid r g 1 (some stack) with
    | some st => usesGo r stamps stamp st out
    | none => none
  | 11, 3 =>
    match pushKid r g 2 (some stack) with
    | some st => usesGo r stamps stamp st out
    | none => none
  | _, _ => none

/-- One constant's expressions, in order, one walk. -/
def usesRoots (r : @& Region) (stamps : Array Nat) (stamp : Nat) (out : Array UInt64) :
    List UInt64 → Option (Array Nat × Array UInt64)
  | [] => some (stamps, out)
  | v :: vs =>
    match r.loc v with
    | none => none
    | some g =>
      match usesGo r stamps stamp #[g] out with
      | none => none
      | some (stamps, out) => usesRoots r stamps stamp out vs

/-- **What each constant mentions**, as `usesGo` writes it: its statement and its values
(`CEntryF.exprs`), a walk of its own per constant. -/
def usesOf (r : @& Region) (stamps : Array Nat) (stamp : Nat) :
    List (CEntryF UInt64 UInt64) → Array (Array UInt64) → Option (Array (Array UInt64))
  | [], outs => some outs
  | c :: cs, outs =>
    match usesRoots r stamps stamp #[] c.exprs with
    | none => none
    | some (stamps, out) => usesOf r stamps (stamp + 1) cs (outs.push out)

/-- The names in `usesGo`'s outputs: roots of the load, so that the walk's output can
be read off its memo. -/
def usesNames (outs : Array (Array UInt64)) : List UInt64 :=
  (outs.foldl (fun acc out => out.foldl (fun acc v =>
    if v == usesNat || v == usesStr then acc else acc.push v) acc) #[]).toList

/-- A name once, in first-visit order. -/
@[inline] def addUse (x : Std.HashSet Name × Array Name) (n : Name) :
    Std.HashSet Name × Array Name :=
  if x.1.contains n then x else (x.1.insert n, x.2.push n)

/-- **What a constant mentions, as names**: in first-visit order, each once, and
the literal dependencies lean4export adds (`dumpNatDeps`, `dumpStrDeps`): `Nat` for a
numeral, `Char.ofNat` and `String.ofList` for a string.  Where a name does not read, the
walk's output has no such name, and it is left out: this is about the records' order
alone. -/
def usesRead (nm : UInt64 → Option Name) (out : Array UInt64) : Array Name :=
  (out.foldl (fun x v =>
    if v == usesNat then addUse x (mkN ["Nat"])
    else if v == usesStr then addUse (addUse x (mkN ["Char", "ofNat"])) (mkN ["String", "ofList"])
    else match nm v with
      | some n => addUse x n
      | none => x) ((Std.HashSet.emptyWithCapacity 64 : Std.HashSet Name), #[])).2

/-! ## A stored constant -/

/-- **One stored constant**, as the merge and the emitter need it: the constant read
(`lazyEntry`: a theorem's value is its reference) and the constants its type and values
mention, in first-visit order. -/
structure CEntry extends CEntryF Name Expr where
  uses : Array Name := #[]

instance : Inhabited CEntry := ⟨{ toCEntryF := default }⟩

/-- `CKindF.skipped` of a stored constant. -/
def CEntry.skipped (c : CEntry) : Bool := c.kind.skipped

/-- **A loaded module**: its constants at the private level, and the frontier its
theorems' values are read over. -/
structure Loaded where
  name : Name
  constants : Array CEntry
  frontier : Frontier

/-! ## A theorem's value: where it is stored -/

/-- What separates the two parts of a reference. -/
def refBase : Nat := 1 <<< 32

/-- **A theorem's value, until its check reads it**: the value at location `g` of module `i`
of the closure's order.  An expression, so that the records' and the check's types are
the stream path's. -/
def valueRef (i g : Nat) : Expr := .bvar (g * refBase + i)

/-- The module a reference's code names. -/
def refModule (code : Nat) : Nat := code % refBase

/-- The location a reference's code names. -/
def refLoc (code : Nat) : Nat := code / refBase

/-- The expressions the load reads of a constant: all but a theorem's value. -/
def lazyRoots (c : CEntryF UInt64 UInt64) : List UInt64 :=
  match c.kind with
  | .thm .. => [c.type]
  | _ => c.exprs

/-- **A constant read, a theorem's value as its reference.** -/
def lazyEntry (nm : UInt64 → Option Name) (ex : UInt64 → Option Expr) (r : Region) (i : Nat)
    (s : CEntryF UInt64 UInt64) : Option (CEntryF Name Expr) :=
  match s.kind with
  | .thm v all => do
    unless i < refBase do none
    let g ← r.loc v
    let name ← nm s.name
    let lps ← s.levelParams.mapM nm
    let type ← ex s.type
    let all ← all.mapM nm
    pure ⟨name, lps, type, .thm (valueRef i g) all⟩
  | _ => s.mapM nm ex

/-- `lazyEntry` of every constant, each with what it mentions (`outs`, by position). -/
def lazyEntries (nm : UInt64 → Option Name) (ex : UInt64 → Option Expr) (r : Region) (i : Nat)
    (outs : Array (Array UInt64)) (k : Nat) : List (CEntryF UInt64 UInt64) → Option (List CEntry)
  | [] => some []
  | s :: ss =>
    match lazyEntry nm ex r i s with
    | none => none
    | some e =>
      match lazyEntries nm ex r i outs (k + 1) ss with
      | none => none
      | some es => some ({ toCEntryF := e, uses := usesRead nm (outs.getD k #[]) } :: es)

/-! ## The frontier -/

/-- A kind as a stack entry's low bits. -/
@[inline] def kindCode (k : UInt8) : Nat :=
  if k = kName then 0 else if k = kLevel then 1 else if k = kLevels then 2 else 3

/-- The kind of a stack entry's low bits. -/
@[inline] def kindOfCode (c : Nat) : UInt8 :=
  if c = 0 then kName else if c = 1 then kLevel else if c = 2 then kLevels else kExpr

/-- **The objects the load read that the values reach directly**: a walk from the values
over what the load did not read (each object once, `seen`), stopping at what it did
(`env`), which goes into `fr`.  Entries are a location and a kind's code. -/
partial def frontierWalk (r : @& Region) (env : @& ByteArray) (seen fr : ByteArray)
    (stack : Array Nat) : ByteArray :=
  if stack.isEmpty then fr else
  let e := stack.back!
  let stack := stack.pop
  let g := e / 8 * 8
  let k := kindOfCode (e % 8)
  let s := g / 8
  if marked env k s then frontierWalk r env seen (mark fr k s) stack
  else if marked seen k s then frontierWalk r env seen fr stack
  else
    let seen := mark seen k s
    match kidTable k (r.tag g) (r.nobjs g) with
    | none => frontierWalk r env seen fr stack
    | some fs =>
      let stack := fs.foldl (fun st (f : Nat × UInt8 × Bool) =>
        if f.2.2 && r.fld g f.1 == 1 then st
        else match r.down g (r.fld g f.1) with
          | some c => st.push (c + kindCode f.2.1)
          | none => st) stack
      frontierWalk r env seen fr stack

/-- A table with one more entry, at the end. -/
@[inline] def Table.add {α : Type} (t : Table α) (c : Nat) (v : α) : Table α :=
  let { keys, vals } := t
  { keys := keys.push c, vals := vals.push v }

/-- Slot `p` of `fr`, where the marks `m` hold it too, into the frontier. -/
@[inline] def frontierStep (m fr : @& ByteArray) (st : @& DS) (p : Nat) (b : Frontier) : Frontier :=
  if marksAt fr p == 0 then b else
  let c := 8 * p
  let { names, levels, lists, exprs } := b
  let names := if marked fr kName p && marked m kName p then names.add c (st.nameV c) else names
  let levels := if marked fr kLevel p && marked m kLevel p then levels.add c (st.levelV c) else levels
  let lists := if marked fr kLevels p && marked m kLevels p then lists.add c (st.levelsV c) else lists
  let exprs := if marked fr kExpr p && marked m kExpr p then exprs.add c (st.exprV c) else exprs
  { names, levels, lists, exprs }

/-- **The frontier**: the slots from `p` to `n` of `fr` that the marks `m` hold, with
their values in the passes' memo.  Ascending, so each table's keys are. -/
def frontierOf (m fr : @& ByteArray) (st : @& DS) (n p : Nat) (b : Frontier) : Frontier :=
  if p < n then frontierOf m fr st n (p + 1) (frontierStep m fr st p b) else b
termination_by n - p

/-! ## A module's load -/

/-- **The load of a module's private view**, everything but its theorems' values.
`none` where the part of the view it reads does not read: `viewError` says why. -/
def loadAt (i : Nat) (m : Name) (f : ModFiles) : Option Loaded := do
  let (r, a) ← f.viewRegion .private
  unless constNamesOk r a do none
  let sk ← moduleSkel r a
  let skels ← sk.consts.mapM (constSkel r)
  let namesB := sk.imports.map (·.module) ++ skels.flatMap CEntryF.names
  let n := maxLoc r (skels.flatMap CEntryF.exprs) (maxLoc r namesB 0) / 8 + 1
  let outs ← usesOf r (Array.replicate n 0) 1 skels (Array.mkEmpty skels.length)
  let (nm, ms, st) ← runMarked r (namesB ++ usesNames outs) (skels.flatMap lazyRoots)
  let imports ← sk.imports.mapM (ImportF.mapM (st.nameOf r))
  unless importsPre f.exported.bytes == some imports.toArray do none
  let cs ← lazyEntries (st.nameOf r) (st.exprOf r) r i outs 0 skels
  let values := skels.filterMap fun c => match c.kind with
    | .thm v _ => (r.loc v).map (· + kindCode kExpr)
    | _ => none
  let fr := frontierWalk r ms (zeros n) (zeros n) values.toArray
  pure { name := m, constants := cs.toArray, frontier := frontierOf ms fr st nm 0 {} }

/-- **The load, with the reason where it does not read.** -/
def loadView (i : Nat) (m : Name) (f : ModFiles) : Except CheckError Loaded :=
  match loadAt i m f with
  | some l => .ok l
  | none => .error (viewError m f .private)

end ConLeche.Frontend.Olean
