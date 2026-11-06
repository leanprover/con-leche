module

public import ConLeche.Cached.ParsedC

@[expose] public section

/-!
# The index of a stream, and a record's job

The stream's index is built once, after the parse and before any check, from the records alone
(`declConstants`, `declTables`): every constant with its counter, its position among all the
constants of the stream, and every table with its record's position.  It is never written again.

The name's FIRST entry wins.  A record whose name an earlier record took sees that entry at its own
view, so its check fails with "duplicate declaration", in fold order.

A record's **job** is its check at the view of its position (`StreamIndex.view`): the index with
everything from that record on hidden.  The jobs read the frozen index and their own record, so they
run independently of one another; that all of them passing is an accept of the fold is
`checkDecls_of_jobs` (`ConLeche/Verify/Cached/StreamIndex.lean`).  A check is over exactly the
declarations before its record in fold order: `Frontend/NatOpGround.lean`'s reordering is what puts
a certificate's ground there.

**What a job may observe of an earlier record that has not passed yet.**  Nothing the theorem reads:
a later job sees an earlier constant before that constant's job has run (a pinned operation before
its certificate, a definition before its value's check), and may read it.  The accepted run needs
every job, so a later job's verdict matters only if every earlier one passed, and then the
environment it ran at is the fold's.  A wrong constant can therefore change nothing but which failure
is computed last, and the walk in fold order (`ConLeche.Driver.collect`) reports the earliest.  A
later job that does not terminate over a wrong constant keeps the run from finishing: no verdict,
never an accept.
-/

namespace ConLeche.Cached

open ConLeche

/-- The index under construction, and finished: the frozen layer (its bounds unused here), each
record's first counter, and the next counter. -/
structure StreamIndex where
  base : FBase := {}
  firsts : Array Nat := #[]
  next : Nat := 0

/-- Insert a record's constants from counter `c` on, a name's first entry winning. -/
def insertConsts (idx : Std.HashMap Name (Nat × ConstantInfo)) (c : Nat) :
    List ConstantInfo → Std.HashMap Name (Nat × ConstantInfo) × Nat
  | [] => (idx, c)
  | ci :: L => insertConsts (idx.insertIfNew ci.name (c, ci)) (c + 1) L

/-- Insert a record's tables, a name's first entry winning. -/
def insertTables (tbls : Std.HashMap Name (Nat × ProjTable)) (r : Nat) :
    List ProjTable → Std.HashMap Name (Nat × ProjTable)
  | [] => tbls
  | t :: Q => insertTables (tbls.insertIfNew t.structName (r, t)) r Q

/-- One record into the index. -/
def StreamIndex.add (I : StreamIndex) (pd : Declaration) : StreamIndex :=
  let (idx, next) := insertConsts I.base.idx I.next (declConstants pd)
  { base := { I.base with idx, tbls := insertTables I.base.tbls I.firsts.size (declTables pd) }
    firsts := I.firsts.push I.next
    next }

/-- **The index of a stream.** -/
def buildIndex (ds : Array Declaration) : StreamIndex :=
  ds.foldl StreamIndex.add {}

/-- **The view of record `k`**: no constants or tables of its own, the index visible below the
record's first counter and its position. -/
def StreamIndex.view (I : StreamIndex) (k : Nat) : FEnv :=
  let c := I.firsts.getD k I.next
  ⟨⟨[], []⟩, {}, { I.base with below := c, belowRec := k }, [], {}⟩

/-- **Record `pd`'s job, at position `k`**: what the fold's step asks of it, at its view. -/
def recordJob (mode : CheckMode) (pins : List NatOpPinSet) (I : StreamIndex) (k : Nat)
    (pd : Declaration) : Except CheckError Unit :=
  if andPinOk pd then
    match checkDeclStepC mode pins (I.view k) pd {} with
    | .ok _ => .ok ()
    | .error e => .error e
  else .error (.invalid "`And` must be the standard `And`")

end ConLeche.Cached
