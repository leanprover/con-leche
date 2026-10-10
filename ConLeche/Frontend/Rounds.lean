module

public import ConLeche.Frontend.Stream

@[expose] public section

/-!
# The rounds parse: counters and finished tables (task #329)

The serial parse (`ConLeche/Frontend/Stream.lean`) applies a stream's
lines in order, on one thread.  The rounds parse applies the chunks of
a WINDOW in parallel, in rounds (`ConLeche/Frontend/RoundsWork.lean`
computes them; `ConLeche/Driver/OwnerParse.lean` drives them).  This
module holds what both share with the proofs:

* **Increasing streams.**  An exporter binds each table's indices in
  increasing order (lean4export: each the next one; another exporter
  may leave gaps).  On such a stream a line's lookups read below the
  counters of the lines before it — one more than the last index each
  table bound (`Ctr`) — and nothing is ever bound twice.
* **The finished tables** (`Pages`, `Prior`): the tables of every
  window before, their entries in binding order in pages of 4096, and
  the runs of consecutive indices that say which index has which entry
  (one run on lean4export's output, so a lookup is a comparison and
  two reads).

Why the rounds' result is the serial parse's is
`ConLeche/Verify/Frontend/Rounds.lean`.
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## Counters -/

/-- One more than the last index each table bound: the least index the
next line of that table may bind, and the bound of every lookup.  Name
`0` and level `0` are bound before the stream starts. -/
structure Ctr where
  n : Nat
  l : Nat
  e : Nat
  deriving Inhabited, DecidableEq

/-- The counters after one line. -/
@[inline] def Ctr.step (c : Ctr) : LineRec → Ctr
  | .name i _ => { c with n := i + 1 }
  | .level i _ => { c with l := i + 1 }
  | .expr i _ => { c with e := i + 1 }
  | _ => c

/-- The counters after a list of lines. -/
def Ctr.stepAll (c : Ctr) : List LineRec → Ctr
  | [] => c
  | r :: rs => (c.step r).stepAll rs

/-- **The order test of one line**: a table line binds an index at or
above its table's counter. -/
@[inline] def Ctr.fits (c : Ctr) : LineRec → Bool
  | .name i _ => c.n ≤ i
  | .level i _ => c.l ≤ i
  | .expr i _ => c.e ≤ i
  | _ => true

/-- Counters compared field by field. -/
@[inline] def Ctr.beq (a b : Ctr) : Bool := a.n == b.n && a.l == b.l && a.e == b.e

theorem Ctr.beq_iff {a b : Ctr} : a.beq b = true ↔ a = b := by
  cases a; cases b; simp [Ctr.beq, and_assoc]

/-! ## Tables as partial maps -/

/-- Three tables as partial maps. -/
structure Tabs where
  n : Nat → Option Name
  l : Nat → Option Level
  e : Nat → Option Expr

/-- The lookups of a line at counters `c`: the tables cut there, with
the serial parse's messages. -/
@[inline] def cutLk (T : Tabs) (c : Ctr) : Lk String where
  name j := match (if j < c.n then T.n j else none) with
    | some n => pure n
    | none => throw s!"undefined name index {j}"
  level j := match (if j < c.l then T.l j else none) with
    | some l => pure l
    | none => throw s!"undefined level index {j}"
  expr j := match (if j < c.e then T.e j else none) with
    | some e => pure e
    | none => throw s!"undefined expr index {j}"

/-! ## The finished tables

The tables of the windows before are kept by BINDING ORDER: the `r`-th
entry a table bound (its rank `r`) is slot `r % 4096` of page
`r / 4096`, so every slot holds an entry and the pages are exactly the
entries.  Which index has which rank is a list of RUNS, each a stretch
of consecutive indices bound one after the other.

**Why runs.**  lean4export binds every index of a table in order, with
no gap, so its tables are one run each and an index's rank is the index
itself (one comparison more than an array read).  An exporter that
leaves gaps between indices is handled the same way, with one run per
stretch between gaps and a binary search over the runs; the pages stay
as small as the entries, whatever the gaps.

**If the export format comes to require dense ids.**  lean4export's
output is dense, and a future revision of the export format may require
dense ids.  Then the runs and the gappy handling can go: here `Run`,
`Run.rank`, `runFind`, the field `Pages.runs` and the search in
`Pages.rank` (a rank becomes `j - first`); in
`ConLeche/Frontend/RoundsWork.lean` `pushRun`, `idsRuns`, `keysRuns`,
`winRunsGo`, and `Keys.ids` with `keysFind`, `keysPush` and the ids
branches of `Keys.keyOf`, `Keys.idx`, `r0Look` and `rawLk`; in the
proofs (`ConLeche/Verify/Frontend/Rounds.lean`, `RoundsWork.lean`)
`findRank`, `RunsOK`, `runFind_spec`, `Pages.rank_eq`, `Run.rank_fuse`,
`pushRun_find`, `RunsOK.push`, `idsRuns_spec`, `keysRuns_spec`,
`winClaim`, `winRunsGo_spec`, the run walk of `Pages.toTable`, and
`keysPush_rep`, `keysFind_spec`, `keysFind_eq` with the ids case of
`Keys.Rep`.  The rounds would then require density (a window whose
indices of a table are not exactly `[start, start + count)` falls back
to the serial parse). -/

/-- A run of a finished table: the indices `[i, e)`, bound one after
the other at the ranks from `r` on. -/
structure Run where
  i : Nat
  e : Nat
  r : Nat
  deriving Inhabited, DecidableEq

/-- The rank of index `j`, if the run holds it. -/
@[inline] def Run.rank (x : @& Run) (j : Nat) : Option Nat :=
  if x.i ≤ j ∧ j < x.e then some (x.r + (j - x.i)) else none

/-- A finished table: its entries by rank, in pages of 4096; its runs,
in increasing order of indices; how many entries it has. -/
structure Pages (α : Type) where
  pages : Array (Array α)
  runs : Array Run
  n : Nat

/-- The entry of rank `r`. -/
@[inline] def Pages.atRank (P : @& Pages α) (r : Nat) : Option α :=
  let p := r >>> 12
  if h : p < P.pages.size then P.pages[p][r &&& 4095]? else none

/-- The last run in `[lo, hi)` whose first index is at most `j` (or
`lo`), by binary search. -/
def runFind (rs : @& Array Run) (j lo hi : Nat) : Nat :=
  if lo + 1 < hi then
    let mid := (lo + hi) / 2
    if (rs.getD mid default).i ≤ j then runFind rs j mid hi else runFind rs j lo mid
  else lo
termination_by hi - lo

/-- The rank of index `j`, if bound: one run (a dense table) is read
directly. -/
@[inline] def Pages.rank (P : @& Pages α) (j : Nat) : Option Nat :=
  let c := if P.runs.size < 2 then 0 else runFind P.runs j 0 P.runs.size
  if h : c < P.runs.size then P.runs[c].rank j else none

/-- Entry `j`. -/
@[inline] def Pages.get (P : @& Pages α) (j : Nat) : Option α :=
  match P.rank j with
  | some r => P.atRank r
  | none => none

/-- The finished tables before a window. -/
structure Prior where
  n : Pages Name
  l : Pages Level
  e : Pages Expr

/-! ### Comparing finished tables

An owner compares the tables a message names with the ones its round 0
was sent (`Cur.is`, `ConLeche/Driver/OwnerParse.lean`): the very object,
which the pointer test answers.  Behind it, the comparison is entry by
entry with the kernel's pointer-first equalities (`Name.beq`,
`Level.beq`, `Expr.beq`), one pass over the tables, never a structural
walk of an expression DAG. -/

instance : LawfulBEq ByteArray where
  rfl {a} := by
    show (a.data == a.data) = true
    simp
  eq_of_beq {a b} h := by
    have : a.data = b.data := by
      have h' : (a.data == b.data) = true := h
      simpa using h'
    exact ByteArray.ext this

instance [BEq α] : BEq (Pages α) :=
  ⟨fun a b => a.pages == b.pages && a.runs == b.runs && a.n == b.n⟩

instance [BEq α] [LawfulBEq α] : LawfulBEq (Pages α) where
  rfl {a} := by
    show (a.pages == a.pages && a.runs == a.runs && a.n == a.n) = true
    simp
  eq_of_beq {a b} h := by
    have h' : (a.pages == b.pages && a.runs == b.runs && a.n == b.n) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    cases a; cases b; simp_all

instance : BEq Prior := ⟨fun a b => a.n == b.n && a.l == b.l && a.e == b.e⟩

instance : LawfulBEq Prior where
  rfl {a} := by
    show (a.n == a.n && a.l == a.l && a.e == a.e) = true
    simp
  eq_of_beq {a b} h := by
    have h' : (a.n == b.n && a.l == b.l && a.e == b.e) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    cases a; cases b; simp_all

/-- The finished tables as partial maps. -/
@[inline] def Prior.tabs (P : Prior) : Tabs := ⟨P.n.get, P.l.get, P.e.get⟩

/-- The tables the parse starts with: name `0` anonymous, level `0`
zero, no expressions. -/
def Prior.init : Prior :=
  ⟨⟨#[#[.anonymous]], #[⟨0, 1, 0⟩], 1⟩, ⟨#[#[.zero]], #[⟨0, 1, 0⟩], 1⟩, ⟨#[], #[], 0⟩⟩

/-- A table as the serial parse keeps it: its entries below index
`cut`, run after run, index after index. -/
def Pages.toTable (P : Pages α) (cut : Nat) : IdTable α :=
  runsGo 0 {}
where
  runsGo (k : Nat) (t : IdTable α) : IdTable α :=
    if h : k < P.runs.size then runsGo (k + 1) (runGo P.runs[k] P.runs[k].i t) else t
  termination_by P.runs.size - k
  runGo (x : Run) (j : Nat) (t : IdTable α) : IdTable α :=
    if j < x.e ∧ j < cut then
      runGo x (j + 1) (match P.atRank (x.r + (j - x.i)) with
        | some v => t.insert j v
        | none => t)
    else t
  termination_by x.e - j

/-- The finished tables below counters `c` as a serial parse state,
with its records (what the serial parse continues from when a window
falls back). -/
def Prior.toState (P : Prior) (c : Ctr) (ds : Array Declaration) : StateD :=
  ⟨P.n.toTable c.n, P.l.toTable c.l, P.e.toTable c.e, ds⟩

/-- A chunk qualifies for the rounds: its scan ended at its end (the
newline cut leaves no tail and no error). -/
@[inline] def scanEnds (b : @& ByteArray) (sc : @& ScannedChunk) : Bool :=
  match sc.stop with
  | .tail i => i.toNat == b.size
  | _ => false

/-! ## The stream between windows -/

/-- The rounds parse between windows: the finished tables and their
counters, the records so far, the line and byte counts. -/
structure GSt where
  P : Prior
  c : Ctr
  ds : Array Declaration
  lineNo : Nat
  total : Nat

/-- The parse's start. -/
def GSt.init : GSt := ⟨Prior.init, ⟨1, 1, 0⟩, #[], 0, 0⟩

end ConLeche.Frontend
