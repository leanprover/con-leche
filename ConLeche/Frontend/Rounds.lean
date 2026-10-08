module

public import ConLeche.Frontend.Pipeline

@[expose] public section

/-!
# The rounds parse: counters, finished tables, the check (task #329)

The pipelined parse (`ConLeche/Frontend/Pipeline.lean`) scans its
chunks in parallel and applies their records on one thread, in order:
the apply is the parse's serial floor.  The rounds parse applies the
chunks of a WINDOW in parallel, in rounds (`ConLeche/Frontend/RoundsWork.lean`
computes them; `ConLeche/Driver/ParParse.lean` drives them).  This
module holds what the rounds parse's correctness rests on, and nothing
of how the rounds compute:

* **Increasing streams.**  An exporter binds each table's indices in
  increasing order (lean4export: each the next one; another exporter
  may leave gaps).  On such a stream a line's lookups read below the
  counters of the lines before it — one more than the last index each
  table bound (`Ctr`) — and nothing is ever bound twice.
* **The finished tables** (`Pages`, `Prior`): the tables of every
  window before, in pages of 4096 indices, a lookup being two reads.
* **The check** (`checkLine`, `checkList`, `checkFlat`).  How the
  rounds found a window's entries does not matter: once the window's
  tables have joined the finished ones, every line of every chunk is
  gone through once more, in order, at the counters the serial parse
  has there — a table line must bind an index at or above its counter
  with nothing bound in the gap, and its builder, reading the finished
  tables cut at the counters, must yield exactly the entry the
  finished tables hold; a declaration line's builder must yield its
  record.  `ConLeche/Verify/Frontend/Rounds.lean` proves that a chunk
  passing the check is the serial parse of its lines
  (`chunk_step`), whatever the rounds did.
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

The tables of the windows before are kept in pages of 4096 indices:
index `j` is slot `j % 4096` of page `j / 4096`, and an index no line
bound holds a placeholder.  The placeholder is chosen so that no
parsed expression is one (a parsed expression is never a free
variable); a parsed name or level that happens to equal its table's
placeholder reads as unbound, which the check then rejects (the window
falls back to the serial parse). -/

/-- A placeholder value of a table's type, and its test. -/
class Sent (α : Type) where
  pend : α
  isPend : α → Bool

/-- The placeholder number (below `2^32`: a literal above that is a
decimal parse at every use). -/
def sentP : Nat := 4000000002

/-- The placeholders, each ONE object: a constant, not a constructor
the compiler would rebuild (and allocate) at every use. -/
@[noinline] def pendName : Name := .num .anonymous sentP
@[noinline] def pendLevel : Level := .param (.num .anonymous sentP)
@[noinline] def pendExpr : Expr := .fvar sentP (.bvar 0)

instance : Sent Name := ⟨pendName, fun
  | .num .anonymous k => k == sentP
  | _ => false⟩
instance : Sent Level := ⟨pendLevel, fun
  | .param (.num .anonymous k) => k == sentP
  | _ => false⟩
instance : Sent Expr := ⟨pendExpr, fun
  | .fvar .. => true
  | _ => false⟩

/-- A finished table, in pages. -/
structure Pages (α : Type) where
  pages : Array (Array α)

/-- Entry `j`. -/
@[inline] def Pages.get [Sent α] (P : @& Pages α) (j : Nat) : Option α :=
  let p := j >>> 12
  if h : p < P.pages.size then
    match P.pages[p][j &&& 4095]? with
    | some v => if Sent.isPend v then none else some v
    | none => none
  else none

/-- The finished tables before a window. -/
structure Prior where
  n : Pages Name
  l : Pages Level
  e : Pages Expr

/-- The finished tables as partial maps. -/
@[inline] def Prior.tabs (P : Prior) : Tabs := ⟨P.n.get, P.l.get, P.e.get⟩

/-- The tables the parse starts with: name `0` anonymous, level `0`
zero, no expressions. -/
def Prior.init : Prior :=
  ⟨⟨#[#[.anonymous]]⟩, ⟨#[#[.zero]]⟩, ⟨#[]⟩⟩

/-- The pages below `p0` kept, then `news`. -/
def Pages.setFrom (P : Pages α) (p0 : Nat) (news : Array (Array α)) : Pages α :=
  ⟨P.pages.extract 0 p0 ++ news⟩

/-- `j < b`: a table after a window, `P.setFrom (b / 4096) news`,
answers what `P` answers below `b`?  Below the kept pages it does by
construction (`p0 ≤ P.pages.size`); the slots of the first new page
below `b` are compared. -/
def Pages.keepsGo [BEq α] [Sent α] (P P' : @& Pages α) (j b : Nat) : Bool :=
  if j < b then P'.get j == P.get j && Pages.keepsGo P P' (j + 1) b
  else true
termination_by b - j

/-- The test of `Pages.keepsGo`, from the first new page. -/
def Pages.keeps [BEq α] [Sent α] (P : @& Pages α) (news : @& Array (Array α)) (b : Nat) : Bool :=
  b / 4096 ≤ P.pages.size && Pages.keepsGo P (P.setFrom (b / 4096) news) (b / 4096 * 4096) b

/-- A table as the serial parse keeps it: the entries below `n`. -/
def Pages.toTable [Sent α] (P : Pages α) (n : Nat) : IdTable α :=
  go 0 {}
where
  go (j : Nat) (t : IdTable α) : IdTable α :=
    if j < n then
      go (j + 1) (match P.get j with
        | some x => t.insert j x
        | none => t)
    else t
  termination_by n - j

/-- The finished tables below counters `c` as a serial parse state,
with its records (what the serial parse continues from when a window
falls back). -/
def Prior.toState (P : Prior) (c : Ctr) (ds : Array Declaration) : StateD :=
  ⟨P.n.toTable c.n, P.l.toTable c.l, P.e.toTable c.e, ds⟩

/-- The finished tables after a window, page by page from the
window's start. -/
def Prior.setFrom (P : Prior) (c : Ctr) (nn : Array (Array Name)) (nl : Array (Array Level))
    (ne : Array (Array Expr)) : Prior :=
  ⟨P.n.setFrom (c.n / 4096) nn, P.l.setFrom (c.l / 4096) nl, P.e.setFrom (c.e / 4096) ne⟩

/-- The driver's test that the tables after a window keep the tables
before below the window's start. -/
def Prior.keeps (P : Prior) (c : Ctr) (nn : Array (Array Name)) (nl : Array (Array Level))
    (ne : Array (Array Expr)) : Bool :=
  P.n.keeps nn c.n && P.l.keeps nl c.l && P.e.keeps ne c.e

/-! ## The check -/

/-- An answer matches an entry. -/
@[inline] def okIs [BEq α] : Except String α → α → Bool
  | .ok w, v => w == v
  | .error _, _ => false

/-- A name entry against its line, without building it. -/
@[inline] def nameCheck (nm : Nat → Except String Name) (r : @& NameRec) (v : Name) : Bool :=
  match r, v with
  | .str pre s, .str p' s' => okIs (nm pre) p' && s == s'
  | .num pre k, .num p' k' => okIs (nm pre) p' && k == k'
  | _, _ => false

/-- A level entry against its line, without building it. -/
@[inline] def levelCheck (nm : Nat → Except String Name) (lv : Nat → Except String Level)
    (r : @& LevelRec) (v : Level) : Bool :=
  match r, v with
  | .succ u, .succ u' => okIs (lv u) u'
  | .max a b, .max a' b' => okIs (lv a) a' && okIs (lv b) b'
  | .imax a b, .imax a' b' => okIs (lv a) a' && okIs (lv b) b'
  | .param n, .param n' => okIs (nm n) n'
  | _, _ => false

/-- **An expression entry against its line**, without building it: a
node's children are the lookups' answers (by the pointer-first
equality); a binder's annotation is built and compared; a leaf is
built and compared. -/
@[inline] def exprCheck (nm : Nat → Except String Name) (lv : Nat → Except String Level)
    (ex : Nat → Except String Expr) (r : @& ExprRec) (v : Expr) : Bool :=
  match r, v with
  | .app f a, .app f' a' => okIs (ex f) f' && okIs (ex a) a'
  | .lam ty bd pw, .lam t' b' m => okIs (ex ty) t' && okIs (ex bd) b' &&
      okIs ((pwOfF nm lv ex pw).map BinderMeta.mk) m
  | .forallE ty bd pw, .forallE t' b' m => okIs (ex ty) t' && okIs (ex bd) b' &&
      okIs ((pwOfF nm lv ex pw).map BinderMeta.mk) m
  | .letE ty vl bd, .letE t' v' b' => okIs (ex ty) t' && okIs (ex vl) v' && okIs (ex bd) b'
  | .proj tn ix st, .proj n' ix' s' => okIs (nm tn) n' && ix == ix' && okIs (ex st) s'
  | r, v => okIs (exprOfF nm lv ex r) v

/-- No entry of a finished table in `[lo, hi)`: the gap a line skips. -/
def Pages.noneIn [Sent α] (P : @& Pages α) (lo hi : Nat) : Bool :=
  if lo < hi then (P.get lo).isNone && Pages.noneIn P (lo + 1) hi else true
termination_by hi - lo

/-- **One line, checked** at counters `c` against the finished tables
`P`: the counters after it and the record it yields, or `none`. -/
@[inline] def checkLine (P : @& Prior) (c : Ctr) (r : @& LineRec) :
    Option (Ctr × Option Declaration) :=
  match r with
  | .name i x =>
    if c.n ≤ i && P.n.noneIn c.n i then
      match P.n.get i with
      | some v => if nameCheck (cutLk P.tabs c).name x v then some ({ c with n := i + 1 }, none)
          else none
      | none => none
    else none
  | .level i x =>
    if c.l ≤ i && P.l.noneIn c.l i then
      match P.l.get i with
      | some v => if levelCheck (cutLk P.tabs c).name (cutLk P.tabs c).level x v then
            some ({ c with l := i + 1 }, none)
          else none
      | none => none
    else none
  | .expr i x =>
    if c.e ≤ i && P.e.noneIn c.e i then
      match P.e.get i with
      | some v => if exprCheck (cutLk P.tabs c).name (cutLk P.tabs c).level (cutLk P.tabs c).expr
            x v then some ({ c with e := i + 1 }, none)
          else none
      | none => none
    else none
  | .decl d =>
    match declOfF (cutLk P.tabs c).name (cutLk P.tabs c).level (cutLk P.tabs c).expr d with
    | .ok (.inl x) => some (c, some x)
    | _ => none
  | .header => some (c, none)
  | .blank => some (c, none)

/-- A record, if any, pushed. -/
@[inline] def pushOpt (acc : Array Declaration) : Option Declaration → Array Declaration
  | some x => acc.push x
  | none => acc

/-- **The check of a list of lines** (the specification): the counters
after them and their records pushed, or `none`. -/
def checkList (P : Prior) (c : Ctr) : List LineRec → Array Declaration →
    Option (Ctr × Array Declaration)
  | [], acc => some (c, acc)
  | r :: rs, acc =>
    match checkLine P c r with
    | some (c', o) => checkList P c' rs (pushOpt acc o)
    | none => none

/-- **The check of a flat chunk**: `k` records from machine-word
position `p`, each read where it is checked (`Flat.withLineU`). -/
def checkFlatGoU (P : @& Prior) (d : @& ByteArray) (p : USize) (k : Nat) (c : Ctr)
    (acc : Array Declaration) : Option (Ctr × Array Declaration) :=
  match k with
  | 0 => some (c, acc)
  | k + 1 =>
    Flat.withLineU d p fun r q =>
      match checkLine P c r with
      | some (c', o) => checkFlatGoU P d q k c' (pushOpt acc o)
      | none => none

/-- A flat chunk's lines, checked from counters `c` (a buffer too large
for a machine word is not checked: the window falls back). -/
def checkFlat (P : @& Prior) (fc : @& FlatChunk) (c : Ctr) : Option (Ctr × Array Declaration) :=
  if fc.data.size < USize.size then checkFlatGoU P fc.data 0 fc.count c #[] else none

/-- A chunk qualifies for the rounds: its scan ended at its end (the
newline cut leaves no tail and no error), and the byte count stays
under the size guard. -/
@[inline] def chunkFits (b : @& ByteArray) (fc : @& FlatChunk) (total : Nat) : Bool :=
  match fc.stop with
  | .tail i => i.toNat == b.size && total + b.size < USize.size
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
