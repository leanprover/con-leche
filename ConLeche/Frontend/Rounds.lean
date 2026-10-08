module

public import ConLeche.Frontend.Pipeline

@[expose] public section

/-!
# The rounds parse (task #329)

The pipelined parse (`ConLeche/Frontend/Pipeline.lean`) scans its
chunks in parallel and applies their records on one thread, in order:
the apply is the parse's serial floor (~80 ns a line).  This module is
the parallel apply.

**Dense streams.**  lean4export binds every table's indices in order,
each the next one: the `k`-th name line binds name `k + 1` (name `0`
is the anonymous name the state starts with), the `k`-th level line
level `k + 1`, the `k`-th expression line expression `k`.  On such a
stream the tables are dense arrays, a line's lookups are reads below
the counts of the lines before it (`Ctr`), and nothing is ever bound
twice.  `Ctr` counts, `Ctr.fits` is the per-line test.
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## Dense tables and counters -/

/-- A dense table: the array, no overflow map. -/
def IdTable.ofDense (a : Array α) : IdTable α := { dense := a }

/-- A state whose three tables are dense. -/
def StateD.ofDense (na : Array Name) (la : Array Level) (ea : Array Expr)
    (ds : Array Declaration) : StateD :=
  ⟨.ofDense na, .ofDense la, .ofDense ea, ds⟩

/-- How many entries each table holds: on a dense stream, the next
index each table binds. -/
structure Ctr where
  n : Nat
  l : Nat
  e : Nat
  deriving Inhabited, DecidableEq

/-- The counters after one line. -/
@[inline] def Ctr.step (c : Ctr) : LineRec → Ctr
  | .name .. => { c with n := c.n + 1 }
  | .level .. => { c with l := c.l + 1 }
  | .expr .. => { c with e := c.e + 1 }
  | _ => c

/-- The counters after a list of lines. -/
def Ctr.stepAll (c : Ctr) : List LineRec → Ctr
  | [] => c
  | r :: rs => (c.step r).stepAll rs

/-- **The density test of one line**: a table line binds the next index
of its table. -/
@[inline] def Ctr.fits (c : Ctr) : LineRec → Bool
  | .name i _ => i == c.n
  | .level i _ => i == c.l
  | .expr i _ => i == c.e
  | _ => true

end ConLeche.Frontend
