/-!
# Throwaway instrumentation counters (task #84 measurement — NEVER MERGE)

Global mutable counter cells, bumped from pure code through an
`implemented_by` identity (`Instr.count i x = x`), read at exit.
-/

namespace Setlec.Instr

/-- Number of counter slots. -/
def nCtrs : Nat := 20

/-- Counter names (task #84 probe). -/
def names : Array String := #[
  "instList_calls",      -- 0  instantiateListI wrapper calls
  "instList_visits",     -- 1  instantiateListIGo non-hit node visits
  "instList_hits",       -- 2  instantiateListIGo memo hits
  "getAppArgs_conses",   -- 3  getAppArgsAccI cons steps
  "mkAppN_interns",      -- 4  mkAppNI app interns
  "instSpine_bulk",      -- 5  instSpineI bulk (reverse) calls
  "instSpine_chain",     -- 6  instSpineI chain fallback calls
  "iotaRec_tried",       -- 7  iotaRecI entries with rec head
  "iotaRec_args",        -- 8  iotaRecI getAppArgs after arity gate
  "inst1_visits",        -- 9  instantiate1IGo non-hit node visits
  "inst1_calls",         -- 10 instantiate1I wrapper calls
  "defEqList_elems",     -- 11 defEqListI element comparisons
  "intern_calls",        -- 12 EStore.intern calls
  "intern_new",          -- 13 EStore.intern misses (new node)
  "whnfApp_steps",       -- 14 whnfAppI arg steps
  "getAppArgs_calls",    -- 15 getAppArgsI wrapper calls
  "c16", "c17", "c18", "c19"]

private unsafe def cellsUnsafe : IO.Ref (Array Nat) :=
  unsafeBaseIO (IO.mkRef (Array.replicate nCtrs 0))

@[never_extract]
private unsafe def countImpl {α : Type} (i : Nat) (x : α) : α :=
  unsafeBaseIO do
    cellsUnsafe.modify fun a => a.set! i (a[i]! + 1)
    pure x

/-- Identity on `x` that bumps counter `i` as a compiled side effect. -/
@[never_extract, implemented_by countImpl]
def count {α : Type} (i : Nat) (x : α) : α := x

private unsafe def readResetImpl : BaseIO (Array Nat) := do
  let a ← cellsUnsafe.get
  cellsUnsafe.set (Array.replicate nCtrs 0)
  pure a

/-- Read all counters and reset them to zero. -/
@[implemented_by readResetImpl]
def readReset : BaseIO (Array Nat) := pure (Array.replicate nCtrs 0)

/-- One `COUNT:` line for the dump. -/
def fmtLine (decl : String) (a : Array Nat) : String := Id.run do
  let mut s := s!"COUNT: {decl}"
  for i in [0:names.size] do
    s := s ++ s!" {names[i]!}={a.getD i 0}"
  return s

end Setlec.Instr
