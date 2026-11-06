module

@[expose] public section

/-!
# How often `--progress` says something

`--progress[=N|P%|Ss]`: a line every `N` items, per `P` percent of a phase's items, or at the first
item done once `S` seconds have passed since the last line (task #484).  So a line comes only when
something finishes: a single long item, or a step that has no items, says nothing until it ends,
which is why every phase says when it starts.  Only the heartbeat reads this: no verdict does.
-/

namespace ConLeche

/-- How often the heartbeat speaks. -/
inductive Pace where
  | off
  | every (n : Nat)
  | percent (p : Nat)
  | seconds (s : Nat)
  deriving Inhabited

/-- Does the heartbeat speak at all? -/
def Pace.on : Pace → Bool
  | .off => false
  | _ => true

/-- Does the heartbeat speak at every item?  Then it is a trace, and a line names its item; at
any other pace the item a line happens to fall on is an arbitrary one. -/
def Pace.trace : Pace → Bool
  | .every 1 => true
  | _ => false

/-- A plain stride over `total` items, for the install's loop: its first line says the phase has
started, and at seconds, which it has no clock for, the only one. -/
def Pace.strideFor (total : Nat) : Pace → Nat
  | .off => 0
  | .every n => n
  | .percent p => max 1 (total * p / 100)
  | .seconds _ => total + 1

/-- A phase's clock, for `Pace.due`. -/
def Pace.clock : IO (IO.Ref Nat) := do IO.mkRef (← IO.monoMsNow)

/-- **Is a line due at item `k` of `total`**, counted from 1?  `last` is when the last line was. -/
def Pace.due (pace : Pace) (last : IO.Ref Nat) (k total : Nat) : IO Bool := do
  match pace with
  | .off => return false
  | .every n => return n > 0 && k % n == 0
  | .percent p =>
    let d := p * total
    return d > 0 && (k * 100 / d) != ((k - 1) * 100 / d)
  | .seconds s =>
    let now ← IO.monoMsNow
    last.modifyGet fun t => if t + s * 1000 ≤ now then (true, now) else (false, t)

end ConLeche
