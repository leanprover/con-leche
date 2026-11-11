module

public import ConLeche.Cached.Ground
public import ConLeche.Cached.Ground2
public import ConLeche.Cached.Ground3

@[expose] public section

/-!
# The ground gate's dispatch (task #423)

The comparison with `Bool.true` that the cached core hands to the ground
engine (`ConLeche/Kernel/Ground.lean`), and the probe switch over the
engine's rounds (`groundMode`).
-/

namespace ConLeche.Cached

open ConLeche

/-- Two site answers agree (the run-twice probe). -/
def g4SameAnswer : Option (Except G4Stop Bool) → Option (Except G4Stop Bool) → Bool
  | some (.ok b), some (.ok b') => b == b'
  | some (.error _), some (.error _) => true
  | none, none => true
  | _, _ => false

/-- A site answer, for the trace. -/
def g4AnswerTag : Option (Except G4Stop Bool) → String
  | some (.ok true) => "true"
  | some (.ok false) => "false"
  | some (.error (.decline m)) => s!"decline {m}"
  | some (.error (.refuse op _ _ post)) => s!"refuse {op} {post}"
  | some (.error (.internal m)) => s!"internal {m}"
  | some (.error (.stuck w)) => s!"stuck {w}"
  | none => "none"

/-- **The ground shortcut** (task #423, spike; `groundMode ≠ 0`): a
comparison with `Bool.true` on either side whose other side is closed
evaluates that side on the ground machine.  Rounds 4 and later
(`groundMode ≥ 10`) answer every such comparison, with no fallback
(task #423 soundness, ruling 4): `true` or `false`, or a stop the caller
raises (a decline, the maximum-`Nat`-size refusal, an internal error).
Rounds 1–3 (the probes below 10) answer `none`, the incumbent path, where
they abort.  Read by `groundGateM` (`ConLeche/Cached/CoreC.lean`). -/
def groundShortcut (eager : Bool) (fe : FEnv) (maxNat : Nat) (P : G3Prog × G4Prog) (a b : Expr) :
    Option (Except G4Stop Bool) × (G3Prog × G4Prog) :=
  let t? : Option Expr :=
    if Expr.isBoolTrue b && (eager || !(Expr.hasFvar a)) then some a
    else if Expr.isBoolTrue a && (eager || !(Expr.hasFvar b)) then some b
    else none
  match t? with
  | none => (none, P)
  | some t =>
    if Expr.hasFvar t then (none, P) else
    let eng : G3Prog × G4Prog → Expr →
        (Option (Except G4Stop Bool) × (Nat × Nat) × String) × (G3Prog × G4Prog) :=
      fun P t =>
      if groundMode ≥ 10 then
        (let ((r, st), P4) := ground4Bool fe maxNat P.2 t; ((some r, st, ""), (P.1, P4)))
      else
        let ((r, st, why), P) : (Option Bool × (Nat × Nat) × String) × (G3Prog × G4Prog) :=
          if groundMode ≥ 7 then (let (r, P3) := ground3Bool fe P.1 t; (r, (P3, P.2)))
          else if groundMode ≥ 3 && groundMode != 5 then (ground2Bool fe t, P)
          else (groundBool fe t, P)
        ((r.map .ok, st, why), P)
    let ((r, steps, why), P) := eng P t
    -- probes 5, 6, 9 and 12: the engine twice (its own cost is the difference)
    let (r, P) := if groundMode == 5 || groundMode == 6 || groundMode == 9 || groundMode == 12 then
        let ((r', _, _), P) := eng P (dbgTrace "" fun _ => t)
        (if g4SameAnswer r' r then r else none, P) else (r, P)
    if groundMode == 2 || groundMode == 4 || groundMode == 8 || groundMode == 11 then
      (dbgTrace s!"GROUND {g4AnswerTag r} {steps.1} {steps.2} {why}" fun _ => r, P)
    else (r, P)

/-- The ground shortcut reads `fe` only through `find?` and
`findTable?` (for `ConLeche/Verify/Cached/KnotCongr.lean`). -/
theorem groundShortcut_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (eager : Bool) :
    groundShortcut eager fe₁ = groundShortcut eager fe₂ := by
  have hp : fe₁.findProj? = fe₂.findProj? := by
    funext T i; unfold FEnv.findProj?; rw [htb]
  have hg : groundBool fe₁ = groundBool fe₂ := by
    funext e; unfold groundBool strLitStoredF natLitStoredF; rw [hfe, hp]
  have hn : natLitStoredF fe₁ = natLitStoredF fe₂ := by
    unfold natLitStoredF; rw [hfe]
  have hs : strLitStoredF fe₁ = strLitStoredF fe₂ := by
    unfold strLitStoredF; rw [hn, hfe]
  have hg2 : ground2Bool fe₁ = ground2Bool fe₂ := by
    funext e; unfold ground2Bool; rw [hfe, hp, hn, hs]
  have hg3 : ground3Bool fe₁ = ground3Bool fe₂ := by
    funext P e; unfold ground3Bool; rw [hfe, hp, hn, hs]
  have hg4 : ground4Bool fe₁ = ground4Bool fe₂ := by
    funext m P e; unfold ground4Bool; rw [hfe, hp, hn, hs]
  funext m P a b; unfold groundShortcut; rw [hg, hg2, hg3, hg4]

end ConLeche.Cached
