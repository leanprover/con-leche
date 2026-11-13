module

import ConLeche.Kernel.Ground
public import ConLeche.Kernel.FEnv

@[expose] public section

/-!
# The ground gate (task #423)

The comparison with `Bool.true` that the cached core hands to the ground
engine (`ConLeche/Kernel/Ground.lean`), on the declaration's kept program.
-/

namespace ConLeche.Cached

open ConLeche

/-- The engine on the declaration's kept program `P₀`, at the engine's fuel
and the maximum `Nat` size `maxNat`. -/
def ground4Bool (fe : FEnv) (maxNat : Nat) (P₀ : G4Prog) (e : Expr) :
    (Except G4Stop Bool × (Nat × Nat)) × G4Prog :=
  ground4BoolCore fe.find? fe.findProj? (natLitStoredF fe) (strLitStoredF fe) (some maxNat) P₀ e

/-- **The ground shortcut** (task #423): a comparison with `Bool.true` on
either side whose other side is closed evaluates that side on the ground
engine, with no fallback (task #423 soundness, ruling 4): `true` or
`false`, or a stop the caller raises (a decline, the maximum-`Nat`-size
refusal, an internal error).  Read by `groundGateM`
(`ConLeche/Cached/CoreC.lean`). -/
def groundShortcut (eager : Bool) (fe : FEnv) (maxNat : Nat) (P : G4Prog) (a b : Expr) :
    Option (Except G4Stop Bool) × G4Prog :=
  match groundTarget eager a b with
  | none => (none, P)
  | some t =>
    let ((r, _), P) := ground4Bool fe maxNat P t
    (some r, P)

/-- The ground shortcut reads `fe` only through `find?` and
`findTable?` (for `ConLeche/Verify/Cached/KnotCongr.lean`). -/
theorem groundShortcut_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (eager : Bool) :
    groundShortcut eager fe₁ = groundShortcut eager fe₂ := by
  have hp : fe₁.findProj? = fe₂.findProj? := by
    funext T i; unfold FEnv.findProj?; rw [htb]
  have hn : natLitStoredF fe₁ = natLitStoredF fe₂ := by
    unfold natLitStoredF; rw [hfe]
  have hs : strLitStoredF fe₁ = strLitStoredF fe₂ := by
    unfold strLitStoredF; rw [hn, hfe]
  have hg4 : ground4Bool fe₁ = ground4Bool fe₂ := by
    funext m P e; unfold ground4Bool; rw [hfe, hp, hn, hs]
  funext m P a b; unfold groundShortcut; rw [hg4]

end ConLeche.Cached
