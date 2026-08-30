import Setlec.SetR.Interp2.Step2.LevelsInst

/-!
# The seam's monotonicity checklist — statements

Seal 26 enumerated the level-sensitive seam **structurally**: thirteen
sites across nine run-path functions. Three have been examined
(`piResultNeverZero`, and the beta certificate's two zero-tests via
`betaCertLevel_flips`). This file freezes the question for the rest.

## The question, uniform across the list

For each guard: **what is its monotonicity direction under level
substitution?** `piResultNeverZero_map_subst` (`Step2/Levels.lean`) is
the worked example — `true` survives substitution, `false → true` is
possible, so the guard is **one-directional**.

One-directional is the *tractable* outcome, not a harmless one. It
means the instantiated run may reduce **further** than the
uninstantiated one, which is exactly why the general `whnf`
commutation **equality** is expect-false and why the discharge target
is the **simulation** form `WhnfInstLevelsUpTo` (a common head normal
form) rather than an equality. A guard that flips **both** ways would
be worse: the two runs could diverge irreconcilably, and that is a
genuine `InstLevels` obstruction rather than a checklist item. **STOP
on any such guard.**

## Why the checklist may collapse

Ten of the thirteen sites are `Level.isEquiv` or `Level.isEquivList`.
If substitution is a congruence for `isEquiv` — the statement below —
then all ten fall at once, and the remaining three are the zero-tests,
which are its special case modulo `subst ks vs .zero = .zero`.

**The one place it could genuinely fail is fuel.** `isEquiv` decides
by `simplify` equality first and otherwise by two `leq` calls at the
fixed `Level.defaultFuel` (`Kernel/Level.lean:132`). Substitution can
make a level *larger*, so a pair decided within budget before
substitution might exhaust it after — turning `some true` into `none`,
not into `some false`. That is a **third** outcome the binary framing
hides, and it is the thing to check first.

## The checklist, by site (seal 26's table)

| function | site | primitive | expected settler |
|---|---|---|---|
| `proofIrrel` | 786, 790 | `isEquiv _ .zero` | zero-test corollary |
| `pairEtaCert` | 856 | `isEquivList` | list congruence |
| `structEtaCertWith` | 940 | `isEquivList` | list congruence |
| `majorToCtor` | 1153 | `piResultNeverZero` | **done** (`_map_subst`) |
| `iotaRec` | 1311 | `isEquivList` | list congruence |
| `projCert` | 1371, 1376 | `isEquiv` | congruence |
| `defeqSpine` | 1694 | `isEquivList` | list congruence |
| `defeqStep` | 1816, 1858 | `isEquiv`, `isEquivList` | congruence, list |
| `isPropType` | 1944 | `isEquiv _ .zero` | zero-test corollary |
-/

namespace Setlec.SetR.Interp2

open Setlec (Level)

/-- **The congruence, and the whole checklist's hinge.**  If this
holds, ten of the thirteen sites fall at once.

Stated at `some true` rather than as an `Option` equation because
`none` is the checker's internal-error channel and the guards branch
on `some true`; the fuel risk is that the conclusion becomes `none`,
which this statement correctly forbids. -/
def IsEquivSubstMono : Prop :=
  ∀ (ks : List Name) (vs : List Level) (l r : Level),
    Level.isEquiv l r = some true →
    Level.isEquiv (Level.subst ks vs l) (Level.subst ks vs r)
      = some true

/-- The list form the six `isEquivList` sites read. -/
def IsEquivListSubstMono : Prop :=
  ∀ (ks : List Name) (vs : List Level) (ls rs : List Level),
    Level.isEquivList ls rs = some true →
    Level.isEquivList (ls.map (Level.subst ks vs))
        (rs.map (Level.subst ks vs)) = some true

/-- The zero-test corollary the three `isEquiv _ .zero` sites read.
Separate because `Level.subst ks vs .zero = .zero` must be discharged
for it to be an instance of the congruence at all. -/
def IsEquivZeroSubstMono : Prop :=
  ∀ (ks : List Name) (vs : List Level) (l : Level),
    Level.isEquiv l .zero = some true →
    Level.isEquiv (Level.subst ks vs l) .zero = some true

/-! ## What is deliberately *not* stated

The converse — that substitution cannot turn `some false` into
`some true` — is **false** and must not be attempted:
`betaCertLevel_flips` and `piResultNeverZero_flips` are the witnesses.
Every guard here is expected to be one-directional in the same
direction, and a proof of the converse would contradict landed
results. -/

end Setlec.SetR.Interp2
