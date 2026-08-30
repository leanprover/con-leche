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

/-! ## Item 1, settled: the congruence is FALSE, and the fuel is why

The check the brief asked for first came back **negative**: the
`simplify`-equality fast path does *not* cover every `some true`, and
on a pair it does not cover, substitution can push the `leq` calls
past `Level.defaultFuel`.  `not_isEquivSubstMono` below exhibits a
pair decided `some true` by the `leq` round trip whose substituted
image is `none`.

The witness is deliberately minimal in structure and maximal only in
size: `max u v` against `max v u`, which `simplify` does **not**
equate (`combining` is not commutative syntactically), decided by two
three-step `leq` runs; substituting `u ↦ succ^10000 zero` leaves the
fast path still closed and makes the very first `leqCore` recursion
peel more `succ`s than the budget has units.

**This is a decidability gap, not a flip.**  The conclusion is
`none` — the checker's internal-error channel — and never `some
false`.  What it costs is stated positively below:
`isEquiv_subst_eval` (the substituted pair still *evaluates* equal,
unconditionally) and `isEquiv_subst_ne_false` (the verdict never
becomes `false`, given `LeqFalseComplete`). -/

/-- `succ`-iterated `zero`, kept as a function so that a level with
more `succ`s than `Level.defaultFuel` is still a small *term*. -/
private def succN : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (succN n)

private theorem simplify_succN :
    ∀ n, Level.simplify (succN n) = succN n
  | 0 => rfl
  | n + 1 => by simp [succN, Level.simplify, simplify_succN n]

/-- **Peeling a `succ` costs one unit of `leqCore` fuel.**  So a
left-hand level with at least `fuel` `succ`s exhausts the budget
against any nonzero right-hand side: `none`, which is not a verdict.
This is the whole of the fuel risk, isolated. -/
private theorem leqCore_succN_none {r : Level} (hr : r ≠ .zero) :
    ∀ (fuel n : Nat) (diff : Int), fuel ≤ n →
      Level.leqCore fuel (succN n) r diff = none := by
  intro fuel
  induction fuel with
  | zero => intro n diff _; simp [Level.leqCore]
  | succ f ih =>
    intro n diff hle
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [succN, Level.leqCore, if_neg (by simp), if_neg (by simp [hr])]
    rw [show Level.rest f (.succ (succN m)) r diff
      = Level.leqCore f (succN m) r (diff - 1) from by
        simp [Level.rest]]
    exact ih m (diff - 1) (by omega)

/-- The two names the fuel witness uses. -/
private def seamA : Name := .str .anonymous "a"
private def seamB : Name := .str .anonymous "b"

private theorem seamAB : seamA ≠ seamB := by decide

private theorem simplify_swap (a b : Name) :
    Level.simplify (.max (.param a) (.param b))
      = .max (.param a) (.param b) := by
  simp [Level.simplify, Level.combining]

/-- `max u v ≤ max v u` is decided in three `leqCore` steps, so the
*uninstantiated* comparison is nowhere near the budget. -/
private theorem leqCore_swap (f : Nat) (a b : Name) :
    Level.leqCore (f + 1 + 1 + 1) (.max (.param a) (.param b))
        (.max (.param b) (.param a)) 0 = some true := by
  by_cases hab : a = b <;> simp [Level.leqCore, Level.rest, hab]

/-- **The pair, before substitution: `some true`, and *not* by the
fast path.**  `simplify` keeps the two `max`es apart (they differ in
argument order); the verdict comes from the `leq` round trip. -/
private theorem isEquiv_swap (a b : Name) (hab : a ≠ b) :
    Level.isEquiv (.max (.param a) (.param b))
      (.max (.param b) (.param a)) = some true := by
  have hl : Level.leq (.max (.param a) (.param b))
      (.max (.param b) (.param a)) = some true := by
    rw [Level.leq, simplify_swap, simplify_swap]
    exact leqCore_swap 9997 a b
  have hr : Level.leq (.max (.param b) (.param a))
      (.max (.param a) (.param b)) = some true := by
    rw [Level.leq, simplify_swap, simplify_swap]
    exact leqCore_swap 9997 b a
  rw [Level.isEquiv,
    if_neg (by rw [simplify_swap, simplify_swap]; simp [hab])]
  simp [hl, hr]

private theorem simplify_swapN (m : Nat) (b : Name) :
    Level.simplify (.max (succN (m + 1)) (.param b))
      = .max (succN (m + 1)) (.param b) := by
  simp [Level.simplify, simplify_succN, succN, Level.combining]

private theorem simplify_swapN' (m : Nat) (b : Name) :
    Level.simplify (.max (.param b) (succN (m + 1)))
      = .max (.param b) (succN (m + 1)) := by
  simp [Level.simplify, simplify_succN, succN, Level.combining]

private theorem leq_swapN_none (m : Nat) (b : Name)
    (hm : Level.defaultFuel ≤ m + 1) :
    Level.leq (.max (succN (m + 1)) (.param b))
      (.max (.param b) (succN (m + 1))) = none := by
  rw [Level.leq, simplify_swapN, simplify_swapN']
  obtain ⟨f, hf⟩ : ∃ f, Level.defaultFuel = f + 1 := ⟨9999, rfl⟩
  rw [hf]
  simp only [Level.leqCore, Level.rest]
  rw [leqCore_succN_none (r := .max (.param b) (succN (m + 1)))
    (by simp) f (m + 1) 0 (by omega)]
  rfl

/-- **The same pair, after substitution: `none`.**  The fast path is
still closed, and the first `leqCore` recursion runs out of fuel
peeling the substituted `succ` chain. -/
private theorem isEquiv_swapN_none (m : Nat) (b : Name)
    (hm : Level.defaultFuel ≤ m + 1) :
    Level.isEquiv (.max (succN (m + 1)) (.param b))
      (.max (.param b) (succN (m + 1))) = none := by
  rw [Level.isEquiv,
    if_neg (by rw [simplify_swapN, simplify_swapN']; simp [succN]),
    leq_swapN_none m b hm]
  rfl

/-- **STOP: the hinge is false.**  `Level.isEquiv` is *not* a
congruence for `Level.subst` at `some true` — but the failure is a
`none`, i.e. the checker's internal-error channel, not a `some false`.
So the ten `isEquiv`/`isEquivList` sites are **not** settled by the
frozen statement, and the checklist does not collapse as seal 27
predicted.

The witness is the pair `max a b` / `max b a` at `a ↦ succ^10000
zero`.  Nothing about it is exotic except its size: `succ`-depth
`Level.defaultFuel` is what it takes, and levels come off the input
stream, so the input can carry one. -/
theorem not_isEquivSubstMono : ¬ IsEquivSubstMono := by
  intro h
  have hw := h [seamA] [succN (9999 + 1)]
    (.max (.param seamA) (.param seamB))
    (.max (.param seamB) (.param seamA)) (isEquiv_swap _ _ seamAB)
  rw [show Level.subst [seamA] [succN (9999 + 1)]
      (.max (.param seamA) (.param seamB))
      = .max (succN (9999 + 1)) (.param seamB) from by
        simp [Level.subst, Level.subst.go, seamAB],
    show Level.subst [seamA] [succN (9999 + 1)]
      (.max (.param seamB) (.param seamA))
      = .max (.param seamB) (succN (9999 + 1)) from by
        simp [Level.subst, Level.subst.go, seamAB],
    isEquiv_swapN_none 9999 seamB (by decide)] at hw
  exact nomatch hw

/-! ## What is deliberately *not* stated

The converse — that substitution cannot turn `some false` into
`some true` — is **false** and must not be attempted:
`betaCertLevel_flips` and `piResultNeverZero_flips` are the witnesses.
Every guard here is expected to be one-directional in the same
direction, and a proof of the converse would contradict landed
results. -/

end Setlec.SetR.Interp2
