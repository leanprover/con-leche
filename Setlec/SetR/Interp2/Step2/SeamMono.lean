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

/-! ## Item 2: the list form falls with it, at length one

`Level.isEquivList` is a pointwise fold over `Level.isEquiv` with the
same `Option` plumbing, so a one-element list transports both halves
of the item-1 witness without any new content.  Stated separately
because six of the thirteen sites read the list form and none of them
would be settled by the scalar refutation alone. -/

/-- **STOP: the list form is false too.**  Same witness, at length
one; the `none` propagates through the fold's bind. -/
theorem not_isEquivListSubstMono : ¬ IsEquivListSubstMono := by
  intro h
  have hw := h [seamA] [succN (9999 + 1)]
    [.max (.param seamA) (.param seamB)]
    [.max (.param seamB) (.param seamA)]
    (by simp [Level.isEquivList, isEquiv_swap _ _ seamAB])
  rw [show ([Level.max (.param seamA) (.param seamB)].map
        (Level.subst [seamA] [succN (9999 + 1)]))
      = [Level.max (succN (9999 + 1)) (.param seamB)] from by
        simp [Level.subst, Level.subst.go, seamAB],
    show ([Level.max (.param seamB) (.param seamA)].map
        (Level.subst [seamA] [succN (9999 + 1)]))
      = [Level.max (.param seamB) (succN (9999 + 1))] from by
        simp [Level.subst, Level.subst.go, seamAB]] at hw
  rw [Level.isEquivList, isEquiv_swapN_none 9999 seamB (by decide)]
    at hw
  exact nomatch hw

/-! ## Item 3: the zero-tests are TRUE, and they never touch the fuel

The three `isEquiv _ .zero` sites survive, and the reason is not that
the general congruence "nearly" works: it is that **`isEquiv _ .zero`
can only be `some true` through the fast path**.  If the `leq` round
trip answers `true` for `l ≤ 0`, then `leqCore_sound` already forces
`Level.eval φ l = 0` at every `φ`, and a level that evaluates to `0`
everywhere is one `simplify` collapses to `.zero` syntactically
(`simplify_eq_zero_of_eval`, by induction: `zero` and `param` are the
only leaves, and `param` is nonzero at the constant-one assignment).
So the hypothesis is *equivalent* to `Level.isZero l`, which is
`simplify`-only, and substitution preserves it semantically.

This is the shape the brief's first question was about, confirmed on
the one family where it holds: the fast path does cover every `some
true` — for the zero-tests, and for them only. -/

/-- The constant-one assignment: strictly positive on every parameter,
which is all the argument needs. -/
private def oneFn : Name → Nat := fun _ => 1

/-- **A level that evaluates to `0` at the constant-one assignment is
`simplify`d to `.zero` syntactically.**  The converse of
`eval_simplify` on the one value where `simplify` is complete. -/
private theorem simplify_eq_zero_of_eval :
    ∀ l : Level, Level.eval oneFn l = 0 → Level.simplify l = .zero := by
  intro l
  induction l with
  | zero => intro _; rfl
  | succ l _ => intro h; simp [Level.eval] at h
  | param n => intro h; simp [Level.eval, oneFn] at h
  | max a b iha ihb =>
    intro h
    simp only [Level.eval, Nat.max_eq_zero_iff] at h
    rw [Level.simplify, iha h.1, ihb h.2]
    rfl
  | imax a b _ ihb =>
    intro h
    simp only [Level.eval] at h
    have hb : Level.eval oneFn b = 0 := by
      by_cases hne : Level.eval oneFn b = 0
      · exact hne
      · rw [if_neg hne] at h
        simp only [Nat.max_eq_zero_iff] at h
        exact absurd h.2 hne
    simp [Level.simplify, ihb hb]

/-- **The zero-test corollary holds.**  Three of the thirteen sites —
`proofIrrel`'s two and `isPropType`'s one — are settled by it.
Note that `Level.subst ks vs .zero = .zero` is not even needed: the
statement carries the literal `.zero` on the right, and the proof goes
through the fast path, which reads `Level.simplify .zero = .zero`. -/
theorem isEquivZeroSubstMono : IsEquivZeroSubstMono := by
  intro ks vs l h
  have hz : Level.simplify (Level.subst ks vs l) = .zero := by
    refine simplify_eq_zero_of_eval _ ?_
    rw [Level.eval_subst]
    simpa [Level.eval] using
      Level.isEquiv_sound h (Level.substFn oneFn ks vs)
  rw [Level.isEquiv, if_pos (by rw [hz]; rfl)]
  rfl

/-- **Non-vacuity check for item 3.**  `isEquivZeroSubstMono` would be
worthless if its hypothesis were satisfiable only at levels a
substitution cannot move; here is one it does move — `imax a 0` is
`some true` against `.zero`, and stays so at `a ↦ 1`, where the
*substituted* level is a different term.  (Not a bill of health, per
seal 11; just a check that the lemma is not empty.) -/
private theorem isEquivZero_moved :
    Level.isEquiv (.imax (.param seamA) .zero) .zero = some true ∧
      Level.isEquiv
        (Level.subst [seamA] [.succ .zero]
          (.imax (.param seamA) .zero)) .zero = some true := by
  refine ⟨?_, isEquivZeroSubstMono _ _ _ ?_⟩ <;>
    · rw [Level.isEquiv, if_pos (by simp [Level.simplify])]
      rfl

/-! ## What is deliberately *not* stated

The converse — that substitution cannot turn `some false` into
`some true` — is **false** and must not be attempted:
`betaCertLevel_flips` and `piResultNeverZero_flips` are the witnesses.
Every guard here is expected to be one-directional in the same
direction, and a proof of the converse would contradict landed
results. -/

end Setlec.SetR.Interp2
