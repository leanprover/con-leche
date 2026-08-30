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

## Amendment: the checklist was worked, and it did not collapse

Verdicts, in the order the work was done (each section below carries
the argument):

1. **`IsEquivSubstMono` is FALSE** (`not_isEquivSubstMono`).  The fuel
   risk this file named first is *real*: the `simplify` fast path does
   not cover every `some true`, and on a pair it does not cover,
   substitution can push the `leq` calls past `Level.defaultFuel`.
   The conclusion is `none` — a decidability gap, not a flip.
2. **`IsEquivListSubstMono` is FALSE** (`not_isEquivListSubstMono`),
   by the same witness at length one.
3. **`IsEquivZeroSubstMono` is TRUE** (`isEquivZeroSubstMono`), and
   *not* as a corollary of 1: `isEquiv _ .zero` can only be `some
   true` through the fast path, so the zero-tests never touch the
   fuel at all.
4. Checking the sites turned up two things the table above got wrong:
   three of them (`iotaRec` 1311, `projCert` 1371/1376) are in the
   **mapped** shape, which none of the three frozen statements has;
   and `defeqSpine` 1694 reads its guard **without `liftFueled`**, so
   there the gap is a `false` branch and the guard genuinely flips
   `true → false` (`spineGuard_flips_to_false`).

Final tally: **four of the thirteen settled** (the three zero-tests
plus `majorToCtor`), eight settled only up to the `none` channel, one
(`defeqSpine`) not settled.
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

/-! ## What survives item 1: the semantic monotonicity, unconditional

`Level.isEquiv`'s `some true` is sound for `Level.eval`
(`isEquiv_sound`) and nothing stronger, and *evaluation* commutes with
substitution on the nose (`eval_subst`).  So the ten sites' guards are
monotone in the only currency the checker's own soundness proofs read
— it is the **decision** that is not, and only through the `none`
channel. -/

/-- **The substituted pair still evaluates equal, at every
assignment.**  Unconditional; no fuel anywhere in the statement. -/
theorem isEquiv_subst_eval (ks : List Name) (vs : List Level)
    {l r : Level} (h : Level.isEquiv l r = some true)
    (φ : Name → Nat) :
    Level.eval φ (Level.subst ks vs l)
      = Level.eval φ (Level.subst ks vs r) := by
  rw [Level.eval_subst, Level.eval_subst]
  exact Level.isEquiv_sound h _

private theorem evalEqList_subst (ks : List Name) (vs : List Level)
    (φ : Name → Nat) :
    ∀ {ls rs : List Level},
      Level.EvalEqList (Level.substFn φ ks vs) ls rs →
      Level.EvalEqList φ (ls.map (Level.subst ks vs))
        (rs.map (Level.subst ks vs)) := by
  intro ls
  induction ls with
  | nil =>
    intro rs h
    cases rs with
    | nil => trivial
    | cons r rs => exact nomatch h
  | cons l ls ih =>
    intro rs h
    cases rs with
    | nil => exact nomatch h
    | cons r rs =>
      obtain ⟨h1, h2⟩ :
        Level.eval (Level.substFn φ ks vs) l
            = Level.eval (Level.substFn φ ks vs) r ∧
          Level.EvalEqList (Level.substFn φ ks vs) ls rs := h
      refine ⟨?_, ih h2⟩
      rw [Level.eval_subst, Level.eval_subst]
      exact h1

/-- The list form of the same, in `EvalEqList` — the currency
`isEquivList_sound` hands out. -/
theorem isEquivList_subst_evalEq (ks : List Name) (vs : List Level)
    {ls rs : List Level} (h : Level.isEquivList ls rs = some true)
    (φ : Name → Nat) :
    Level.EvalEqList φ (ls.map (Level.subst ks vs))
      (rs.map (Level.subst ks vs)) :=
  evalEqList_subst ks vs φ
    (Level.isEquivList_sound h (Level.substFn φ ks vs))

/-! ## The usable repair, and its one residue

A `none` is an internal error the checker turns into a throw, not a
verdict; what a simulation argument between an uninstantiated and an
instantiated run must exclude is the guard answering **`false`** where
it answered `true`.  That statement *is* provable — from the semantic
monotonicity above plus one fact about `Level.leqCore` alone:
**a `some false` verdict is correct**.

That fact is not in the tree.  `Setlec/Verify/Level.lean` proves the
`true` direction only, by design ("a `false` verdict leads to
rejection, which needs no justification").  Under this seam it is
needed after all, and it is stated here rather than assumed.

**Where a proof of it would have to do work** (recorded so the next
worker does not rediscover it): `Level.rest`'s rows
`.param _, .max x y` and `.zero, .max x y` answer `false` only when
*both* recursive calls do, so the proof must turn two separate
counter-assignments into one — and `Level.eval` is monotone in the
assignment, so the pointwise maximum moves both sides the wrong way.
Every other row is a one-line semantic argument.

**Trap-check, and its limit.**  `LeqFalseComplete` asserts a negative
conclusion from a `leqCore` success, so the smallest-fuel test
applies: at `fuel = 0` `leqCore` is `none`, the hypothesis is
unsatisfiable, and the instance is **vacuous** — the test says
nothing.  Seal 11's caveat, again. -/

/-- **The residue: `leqCore`'s `false` verdicts are correct.**  A
statement about the level decision procedure alone — no substitution,
no seam, no environment.  Open. -/
def LeqFalseComplete : Prop :=
  ∀ (fuel : Nat) (l r : Level) (diff : Int),
    Level.leqCore fuel l r diff = some false → ¬ Level.Sem l r diff

private theorem sem_simplify_of_eval {a b : Level}
    (h : ∀ φ, Level.eval φ a = Level.eval φ b) :
    Level.Sem (Level.simplify a) (Level.simplify b) 0 := by
  intro φ
  rw [Level.eval_simplify, Level.eval_simplify, h φ]
  omega

/-- **A pair that evaluates equal is never decided `false`** — given
the residue.  Both branches of `isEquiv`'s `else` are `leq` calls, and
each contradicts the evaluation equality through
`LeqFalseComplete`. -/
theorem isEquiv_ne_false_of_eval (hc : LeqFalseComplete) {a b : Level}
    (h : ∀ φ, Level.eval φ a = Level.eval φ b) :
    Level.isEquiv a b ≠ some false := by
  intro hf
  by_cases hss : Level.simplify a = Level.simplify b
  · rw [Level.isEquiv, if_pos hss] at hf; exact nomatch hf
  rw [Level.isEquiv, if_neg hss] at hf
  cases hlr : Level.leq a b with
  | none => rw [hlr] at hf; exact nomatch hf
  | some bl =>
    cases bl with
    | false =>
      have hq : Level.leq a b = some false := hlr
      rw [Level.leq] at hq
      exact hc _ _ _ _ hq (sem_simplify_of_eval h)
    | true =>
      rw [hlr] at hf
      have hq : Level.leq b a = some false := by
        simpa using hf
      rw [Level.leq] at hq
      exact hc _ _ _ _ hq
        (sem_simplify_of_eval fun φ => (h φ).symm)

/-- **The checklist's usable form for the ten sites.**  Substitution
never turns a level guard's `true` into a `false`; the only thing it
can do is exhaust the fuel.  Conditional on the one residue. -/
theorem isEquiv_subst_ne_false (hc : LeqFalseComplete)
    (ks : List Name) (vs : List Level) {l r : Level}
    (h : Level.isEquiv l r = some true) :
    Level.isEquiv (Level.subst ks vs l) (Level.subst ks vs r)
      ≠ some false :=
  isEquiv_ne_false_of_eval hc (isEquiv_subst_eval ks vs h)

/-! ## The three sites the frozen statements do not even *fit*

Checking the table site by site turned up a shape error in it, not
only a truth-value.  At `iotaRec` (1311) and `projCert` (1371, 1376)
the two comparands are **not** both subject-side:

* `projCert` is called with
  `Level.subst entry.levelParams us entry.fieldSort` (and the same at
  `structSort`), where `entry.fieldSort` is *stored* and `us` are the
  scrutinee's level arguments;
* `iotaRec` compares `usj` against `recFireComparands`' first
  component, which is `lvls.map (Level.subst lps us)` or
  `cvjLps.map fun p => Level.subst lps us (.param p)`.

Instantiating the subject maps `Level.subst ks vs` over `us`, so the
right-hand comparand becomes `Level.subst ps (ws.map (Level.subst ks
vs)) r` — **not** `Level.subst ks vs (Level.subst ps ws r)`.  That is
the shape `piResultNeverZero_map_subst` and `isNeverZero_subst_map`
already have, and the frozen `IsEquivSubstMono` does not.  So those
three sites were never covered by the statement that was supposed to
settle them, independently of item 1's refutation.

The mapped statements are given here, refuted (they specialise to the
direct ones at `ws = ps.map .param`), and replaced by the semantic
form, which needs the two alignment facts the call sites check. -/

/-- The mapped congruence — the shape `projCert`'s two sites read. -/
def IsEquivSubstMonoMapped : Prop :=
  ∀ (ks : List Name) (vs : List Level) (ps : List Name)
    (ws : List Level) (l r : Level),
    Level.isEquiv l (Level.subst ps ws r) = some true →
    Level.isEquiv (Level.subst ks vs l)
        (Level.subst ps (ws.map (Level.subst ks vs)) r) = some true

/-- The mapped list congruence — the shape `iotaRec`'s site reads. -/
def IsEquivListSubstMonoMapped : Prop :=
  ∀ (ks : List Name) (vs : List Level) (ps : List Name)
    (ws : List Level) (ls rs : List Level),
    Level.isEquivList ls (rs.map (Level.subst ps ws)) = some true →
    Level.isEquivList (ls.map (Level.subst ks vs))
        (rs.map (Level.subst ps (ws.map (Level.subst ks vs))))
      = some true

/-- **The mapped forms are false too**, and for the same reason: at
`ws = ps.map .param` the substitution `Level.subst ps ws` is the
identity on the witness, so the mapped statement specialises to the
direct one. -/
theorem not_isEquivSubstMonoMapped : ¬ IsEquivSubstMonoMapped := by
  intro h
  have hid : Level.subst [seamA] [Level.param seamA]
      (.max (.param seamB) (.param seamA))
      = .max (.param seamB) (.param seamA) := by
    simp [Level.subst, Level.subst.go]
  have hw := h [seamA] [succN (9999 + 1)] [seamA] [.param seamA]
    (.max (.param seamA) (.param seamB))
    (.max (.param seamB) (.param seamA))
    (by rw [hid]; exact isEquiv_swap _ _ seamAB)
  rw [show Level.subst [seamA] [succN (9999 + 1)]
      (.max (.param seamA) (.param seamB))
      = .max (succN (9999 + 1)) (.param seamB) from by
        simp [Level.subst, Level.subst.go, seamAB],
    show Level.subst [seamA]
        ([Level.param seamA].map
          (Level.subst [seamA] [succN (9999 + 1)]))
        (.max (.param seamB) (.param seamA))
      = .max (.param seamB) (succN (9999 + 1)) from by
        simp [Level.subst, Level.subst.go, seamAB],
    isEquiv_swapN_none 9999 seamB (by decide)] at hw
  exact nomatch hw

/-- **The mapped semantic monotonicity**, which is what the three
sites actually get.  The two hypotheses are exactly what the call
sites check: `us.length = entry.levelParams.length` is tested inline
at `projCert`'s caller, and a stored sort's parameters lying among the
declaration's own `levelParams` is an environment invariant. -/
theorem isEquiv_subst_eval_mapped (ks : List Name) (vs : List Level)
    {ps : List Name} {ws : List Level} {l r : Level}
    (hlen : ws.length = ps.length)
    (hdef : r.allParamsDefined ps = true)
    (h : Level.isEquiv l (Level.subst ps ws r) = some true)
    (φ : Name → Nat) :
    Level.eval φ (Level.subst ks vs l)
      = Level.eval φ
        (Level.subst ps (ws.map (Level.subst ks vs)) r) := by
  rw [Level.eval_subst, Level.eval_subst,
    Level.isEquiv_sound h (Level.substFn φ ks vs), Level.eval_subst]
  exact Level.eval_ext hdef
    (fun p hp => (Level.substFn_map_subst hlen hp).symm)

/-! ## One site reads the gap as a verdict, not as an error

Twelve of the thirteen sites take their guard through `liftFueled`
(`Kernel/Core.lean:105`), which turns a `none` into
`throw (.internal "fuel exhausted: level comparison")` — the run
aborts, and no verdict is produced.  **`defeqSpine` (1694) does
not**:

```
match Level.isEquivList us us' with
| some true => defEqList r env depth a.getAppArgs b.getAppArgs
| _ => pure false
```

so there `none` is *indistinguishable from `some false`* — the
short-circuit is skipped and the caller falls back to unfolding both
sides.  At that one site the substituted run therefore takes a
**different branch** rather than erroring out, and the branch is final
whenever neither side unfolds (a constructor, an inductive, a
recursor).  So the guard as the site reads it does go `true → false`
under substitution, while `piResultNeverZero_flips` has the same
family going `false → true` elsewhere: taken together the seam is
**not** uniformly one-directional.

This is worth stating as a Bool, because `isEquiv_subst_ne_false`
(the usable repair) does **not** cover it: that repair excludes
`some false`, and here the branch is chosen by `≠ some true`. -/

/-- The guard exactly as `defeqSpine` reads it — `none` collapsed
into the `false` branch. -/
private def spineGuard (ls rs : List Level) : Bool :=
  match Level.isEquivList ls rs with
  | some true => true
  | _ => false

/-- **The `defeqSpine` guard flips `true → false` under
substitution.**  Not through a `some false` verdict — through the
fuel gap, which that site reads as `false`.  Same witness as item
2. -/
theorem spineGuard_flips_to_false :
    spineGuard [.max (.param seamA) (.param seamB)]
        [.max (.param seamB) (.param seamA)] = true ∧
      spineGuard
        ([Level.max (.param seamA) (.param seamB)].map
          (Level.subst [seamA] [succN (9999 + 1)]))
        ([Level.max (.param seamB) (.param seamA)].map
          (Level.subst [seamA] [succN (9999 + 1)])) = false := by
  constructor
  · rw [spineGuard, Level.isEquivList, isEquiv_swap _ _ seamAB]
    rfl
  · rw [show ([Level.max (.param seamA) (.param seamB)].map
        (Level.subst [seamA] [succN (9999 + 1)]))
      = [Level.max (succN (9999 + 1)) (.param seamB)] from by
        simp [Level.subst, Level.subst.go, seamAB],
      show ([Level.max (.param seamB) (.param seamA)].map
        (Level.subst [seamA] [succN (9999 + 1)]))
      = [Level.max (.param seamB) (succN (9999 + 1))] from by
        simp [Level.subst, Level.subst.go, seamAB]]
    rw [spineGuard, Level.isEquivList,
      isEquiv_swapN_none 9999 seamB (by decide)]
    rfl

/-! ## The thirteen sites, checked

| function | site | shape | verdict |
|---|---|---|---|
| `proofIrrel` | 786 | `isEquiv _ .zero` | **settled** (item 3) |
| `proofIrrel` | 790 | `isEquiv _ .zero` | **settled** (item 3) |
| `pairEtaCert` | 856 | `isEquivList` direct | refuted (item 2) |
| `structEtaCertWith` | 940 | `isEquivList` direct | refuted (item 2) |
| `majorToCtor` | 1153 | `piResultNeverZero` | settled (seal 19) |
| `iotaRec` | 1311 | `isEquivList` **mapped** | refuted; wrong shape |
| `projCert` | 1371 | `isEquiv` **mapped** | refuted; wrong shape |
| `projCert` | 1376 | `isEquiv` **mapped** | refuted; wrong shape |
| `defeqSpine` | 1694 | `isEquivList` direct | refuted; **flips** |
| `defeqStep` | 1816 | `isEquiv` direct | refuted (item 1) |
| `defeqStep` | 1858 | `isEquivList` direct | refuted (item 2) |
| `isPropType` | 1944 | `isEquiv _ .zero` | **settled** (item 3) |

"Direct" means both comparands are subject-side, so instantiation
substitutes both; "mapped" means the right one is a stored level read
at the subject's level arguments, so instantiation maps the
substitution over those arguments instead.

**So four of the thirteen are settled outright** (the three zero-tests
and `majorToCtor`), eight are settled only up to the `none` channel,
and one — `defeqSpine` — is not settled at all, because there the
`none` *is* the `false` branch (`spineGuard_flips_to_false`).

For the eight: they still *evaluate* equal after substitution
(`isEquiv_subst_eval`, `isEquivList_subst_evalEq`,
`isEquiv_subst_eval_mapped` — all unconditional), and they never
answer `false` given `LeqFalseComplete`.  Their failure mode is a
`throw (.internal …)`, i.e. exit 3, never a wrong verdict.

**What this does to the discharge target, stated without slack.**  The
crossing is an implication *uninstantiated success ⟹ instantiated
success*, so what it must exclude is the instantiated run doing
**less**.  The fuel gap does exactly that: it is not a harmless side
channel but a counterexample generator for the implication itself, at
nine of the thirteen sites.  Two consequences, and neither is what
seal 27 expected:

* **`LeqFalseComplete` does not repair the crossing.**  It says the
  substituted guard never answers `false`; it says nothing about
  `none`, and at the eight `liftFueled` sites `none` aborts the run.
  What it buys is the *verdict* reading — the two runs never reach
  contradictory answers — which is what rules out the "diverges
  irreconcilably" STOP.  An unconditional `WhnfInstLevelsUpTo` needs a
  **budget hypothesis** (the instantiating levels stay inside
  `Level.defaultFuel`), which no statement in the tree carries today.
* **`defeqSpine` needs more than a budget.**  There the fallback is a
  different *reduction path*, not an abort, so even with the residue
  the two runs can end at different reducts.  That is where the next
  piece of work belongs.

None of it is a soundness hole: every failure mode here makes the
checker do *less* (throw, or reject), never accept more.  It is the
crossing's own direction that the gap is on the wrong side of. -/

end Setlec.SetR.Interp2
