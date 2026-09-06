/-!
The K rescue runs on the *raw* major, before its whnf (the Mathlib
`decide`-over-`Rat` frontier, 2026-09-06).

The official kernel's `inductive_reduce_rec` (and lean4lean's
`Inductive/Reduce.lean`) converts the major of a K-flagged recursor
with `to_ctor_when_K` *first* — it reads only the major's type and
fabricates `Eq.refl` from it — and head-normalizes the major only
afterwards.  With the two steps in the other order the major, a
*theorem application*, is delta-unfolded and its proof term reduced:
here `k_major_raw_beq_true 604800` unfolds to a `Nat.rec` on the
literal, which iota-grinds down `604800` one `succ` per knot level —
fuel exhaustion (exit 3).  In the official order the fabricated
`Eq.refl (Nat.beq 604800 604800)` is checked against the major's type
(`Nat.beq 604800 604800 ≡ true`, one literal fold) and the proof is
never opened.  Minimal spelling of the `Eq.ndrec … (Int.decEq._proof_1
… (Nat.eq_of_beq_eq_true …))` shape `instDecidableEqRat` produces in
`Std.Time.Week.Offset.ofMilliseconds._proof_1` (record 126,329 of the
full Mathlib stream).
-/

/-- Structural recursion whose unfolding at a literal is a unary
`Nat.rec` descent. -/
theorem k_major_raw_beq_true (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- A `Nat` computed through an `Eq.rec` whose major is the theorem
applied to a large literal. -/
def k_major_raw_val : Nat :=
  @Eq.rec Bool (Nat.beq 604800 604800) (fun _ _ => Nat) 7 true
    (k_major_raw_beq_true 604800)

theorem k_major_raw : k_major_raw_val = 7 := rfl

--#export k_major_raw
